import SyncReplication.Safety

/-!
# Leases and linearizable reads

The replication model (`SyncReplication.Step`, replication delayed) plus the two leases of design §5, in
real time, and the rule for when a node may serve a linearizable read. The protocol
as modelled is described in prose in the README (§1, "Leases" and "Linearizable
reads"); the timing rules and the drift model in README §3.2 and `Lease/Additive.lean`.
The theorem, `SyncReplication.noStaleRead`, is in `LeaseInvariant.lean`.

## Encoding choices

- `now` is real time in ticks. A holder believes its lease valid while
  `now - start < dur - margin + drift` (its clock may run slow, `HolderValid`); a
  grantor's promise is over once `now - recv ≥ dur - drift` (its clock may run fast,
  `GrantorOver`). `None` as a lease start means "no lease".
- Lease messages are delayed. A `REPLCONF COMMIT` from a primary to a replica
  (`Msg.data`: send time, the primary's committed offset, and optionally the echo of
  the replica's acknowledgement) and an acknowledgement from a replica (`Msg.ack`:
  send time, and the send time of the data it confirms) go into `net` when sent, and
  are delivered later, in any order, or never (`drop`). Delay is unbounded. Log
  entries and acknowledged offsets travel separately, as `Step`'s replication messages
  (`rnet`), which the lease layer takes as core actions.
- Each lease connection has a generation (`gen p r`, from primary `p` to replica `r`).
  A message records its connection's when sent and is delivered only while it is
  unchanged: a planned demotion's drop request closes that one connection, a learn of a
  different primary closes the node's connections to its primary; a restart,
  a takeover, a resync, or learning a configuration with a different primary closes
  the node's connections, as Valkey drops the link.
- The instant lease layer, in which every lease message is delivered in the step that
  sends it, is `InstantLeaseStep`. `instant_simulates` shows each of its steps is a run of
  `LeaseStep`, so everything reachable with instant messages is reachable here.
- Lease state is in memory: every restart clears the node's leases and committed view
  and restarts its takeover timer and its demotion timer (`primarySince`). For reads
  the model only clears the leases, so a restarted node may read as soon as it holds
  a new one; the proof shows that suffices.
- After a takeover, the one-read-lease-plus-margin wait blocks demotion only of
  replicas of the configuration the takeover replaced (`oldEligible`), as the design
  says. After a restart it blocks demotion of every replica: the node has forgotten
  which configuration it took over from.
-/

open Cslib

namespace SyncReplication

/-- A lease message in flight. `src` sent it to `dst`; `g` is the generation of their
connection when it was sent. -/
inductive Msg (Node : Type)
  /-- `REPLCONF COMMIT` from primary `src` to replica `dst`, sent at `sent`, carrying
  `src`'s committed offset and, if set, the echo of `dst`'s acknowledgement. -/
  | data (src dst : Node) (g sent commit : Nat) (echo : Option Nat)
  /-- An acknowledgement from replica `src` to primary `dst`, sent at `sent`, confirming
  data that `dst` sent at `dataSent`. -/
  | ack (src dst : Node) (g sent dataSent : Nat)
  /-- A planned demotion: primary `src` asks replica `dst` to drop its read lease. -/
  | dropReq (src dst : Node) (g sent : Nat)
  /-- Replica `src` tells primary `dst` it has dropped its read lease. -/
  | dropAck (src dst : Node) (g sent : Nat)
  deriving DecidableEq

/-- The sender of a message. -/
def Msg.src {Node : Type} : Msg Node → Node
  | .data p _ _ _ _ _ => p
  | .ack r _ _ _ _ => r
  | .dropReq p _ _ _ => p
  | .dropAck r _ _ _ => r
/-- The receiver of a message. -/
def Msg.dst {Node : Type} : Msg Node → Node
  | .data _ r _ _ _ _ => r
  | .ack _ p _ _ _ => p
  | .dropReq _ r _ _ => r
  | .dropAck _ p _ _ => p
/-- The connection's generation at the send. -/
def Msg.g {Node : Type} : Msg Node → Nat
  | .data _ _ g _ _ _ => g
  | .ack _ _ g _ _ => g
  | .dropReq _ _ g _ => g
  | .dropAck _ _ g _ => g
/-- A message's connection: its primary end and its replica end. -/
def Msg.link {Node : Type} : Msg Node → Node × Node
  | .data p r _ _ _ _ => (p, r)
  | .ack r p _ _ _ => (p, r)
  | .dropReq p r _ _ => (p, r)
  | .dropAck r p _ _ => (p, r)
/-- The send time. -/
def Msg.sent {Node : Type} : Msg Node → Nat
  | .data _ _ _ t _ _ => t
  | .ack _ _ _ t _ => t
  | .dropReq _ _ _ t => t
  | .dropAck _ _ _ t => t
/-- The echo a `REPLCONF COMMIT` carries: the start of the read lease it renews. -/
def Msg.echo {Node : Type} : Msg Node → Option Nat
  | .data _ _ _ _ _ e => e
  | _ => none
/-- The start of the primary lease an acknowledgement gives: the send time of the data
it confirms. -/
def Msg.ackStart {Node : Type} : Msg Node → Option Nat
  | .ack _ _ _ _ d => some d
  | _ => none
/-- The committed offset a `REPLCONF COMMIT` carries. -/
def Msg.commitOf {Node : Type} : Msg Node → Option Nat
  | .data _ _ _ _ c _ => some c
  | _ => none

/-- The lease parameters: the two durations, the drift bound and the margin. -/
structure LeaseParams where
  /-- Duration of the primary lease. -/
  primDur : Nat
  /-- Duration of the replica read lease. -/
  readDur : Nat
  /-- Bound on how far a local clock drifts from real time over one lease. -/
  drift   : Nat
  /-- The clock-drift margin the holder subtracts. -/
  margin  : Nat

/-- The replication state plus real time, each replica's committed view, and the lease
timestamps. -/
structure LeaseState (Node : Type) [DecidableEq Node] where
  /-- The replication state. -/
  core     : State Node
  /-- Real time. -/
  now      : Nat
  /-- `committedView r`: the committed offset replica `r` has been told of (`REPLCONF COMMIT`).
  A replica serves reads from here. -/
  committedView    : Node → Nat
  /-- `primaryLease p r`: the start of the primary lease `p` holds from `r`: the send time of the
  data `r` last acknowledged to `p`. -/
  primaryLease       : Node → Node → Option Nat
  /-- `ackReceived p r`: when `p` last received an acknowledgement from `r`. `p` as grantor
  of `r`'s read lease measures its promise from here. -/
  ackReceived  : Node → Node → Option Nat
  /-- `ackEcho p r`: the send time of the acknowledgement from `r` that `p` will echo
  in its next `REPLCONF COMMIT`. -/
  ackEcho  : Node → Node → Option Nat
  /-- `readLease r`: the start of the read lease `r` holds: the send time of its acknowledgement
  that the primary echoed. -/
  readLease       : Node → Option Nat
  /-- `primaryTraffic r`: when `r` last received traffic from its primary, or learned a new
  configuration, or restarted. `r` as grantor of the primary lease measures its
  promise from here. -/
  primaryTraffic : Node → Nat
  /-- `dataSent r`: the send time of the latest data `r` received. The next
  acknowledgement confirms it, and the primary's lease from `r` starts there. -/
  dataSent    : Node → Nat
  /-- `primarySince p`: when `p`'s current primaryship began on this node, by takeover or by a
  restart. A primary does not demote a replica until one read lease plus the margin
  after this. -/
  primarySince      : Node → Option Nat
  /-- `oldEligible p r`: `r` was eligible in the configuration `p`'s takeover replaced
  ("a replica from the old configuration", design §5). After a restart, which forgets
  this, every replica counts as old. -/
  oldEligible : Node → Node → Bool
  /-- The lease messages in flight. -/
  net : List (Msg Node)
  /-- `gen p r`: the generation of the lease connection from `p` to `r`. It goes up when
  the connection closes, which discards every message on it still in flight. -/
  gen : Node → Node → Nat
  /-- `dropConfirmed p r`: `r` has confirmed to `p` that it dropped its read lease, and `p`
  has received no acknowledgement from `r` since it asked. `p` may then demote `r`
  without waiting out the lease (a planned demotion, design §4). -/
  dropConfirmed : Node → Node → Bool

variable {Node : Type} [DecidableEq Node]

/-- The initial state: the replication model's initial state at time 0, no leases. -/
def leaseInit (i : Node) : LeaseState Node :=
  ⟨init i, 0, fun _ => 0, fun _ _ => none, fun _ _ => none, fun _ _ => none, fun _ => none,
   fun _ => 0, fun _ => 0, fun _ => none, fun _ _ => true, [], fun _ _ => 0, fun _ _ => false⟩

/-- A message is current while its connection has not closed since it was sent. -/
def Msg.Current (a : LeaseState Node) (m : Msg Node) : Prop :=
  a.gen m.link.1 m.link.2 = m.g

instance (a : LeaseState Node) (m : Msg Node) : Decidable (m.Current a) := by
  unfold Msg.Current; infer_instance


/-- The later of a lease start and a new candidate. -/
def maxOpt (x : Option Nat) (y : Nat) : Nat :=
  match x with
  | none => y
  | some v => max v y

/-- Update of a two-argument function at one pair. -/
def update2 {β : Type} (f : Node → Node → β) (p r : Node) (b : β) : Node → Node → β :=
  update f p (update (f p) r b)

/-! ### Lease validity -/

/-- The holder believes a lease that started at `start` with duration `dur` is still
valid: in real time, `now - start < dur - margin + drift`. No start, no lease. -/
def HolderValid (P : LeaseParams) (now : Nat) (start : Option Nat) (dur : Nat) : Prop :=
  match start with
  | none => False
  | some t0 => now + P.margin < t0 + dur + P.drift

/-- The grantor's promise, measured from `recv`, is over: `now - recv ≥ dur - drift`.
Nothing received, nothing promised. -/
def GrantorOver (P : LeaseParams) (now : Nat) (recv : Option Nat) (dur : Nat) : Prop :=
  match recv with
  | none => True
  | some t0 => t0 + dur ≤ now + P.drift

instance (P : LeaseParams) (now : Nat) (start : Option Nat) (dur : Nat) :
    Decidable (HolderValid P now start dur) := by
  unfold HolderValid; split <;> infer_instance
instance (P : LeaseParams) (now : Nat) (recv : Option Nat) (dur : Nat) :
    Decidable (GrantorOver P now recv dur) := by
  unfold GrantorOver; split <;> infer_instance

/-- `p` holds a valid primary lease from every eligible replica in the configuration it
knows. -/
def PrimLeaseValid (P : LeaseParams) (a : LeaseState Node) (p : Node) : Prop :=
  ∀ r, (a.core.localCfg p).eligible r = true → r ≠ p → HolderValid P a.now (a.primaryLease p r) P.primDur

/-- `r` holds a valid read lease. -/
def ReadLeaseValid (P : LeaseParams) (a : LeaseState Node) (r : Node) : Prop :=
  HolderValid P a.now (a.readLease r) P.readDur

/-- `p` may renew `r`'s read lease: `p` still holds its primary lease (a deposed primary
stops granting, design §5 "Leases across a failover"), and `r` is a sync member that
is eligible with a matching incarnation in `p`'s configuration. -/
def MayGrant (P : LeaseParams) (a : LeaseState Node) (p r : Node) : Prop :=
  PrimLeaseValid P a p ∧ a.core.sync p r = true ∧ (a.core.localCfg p).eligible r = true ∧
    (a.core.localCfg p).incarnation r = a.core.incarnation r

/-! ### The read rule -/

/-- A primary may serve a linearizable read: it thinks it is primary, holds its
primary lease from every eligible replica it knows, and has nothing uncommitted. -/
def PrimCanRead (P : LeaseParams) (a : LeaseState Node) (p : Node) : Prop :=
  ThinksPrimary a.core p ∧ PrimLeaseValid P a p ∧ a.core.commit p = (a.core.log p).length

/-- A sync replica may serve a linearizable read: it does not think it is primary,
holds a valid read lease, and has nothing uncommitted (its committed view covers its
whole log). -/
def ReplCanRead (P : LeaseParams) (a : LeaseState Node) (r : Node) : Prop :=
  ¬ ThinksPrimary a.core r ∧ ReadLeaseValid P a r ∧ a.committedView r = (a.core.log r).length

/-- No stale linearizable read: whenever a node may serve one, its log is exactly the
committed history, so the value it returns is the latest committed value. -/
def NoStaleRead (P : LeaseParams) (a : LeaseState Node) : Prop :=
  (∀ p, PrimCanRead P a p → a.core.log p = a.core.hist) ∧
  (∀ r, ReplCanRead P a r → a.core.log r = a.core.hist)

/-! ### Post-states -/

/-- Time advances by one tick. -/
def tick (a : LeaseState Node) : LeaseState Node := { a with now := a.now + 1 }

/-- A replication step that touches no lease state. -/
def withCore (a : LeaseState Node) (c : State Node) : LeaseState Node := { a with core := c }

/-- `r` receives a data message from its primary, carrying the primary's committed
offset and, if `echo` is set, the echo of `r`'s acknowledgement. `c` is the replication
state after the data is applied. `r`'s view advances to the committed offset, capped by
its log; it records the traffic; its read lease starts at the echo if that is later. -/
def recvData (a : LeaseState Node) (r : Node) (c : State Node) (echo : Option Nat) : LeaseState Node :=
  { a with core := c,
           committedView := update a.committedView r
             (max (a.committedView r) (min (a.core.commit (primaryOf a.core r)) (c.log r).length)),
           primaryTraffic := update a.primaryTraffic r a.now,
           dataSent := update a.dataSent r a.now,
           readLease := match echo with
                 | none => a.readLease
                 | some e => update a.readLease r (some (maxOpt (a.readLease r) e)) }

/-- `r`'s primary receives an acknowledgement from `r`. `c` is the replication state
after it. The primary's lease from `r` starts at the send time of the data `r`
confirms; it records when it received the acknowledgement and when `r` sent it. -/
def recvAck (a : LeaseState Node) (r : Node) (c : State Node) : LeaseState Node :=
  let p := primaryOf a.core r
  { a with core := c,
           primaryLease := update2 a.primaryLease p r (some (maxOpt (a.primaryLease p r) (a.dataSent r))),
           ackReceived := update2 a.ackReceived p r (some a.now),
           ackEcho := update2 a.ackEcho p r (some a.now),
           dropConfirmed := update2 a.dropConfirmed p r false }

/-- `n` learns the latest configuration and restarts its takeover timer ("Takeover
timers restart on a configuration change"). If its primary changes, its connection to
its old primary closes; its own replicas stay connected. -/
def leaseLearn (a : LeaseState Node) (n : Node) : LeaseState Node :=
  { a with core := learn a.core n, primaryTraffic := update a.primaryTraffic n a.now,
           gen := if a.core.cfg.primary = (a.core.localCfg n).primary then a.gen else closeInto a.gen n }

/-- `n` takes over. It has heard nothing from its replicas as primary: no primary
lease, no acknowledgements; it holds no read lease; its primaryship starts now. -/
def leaseTakeover (a : LeaseState Node) (n : Node) : LeaseState Node :=
  { a with core := takeover a.core n,
           primarySince := update a.primarySince n (some a.now),
           oldEligible := update a.oldEligible n a.core.cfg.eligible,
           primaryLease := update a.primaryLease n (fun _ => none),
           ackReceived := update a.ackReceived n (fun _ => none),
           ackEcho := update a.ackEcho n (fun _ => none),
           readLease := update a.readLease n none,
           gen := closeAll a.gen n,
           dropConfirmed := update a.dropConfirmed n (fun _ => false) }

/-- A full resync replaces `r`'s data; its committed view starts over. -/
def leaseResync (a : LeaseState Node) (r : Node) : LeaseState Node :=
  { a with core := resync a.core r, committedView := update a.committedView r 0,
           gen := closeAll a.gen r }

/-- `n` restarts, with replication state `c` afterwards. Lease state is in memory, so
`n` loses its leases and its committed view, and its timers start afresh: it has just
"received traffic" (no takeover for one lease), and its primaryship, if any, starts
now (no demotion for one read lease plus the margin). `dataSent n := now` treats the
restart as traffic received now, so an acknowledgement before any new data gives the
primary a lease from the restart time, matching `primaryTraffic n`. -/
def leaseRestart (a : LeaseState Node) (n : Node) (c : State Node) : LeaseState Node :=
  { a with core := c,
           committedView := update a.committedView n 0,
           primaryLease := update a.primaryLease n (fun _ => none),
           ackReceived := update a.ackReceived n (fun _ => none),
           ackEcho := update a.ackEcho n (fun _ => none),
           readLease := update a.readLease n none,
           primaryTraffic := update a.primaryTraffic n a.now,
           dataSent := update a.dataSent n a.now,
           primarySince := update a.primarySince n (some a.now),
           oldEligible := update a.oldEligible n (fun _ => true),
           gen := closeAll a.gen n }

/-- A message is sent. -/
def send (a : LeaseState Node) (msg : Msg Node) : LeaseState Node := { a with net := msg :: a.net }

/-- A message is lost. -/
def dropMsg (a : LeaseState Node) (msg : Msg Node) : LeaseState Node := { a with net := a.net.erase msg }

/-- `REPLCONF COMMIT` `msg`, sent at `t` with committed offset `c` and echo `e`, reaches
replica `r`. As `recvData`, with the message's committed offset, and with the data's
send time `t` in place of now. -/
def deliverData (a : LeaseState Node) (msg : Msg Node) (r : Node) (t c : Nat) (e : Option Nat) :
    LeaseState Node :=
  { a with net := a.net.erase msg,
           committedView := update a.committedView r (max (a.committedView r) (min c (a.core.log r).length)),
           primaryTraffic := update a.primaryTraffic r a.now,
           dataSent := update a.dataSent r t,
           readLease := match e with
                 | none => a.readLease
                 | some e => update a.readLease r (some (maxOpt (a.readLease r) e)) }

/-- Acknowledgement `msg` from `r`, sent at `t` and confirming data sent at `d`, reaches
`p`. As `recvAck`: `p`'s lease from `r` starts at `d`; `p` records the receipt now and
will echo the acknowledgement's send time. -/
def deliverAck (a : LeaseState Node) (msg : Msg Node) (r p : Node) (t d : Nat) : LeaseState Node :=
  { a with net := a.net.erase msg,
           primaryLease := update2 a.primaryLease p r (some (maxOpt (a.primaryLease p r) d)),
           ackReceived := update2 a.ackReceived p r (some a.now),
           ackEcho := update2 a.ackEcho p r (some t),
           dropConfirmed := update2 a.dropConfirmed p r false }

/-- `p` asks `r` to drop its read lease (planned demotion). `p` stops echoing `r`'s
acknowledgements until a new one arrives, and closes and reopens its connection to `r`,
which discards every message on it still in flight; the request goes on the new
connection. -/
def sendDropRequest (a : LeaseState Node) (p r : Node) : LeaseState Node :=
  send { a with ackEcho := update2 a.ackEcho p r none, gen := closeLink a.gen p r }
    (.dropReq p r (a.gen p r + 1) a.now)

/-- Drop request `msg` from `p` reaches `r`: `r` drops its read lease and confirms. -/
def deliverDropRequest (a : LeaseState Node) (msg : Msg Node) (r p : Node) : LeaseState Node :=
  send { a with net := a.net.erase msg, readLease := update a.readLease r none }
    (.dropAck r p (a.gen p r) a.now)

/-- Confirmation `msg` from `r` reaches `p`. -/
def deliverDropConfirm (a : LeaseState Node) (msg : Msg Node) (p r : Node) : LeaseState Node :=
  { a with net := a.net.erase msg, dropConfirmed := update2 a.dropConfirmed p r true }

/-- The replication actions that the lease layer takes as they are: those that touch no
lease state, and the replication messages, whose lease effects travel separately as
lease messages. -/
def Action.isCore : Action Node → Bool
  | .append _ | .commit _ | .addToSyncSet _ _ | .removeFromSyncSet _ _
  | .makeEligible _ _ => true
  | .psync _ | .sendData _ _ | .sendAck _ | .deliver _ | .dropMsg _ => true
  | .replicate _ | .ack _ | .makeIneligible _ _ | .learn _ | .takeover _ | .resync _
  | .restartEmpty _ | .restartKeep _ | .restartPartial _ _ => false

/-- The actions of the lease layer. -/
inductive LeaseAction (Node : Type)
  | tick
  | core (μ : Action Node)
  | heartbeat (r : Node) | ack (r : Node)
  | learn (n : Node) | demote (p r : Node) | takeover (n : Node) | resync (r : Node)
  | restartEmpty (n : Node) | restartKeep (n : Node) | restartPartial (n : Node) (k : Nat)
  | sendData (p r : Node) | sendAck (r : Node) | deliver (msg : Msg Node) | drop (msg : Msg Node)
  | sendDropRequest (p r : Node)

/-- The lease layer with instant lease messages: every lease message is delivered in the
step that sends it. `instant_simulates` shows each step is a run of `LeaseStep`. -/
inductive InstantLeaseStep (m : Nat) (P : LeaseParams) : LeaseState Node → LeaseAction Node → LeaseState Node → Prop
  /-- Real time advances. -/
  | tick (a) : InstantLeaseStep m P a .tick (tick a)
  /-- A replication action that touches no lease state, with its guards: AppendWrite,
  Commit, AddToSyncSet, RemoveFromSyncSet, MakeEligible, and the replication messages. -/
  | core (a μ c) : Step m a.core μ c → μ.isCore = true → InstantLeaseStep m P a (.core μ) (withCore a c)
  /-- A heartbeat from the primary: committed offset, no echo. -/
  | heartbeat (a r) : primaryOf a.core r ≠ r → StreamOpen a.core (primaryOf a.core r) r →
      InstantLeaseStep m P a (.heartbeat r) (recvData a r a.core none)
  /-- A heartbeat that echoes `r`'s latest acknowledgement, renewing its read lease. -/
  | heartbeatGrant (a r) : primaryOf a.core r ≠ r → ThinksPrimary a.core (primaryOf a.core r) →
      StreamOpen a.core (primaryOf a.core r) r → MayGrant P a (primaryOf a.core r) r →
      InstantLeaseStep m P a (.heartbeat r) (recvData a r a.core (a.ackEcho (primaryOf a.core r) r))
  /-- A lease acknowledgement (a heartbeat reply); it renews the leases. -/
  | ackRenew (a r) : primaryOf a.core r ≠ r → InstantLeaseStep m P a (.ack r) (recvAck a r a.core)
  /-- A node learns the latest configuration. -/
  | learn (a n) : (hStale : ¬ KnowsLatest a.core n) → InstantLeaseStep m P a (.learn n) (leaseLearn a n)
  /-- Demotion (design §4 and §5): the primary waits until the replica's read lease
  must have expired, measured from the last acknowledgement it received from it, and,
  for a replica of the configuration its takeover replaced, until one read lease plus
  the margin after that takeover. -/
  | demote (a p r) : (hThinksPrimary : ThinksPrimary a.core p) → (hKnowsLatest : KnowsLatest a.core p) → (hEligible : a.core.cfg.eligible r = true) →
      GrantorOver P a.now (a.ackReceived p r) P.readDur →
      (∀ T, a.primarySince p = some T → a.oldEligible p r = true →
        T + P.readDur + P.margin ≤ a.now + P.drift) →
      InstantLeaseStep m P a (.demote p r) (withCore a (makeIneligible a.core p r))
  /-- Takeover: the replica waits until the primary's lease must have expired, measured
  from the last traffic it received from the primary. -/
  | takeover (a n) : (hKnowsLatest : KnowsLatest a.core n) → (hEligible : a.core.cfg.eligible n = true) → (hNotPrimary : n ≠ a.core.cfg.primary) →
      a.core.cfg.incarnation n = a.core.incarnation n →
      a.primaryTraffic n + P.primDur ≤ a.now + P.drift →
      InstantLeaseStep m P a (.takeover n) (leaseTakeover a n)
  /-- A full resync. -/
  | resync (a r) : primaryOf a.core r ≠ r →
      a.core.sync (primaryOf a.core r) r = false → (a.core.localCfg (primaryOf a.core r)).eligible r = false →
      InstantLeaseStep m P a (.resync r) (leaseResync a r)
  /-- The restarts, each clearing the node's lease state. -/
  | restartEmpty (a n) : (hKnowsLatest : KnowsLatest a.core n) → (hSurvivor : ∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      InstantLeaseStep m P a (.restartEmpty n) (leaseRestart a n (restartEmpty a.core n))
  | restartKeep (a n) : (hKnowsLatest : KnowsLatest a.core n) →
      InstantLeaseStep m P a (.restartKeep n) (leaseRestart a n (restartKeep a.core n))
  | restartPartialKeep (a n k) : (hKnowsLatest : KnowsLatest a.core n) → (hFileShorter : k < (a.core.log n).length) → (hCoversAcks : a.core.ackHigh n ≤ k) →
      InstantLeaseStep m P a (.restartPartial n k) (leaseRestart a n (restartPartialKeep a.core n k))
  | restartPartialFresh (a n k) : (hKnowsLatest : KnowsLatest a.core n) → (hFileShorter : k < (a.core.log n).length) → (hMissesAcks : k < a.core.ackHigh n) →
      (∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      InstantLeaseStep m P a (.restartPartial n k) (leaseRestart a n (restartPartialFresh a.core n k))

/-- The step relation. `m` is `min-sync-replicas`, `P` the lease parameters. Lease
messages go through `net`: a send adds one, a delivery takes any current one, in any
order, at any later time, and a drop loses one. -/
inductive LeaseStep (m : Nat) (P : LeaseParams) : LeaseState Node → LeaseAction Node → LeaseState Node → Prop
  /-- Real time advances. -/
  | tick (a) : LeaseStep m P a .tick (tick a)
  /-- A replication action whose lease effects, if any, travel as lease messages:
  AppendWrite, Commit, AddToSyncSet, RemoveFromSyncSet, MakeEligible, and the replication
  messages, with their guards. -/
  | core (a μ c) : Step m a.core μ c → μ.isCore = true → LeaseStep m P a (.core μ) (withCore a c)
  /-- `p` sends `REPLCONF COMMIT` to a replica that follows it: its committed offset, no echo. -/
  | sendData (a p r) : (hNotSelf : p ≠ r) → (hFollows : primaryOf a.core r = p) →
      LeaseStep m P a (.sendData p r)
        (send a (.data p r (a.gen p r) a.now (a.core.commit p) none))
  /-- `p` sends `REPLCONF COMMIT` echoing `r`'s latest acknowledgement, renewing its read
  lease. The grant is checked when it is sent. -/
  | sendGrant (a p r) : (hNotSelf : p ≠ r) → (hFollows : primaryOf a.core r = p) →
      (hThinksPrimary : ThinksPrimary a.core p) → (hMayGrant : MayGrant P a p r) →
      LeaseStep m P a (.sendData p r)
        (send a (.data p r (a.gen p r) a.now (a.core.commit p) (a.ackEcho p r)))
  /-- A replica acknowledges to its primary the data it last received. -/
  | sendAck (a r) : (hNotSelf : primaryOf a.core r ≠ r) →
      LeaseStep m P a (.sendAck r)
        (send a (.ack r (primaryOf a.core r) (a.gen (primaryOf a.core r) r) a.now (a.dataSent r)))
  /-- A current `REPLCONF COMMIT` reaches a replica that still follows its sender, on the
  replication connection whose PSYNC the sender accepted. -/
  | deliverData (a p r g t c e) : (hIn : Msg.data p r g t c e ∈ a.net) →
      (hCurrent : (Msg.data p r g t c e).Current a) → (hFollows : primaryOf a.core r = p) →
      (hStream : StreamOpen a.core p r) →
      LeaseStep m P a (.deliver (.data p r g t c e)) (deliverData a (.data p r g t c e) r t c e)
  /-- A current acknowledgement reaches the primary it was sent to. -/
  | deliverAck (a r p g t d) : (hIn : Msg.ack r p g t d ∈ a.net) →
      (hCurrent : (Msg.ack r p g t d).Current a) →
      LeaseStep m P a (.deliver (.ack r p g t d)) (deliverAck a (.ack r p g t d) r p t d)
  /-- A message is lost. -/
  | drop (a msg) : (hIn : msg ∈ a.net) → LeaseStep m P a (.drop msg) (dropMsg a msg)
  /-- A node learns the latest configuration. -/
  | learn (a n) : (hStale : ¬ KnowsLatest a.core n) → LeaseStep m P a (.learn n) (leaseLearn a n)
  /-- Demotion (design §4 and §5): the primary waits until the replica's read lease
  must have expired, measured from the last acknowledgement it received from it, and,
  for a replica of the configuration its takeover replaced, until one read lease plus
  the margin after that takeover. Or, for a planned demotion, it has the replica's
  confirmation that it dropped its lease. -/
  | demote (a p r) : (hThinksPrimary : ThinksPrimary a.core p) → (hKnowsLatest : KnowsLatest a.core p) → (hEligible : a.core.cfg.eligible r = true) →
      (hWaited : (GrantorOver P a.now (a.ackReceived p r) P.readDur ∧
        ∀ T, a.primarySince p = some T → a.oldEligible p r = true →
          T + P.readDur + P.margin ≤ a.now + P.drift) ∨ a.dropConfirmed p r = true) →
      LeaseStep m P a (.demote p r) (withCore a (makeIneligible a.core p r))
  /-- A primary asks a replica that follows it to drop its read lease. -/
  | sendDropRequest (a p r) : (hNotSelf : p ≠ r) → (hFollows : primaryOf a.core r = p) →
      (hThinksPrimary : ThinksPrimary a.core p) →
      LeaseStep m P a (.sendDropRequest p r) (sendDropRequest a p r)
  /-- A current drop request reaches the replica. -/
  | deliverDropRequest (a p r g t) : (hIn : Msg.dropReq p r g t ∈ a.net) →
      (hCurrent : (Msg.dropReq p r g t).Current a) →
      LeaseStep m P a (.deliver (.dropReq p r g t)) (deliverDropRequest a (.dropReq p r g t) r p)
  /-- A current confirmation reaches the primary, which has received no acknowledgement
  from the replica since it asked. -/
  | deliverDropConfirm (a r p g t) : (hIn : Msg.dropAck r p g t ∈ a.net) →
      (hCurrent : (Msg.dropAck r p g t).Current a) → (hNoAck : a.ackEcho p r = none) →
      LeaseStep m P a (.deliver (.dropAck r p g t)) (deliverDropConfirm a (.dropAck r p g t) p r)
  /-- Takeover: the replica waits until the primary's lease must have expired, measured
  from the last traffic it received from the primary. -/
  | takeover (a n) : (hKnowsLatest : KnowsLatest a.core n) → (hEligible : a.core.cfg.eligible n = true) → (hNotPrimary : n ≠ a.core.cfg.primary) →
      a.core.cfg.incarnation n = a.core.incarnation n →
      a.primaryTraffic n + P.primDur ≤ a.now + P.drift →
      LeaseStep m P a (.takeover n) (leaseTakeover a n)
  /-- A full resync. -/
  | resync (a r) : primaryOf a.core r ≠ r →
      a.core.sync (primaryOf a.core r) r = false → (a.core.localCfg (primaryOf a.core r)).eligible r = false →
      LeaseStep m P a (.resync r) (leaseResync a r)
  /-- The restarts, each clearing the node's lease state and closing its connections. -/
  | restartEmpty (a n) : (hKnowsLatest : KnowsLatest a.core n) → (hSurvivor : ∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      LeaseStep m P a (.restartEmpty n) (leaseRestart a n (restartEmpty a.core n))
  | restartKeep (a n) : (hKnowsLatest : KnowsLatest a.core n) →
      LeaseStep m P a (.restartKeep n) (leaseRestart a n (restartKeep a.core n))
  | restartPartialKeep (a n k) : (hKnowsLatest : KnowsLatest a.core n) → (hFileShorter : k < (a.core.log n).length) → (hCoversAcks : a.core.ackHigh n ≤ k) →
      LeaseStep m P a (.restartPartial n k) (leaseRestart a n (restartPartialKeep a.core n k))
  | restartPartialFresh (a n k) : (hKnowsLatest : KnowsLatest a.core n) → (hFileShorter : k < (a.core.log n).length) → (hMissesAcks : k < a.core.ackHigh n) →
      (∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      LeaseStep m P a (.restartPartial n k) (leaseRestart a n (restartPartialFresh a.core n k))

/-- The lease layer as a labelled transition system. -/
def leaseTransitionSystem (m : Nat) (P : LeaseParams) : LTS (LeaseState Node) (LeaseAction Node) where
  Tr := LeaseStep m P

/-- The instant lease layer as a labelled transition system. -/
def instantTransitionSystem (m : Nat) (P : LeaseParams) : LTS (LeaseState Node) (LeaseAction Node) where
  Tr := InstantLeaseStep m P

/-- The states reachable from `leaseInit i`. -/
def LeaseReachable (m : Nat) (P : LeaseParams) (i : Node) (a : LeaseState Node) : Prop :=
  (leaseTransitionSystem m P).CanReach (leaseInit i) a

end SyncReplication
