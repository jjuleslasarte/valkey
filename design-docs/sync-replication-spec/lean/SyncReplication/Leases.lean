import SyncReplication.Safety

/-!
# Leases and linearizable reads

The replication model (`SyncReplication.Step`) plus the two leases of design §5, in
real time, and the rule for when a node may serve a linearizable read. The protocol
as modelled is described in prose in the README (§1, "Leases" and "Linearizable
reads"); the timing rules and the drift model in README §3.2 and `Lease/Additive.lean`.
The theorem, `SyncReplication.noStaleRead`, is in `LeaseInvariant.lean`.

## Encoding choices

- `now` is real time in ticks. A holder believes its lease valid while
  `now - start < dur - margin + drift` (its clock may run slow, `HolderValid`); a
  grantor's promise is over once `now - recv ≥ dur - drift` (its clock may run fast,
  `GrantorOver`). `None` as a lease start means "no lease".
- Messages are instant, as in the replication model. A lease's start is therefore
  the real time of the event it is measured from, which is the tightest case for a
  lease argument: delivery delay only widens the gap between the holder's expiry and
  the grantor's promise.
- A data message from the primary carries its committed offset and the echo of the
  replica's latest acknowledgement. `replicate` carries data without an echo; the
  echo rides on a separate `heartbeat`. Since a heartbeat may follow any data
  message immediately, this reaches the same states as putting the echo on both.
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

variable {Node : Type} [DecidableEq Node]

/-- The initial state: the replication model's initial state at time 0, no leases. -/
def leaseInit (i : Node) : LeaseState Node :=
  ⟨init i, 0, fun _ => 0, fun _ _ => none, fun _ _ => none, fun _ _ => none, fun _ => none,
   fun _ => 0, fun _ => 0, fun _ => none, fun _ _ => true⟩

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
  ∀ r, (a.core.known p).eligible r = true → r ≠ p → HolderValid P a.now (a.primaryLease p r) P.primDur

/-- `r` holds a valid read lease. -/
def ReadLeaseValid (P : LeaseParams) (a : LeaseState Node) (r : Node) : Prop :=
  HolderValid P a.now (a.readLease r) P.readDur

/-- `p` may renew `r`'s read lease: `p` still holds its primary lease (a deposed primary
stops granting, design §5 "Leases across a failover"), and `r` is a sync member that
is eligible with a matching incarnation in `p`'s configuration. -/
def MayGrant (P : LeaseParams) (a : LeaseState Node) (p r : Node) : Prop :=
  PrimLeaseValid P a p ∧ a.core.sync p r = true ∧ (a.core.known p).eligible r = true ∧
    (a.core.known p).incarnation r = a.core.incarnation r

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
           ackEcho := update2 a.ackEcho p r (some a.now) }

/-- `n` learns the latest configuration and restarts its takeover timer ("Takeover
timers restart on a configuration change"). -/
def learnL (a : LeaseState Node) (n : Node) : LeaseState Node :=
  { a with core := learn a.core n, primaryTraffic := update a.primaryTraffic n a.now }

/-- `n` takes over. It has heard nothing from its replicas as primary: no primary
lease, no acknowledgements; it holds no read lease; its primaryship starts now. -/
def takeoverL (a : LeaseState Node) (n : Node) : LeaseState Node :=
  { a with core := takeover a.core n,
           primarySince := update a.primarySince n (some a.now),
           oldEligible := update a.oldEligible n a.core.cfg.eligible,
           primaryLease := update a.primaryLease n (fun _ => none),
           ackReceived := update a.ackReceived n (fun _ => none),
           ackEcho := update a.ackEcho n (fun _ => none),
           readLease := update a.readLease n none }

/-- A full resync replaces `r`'s data; its committed view starts over. -/
def resyncL (a : LeaseState Node) (r : Node) : LeaseState Node :=
  { a with core := resync a.core r, committedView := update a.committedView r 0 }

/-- `n` restarts, with replication state `c` afterwards. Lease state is in memory, so
`n` loses its leases and its committed view, and its timers start afresh: it has just
"received traffic" (no takeover for one lease), and its primaryship, if any, starts
now (no demotion for one read lease plus the margin). `dataSent n := now` treats the
restart as traffic received now, so an acknowledgement before any new data gives the
primary a lease from the restart time, matching `primaryTraffic n`. -/
def restartL (a : LeaseState Node) (n : Node) (c : State Node) : LeaseState Node :=
  { a with core := c,
           committedView := update a.committedView n 0,
           primaryLease := update a.primaryLease n (fun _ => none),
           ackReceived := update a.ackReceived n (fun _ => none),
           ackEcho := update a.ackEcho n (fun _ => none),
           readLease := update a.readLease n none,
           primaryTraffic := update a.primaryTraffic n a.now,
           dataSent := update a.dataSent n a.now,
           primarySince := update a.primarySince n (some a.now),
           oldEligible := update a.oldEligible n (fun _ => true) }

/-- The replication actions that touch no lease state and keep their guards. -/
def Action.isPlain : Action Node → Bool
  | .append _ | .commit _ | .count _ _ | .uncount _ _ | .makeEligible _ _ => true
  | _ => false

/-- The actions of the lease layer. -/
inductive LeaseAction (Node : Type)
  | tick
  | core (μ : Action Node)
  | replicate (r : Node) | heartbeat (r : Node) | ack (r : Node)
  | learn (n : Node) | demote (p r : Node) | takeover (n : Node) | resync (r : Node)
  | restartEmpty (n : Node) | restartKeep (n : Node) | restartPartial (n : Node) (k : Nat)

/-- The step relation. `m` is `min-sync-replicas`, `P` the lease parameters. -/
inductive LeaseStep (m : Nat) (P : LeaseParams) : LeaseState Node → LeaseAction Node → LeaseState Node → Prop
  /-- Real time advances. -/
  | tick (a) : LeaseStep m P a .tick (tick a)
  /-- A replication action that touches no lease state: AppendWrite, Commit, Count,
  Uncount, MakeEligible, with their guards. -/
  | core (a μ c) : Step m a.core μ c → μ.isPlain = true → LeaseStep m P a (.core μ) (withCore a c)
  /-- A replica copies the next entry of its primary's log; the message carries the
  primary's committed offset. -/
  | replicate (a r) : primaryOf a.core r ≠ r → a.core.log r <+: a.core.log (primaryOf a.core r) →
      (a.core.log r).length < (a.core.log (primaryOf a.core r)).length →
      LeaseStep m P a (.replicate r) (recvData a r (replicate a.core r) none)
  /-- A heartbeat from the primary: committed offset, no echo. -/
  | heartbeat (a r) : primaryOf a.core r ≠ r → a.core.log r <+: a.core.log (primaryOf a.core r) →
      LeaseStep m P a (.heartbeat r) (recvData a r a.core none)
  /-- A heartbeat that echoes `r`'s latest acknowledgement, renewing its read lease. -/
  | heartbeatGrant (a r) : primaryOf a.core r ≠ r → ThinksPrimary a.core (primaryOf a.core r) →
      a.core.log r <+: a.core.log (primaryOf a.core r) → MayGrant P a (primaryOf a.core r) r →
      LeaseStep m P a (.heartbeat r) (recvData a r a.core (a.ackEcho (primaryOf a.core r) r))
  /-- An acknowledgement of new entries. -/
  | ack (a r) : primaryOf a.core r ≠ r → a.core.log r <+: a.core.log (primaryOf a.core r) →
      a.core.acked (primaryOf a.core r) r < (a.core.log r).length →
      LeaseStep m P a (.ack r) (recvAck a r (ack a.core r))
  /-- An acknowledgement that confirms nothing new (a heartbeat reply); it still renews
  the leases. -/
  | ackRenew (a r) : primaryOf a.core r ≠ r → a.core.log r <+: a.core.log (primaryOf a.core r) →
      LeaseStep m P a (.ack r) (recvAck a r a.core)
  /-- A node learns the latest configuration. -/
  | learn (a n) : ¬ KnowsLatest a.core n → LeaseStep m P a (.learn n) (learnL a n)
  /-- Demotion (design §4 and §5): the primary waits until the replica's read lease
  must have expired, measured from the last acknowledgement it received from it, and,
  for a replica of the configuration its takeover replaced, until one read lease plus
  the margin after that takeover. -/
  | demote (a p r) : ThinksPrimary a.core p → KnowsLatest a.core p → a.core.cfg.eligible r = true →
      GrantorOver P a.now (a.ackReceived p r) P.readDur →
      (∀ T, a.primarySince p = some T → a.oldEligible p r = true →
        T + P.readDur + P.margin ≤ a.now + P.drift) →
      LeaseStep m P a (.demote p r) (withCore a (makeIneligible a.core p r))
  /-- Takeover: the replica waits until the primary's lease must have expired, measured
  from the last traffic it received from the primary. -/
  | takeover (a n) : KnowsLatest a.core n → a.core.cfg.eligible n = true → n ≠ a.core.cfg.primary →
      a.core.cfg.incarnation n = a.core.incarnation n →
      a.primaryTraffic n + P.primDur ≤ a.now + P.drift →
      LeaseStep m P a (.takeover n) (takeoverL a n)
  /-- A full resync. -/
  | resync (a r) : primaryOf a.core r ≠ r → ¬ (a.core.log r <+: a.core.log (primaryOf a.core r)) →
      a.core.sync (primaryOf a.core r) r = false → (a.core.known (primaryOf a.core r)).eligible r = false →
      LeaseStep m P a (.resync r) (resyncL a r)
  /-- The restarts, each clearing the node's lease state. -/
  | restartEmpty (a n) : KnowsLatest a.core n → (∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      LeaseStep m P a (.restartEmpty n) (restartL a n (restartEmpty a.core n))
  | restartKeep (a n) : KnowsLatest a.core n →
      LeaseStep m P a (.restartKeep n) (restartL a n (restartKeep a.core n))
  | restartPartialKeep (a n k) : KnowsLatest a.core n → k < (a.core.log n).length → a.core.ackHigh n ≤ k →
      LeaseStep m P a (.restartPartial n k) (restartL a n (restartPartialKeep a.core n k))
  | restartPartialFresh (a n k) : KnowsLatest a.core n → k < (a.core.log n).length → k < a.core.ackHigh n →
      (∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      LeaseStep m P a (.restartPartial n k) (restartL a n (restartPartialFresh a.core n k))

/-- The lease layer as a labelled transition system. -/
def leaseLTS (m : Nat) (P : LeaseParams) : LTS (LeaseState Node) (LeaseAction Node) where
  Tr := LeaseStep m P

/-- The states reachable from `leaseInit i`. -/
def LeaseReachable (m : Nat) (P : LeaseParams) (i : Node) (a : LeaseState Node) : Prop :=
  (leaseLTS m P).CanReach (leaseInit i) a

end SyncReplication
