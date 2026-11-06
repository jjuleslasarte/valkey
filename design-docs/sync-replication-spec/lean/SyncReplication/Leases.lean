import SyncReplication.Safety

/-!
# Leases and linearizable reads

The replication model (`SyncReplication.Step`) plus the two leases of design §5, in
real time, and the rule for when a node may serve a linearizable read.

## In prose

Leases ride on replication traffic. A **primary lease** is held by the primary from
each eligible replica: it runs from when the primary sent the data an acknowledgement
confirms, and the replica promises not to take over until one lease duration after it
last received traffic from the primary. A **read lease** is held by a sync replica
from the primary: it runs from when the replica sent the acknowledgement that a
`REPLCONF COMMIT` echoes, and the primary promises not to commit without that replica
until one lease duration after it last received an acknowledgement from it.

A primary may serve a linearizable read while it holds a valid primary lease from
every eligible replica it knows of and has nothing uncommitted. A sync replica may
serve one while it holds a valid read lease and has nothing uncommitted.

The theorem (`SyncReplication.noStaleRead`, in `LeaseInvariant.lean`): whenever a
node may serve a linearizable read, its log is exactly the committed history. It
needs the clock-drift margin to be at least twice the drift bound.

## Time and clocks

`now` is real time in ticks. Nodes read local monotonic clocks; over one lease
interval the local elapsed time differs from the real one by at most `drift`. Each
side takes its worst case: a holder believes its lease valid while
`now - start < dur - margin + drift` (its clock may run slow), a grantor's promise is
over once `now - recv ≥ dur - drift` (its clock may run fast). `margin` is the
clock-drift margin the design subtracts; `Lease/Additive.lean` proves these two
worst cases are the right reading of the design's drift model.

## Encoding choices

- Messages are instant, as in the replication model. A lease's start is therefore
  the real time of the event it is measured from, which is the tightest case for a
  lease argument: delivery delay only widens the gap between the holder's expiry and
  the grantor's promise.
- A data message from the primary carries its committed offset and the echo of the
  replica's latest acknowledgement. `replicate` carries data without an echo; the
  echo rides on a separate `heartbeat`. Since a heartbeat may follow any data
  message immediately, this reaches the same states as putting the echo on both.
- Lease state is in memory: every restart clears the node's leases and starts its
  takeover timer and its demotion timer afresh (the design's "a node that restarts
  waits one full lease duration before it attempts a takeover or serves reads under a
  lease", applied to demotion too, see `tko`).
- `None` as a lease start means "no lease".
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
structure LState (Node : Type) [DecidableEq Node] where
  /-- The replication state. -/
  core     : State Node
  /-- Real time. -/
  now      : Nat
  /-- `rview r`: the committed offset replica `r` has been told of (`REPLCONF COMMIT`).
  A replica serves reads from here. -/
  rview    : Node → Nat
  /-- `pl p r`: the start of the primary lease `p` holds from `r`: the send time of the
  data `r` last acknowledged to `p`. -/
  pl       : Node → Node → Option Nat
  /-- `ackRecv p r`: when `p` last received an acknowledgement from `r`. `p` as grantor
  of `r`'s read lease measures its promise from here. -/
  ackRecv  : Node → Node → Option Nat
  /-- `ackEcho p r`: the send time of the acknowledgement from `r` that `p` will echo
  in its next `REPLCONF COMMIT`. -/
  ackEcho  : Node → Node → Option Nat
  /-- `rl r`: the start of the read lease `r` holds: the send time of its acknowledgement
  that the primary echoed. -/
  rl       : Node → Option Nat
  /-- `primRecv r`: when `r` last received traffic from its primary, or learned a new
  configuration, or restarted. `r` as grantor of the primary lease measures its
  promise from here. -/
  primRecv : Node → Nat
  /-- `dataT r`: the send time of the latest data `r` received. The next
  acknowledgement confirms it, and the primary's lease from `r` starts there. -/
  dataT    : Node → Nat
  /-- `tko p`: when `p`'s current primaryship began on this node, by takeover or by a
  restart. A primary does not demote a replica until one read lease plus the margin
  after this. -/
  tko      : Node → Option Nat

variable {Node : Type} [DecidableEq Node]

/-- The initial state: the replication model's initial state at time 0, no leases. -/
def linit (i : Node) : LState Node :=
  ⟨init i, 0, fun _ => 0, fun _ _ => none, fun _ _ => none, fun _ _ => none, fun _ => none,
   fun _ => 0, fun _ => 0, fun _ => none⟩

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
def PrimLeaseValid (P : LeaseParams) (a : LState Node) (p : Node) : Prop :=
  ∀ r, (a.core.known p).eligible r = true → r ≠ p → HolderValid P a.now (a.pl p r) P.primDur

/-- `r` holds a valid read lease. -/
def ReadLeaseValid (P : LeaseParams) (a : LState Node) (r : Node) : Prop :=
  HolderValid P a.now (a.rl r) P.readDur

/-- `p` may renew `r`'s read lease: `p` still holds its primary lease (a deposed primary
stops granting, design §5 "Leases across a failover"), and `r` is a sync member that
is eligible with a matching incarnation in `p`'s configuration. -/
def MayGrant (P : LeaseParams) (a : LState Node) (p r : Node) : Prop :=
  PrimLeaseValid P a p ∧ a.core.sync p r = true ∧ (a.core.known p).eligible r = true ∧
    (a.core.known p).incarnation r = a.core.incarnation r

/-! ### The read rule -/

/-- A primary may serve a linearizable read: it thinks it is primary, holds its
primary lease from every eligible replica it knows, and has nothing uncommitted. -/
def PrimCanRead (P : LeaseParams) (a : LState Node) (p : Node) : Prop :=
  ThinksPrimary a.core p ∧ PrimLeaseValid P a p ∧ a.core.commit p = (a.core.log p).length

/-- A sync replica may serve a linearizable read: it does not think it is primary,
holds a valid read lease, and has nothing uncommitted (its committed view covers its
whole log). -/
def ReplCanRead (P : LeaseParams) (a : LState Node) (r : Node) : Prop :=
  ¬ ThinksPrimary a.core r ∧ ReadLeaseValid P a r ∧ a.rview r = (a.core.log r).length

/-- No stale linearizable read: whenever a node may serve one, its log is exactly the
committed history, so the value it returns is the latest committed value. -/
def NoStaleRead (P : LeaseParams) (a : LState Node) : Prop :=
  (∀ p, PrimCanRead P a p → a.core.log p = a.core.hist) ∧
  (∀ r, ReplCanRead P a r → a.core.log r = a.core.hist)

/-! ### Post-states -/

/-- Time advances by one tick. -/
def tick (a : LState Node) : LState Node := { a with now := a.now + 1 }

/-- A replication step that touches no lease state. -/
def withCore (a : LState Node) (c : State Node) : LState Node := { a with core := c }

/-- `r` receives a data message from its primary, carrying the primary's committed
offset and, if `echo` is set, the echo of `r`'s acknowledgement. `c` is the replication
state after the data is applied. `r`'s view advances to the committed offset, capped by
its log; it records the traffic; its read lease starts at the echo if that is later. -/
def recvData (a : LState Node) (r : Node) (c : State Node) (echo : Option Nat) : LState Node :=
  { a with core := c,
           rview := update a.rview r
             (max (a.rview r) (min (a.core.commit (primaryOf a.core r)) (c.log r).length)),
           primRecv := update a.primRecv r a.now,
           dataT := update a.dataT r a.now,
           rl := match echo with
                 | none => a.rl
                 | some e => update a.rl r (some (maxOpt (a.rl r) e)) }

/-- `r`'s primary receives an acknowledgement from `r`. `c` is the replication state
after it. The primary's lease from `r` starts at the send time of the data `r`
confirms; it records when it received the acknowledgement and when `r` sent it. -/
def recvAck (a : LState Node) (r : Node) (c : State Node) : LState Node :=
  let p := primaryOf a.core r
  { a with core := c,
           pl := update2 a.pl p r (some (maxOpt (a.pl p r) (a.dataT r))),
           ackRecv := update2 a.ackRecv p r (some a.now),
           ackEcho := update2 a.ackEcho p r (some a.now) }

/-- `n` learns the latest configuration and restarts its takeover timer ("Takeover
timers restart on a configuration change"). -/
def learnL (a : LState Node) (n : Node) : LState Node :=
  { a with core := learn a.core n, primRecv := update a.primRecv n a.now }

/-- `n` takes over. It has heard nothing from its replicas as primary: no primary
lease, no acknowledgements; it holds no read lease; its primaryship starts now. -/
def takeoverL (a : LState Node) (n : Node) : LState Node :=
  { a with core := takeover a.core n,
           tko := update a.tko n (some a.now),
           pl := update a.pl n (fun _ => none),
           ackRecv := update a.ackRecv n (fun _ => none),
           ackEcho := update a.ackEcho n (fun _ => none),
           rl := update a.rl n none }

/-- A full resync replaces `r`'s data; its committed view starts over. -/
def resyncL (a : LState Node) (r : Node) : LState Node :=
  { a with core := resync a.core r, rview := update a.rview r 0 }

/-- `n` restarts, with replication state `c` afterwards. Lease state is in memory, so
`n` loses its leases and its committed view, and its timers start afresh: it has just
"received traffic" (no takeover for one lease), and its primaryship, if any, starts
now (no demotion for one read lease plus the margin). -/
def restartL (a : LState Node) (n : Node) (c : State Node) : LState Node :=
  { a with core := c,
           rview := update a.rview n 0,
           pl := update a.pl n (fun _ => none),
           ackRecv := update a.ackRecv n (fun _ => none),
           ackEcho := update a.ackEcho n (fun _ => none),
           rl := update a.rl n none,
           primRecv := update a.primRecv n a.now,
           dataT := update a.dataT n a.now,
           tko := update a.tko n (some a.now) }

/-- The replication actions that touch no lease state and keep their guards. -/
def Action.isPlain : Action Node → Bool
  | .append _ | .commit _ | .count _ _ | .uncount _ _ | .makeEligible _ _ => true
  | _ => false

/-- The actions of the lease layer. -/
inductive LAction (Node : Type)
  | tick
  | core (μ : Action Node)
  | replicate (r : Node) | heartbeat (r : Node) | ack (r : Node)
  | learn (n : Node) | demote (p r : Node) | takeover (n : Node) | resync (r : Node)
  | restartEmpty (n : Node) | restartKeep (n : Node) | restartPartial (n : Node) (k : Nat)

/-- The step relation. `m` is `min-sync-replicas`, `P` the lease parameters. -/
inductive LStep (m : Nat) (P : LeaseParams) : LState Node → LAction Node → LState Node → Prop
  /-- Real time advances. -/
  | tick (a) : LStep m P a .tick (tick a)
  /-- A replication action that touches no lease state: AppendWrite, Commit, Count,
  Uncount, MakeEligible, with their guards. -/
  | core (a μ c) : Step m a.core μ c → μ.isPlain = true → LStep m P a (.core μ) (withCore a c)
  /-- A replica copies the next entry of its primary's log; the message carries the
  primary's committed offset. -/
  | replicate (a r) : primaryOf a.core r ≠ r → a.core.log r <+: a.core.log (primaryOf a.core r) →
      (a.core.log r).length < (a.core.log (primaryOf a.core r)).length →
      LStep m P a (.replicate r) (recvData a r (replicate a.core r) none)
  /-- A heartbeat from the primary: committed offset, no echo. -/
  | heartbeat (a r) : primaryOf a.core r ≠ r → a.core.log r <+: a.core.log (primaryOf a.core r) →
      LStep m P a (.heartbeat r) (recvData a r a.core none)
  /-- A heartbeat that echoes `r`'s latest acknowledgement, renewing its read lease. -/
  | heartbeatGrant (a r) : primaryOf a.core r ≠ r → ThinksPrimary a.core (primaryOf a.core r) →
      a.core.log r <+: a.core.log (primaryOf a.core r) → MayGrant P a (primaryOf a.core r) r →
      LStep m P a (.heartbeat r) (recvData a r a.core (a.ackEcho (primaryOf a.core r) r))
  /-- An acknowledgement of new entries. -/
  | ack (a r) : primaryOf a.core r ≠ r → a.core.log r <+: a.core.log (primaryOf a.core r) →
      a.core.acked (primaryOf a.core r) r < (a.core.log r).length →
      LStep m P a (.ack r) (recvAck a r (ack a.core r))
  /-- An acknowledgement that confirms nothing new (a heartbeat reply); it still renews
  the leases. -/
  | ackRenew (a r) : primaryOf a.core r ≠ r → a.core.log r <+: a.core.log (primaryOf a.core r) →
      LStep m P a (.ack r) (recvAck a r a.core)
  /-- A node learns the latest configuration. -/
  | learn (a n) : ¬ KnowsLatest a.core n → LStep m P a (.learn n) (learnL a n)
  /-- Demotion (design §4 and §5): the primary waits until the replica's read lease
  must have expired, measured from the last acknowledgement it received from it, and,
  as a new primary, until one read lease plus the margin after its takeover. -/
  | demote (a p r) : ThinksPrimary a.core p → KnowsLatest a.core p → a.core.cfg.eligible r = true →
      GrantorOver P a.now (a.ackRecv p r) P.readDur →
      (∀ T, a.tko p = some T → T + P.readDur + P.margin ≤ a.now + P.drift) →
      LStep m P a (.demote p r) (withCore a (makeIneligible a.core p r))
  /-- Takeover: the replica waits until the primary's lease must have expired, measured
  from the last traffic it received from the primary. -/
  | takeover (a n) : KnowsLatest a.core n → a.core.cfg.eligible n = true → n ≠ a.core.cfg.primary →
      a.core.cfg.incarnation n = a.core.incarnation n →
      a.primRecv n + P.primDur ≤ a.now + P.drift →
      LStep m P a (.takeover n) (takeoverL a n)
  /-- A full resync. -/
  | resync (a r) : primaryOf a.core r ≠ r → ¬ (a.core.log r <+: a.core.log (primaryOf a.core r)) →
      a.core.sync (primaryOf a.core r) r = false → (a.core.known (primaryOf a.core r)).eligible r = false →
      LStep m P a (.resync r) (resyncL a r)
  /-- The restarts, each clearing the node's lease state. -/
  | restartEmpty (a n) : KnowsLatest a.core n → (∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      LStep m P a (.restartEmpty n) (restartL a n (restartEmpty a.core n))
  | restartKeep (a n) : KnowsLatest a.core n →
      LStep m P a (.restartKeep n) (restartL a n (restartKeep a.core n))
  | restartPartialKeep (a n k) : KnowsLatest a.core n → k < (a.core.log n).length → a.core.ackHigh n ≤ k →
      LStep m P a (.restartPartial n k) (restartL a n (restartPartialKeep a.core n k))
  | restartPartialFresh (a n k) : KnowsLatest a.core n → k < (a.core.log n).length → k < a.core.ackHigh n →
      (∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      LStep m P a (.restartPartial n k) (restartL a n (restartPartialFresh a.core n k))

/-- The lease layer as a labelled transition system. -/
def llts (m : Nat) (P : LeaseParams) : LTS (LState Node) (LAction Node) where
  Tr := LStep m P

/-- The states reachable from `linit i`. -/
def LReachable (m : Nat) (P : LeaseParams) (i : Node) (a : LState Node) : Prop :=
  (llts m P).CanReach (linit i) a

end SyncReplication
