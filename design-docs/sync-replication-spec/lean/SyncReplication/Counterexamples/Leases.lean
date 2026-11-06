import SyncReplication.LeaseInvariant
import SyncReplication.Counterexamples.Basic

/-!
# What each lease rule prevents

Four runs on three nodes, each in the lease layer with one rule removed, each ending
in a stale linearizable read: a node that may serve a linearizable read whose log is
not the committed history.

- `noWaitPrim_stale`: a replica takes over without waiting out the primary's lease.
  The old primary still holds a valid lease from it and serves a read of a log that
  misses the new primary's committed write.
- `noWaitRead_stale`: the primary demotes a replica without waiting out its read
  lease, then commits without it. The replica still holds a valid read lease and
  serves a read that misses the write.
- `smallMargin_stale`: the margin is less than twice the drift. Every rule is kept,
  but the replica's wait ends while the old primary still believes its lease valid.
- `grantAny_stale`: the primary echoes acknowledgements to a replica that is not an
  eligible sync member, giving it a read lease; it then commits without it.

Lease parameters: primary lease 5, read lease 2, drift 1, margin 2 (`P0`); the margin
run uses margin 1 (`P1`). `min-sync-replicas = 0` throughout, so a primary may commit
alone. Time does not need to advance for the first two and the last; the margin run
ticks four times so that the takeover wait is satisfied.
-/

open Cslib

namespace SyncReplication

/-- Primary lease 5, read lease 2, drift 1, margin 2. -/
def P0 : LeaseParams := ⟨5, 2, 1, 2⟩
/-- As `P0` with margin 1, below twice the drift. -/
def P1 : LeaseParams := ⟨5, 2, 1, 1⟩

instance (P : LeaseParams) (a : LState N) (p : N) : Decidable (PrimLeaseValid P a p) := by
  unfold PrimLeaseValid; infer_instance
instance (P : LeaseParams) (a : LState N) (p : N) : Decidable (PrimCanRead P a p) := by
  unfold PrimCanRead; infer_instance
instance (P : LeaseParams) (a : LState N) (r : N) : Decidable (ReplCanRead P a r) := by
  unfold ReplCanRead ReadLeaseValid; infer_instance
instance (P : LeaseParams) (a : LState N) (p r : N) : Decidable (MayGrant P a p r) := by
  unfold MayGrant; infer_instance

/-- A run of the lease layer is a run of any weakening of it. -/
theorem lmtr_of_step {L : LTS (LState N) (LAction N)} {m : Nat} {P : LeaseParams}
    (hL : ∀ {a μ a'}, LStep m P a μ a' → L.Tr a μ a') {a b : LState N} {μs : List (LAction N)}
    (h : (llts m P).MTr a μs b) : L.MTr a μs b := by
  induction h with
  | refl => exact .refl
  | stepL hs _ ih => exact .stepL (hL hs) ih

/-! ## Shared prefix: both leases established

n0 counts n1 and makes it eligible; n1 learns the configuration; a heartbeat from n0
reaches n1 and n1 acknowledges it. n0 now holds a primary lease from n1 (from time 0),
and n0 has n1's acknowledgement to echo. -/

def l0 : LState N := linit 0
def l1 := withCore l0 (count l0.core 0 1)
def l2 := withCore l1 (makeEligible l1.core 0 1)
def l3 := learnL l2 1
def l4 := recvData l3 1 l3.core none
def l5 := recvAck l4 1 l4.core

/-- The prefix, for any lease parameters: none of its steps consults them. -/
theorem leases_prefix (P : LeaseParams) : (llts 0 P).MTr l0
    [.core (.count 0 1), .core (.makeEligible 0 1), .learn 1, .heartbeat 1, .ack 1] l5 :=
  .stepL (LStep.core l0 _ _ (Step.count l0.core 0 1 (by decide) (by decide) (by decide) (by decide)
    (by decide)) rfl) <|
  .stepL (LStep.core l1 _ _ (Step.makeEligible l1.core 0 1 (by decide) (by decide) (by decide)
    (by decide)) rfl) <|
  .stepL (LStep.learn l2 1 (by decide)) <|
  .stepL (LStep.heartbeat l3 1 (by decide) (by decide)) <|
  .stepL (LStep.ackRenew l4 1 (by decide) (by decide)) <|
  .refl

/-! ## Takeover without waiting out the primary lease -/

/-- `LStep`, plus a takeover with no wait. -/
inductive LStepNoWaitPrim (m : Nat) (P : LeaseParams) : LState N → LAction N → LState N → Prop
  | step {a μ a'} : LStep m P a μ a' → LStepNoWaitPrim m P a μ a'
  | takeover (a : LState N) (n : N) : KnowsLatest a.core n → a.core.cfg.eligible n = true →
      n ≠ a.core.cfg.primary → a.core.cfg.incarnation n = a.core.incarnation n →
      LStepNoWaitPrim m P a (.takeover n) (takeoverL a n)

def lltsNoWaitPrim (m : Nat) (P : LeaseParams) : LTS (LState N) (LAction N) where
  Tr := LStepNoWaitPrim m P

def lw6 := takeoverL l5 1                           -- n1 takes over at once
def lw7 := withCore lw6 (appendWrite lw6.core 1)      -- n1 writes
def lw8 := withCore lw7 (commitNext lw7.core 1)       -- n1 commits alone: the history is [3]

theorem noWaitPrim_run : (lltsNoWaitPrim 0 P0).MTr l0
    [.core (.count 0 1), .core (.makeEligible 0 1), .learn 1, .heartbeat 1, .ack 1,
     .takeover 1, .core (.append 1), .core (.commit 1)] lw8 :=
  LTS.MTr.comp (lltsNoWaitPrim 0 P0) (lmtr_of_step LStepNoWaitPrim.step (leases_prefix P0)) <|
  .stepL (LStepNoWaitPrim.takeover l5 1 (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (.step (LStep.core lw6 _ _ (Step.append lw6.core 1 (by decide) (writable_zero _ _) (by decide)) rfl)) <|
  .stepL (.step (LStep.core lw7 _ _ (Step.commit lw7.core 1 (by decide) (writable_zero _ _) (by decide)
    (by decide)) rfl)) <|
  .refl

/-- Without the takeover wait, the deposed n0 may still serve a linearizable read, and
its log misses the committed write. -/
theorem noWaitPrim_stale : ∃ a, (lltsNoWaitPrim 0 P0).CanReach (linit 0) a ∧
    PrimCanRead P0 a 0 ∧ a.core.log 0 ≠ a.core.hist :=
  ⟨lw8, ⟨_, noWaitPrim_run⟩, by decide, by decide⟩

/-! ## Demotion without waiting out the read lease -/

/-- `LStep`, plus a demotion with no wait. -/
inductive LStepNoWaitRead (m : Nat) (P : LeaseParams) : LState N → LAction N → LState N → Prop
  | step {a μ a'} : LStep m P a μ a' → LStepNoWaitRead m P a μ a'
  | demote (a : LState N) (p r : N) : ThinksPrimary a.core p → KnowsLatest a.core p →
      a.core.cfg.eligible r = true →
      LStepNoWaitRead m P a (.demote p r) (withCore a (makeIneligible a.core p r))

def lltsNoWaitRead (m : Nat) (P : LeaseParams) : LTS (LState N) (LAction N) where
  Tr := LStepNoWaitRead m P

def ld6 := recvData l5 1 l5.core (l5.ackEcho 0 1)     -- n0 echoes n1's acknowledgement: read lease
def ld7 := withCore ld6 (makeIneligible ld6.core 0 1)   -- n0 demotes n1 at once
def ld8 := withCore ld7 (appendWrite ld7.core 0)        -- n0 writes
def ld9 := withCore ld8 (commitNext ld8.core 0)         -- n0 commits alone: the history is [1]

theorem noWaitRead_run : (lltsNoWaitRead 0 P0).MTr l0
    [.core (.count 0 1), .core (.makeEligible 0 1), .learn 1, .heartbeat 1, .ack 1,
     .heartbeat 1, .demote 0 1, .core (.append 0), .core (.commit 0)] ld9 :=
  LTS.MTr.comp (lltsNoWaitRead 0 P0) (lmtr_of_step LStepNoWaitRead.step (leases_prefix P0)) <|
  .stepL (.step (LStep.heartbeatGrant l5 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (LStepNoWaitRead.demote ld6 0 1 (by decide) (by decide) (by decide)) <|
  .stepL (.step (LStep.core ld7 _ _ (Step.append ld7.core 0 (by decide) (writable_zero _ _) (by decide)) rfl)) <|
  .stepL (.step (LStep.core ld8 _ _ (Step.commit ld8.core 0 (by decide) (writable_zero _ _) (by decide)
    (by decide)) rfl)) <|
  .refl

/-- Without the demotion wait, the demoted n1 may still serve a linearizable read, and
its log misses the committed write. -/
theorem noWaitRead_stale : ∃ a, (lltsNoWaitRead 0 P0).CanReach (linit 0) a ∧
    ReplCanRead P0 a 1 ∧ a.core.log 1 ≠ a.core.hist :=
  ⟨ld9, ⟨_, noWaitRead_run⟩, by decide, by decide⟩

/-! ## A margin below twice the drift

With `P1`, every rule is in force. n1 waits until the primary lease must have expired
(four ticks), takes over, writes and commits. n0's clock may be a drift slow and n1's a
drift fast; with a margin of one, n0 still believes its lease valid. -/

def ls6 := tick l5
def ls7 := tick ls6
def ls8 := tick ls7
def ls9 := tick ls8                                   -- now = 4
def ls10 := takeoverL ls9 1                          -- n1's wait is satisfied: 0 + 5 ≤ 4 + 1
def ls11 := withCore ls10 (appendWrite ls10.core 1)
def ls12 := withCore ls11 (commitNext ls11.core 1)

theorem smallMargin_run : (llts 0 P1).MTr l0
    [.core (.count 0 1), .core (.makeEligible 0 1), .learn 1, .heartbeat 1, .ack 1,
     .tick, .tick, .tick, .tick, .takeover 1, .core (.append 1), .core (.commit 1)] ls12 :=
  LTS.MTr.comp (llts 0 P1) (leases_prefix P1) <|
  .stepL (LStep.tick l5) <| .stepL (LStep.tick ls6) <| .stepL (LStep.tick ls7) <| .stepL (LStep.tick ls8) <|
  .stepL (LStep.takeover ls9 1 (by decide) (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (LStep.core ls10 _ _ (Step.append ls10.core 1 (by decide) (writable_zero _ _) (by decide)) rfl) <|
  .stepL (LStep.core ls11 _ _ (Step.commit ls11.core 1 (by decide) (writable_zero _ _) (by decide)
    (by decide)) rfl) <|
  .refl

/-- `margin ≥ 2 · drift` is needed: with margin 1 and drift 1, and every rule kept, the
deposed n0 may serve a linearizable read of a log that misses the committed write. -/
theorem smallMargin_stale : ∃ a, LReachable 0 P1 (0 : N) a ∧
    PrimCanRead P1 a 0 ∧ a.core.log 0 ≠ a.core.hist :=
  ⟨ls12, ⟨_, smallMargin_run⟩, by decide, by decide⟩

/-! ## Granting a read lease to a replica that is not an eligible sync member -/

/-- `LStep`, plus an echo to any follower. -/
inductive LStepGrantAny (m : Nat) (P : LeaseParams) : LState N → LAction N → LState N → Prop
  | step {a μ a'} : LStep m P a μ a' → LStepGrantAny m P a μ a'
  | heartbeatGrant (a : LState N) (r : N) : primaryOf a.core r ≠ r →
      ThinksPrimary a.core (primaryOf a.core r) → a.core.log r <+: a.core.log (primaryOf a.core r) →
      PrimLeaseValid P a (primaryOf a.core r) →
      LStepGrantAny m P a (.heartbeat r) (recvData a r a.core (a.ackEcho (primaryOf a.core r) r))

def lltsGrantAny (m : Nat) (P : LeaseParams) : LTS (LState N) (LAction N) where
  Tr := LStepGrantAny m P

def lg1 := recvData l0 2 l0.core none                 -- a heartbeat reaches n2, which follows n0
def lg2 := recvAck lg1 2 lg1.core                       -- n2 acknowledges
def lg3 := recvData lg2 2 lg2.core (lg2.ackEcho 0 2)     -- n0 echoes it: n2 gets a read lease
def lg4 := withCore lg3 (appendWrite lg3.core 0)        -- n0 writes
def lg5 := withCore lg4 (commitNext lg4.core 0)         -- n0 commits alone: the history is [1]

theorem grantAny_run : (lltsGrantAny 0 P0).MTr l0
    [.heartbeat 2, .ack 2, .heartbeat 2, .core (.append 0), .core (.commit 0)] lg5 :=
  .stepL (.step (LStep.heartbeat l0 2 (by decide) (by decide))) <|
  .stepL (.step (LStep.ackRenew lg1 2 (by decide) (by decide))) <|
  .stepL (LStepGrantAny.heartbeatGrant lg2 2 (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (.step (LStep.core lg3 _ _ (Step.append lg3.core 0 (by decide) (writable_zero _ _) (by decide)) rfl)) <|
  .stepL (.step (LStep.core lg4 _ _ (Step.commit lg4.core 0 (by decide) (writable_zero _ _) (by decide)
    (by decide)) rfl)) <|
  .refl

/-- Read leases must go only to eligible sync members: a follower outside the sync set
that is granted one may serve a linearizable read of a log that misses the write. -/
theorem grantAny_stale : ∃ a, (lltsGrantAny 0 P0).CanReach (linit 0) a ∧
    ReplCanRead P0 a 2 ∧ a.core.log 2 ≠ a.core.hist :=
  ⟨lg5, ⟨_, grantAny_run⟩, by decide, by decide⟩

end SyncReplication
