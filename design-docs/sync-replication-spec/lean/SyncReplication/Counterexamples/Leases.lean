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

instance (P : LeaseParams) (a : LeaseState N) (p : N) : Decidable (PrimLeaseValid P a p) := by
  unfold PrimLeaseValid; infer_instance
instance (P : LeaseParams) (a : LeaseState N) (p : N) : Decidable (PrimCanRead P a p) := by
  unfold PrimCanRead; infer_instance
instance (P : LeaseParams) (a : LeaseState N) (r : N) : Decidable (ReplCanRead P a r) := by
  unfold ReplCanRead ReadLeaseValid; infer_instance
instance (P : LeaseParams) (a : LeaseState N) (p r : N) : Decidable (MayGrant P a p r) := by
  unfold MayGrant; infer_instance

/-- A run of the lease layer is a run of any weakening of it. -/
theorem leaseMtr_of_step {L : LTS (LeaseState N) (LeaseAction N)} {m : Nat} {P : LeaseParams}
    (hL : ∀ {a μ a'}, LeaseStep m P a μ a' → L.Tr a μ a') {a b : LeaseState N} {μs : List (LeaseAction N)}
    (h : (leaseLTS m P).MTr a μs b) : L.MTr a μs b := by
  induction h with
  | refl => exact .refl
  | stepL hs _ ih => exact .stepL (hL hs) ih

/-! ## Shared prefix: both leases established

n0 counts n1 and makes it eligible; n1 learns the configuration; a heartbeat from n0
reaches n1 and n1 acknowledges it. n0 now holds a primary lease from n1 (from time 0),
and n0 has n1's acknowledgement to echo. -/

def l0 : LeaseState N := leaseInit 0
def l1 := withCore l0 (count l0.core 0 1)
def l2 := withCore l1 (makeEligible l1.core 0 1)
def l3 := leaseLearn l2 1
def l4 := recvData l3 1 l3.core none
def l5 := recvAck l4 1 l4.core

/-- The prefix, for any lease parameters: none of its steps consults them. -/
theorem leases_prefix (P : LeaseParams) : (leaseLTS 0 P).MTr l0
    [.core (.count 0 1), .core (.makeEligible 0 1), .learn 1, .heartbeat 1, .ack 1] l5 :=
  .stepL (LeaseStep.core l0 _ _ (Step.count l0.core 0 1 (by decide) (by decide) (by decide) (by decide)
    (by decide)) rfl) <|
  .stepL (LeaseStep.core l1 _ _ (Step.makeEligible l1.core 0 1 (by decide) (by decide) (by decide)
    (by decide)) rfl) <|
  .stepL (LeaseStep.learn l2 1 (by decide)) <|
  .stepL (LeaseStep.heartbeat l3 1 (by decide) (by decide)) <|
  .stepL (LeaseStep.ackRenew l4 1 (by decide) (by decide)) <|
  .refl

/-! ## The read rule is not vacuous

In the protocol itself (no rule removed), both halves of `NoStaleRead` have a reachable
state in which their premise holds, so the theorem says something. -/

/-- After the prefix, n0 holds a valid primary lease from the eligible n1 and may serve a
linearizable read. -/
theorem primCanRead_reachable : ∃ a, LeaseReachable 0 P0 (0 : N) a ∧
    PrimCanRead P0 a 0 ∧ (a.core.known 0).eligible 1 = true :=
  ⟨l5, ⟨_, leases_prefix P0⟩, by decide, by decide⟩

def l6 := recvData l5 1 l5.core (l5.ackEcho 0 1)   -- n0 echoes n1's acknowledgement

/-- After one echo, n1 holds a valid read lease and may serve a linearizable read. -/
theorem replCanRead_reachable : ∃ a, LeaseReachable 0 P0 (0 : N) a ∧ ReplCanRead P0 a 1 :=
  ⟨l6, ⟨_, LTS.MTr.comp (leaseLTS 0 P0) (leases_prefix P0)
    (.stepL (LeaseStep.heartbeatGrant l5 1 (by decide) (by decide) (by decide) (by decide)) .refl)⟩,
   by decide⟩

/-! ## A new primary may demote a replica it promoted itself, inside the window

The post-takeover wait applies only to replicas of the configuration the takeover
replaced. A replica the new primary promoted afterwards can be demoted as soon as its
own read lease has expired. This run reaches such a demotion with no tick after the
takeover, which the earlier blanket wait forbade. -/

def ln6 := leaseLearn l5 2                               -- n2 learns the configuration
def ln7 := tick ln6
def ln8 := tick ln7
def ln9 := tick ln8
def ln10 := tick ln9                                -- now = 4
def ln11 := leaseTakeover ln10 1                         -- n1 takes over (0 + 5 ≤ 4 + 1)
def ln12 := leaseLearn ln11 2                            -- n2 learns it and follows n1
def ln13 := withCore ln12 (count ln12.core 1 2)      -- n1 counts n2
def ln14 := withCore ln13 (makeEligible ln13.core 1 2)  -- n1 makes n2 eligible: not of the old configuration
def ln15 := withCore ln14 (makeIneligible ln14.core 1 2) -- n1 demotes n2 at once: n2 never held a lease

theorem demoteNew_run : (leaseLTS 0 P0).MTr l0
    [.core (.count 0 1), .core (.makeEligible 0 1), .learn 1, .heartbeat 1, .ack 1,
     .learn 2, .tick, .tick, .tick, .tick, .takeover 1, .learn 2, .core (.count 1 2),
     .core (.makeEligible 1 2), .demote 1 2] ln15 :=
  LTS.MTr.comp (leaseLTS 0 P0) (leases_prefix P0) <|
  .stepL (LeaseStep.learn l5 2 (by decide)) <|
  .stepL (LeaseStep.tick ln6) <| .stepL (LeaseStep.tick ln7) <| .stepL (LeaseStep.tick ln8) <|
  .stepL (LeaseStep.tick ln9) <|
  .stepL (LeaseStep.takeover ln10 1 (by decide) (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (LeaseStep.learn ln11 2 (by decide)) <|
  .stepL (LeaseStep.core ln12 _ _ (Step.count ln12.core 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide)) rfl) <|
  .stepL (LeaseStep.core ln13 _ _ (Step.makeEligible ln13.core 1 2 (by decide) (by decide) (by decide)
    (by decide)) rfl) <|
  .stepL (LeaseStep.demote ln14 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)) <|
  .refl

/-- The design's behaviour is reachable: a new primary demotes a replica it promoted
itself without waiting out the post-takeover window. -/
theorem demoteNew_reachable : ∃ a, LeaseReachable 0 P0 (0 : N) a ∧
    a.core.cfg.primary = 1 ∧ a.core.cfg.eligible 2 = false ∧ a.primarySince 1 = some a.now :=
  ⟨ln15, ⟨_, demoteNew_run⟩, by decide, by decide, by decide⟩

/-! ## Granting a read lease to a sync member that is not yet eligible

Early removal (`uncount`) drops a counted, not-yet-eligible replica with no read-lease
wait. So if such a replica could be granted a read lease, the primary could drop it and
commit without it while the lease is still valid. -/

/-- `LeaseStep`, plus an echo to any sync member, eligible or not. -/
inductive LeaseStepGrantSync (m : Nat) (P : LeaseParams) : LeaseState N → LeaseAction N → LeaseState N → Prop
  | step {a μ a'} : LeaseStep m P a μ a' → LeaseStepGrantSync m P a μ a'
  | heartbeatGrant (a : LeaseState N) (r : N) : primaryOf a.core r ≠ r →
      ThinksPrimary a.core (primaryOf a.core r) → a.core.log r <+: a.core.log (primaryOf a.core r) →
      PrimLeaseValid P a (primaryOf a.core r) → a.core.sync (primaryOf a.core r) r = true →
      LeaseStepGrantSync m P a (.heartbeat r) (recvData a r a.core (a.ackEcho (primaryOf a.core r) r))

def leaseLTSGrantSync (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepGrantSync m P

def lu1 := withCore l0 (count l0.core 0 2)          -- n0 counts n2, which stays ineligible
def lu2 := recvData lu1 2 lu1.core none              -- a heartbeat reaches n2
def lu3 := recvAck lu2 2 lu2.core                    -- n2 acknowledges
def lu4 := recvData lu3 2 lu3.core (lu3.ackEcho 0 2) -- n0 echoes it: n2 gets a read lease
def lu5 := withCore lu4 (uncount lu4.core 0 2)       -- n0 drops n2 at once (early removal)
def lu6 := withCore lu5 (appendWrite lu5.core 0)     -- n0 writes
def lu7 := withCore lu6 (commitNext lu6.core 0)      -- n0 commits alone: the history is [1]

theorem grantSync_run : (leaseLTSGrantSync 0 P0).MTr l0
    [.core (.count 0 2), .heartbeat 2, .ack 2, .heartbeat 2, .core (.uncount 0 2),
     .core (.append 0), .core (.commit 0)] lu7 :=
  .stepL (.step (LeaseStep.core l0 _ _ (Step.count l0.core 0 2 (by decide) (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.heartbeat lu1 2 (by decide) (by decide))) <|
  .stepL (.step (LeaseStep.ackRenew lu2 2 (by decide) (by decide))) <|
  .stepL (LeaseStepGrantSync.heartbeatGrant lu3 2 (by decide) (by decide) (by decide) (by decide)
    (by decide)) <|
  .stepL (.step (LeaseStep.core lu4 _ _ (Step.uncount lu4.core 0 2 (by decide) (by decide) (by decide)
    (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core lu5 _ _ (Step.append lu5.core 0 (by decide) (writable_zero _ _)
    (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core lu6 _ _ (Step.commit lu6.core 0 (by decide) (writable_zero _ _)
    (by decide) (by decide)) rfl)) <|
  .refl

/-- Read leases must go only to *eligible* sync members: a counted replica that is not
yet eligible can be dropped by early removal without a wait, and then serve a stale
read on the lease it was granted. -/
theorem grantSync_stale : ∃ a, (leaseLTSGrantSync 0 P0).CanReach (leaseInit 0) a ∧
    ReplCanRead P0 a 2 ∧ a.core.log 2 ≠ a.core.hist :=
  ⟨lu7, ⟨_, grantSync_run⟩, by decide, by decide⟩

/-! ## Granting a read lease to an eligible sync member with a stale incarnation

A replica that restarted empty stays listed as eligible until demoted, and may be
counted again once it catches up. It is not authoritative: a takeover does not count it
and so never waits for it. If it could be granted a read lease, a new primary could
commit without it while the lease is still valid.

The run uses `P3`: primary lease 6, read lease 3, drift 1, margin 2, which satisfies
the design's "Lease durations" rule (`readDur + margin < primDur`) and the margin bound.
The grant must come as late as the granting primary's own lease allows: at time `g` the
primary needs `g + margin < traffic + primDur + drift` from the future taker, and the
taker may move once `traffic + primDur ≤ T + drift`, so the gap between grant and
takeover is only `margin - 2 · drift`. With integer ticks the stale read then needs
`readDur ≥ 3` and nothing about `primDur`. -/

/-- Primary lease 6, read lease 3, drift 1, margin 2: within the design's duration rule. -/
def P3 : LeaseParams := ⟨6, 3, 1, 2⟩

/-- `LeaseStep`, plus an echo to any eligible sync member, matching incarnation or not. -/
inductive LeaseStepGrantNoInc (m : Nat) (P : LeaseParams) : LeaseState N → LeaseAction N → LeaseState N → Prop
  | step {a μ a'} : LeaseStep m P a μ a' → LeaseStepGrantNoInc m P a μ a'
  | heartbeatGrant (a : LeaseState N) (r : N) : primaryOf a.core r ≠ r →
      ThinksPrimary a.core (primaryOf a.core r) → a.core.log r <+: a.core.log (primaryOf a.core r) →
      PrimLeaseValid P a (primaryOf a.core r) → a.core.sync (primaryOf a.core r) r = true →
      (a.core.known (primaryOf a.core r)).eligible r = true →
      LeaseStepGrantNoInc m P a (.heartbeat r) (recvData a r a.core (a.ackEcho (primaryOf a.core r) r))

def leaseLTSGrantNoInc (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepGrantNoInc m P

def li1 := withCore l0 (count l0.core 0 1)          -- n0 counts n1
def li2 := withCore li1 (makeEligible li1.core 0 1) -- n1 eligible (version 2)
def li3 := withCore li2 (count li2.core 0 2)        -- n0 counts n2
def li4 := withCore li3 (makeEligible li3.core 0 2) -- n2 eligible (version 3)
def li5 := leaseLearn li4 1                             -- n1 learns version 3
def li6 := leaseLearn li5 2                             -- n2 learns version 3; its takeover timer starts at 0
def li7 := recvData li6 2 li6.core none             -- a heartbeat reaches n2 at time 0
def li8 := recvAck li7 2 li7.core                   -- n2 acknowledges: n0's lease from n2 starts at 0
def li9 := leaseRestart li8 1 (restartEmpty li8.core 1) -- n1 restarts empty: new incarnation, still listed eligible
def li10 := withCore li9 (count li9.core 0 1)       -- n0 counts n1 again
def li11 := tick li10
def li12 := tick li11
def li13 := tick li12
def li14 := tick li13                               -- now = 4: the last tick at which n0 holds its lease from n2
def li15 := recvData li14 1 li14.core none          -- a heartbeat reaches n1
def li16 := recvAck li15 1 li15.core                -- n1 acknowledges
def li17 := recvData li16 1 li16.core (li16.ackEcho 0 1)  -- n0 echoes it: n1's read lease starts at 4
def li18 := tick li17                               -- now = 5
def li19 := leaseTakeover li18 2                        -- n2's wait is over: 0 + 6 ≤ 5 + 1; n1 is not counted
def li20 := withCore li19 (appendWrite li19.core 2) -- n2 writes
def li21 := withCore li20 (commitNext li20.core 2)  -- n2 commits alone: the history is [4]

theorem grantNoInc_run : (leaseLTSGrantNoInc 0 P3).MTr l0
    [.core (.count 0 1), .core (.makeEligible 0 1), .core (.count 0 2), .core (.makeEligible 0 2),
     .learn 1, .learn 2, .heartbeat 2, .ack 2, .restartEmpty 1, .core (.count 0 1),
     .tick, .tick, .tick, .tick, .heartbeat 1, .ack 1, .heartbeat 1, .tick,
     .takeover 2, .core (.append 2), .core (.commit 2)] li21 :=
  .stepL (.step (LeaseStep.core l0 _ _ (Step.count l0.core 0 1 (by decide) (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core li1 _ _ (Step.makeEligible li1.core 0 1 (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core li2 _ _ (Step.count li2.core 0 2 (by decide) (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core li3 _ _ (Step.makeEligible li3.core 0 2 (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.learn li4 1 (by decide))) <|
  .stepL (.step (LeaseStep.learn li5 2 (by decide))) <|
  .stepL (.step (LeaseStep.heartbeat li6 2 (by decide) (by decide))) <|
  .stepL (.step (LeaseStep.ackRenew li7 2 (by decide) (by decide))) <|
  .stepL (.step (LeaseStep.restartEmpty li8 1 (by decide) ⟨0, by decide, by decide⟩)) <|
  .stepL (.step (LeaseStep.core li9 _ _ (Step.count li9.core 0 1 (by decide) (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.tick li10)) <| .stepL (.step (LeaseStep.tick li11)) <|
  .stepL (.step (LeaseStep.tick li12)) <| .stepL (.step (LeaseStep.tick li13)) <|
  .stepL (.step (LeaseStep.heartbeat li14 1 (by decide) (by decide))) <|
  .stepL (.step (LeaseStep.ackRenew li15 1 (by decide) (by decide))) <|
  .stepL (LeaseStepGrantNoInc.heartbeatGrant li16 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) <|
  .stepL (.step (LeaseStep.tick li17)) <|
  .stepL (.step (LeaseStep.takeover li18 2 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (LeaseStep.core li19 _ _ (Step.append li19.core 2 (by decide) (writable_zero _ _)
    (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core li20 _ _ (Step.commit li20.core 2 (by decide) (writable_zero _ _)
    (by decide) (by decide)) rfl)) <|
  .refl

/-- The incarnation match in `MayGrant` is needed, within the design's duration rule: a
restarted-empty replica that is granted a read lease is never waited for by a new
primary, and serves a stale read. -/
theorem grantNoInc_stale : ∃ a, (leaseLTSGrantNoInc 0 P3).CanReach (leaseInit 0) a ∧
    ReplCanRead P3 a 1 ∧ a.core.log 1 ≠ a.core.hist :=
  ⟨li21, ⟨_, grantNoInc_run⟩, by decide, by decide⟩

/-! ## Takeover without waiting out the primary lease -/

/-- `LeaseStep`, plus a takeover with no wait. -/
inductive LeaseStepNoWaitPrim (m : Nat) (P : LeaseParams) : LeaseState N → LeaseAction N → LeaseState N → Prop
  | step {a μ a'} : LeaseStep m P a μ a' → LeaseStepNoWaitPrim m P a μ a'
  | takeover (a : LeaseState N) (n : N) : KnowsLatest a.core n → a.core.cfg.eligible n = true →
      n ≠ a.core.cfg.primary → a.core.cfg.incarnation n = a.core.incarnation n →
      LeaseStepNoWaitPrim m P a (.takeover n) (leaseTakeover a n)

def leaseLTSNoWaitPrim (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepNoWaitPrim m P

def lw6 := leaseTakeover l5 1                           -- n1 takes over at once
def lw7 := withCore lw6 (appendWrite lw6.core 1)      -- n1 writes
def lw8 := withCore lw7 (commitNext lw7.core 1)       -- n1 commits alone: the history is [3]

theorem noWaitPrim_run : (leaseLTSNoWaitPrim 0 P0).MTr l0
    [.core (.count 0 1), .core (.makeEligible 0 1), .learn 1, .heartbeat 1, .ack 1,
     .takeover 1, .core (.append 1), .core (.commit 1)] lw8 :=
  LTS.MTr.comp (leaseLTSNoWaitPrim 0 P0) (leaseMtr_of_step LeaseStepNoWaitPrim.step (leases_prefix P0)) <|
  .stepL (LeaseStepNoWaitPrim.takeover l5 1 (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (.step (LeaseStep.core lw6 _ _ (Step.append lw6.core 1 (by decide) (writable_zero _ _) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core lw7 _ _ (Step.commit lw7.core 1 (by decide) (writable_zero _ _) (by decide)
    (by decide)) rfl)) <|
  .refl

/-- Without the takeover wait, the deposed n0 may still serve a linearizable read, and
its log misses the committed write. -/
theorem noWaitPrim_stale : ∃ a, (leaseLTSNoWaitPrim 0 P0).CanReach (leaseInit 0) a ∧
    PrimCanRead P0 a 0 ∧ a.core.log 0 ≠ a.core.hist :=
  ⟨lw8, ⟨_, noWaitPrim_run⟩, by decide, by decide⟩

/-! ## Demotion without waiting out the read lease -/

/-- `LeaseStep`, plus a demotion with no wait. -/
inductive LeaseStepNoWaitRead (m : Nat) (P : LeaseParams) : LeaseState N → LeaseAction N → LeaseState N → Prop
  | step {a μ a'} : LeaseStep m P a μ a' → LeaseStepNoWaitRead m P a μ a'
  | demote (a : LeaseState N) (p r : N) : ThinksPrimary a.core p → KnowsLatest a.core p →
      a.core.cfg.eligible r = true →
      LeaseStepNoWaitRead m P a (.demote p r) (withCore a (makeIneligible a.core p r))

def leaseLTSNoWaitRead (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepNoWaitRead m P

def ld6 := recvData l5 1 l5.core (l5.ackEcho 0 1)     -- n0 echoes n1's acknowledgement: read lease
def ld7 := withCore ld6 (makeIneligible ld6.core 0 1)   -- n0 demotes n1 at once
def ld8 := withCore ld7 (appendWrite ld7.core 0)        -- n0 writes
def ld9 := withCore ld8 (commitNext ld8.core 0)         -- n0 commits alone: the history is [1]

theorem noWaitRead_run : (leaseLTSNoWaitRead 0 P0).MTr l0
    [.core (.count 0 1), .core (.makeEligible 0 1), .learn 1, .heartbeat 1, .ack 1,
     .heartbeat 1, .demote 0 1, .core (.append 0), .core (.commit 0)] ld9 :=
  LTS.MTr.comp (leaseLTSNoWaitRead 0 P0) (leaseMtr_of_step LeaseStepNoWaitRead.step (leases_prefix P0)) <|
  .stepL (.step (LeaseStep.heartbeatGrant l5 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (LeaseStepNoWaitRead.demote ld6 0 1 (by decide) (by decide) (by decide)) <|
  .stepL (.step (LeaseStep.core ld7 _ _ (Step.append ld7.core 0 (by decide) (writable_zero _ _) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core ld8 _ _ (Step.commit ld8.core 0 (by decide) (writable_zero _ _) (by decide)
    (by decide)) rfl)) <|
  .refl

/-- Without the demotion wait, the demoted n1 may still serve a linearizable read, and
its log misses the committed write. -/
theorem noWaitRead_stale : ∃ a, (leaseLTSNoWaitRead 0 P0).CanReach (leaseInit 0) a ∧
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
def ls10 := leaseTakeover ls9 1                          -- n1's wait is satisfied: 0 + 5 ≤ 4 + 1
def ls11 := withCore ls10 (appendWrite ls10.core 1)
def ls12 := withCore ls11 (commitNext ls11.core 1)

theorem smallMargin_run : (leaseLTS 0 P1).MTr l0
    [.core (.count 0 1), .core (.makeEligible 0 1), .learn 1, .heartbeat 1, .ack 1,
     .tick, .tick, .tick, .tick, .takeover 1, .core (.append 1), .core (.commit 1)] ls12 :=
  LTS.MTr.comp (leaseLTS 0 P1) (leases_prefix P1) <|
  .stepL (LeaseStep.tick l5) <| .stepL (LeaseStep.tick ls6) <| .stepL (LeaseStep.tick ls7) <| .stepL (LeaseStep.tick ls8) <|
  .stepL (LeaseStep.takeover ls9 1 (by decide) (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (LeaseStep.core ls10 _ _ (Step.append ls10.core 1 (by decide) (writable_zero _ _) (by decide)) rfl) <|
  .stepL (LeaseStep.core ls11 _ _ (Step.commit ls11.core 1 (by decide) (writable_zero _ _) (by decide)
    (by decide)) rfl) <|
  .refl

/-- `margin ≥ 2 · drift` is needed: with margin 1 and drift 1, and every rule kept, the
deposed n0 may serve a linearizable read of a log that misses the committed write. -/
theorem smallMargin_stale : ∃ a, LeaseReachable 0 P1 (0 : N) a ∧
    PrimCanRead P1 a 0 ∧ a.core.log 0 ≠ a.core.hist :=
  ⟨ls12, ⟨_, smallMargin_run⟩, by decide, by decide⟩

/-! ## Granting a read lease to a replica that is not an eligible sync member -/

/-- `LeaseStep`, plus an echo to any follower. -/
inductive LeaseStepGrantAny (m : Nat) (P : LeaseParams) : LeaseState N → LeaseAction N → LeaseState N → Prop
  | step {a μ a'} : LeaseStep m P a μ a' → LeaseStepGrantAny m P a μ a'
  | heartbeatGrant (a : LeaseState N) (r : N) : primaryOf a.core r ≠ r →
      ThinksPrimary a.core (primaryOf a.core r) → a.core.log r <+: a.core.log (primaryOf a.core r) →
      PrimLeaseValid P a (primaryOf a.core r) →
      LeaseStepGrantAny m P a (.heartbeat r) (recvData a r a.core (a.ackEcho (primaryOf a.core r) r))

def leaseLTSGrantAny (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepGrantAny m P

def lg1 := recvData l0 2 l0.core none                 -- a heartbeat reaches n2, which follows n0
def lg2 := recvAck lg1 2 lg1.core                       -- n2 acknowledges
def lg3 := recvData lg2 2 lg2.core (lg2.ackEcho 0 2)     -- n0 echoes it: n2 gets a read lease
def lg4 := withCore lg3 (appendWrite lg3.core 0)        -- n0 writes
def lg5 := withCore lg4 (commitNext lg4.core 0)         -- n0 commits alone: the history is [1]

theorem grantAny_run : (leaseLTSGrantAny 0 P0).MTr l0
    [.heartbeat 2, .ack 2, .heartbeat 2, .core (.append 0), .core (.commit 0)] lg5 :=
  .stepL (.step (LeaseStep.heartbeat l0 2 (by decide) (by decide))) <|
  .stepL (.step (LeaseStep.ackRenew lg1 2 (by decide) (by decide))) <|
  .stepL (LeaseStepGrantAny.heartbeatGrant lg2 2 (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (.step (LeaseStep.core lg3 _ _ (Step.append lg3.core 0 (by decide) (writable_zero _ _) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core lg4 _ _ (Step.commit lg4.core 0 (by decide) (writable_zero _ _) (by decide)
    (by decide)) rfl)) <|
  .refl

/-- Read leases must go only to eligible sync members: a follower outside the sync set
that is granted one may serve a linearizable read of a log that misses the write. -/
theorem grantAny_stale : ∃ a, (leaseLTSGrantAny 0 P0).CanReach (leaseInit 0) a ∧
    ReplCanRead P0 a 2 ∧ a.core.log 2 ≠ a.core.hist :=
  ⟨lg5, ⟨_, grantAny_run⟩, by decide, by decide⟩

end SyncReplication
