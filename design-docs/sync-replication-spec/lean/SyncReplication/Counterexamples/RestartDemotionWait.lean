import SyncReplication.Counterexamples.Leases

/-!
# A restarted primary must wait before demoting

A primary that restarts loses `ackReceived`, the record of when it last heard from
each replica, so the demotion guard's read-lease wait (`GrantorOver`) is vacuous for
every replica. The model's restart therefore starts a new primaryship at `now` and
marks every replica as old (`oldEligible n := fun _ => true`), so the primary waits one
read lease plus the margin before demoting anyone.

`LeaseStepRestartNoDemotionWait` is `InstantLeaseStep` plus RestartKeep that does not arm
that wait: it marks no replica as old. The run, at `P0` and `min-sync-replicas = 0`: the
shared prefix and one echo, so n1 holds a read lease from n0 (as in
`replCanRead_reachable`); n0 restarts with its data, demotes n1 at once, writes and
commits alone, with no time passing. n1's read lease is still valid.
-/

open Cslib

namespace SyncReplication

/-- `leaseRestart`, except that the restarted node marks no replica as one of the old
configuration, so no demotion wait follows the restart. -/
def leaseRestartWithoutDemotionWait (a : LeaseState N) (n : N) (c : State N) : LeaseState N :=
  { leaseRestart a n c with oldEligible := update a.oldEligible n (fun _ => false) }

/-- `InstantLeaseStep`, plus RestartKeep without the demotion wait. -/
inductive LeaseStepRestartNoDemotionWait (m : Nat) (P : LeaseParams) :
    LeaseState N → LeaseAction N → LeaseState N → Prop
  /-- Every step of the lease layer. -/
  | step {a μ a'} : InstantLeaseStep m P a μ a' → LeaseStepRestartNoDemotionWait m P a μ a'
  /-- RestartKeep, with its guard, arming no demotion wait. -/
  | restartKeep (a : LeaseState N) (n : N) : KnowsLatest a.core n →
      LeaseStepRestartNoDemotionWait m P a (.restartKeep n)
        (leaseRestartWithoutDemotionWait a n (restartKeep a.core n))

/-- The weakened lease layer as a transition system. -/
def leaseTransitionSystemRestartNoDemotionWait (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepRestartNoDemotionWait m P

def lp7 := leaseRestartWithoutDemotionWait l6 0 (restartKeep l6.core 0) -- n0 restarts with its data
def lp8 := withCore lp7 (makeIneligible lp7.core 0 1)   -- n0 demotes n1 at once
def lp9 := withCore lp8 (appendWrite lp8.core 0)        -- n0 writes
def lp10 := withCore lp9 (commitNext lp9.core 0)        -- n0 commits alone: the history is [1]

/-- The run; the label list is its trace. Only `restartKeep 0` is the weakened action;
the demotion that follows is a step of the lease layer. -/
theorem restartNoDemotionWait_run : (leaseTransitionSystemRestartNoDemotionWait 0 P0).MTr l0
    [.core (.addToSyncSet 0 1), .core (.makeEligible 0 1), .learn 1, .core (.psync 1), .heartbeat 1, .ack 1,
     .heartbeat 1, .restartKeep 0, .demote 0 1, .core (.append 0), .core (.commit 0)] lp10 :=
  LTS.MTr.comp (leaseTransitionSystemRestartNoDemotionWait 0 P0)
    (leaseMtr_of_step LeaseStepRestartNoDemotionWait.step (leases_prefix P0)) <|
  .stepL (.step (InstantLeaseStep.heartbeatGrant l5 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (LeaseStepRestartNoDemotionWait.restartKeep l6 0 (by decide)) <|
  .stepL (.step (InstantLeaseStep.demote lp7 0 1 (by decide) (by decide) (by decide) (by decide)
    (by decide))) <|
  .stepL (.step (InstantLeaseStep.core lp8 _ _ (Step.append lp8.core 0 (by decide) (writable_zero _ _)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core lp9 _ _ (Step.commit lp9.core 0 (by decide) (writable_zero _ _)
    (by decide) (by decide)) rfl)) <|
  .refl

/-- The restart demotion wait is needed: a primary that restarts and demotes a replica
at once commits without it while the replica's read lease is still valid, and the
replica may serve a linearizable read that misses the write. -/
theorem restartNoDemotionWait_stale :
    ∃ a, (leaseTransitionSystemRestartNoDemotionWait 0 P0).CanReach (leaseInit 0) a ∧
      ReplCanRead P0 a 1 ∧ a.core.log 1 ≠ a.core.hist :=
  ⟨lp10, ⟨_, restartNoDemotionWait_run⟩, by decide, by decide⟩

end SyncReplication
