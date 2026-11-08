import SyncReplication.Counterexamples.Leases

/-!
# A restart must clear the restarted node's read lease

Lease state is in memory, so a restart loses the node's read lease (`leaseRestart`
sets `readLease n := none`). If a replica kept its read lease across a restart
without its data, it would come back empty, with committed view 0, still believing
its lease valid: nothing uncommitted, so it may serve a linearizable read of an empty
log.

`LeaseStepRestartKeepsReadLease` is `LeaseStep` plus RestartEmpty that keeps the
node's read lease. The run, at `P0` and `min-sync-replicas = 0`: the shared prefix,
then n0 writes, n1 replicates and acknowledges, n0 commits (the history is `[1]`),
echoes n1's acknowledgement (n1's read lease starts), and n1 restarts empty with no
time passing.
-/

open Cslib

namespace SyncReplication

/-- `leaseRestart`, except that the restarted node keeps its read lease. -/
def leaseRestartKeepingReadLease (a : LeaseState N) (n : N) (c : State N) : LeaseState N :=
  { leaseRestart a n c with readLease := a.readLease }

/-- `LeaseStep`, plus RestartEmpty that keeps the restarted node's read lease. -/
inductive LeaseStepRestartKeepsReadLease (m : Nat) (P : LeaseParams) :
    LeaseState N → LeaseAction N → LeaseState N → Prop
  /-- Every step of the lease layer. -/
  | step {a μ a'} : LeaseStep m P a μ a' → LeaseStepRestartKeepsReadLease m P a μ a'
  /-- RestartEmpty, with its guards, leaving `readLease n` as it was. -/
  | restartEmpty (a : LeaseState N) (n : N) : KnowsLatest a.core n →
      (∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      LeaseStepRestartKeepsReadLease m P a (.restartEmpty n)
        (leaseRestartKeepingReadLease a n (restartEmpty a.core n))

/-- The weakened lease layer as a transition system. -/
def leaseLTSRestartKeepsReadLease (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepRestartKeepsReadLease m P

def lk6 := withCore l5 (appendWrite l5.core 0)       -- n0 writes at offset 1
def lk7 := recvData lk6 1 (replicate lk6.core 1) none -- n1 copies it
def lk8 := recvAck lk7 1 (ack lk7.core 1)              -- n1 acknowledges
def lk9 := withCore lk8 (commitNext lk8.core 0)        -- n0 commits: the history is [1]
def lk10 := recvData lk9 1 lk9.core (lk9.ackEcho 0 1)  -- n0 echoes n1's acknowledgement: read lease
def lk11 := leaseRestartKeepingReadLease lk10 1 (restartEmpty lk10.core 1) -- n1 restarts empty, lease kept

/-- The run; the label list is its trace. Only `restartEmpty 1` is the weakened action. -/
theorem restartKeepsReadLease_run : (leaseLTSRestartKeepsReadLease 0 P0).MTr l0
    [.core (.count 0 1), .core (.makeEligible 0 1), .learn 1, .heartbeat 1, .ack 1,
     .core (.append 0), .replicate 1, .ack 1, .core (.commit 0), .heartbeat 1, .restartEmpty 1] lk11 :=
  LTS.MTr.comp (leaseLTSRestartKeepsReadLease 0 P0)
    (leaseMtr_of_step LeaseStepRestartKeepsReadLease.step (leases_prefix P0)) <|
  .stepL (.step (LeaseStep.core l5 _ _ (Step.append l5.core 0 (by decide) (writable_zero _ _)) rfl)) <|
  .stepL (.step (LeaseStep.replicate lk6 1 (by decide) (by decide) (by decide))) <|
  .stepL (.step (LeaseStep.ack lk7 1 (by decide) (by decide) (by decide))) <|
  .stepL (.step (LeaseStep.core lk8 _ _ (Step.commit lk8.core 0 (by decide) (writable_zero _ _)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.heartbeatGrant lk9 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (LeaseStepRestartKeepsReadLease.restartEmpty lk10 1 (by decide) ⟨0, by decide, by decide⟩) <|
  .refl

/-- A restart must clear the node's read lease: a replica that restarts empty and
keeps its lease may serve a linearizable read of an empty log while the committed
history is `[1]`. -/
theorem restartKeepsReadLease_stale :
    ∃ a, (leaseLTSRestartKeepsReadLease 0 P0).CanReach (leaseInit 0) a ∧
      ReplCanRead P0 a 1 ∧ a.core.log 1 ≠ a.core.hist :=
  ⟨lk11, ⟨_, restartKeepsReadLease_run⟩, by decide, by decide⟩

end SyncReplication
