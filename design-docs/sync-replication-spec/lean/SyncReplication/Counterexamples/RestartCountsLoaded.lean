import SyncReplication.Counterexamples.Leases

/-!
# A node that restarts with its data must hold reads until what it restored commits

A node's committed view and committed offset are in memory, so a restart loses them, and
the file it restores from can hold writes that never committed: an AOF holds every write
the node applied. The model's RestartKeep therefore starts the node's committed view
(`leaseRestart`) and its committed offset (`restartKeep`) at 0. With whole-keyspace dirty
tracking, every entry past the committed view is dirty, so a restarted replica holds
every read until a `REPLCONF COMMIT` covers its whole log, and a restarted primary serves
none until it has committed its whole log again. In the design's per-key terms, a node
that restarts with its data treats its whole keyspace as dirty until its committed offset
passes the offset it restored.

`LeaseStepRestartCountsLoaded` is `InstantLeaseStep` plus a RestartKeep that counts the
restored log as committed: the node's committed view and committed offset are set to
its log's length. This is the per-key gap in the model's terms: the dirty key set, lost
with the restart, is rebuilt empty. Two runs at `P0` and `min-sync-replicas = 0`, each
from the shared prefix and a write by n0 that nobody commits:

- `restartCountsLoaded_stale`: n1 copies the write and acknowledges it, restarts with
  its data, reconnects with PSYNC, and n0 echoes n1's acknowledgement. n1 holds a read
  lease and serves a linearizable read of the uncommitted write.
- `restartCountsLoaded_primaryStale`: n0 restarts with its data, n1 reconnects with PSYNC
  (on n0's secondary ID) and acknowledges a heartbeat. n0 holds its primary lease from
  n1 and serves a linearizable read of the uncommitted write.

Keeping the committed view from before the restart is safe, by contrast
(`noStaleRead_restartKeepsView`): it never covers an uncommitted entry.
-/

open Cslib

namespace SyncReplication

/-- `restartKeep`, except that `n` counts its whole restored log as committed. -/
def restartKeepCountingLoaded (s : State N) (n : N) : State N :=
  { restartKeep s n with commit := update s.commit n (s.log n).length }

/-- `leaseRestart` after `restartKeepCountingLoaded`, except that `n`'s committed view
covers its whole restored log. -/
def leaseRestartCountingLoaded (a : LeaseState N) (n : N) : LeaseState N :=
  { leaseRestart a n (restartKeepCountingLoaded a.core n) with
    committedView := update a.committedView n (a.core.log n).length }

/-- `InstantLeaseStep`, plus a RestartKeep that counts the restored log as committed. -/
inductive LeaseStepRestartCountsLoaded (m : Nat) (P : LeaseParams) :
    LeaseState N → LeaseAction N → LeaseState N → Prop
  /-- Every step of the lease layer. -/
  | step {a μ a'} : InstantLeaseStep m P a μ a' → LeaseStepRestartCountsLoaded m P a μ a'
  /-- RestartKeep, with its guard, counting the restored log as committed. -/
  | restartKeep (a : LeaseState N) (n : N) : KnowsLatest a.core n →
      LeaseStepRestartCountsLoaded m P a (.restartKeep n) (leaseRestartCountingLoaded a n)

/-- The weakened lease layer as a transition system. -/
def leaseTransitionSystemRestartCountsLoaded (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepRestartCountsLoaded m P

/-! ## A restarted replica -/

def rcl6 := withCore l5 (appendWrite l5.core 0)              -- n0 writes at offset 1
def rcl7b := withCore rcl6 (streamNext rcl6.core 0 1 0)      -- n0 streams the entry
def rcl7 := withCore rcl7b (applyData rcl7b.core (.data 0 1 1 1 1) 1 1 1) -- n1 copies it
def rcl8a := withCore rcl7 (sendAckMsg rcl7.core 1)          -- n1 acknowledges
def rcl8 := withCore rcl8a (recordAck rcl8a.core (.ack 1 0 1 1) 0 1 1) -- n0 records it; no commit
def rcl9 := leaseRestartCountingLoaded rcl8 1                -- n1 restarts with its data, counted committed
def rcl10 := withCore rcl9 (reconnect rcl9.core 1)           -- n1 reconnects with PSYNC
def rcl11 := recvData rcl10 1 rcl10.core (rcl10.ackEcho 0 1) -- n0 echoes n1's acknowledgement

/-- The run; the label list is its trace. Only `restartKeep 1` is the weakened action. -/
theorem restartCountsLoaded_run : (leaseTransitionSystemRestartCountsLoaded 0 P0).MTr l0
    [.core (.addToSyncSet 0 1), .core (.makeEligible 0 1), .learn 0, .learn 1, .core (.psync 1), .heartbeat 1, .ack 1,
     .core (.append 0), .core (.sendData 0 1), .core (.deliver (.data 0 1 1 1 1)),
     .core (.sendAck 1), .core (.deliver (.ack 1 0 1 1)), .restartKeep 1, .core (.psync 1),
     .heartbeat 1] rcl11 :=
  LTS.MTr.comp (leaseTransitionSystemRestartCountsLoaded 0 P0)
    (leaseMtr_of_step LeaseStepRestartCountsLoaded.step (leases_prefix P0)) <|
  .stepL (.step (InstantLeaseStep.core l5 _ _ (Step.append l5.core 0 (by decide) (writable_zero _ _)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core rcl6 _ _ (Step.sendData rcl6.core 0 1 0 (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core rcl7b _ _
    (Step.deliverData rcl7b.core 0 1 1 1 1 (by decide) (by decide) (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core rcl7 _ _ (Step.sendAck rcl7.core 1 (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core rcl8a _ _
    (Step.deliverAck rcl8a.core 1 0 1 1 1 (by decide) (by decide) (by decide) (by decide)) rfl)) <|
  .stepL (LeaseStepRestartCountsLoaded.restartKeep rcl8 1 (by decide)) <|
  .stepL (.step (InstantLeaseStep.core rcl9 _ _ (Step.psync rcl9.core 1 (by decide) (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.heartbeatGrant rcl10 1 (by decide) (by decide) (by decide) (by decide))) <|
  .refl

/-- A replica that restarts with its data must hold reads until what it restored
commits: one that counts its restored log as committed is granted a read lease again
and serves a linearizable read of a write nobody has committed. -/
theorem restartCountsLoaded_stale :
    ∃ a, (leaseTransitionSystemRestartCountsLoaded 0 P0).CanReach (leaseInit 0) a ∧
      ReplCanRead P0 a 1 ∧ a.core.log 1 ≠ a.core.hist ∧ a.core.hist = [] :=
  ⟨rcl11, ⟨_, restartCountsLoaded_run⟩, by decide, by decide, by decide⟩

/-! ## A restarted primary -/

def rcp7 := leaseRestartCountingLoaded rcl6 0     -- n0 restarts with its data, counted committed
def rcp8 := withCore rcp7 (reconnect rcp7.core 1) -- n1 reconnects on n0's secondary ID
def rcp9 := recvData rcp8 1 rcp8.core none        -- a heartbeat reaches n1
def rcp10 := recvAck rcp9 1 rcp9.core             -- n1 acknowledges: n0's lease from n1

/-- The run; the label list is its trace. Only `restartKeep 0` is the weakened action. -/
theorem restartCountsLoaded_primaryRun : (leaseTransitionSystemRestartCountsLoaded 0 P0).MTr l0
    [.core (.addToSyncSet 0 1), .core (.makeEligible 0 1), .learn 0, .learn 1, .core (.psync 1), .heartbeat 1, .ack 1,
     .core (.append 0), .restartKeep 0, .core (.psync 1), .heartbeat 1, .ack 1] rcp10 :=
  LTS.MTr.comp (leaseTransitionSystemRestartCountsLoaded 0 P0)
    (leaseMtr_of_step LeaseStepRestartCountsLoaded.step (leases_prefix P0)) <|
  .stepL (.step (InstantLeaseStep.core l5 _ _ (Step.append l5.core 0 (by decide) (writable_zero _ _)) rfl)) <|
  .stepL (LeaseStepRestartCountsLoaded.restartKeep rcl6 0 (by decide)) <|
  .stepL (.step (InstantLeaseStep.core rcp7 _ _ (Step.psync rcp7.core 1 (by decide) (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.heartbeat rcp8 1 (by decide) (by decide))) <|
  .stepL (.step (InstantLeaseStep.ackRenew rcp9 1 (by decide))) <|
  .refl

/-- A primary that restarts with its data must commit what it restored before it serves
reads: one that counts its restored log as committed serves a linearizable read of a
write nobody has committed as soon as it holds its primary lease again. -/
theorem restartCountsLoaded_primaryStale :
    ∃ a, (leaseTransitionSystemRestartCountsLoaded 0 P0).CanReach (leaseInit 0) a ∧
      PrimCanRead P0 a 0 ∧ a.core.log 0 ≠ a.core.hist ∧ a.core.hist = [] :=
  ⟨rcp10, ⟨_, restartCountsLoaded_primaryRun⟩, by decide, by decide, by decide⟩

end SyncReplication
