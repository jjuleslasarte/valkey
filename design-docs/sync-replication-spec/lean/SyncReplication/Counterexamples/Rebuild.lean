import SyncReplication.Counterexamples.Basic

/-!
# A restarted primary must rebuild its sync replica set

A primary that restarts with its data loses its in-memory sync replica set. If it
starts again from an empty set instead of rebuilding it from the configuration, it can
commit without an eligible replica that was counting on being waited for.

`StepNoRebuild` is `Step` plus RestartKeep with the sync replica set emptied. The run,
at min-sync-replicas = 1: n0 promotes n1 and writes, restarts with its data, counts and
promotes n2 (which has the write), and commits with n2's acknowledgement only. n1 is
authoritative and lacks the committed write.
-/

open Cslib

namespace SyncReplication

/-- RestartKeep with the sync replica set emptied instead of rebuilt. -/
def restartKeepNoRebuild (s : State N) (n : N) : State N :=
  { restartKeep s n with sync := update s.sync n (fun _ => false) }

/-- `Step`, plus RestartKeep without the rebuilt sync replica set. -/
inductive StepNoRebuild (m : Nat) : State N → Action N → State N → Prop
  | step {s μ s'} : Step m s μ s' → StepNoRebuild m s μ s'
  | restartKeep (s : State N) (n : N) : KnowsLatest s n →
      StepNoRebuild m s (.restartKeep n) (restartKeepNoRebuild s n)

/-- The weakened protocol as a transition system. -/
def transitionSystemNoRebuild (m : Nat) : LTS (State N) (Action N) where
  Tr := StepNoRebuild m

def d0 : State N := init 0
def d1 := addToSyncSet d0 0 1             -- n0 counts n1
def d2 := makeEligible d1 0 1          -- n1 eligible
def d3 := appendWrite d2 0         -- n0 writes at offset 1
def d4 := restartKeepNoRebuild d3 0   -- n0 restarts with its data; sync set empty
def d5 := applyData (streamNext (reconnect d4 2) 0 2 0) (.data 0 2 2 1 2) 2 1 2   -- n2 copies the write
def d6 := recordAck (sendAckMsg d5 2) (.ack 2 0 2 1) 0 2 1                        -- n2 acknowledges it
def d7 := addToSyncSet d6 0 2             -- n0 counts n2
def d8 := makeEligible d7 0 2          -- n2 eligible
def d9 := commitNext d8 0          -- n0 commits with n2's ack only; n1 lacks the write

/-- The run; the label list is its trace. Only the restart is the weakened action. -/
theorem noRebuild_run : (transitionSystemNoRebuild 1).MTr d0
    [.addToSyncSet 0 1, .makeEligible 0 1, .append 0, .restartKeep 0, .psync 2, .sendData 0 2, .deliver (.data 0 2 2 1 2),
     .sendAck 2, .deliver (.ack 2 0 2 1),
     .addToSyncSet 0 2, .makeEligible 0 2, .commit 0] d9 :=
  .stepL (.step (Step.addToSyncSet d0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.makeEligible d1 0 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.append d2 0 (by decide) (writable_one (r := 1) (by decide) (by decide)
    (by decide)))) <|
  .stepL (StepNoRebuild.restartKeep d3 0 (by decide)) <|
  .stepL (.step (Step.psync d4 2 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.sendData _ 0 2 0 (by decide) (by decide))) <|
  .stepL (.step (Step.deliverData _ 0 2 2 1 2 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.sendAck _ 2 (by decide))) <|
  .stepL (.step (Step.deliverAck _ 2 0 2 1 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.addToSyncSet d6 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.makeEligible d7 0 2 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.commit d8 0 (by decide) (writable_one (r := 2) (by decide) (by decide)
    (by decide)) (by decide) (by decide))) <|
  .refl

/-- Rebuilding the sync replica set is needed: without it, a reachable state at
min-sync-replicas = 1 has an authoritative eligible replica (n1) that lacks the
committed history. -/
theorem noRebuild_unsafe : ∃ s, (transitionSystemNoRebuild 1).CanReach (init 0) s ∧ ¬ Safety s := by
  refine ⟨d9, ⟨_, noRebuild_run⟩, ?_⟩
  intro ⟨hholds, _⟩
  exact absurd (hholds 1 (by decide)) (by decide)

end SyncReplication
