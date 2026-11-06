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
  { restartKeep s n with sync := upd s.sync n (fun _ => false) }

/-- `Step`, plus RestartKeep without the rebuilt sync replica set. -/
inductive StepNoRebuild (m : Nat) : State N → Action N → State N → Prop
  | step {s μ s'} : Step m s μ s' → StepNoRebuild m s μ s'
  | restartKeep (s : State N) (n : N) : KnowsLatest s n →
      StepNoRebuild m s (.restartKeep n) (restartKeepNoRebuild s n)

/-- The weakened protocol as a transition system. -/
def ltsNoRebuild (m : Nat) : LTS (State N) (Action N) where
  Tr := StepNoRebuild m

def d0 : State N := init 0
def d1 := count d0 0 1             -- n0 counts n1
def d2 := makeElig d1 0 1          -- n1 eligible
def d3 := appendWrite d2 0         -- n0 writes at offset 1
def d4 := restartKeepNoRebuild d3 0   -- n0 restarts with its data; sync set empty
def d5 := replicate d4 2           -- n2 copies the write
def d6 := ack d5 2                 -- n2 acknowledges it
def d7 := count d6 0 2             -- n0 counts n2
def d8 := makeElig d7 0 2          -- n2 eligible
def d9 := commitNext d8 0          -- n0 commits with n2's ack only; n1 lacks the write

/-- The run; the label list is its trace. Only the restart is the weakened action. -/
theorem noRebuild_run : (ltsNoRebuild 1).MTr d0
    [.count 0 1, .makeElig 0 1, .append 0, .restartKeep 0, .replicate 2, .ack 2,
     .count 0 2, .makeElig 0 2, .commit 0] d9 :=
  .stepL (.step (Step.count d0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.makeElig d1 0 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.append d2 0 (by decide) (writable_one (r := 1) (by decide) (by decide)
    (by decide)) (by decide))) <|
  .stepL (StepNoRebuild.restartKeep d3 0 (by decide)) <|
  .stepL (.step (Step.replicate d4 2 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.ack d5 2 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.count d6 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.makeElig d7 0 2 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.commit d8 0 (by decide) (writable_one (r := 2) (by decide) (by decide)
    (by decide)) (by decide) (by decide))) <|
  .refl

/-- Rebuilding the sync replica set is needed: without it, a reachable state at
min-sync-replicas = 1 has an authoritative eligible replica (n1) that lacks the
committed history. -/
theorem noRebuild_unsafe : ∃ s, (ltsNoRebuild 1).CanReach (init 0) s ∧ ¬ Safety s := by
  refine ⟨d9, ⟨_, noRebuild_run⟩, ?_⟩
  intro ⟨hehc, _⟩
  exact absurd (hehc 1 (by decide)) (by decide)

end SyncReplication
