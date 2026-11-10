import SyncReplication.Counterexamples.Reconcile

/-!
# AddToSyncSet's catch-up guard is needed

AddToSyncSet lets a primary add a replica to its sync replica set only once the replica has
acknowledged up to the primary's catch-up point (`catchUpPoint s p ≤ s.acked p r`).
`StepNoCatchUp` is `Step` plus AddToSyncSet with that guard deleted outright: a primary may
count any replica that follows it.

The guard has two halves: the design's (promotion step 1: acknowledged at or past the
committed offset) and the reconciliation fix (while unreconciled, the inherited end).
`noCatchUp_run` breaks the first: after `committed_run`, the reconciled n0 counts and
promotes n2, which has acknowledged nothing, so n2 is eligible, authoritative and
empty. For the second, `StepNoReconcile` (`Reconcile.lean`) keeps only the design's
half, so each of its steps is a step of `StepNoCatchUp`
(`stepNoCatchUp_of_stepNoReconcile`) and `noReconcile_run` is also a run without the
guard.
-/

open Cslib

namespace SyncReplication

/-- `Step`, plus AddToSyncSet with no catch-up guard: a primary may count any replica that
follows it, whatever the replica has acknowledged. -/
inductive StepNoCatchUp (m : Nat) : State N → Action N → State N → Prop
  /-- Every step of the model. -/
  | step {s μ s'} : Step m s μ s' → StepNoCatchUp m s μ s'
  /-- AddToSyncSet without `catchUpPoint s p ≤ s.acked p r`. -/
  | addToSyncSet (s : State N) (p r : N) : ThinksPrimary s p → r ≠ p → primaryOf s r = p →
      s.sync p r = false → StepNoCatchUp m s (.addToSyncSet p r) (addToSyncSet s p r)

/-- The weakened protocol as a transition system. -/
def transitionSystemNoCatchUp (m : Nat) : LTS (State N) (Action N) where
  Tr := StepNoCatchUp m

/-- AddToSyncSet measured against the primary's own commit point is a special case of AddToSyncSet
with no guard, so every step of `StepNoReconcile` is a step of `StepNoCatchUp`. -/
theorem stepNoCatchUp_of_stepNoReconcile {m : Nat} {s s' : State N} {μ : Action N} :
    StepNoReconcile m s μ s' → StepNoCatchUp m s μ s' := by
  intro h
  cases h with
  | step h => exact .step h
  | addToSyncSet p r hp hrp hfollows hsy _ => exact .addToSyncSet _ p r hp hrp hfollows hsy

/-- Every run of `StepNoReconcile` is a run of `StepNoCatchUp`. -/
theorem mtrNoCatchUp_of_mtrNoReconcile {m : Nat} {s t : State N} {μs : List (Action N)}
    (h : (transitionSystemNoReconcile m).MTr s μs t) : (transitionSystemNoCatchUp m).MTr s μs t := by
  induction h with
  | refl => exact .refl
  | stepL hs _ ih => exact .stepL (stepNoCatchUp_of_stepNoReconcile hs) ih

/-- `committed_run`'s write is committed on n0 (commit point 1); n0 counts n2, which
has acknowledged nothing. The design's own guard (acknowledged at or past the
committed offset, `0 < 1`) forbids this step, so this is the half of the rule the
design states. -/
def catchUp7 := addToSyncSet c6 0 2
/-- n0 makes n2 eligible: authoritative with an empty log. -/
def catchUp8 := makeEligible catchUp7 0 2

/-- The direct run: a reconciled primary counts a replica behind its commit point. Only
`addToSyncSet 0 2` is the weakened action. -/
theorem noCatchUp_run : (transitionSystemNoCatchUp 1).MTr c0
    [.addToSyncSet 0 1, .makeEligible 0 1, .append 0, .replicate 1, .ack 1, .commit 0,
     .addToSyncSet 0 2, .makeEligible 0 2] catchUp8 :=
  LTS.MTr.comp (transitionSystemNoCatchUp 1) (mtr_of_step StepNoCatchUp.step committed_run) <|
  .stepL (StepNoCatchUp.addToSyncSet c6 0 2 (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (.step (Step.makeEligible catchUp7 0 2 (by decide) (by decide) (by decide) (by decide))) <|
  .refl

/-- AddToSyncSet's catch-up guard is needed: without it a reachable state has an
authoritative eligible replica that lacks the committed history. The run is
`noCatchUp_run` (8 steps, `min-sync-replicas = 1`), in which the primary has
reconciled, so it is the design's commit-point guard that is missing; `noReconcile_run`
(through `mtrNoCatchUp_of_mtrNoReconcile`) is a second run, for the reconciliation
half. -/
theorem noCatchUp_unsafe : ∃ s, (transitionSystemNoCatchUp 1).CanReach (init 0) s ∧ ¬ Safety s := by
  refine ⟨catchUp8, ⟨_, noCatchUp_run⟩, ?_⟩
  intro ⟨hholds, _⟩
  exact absurd (hholds 2 (by decide)) (by decide)

end SyncReplication
