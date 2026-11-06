import SyncReplication.Counterexamples.Basic

/-!
# The survival condition is needed

The guarantee holds "as long as the primary or at least one eligible sync replica
survives". Without that condition both copies of a committed write can restart
empty. No node is authoritative afterwards, so EligibleHoldsCommitted holds vacuously;
the theorem states the loss directly.

`StepNoSurv` is `Step` plus RestartEmpty without the survival guard. The run: a write
commits on n0 and n1, n1 restarts empty, then n0 restarts empty.
-/

open Cslib

namespace SyncReplication

/-- `Step`, plus RestartEmpty without the survival guard. -/
inductive StepNoSurv (m : Nat) : State N → Action N → State N → Prop
  | step {s μ s'} : Step m s μ s' → StepNoSurv m s μ s'
  | restartEmpty (s : State N) (n : N) : KnowsLatest s n →
      StepNoSurv m s (.restartEmpty n) (restartEmpty s n)

/-- The protocol without the survival guard, as a transition system. -/
def ltsNoSurv (m : Nat) : LTS (State N) (Action N) where
  Tr := StepNoSurv m

def f7 := learn c6 1               -- n1 learns the latest configuration
def f8 := restartEmpty f7 1        -- n1 restarts empty (n0 survives)
def f9 := restartEmpty f8 0        -- n0 restarts empty: no other authoritative node

/-- The run; the label list is its trace. Only the last action is unguarded. -/
theorem noSurvivor_run : (ltsNoSurv 1).MTr c0
    [.count 0 1, .makeElig 0 1, .append 0, .replicate 1, .ack 1, .commit 0,
     .learn 1, .restartEmpty 1, .restartEmpty 0] f9 :=
  LTS.MTr.comp (ltsNoSurv 1) (mtr_of_step StepNoSurv.step committed_run) <|
  .stepL (.step (Step.learn c6 1 (by decide))) <|
  .stepL (.step (Step.restartEmpty f7 1 (by decide) ⟨0, by decide, by decide⟩)) <|
  .stepL (StepNoSurv.restartEmpty f8 0 (by decide)) <|
  .refl

/-- The survival condition is needed: without it, a reachable state has a non-empty
committed history that no node's log holds. No node is authoritative there, so
EligibleHoldsCommitted holds only vacuously; this statement names the loss itself. -/
theorem noSurvivor_loses : ∃ s, (ltsNoSurv 1).CanReach (init 0) s ∧
    s.hist ≠ [] ∧ (∀ n, ¬ s.hist <+: s.log n) ∧ (∀ n, ¬ IsAuthoritative s n) :=
  ⟨f9, ⟨_, noSurvivor_run⟩, by decide, by decide, by decide⟩

end SyncReplication
