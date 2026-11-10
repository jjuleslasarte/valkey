import SyncReplication.Counterexamples.Basic

/-!
# Resync only a replica its primary has not made eligible

Resync replaces a diverged replica's log with its primary's. The model allows it only
for a replica that the primary's configuration does not list as eligible: an eligible
replica may be the one authoritative copy of the committed history, and its primary's
log may be shorter than it.

`StepResyncEligible` is `Step` plus Resync without that guard. The run, at
`min-sync-replicas = 1`: a write commits on n0 and n1 (`committed_run`); n0 restarts
from a persistence file holding none of its log, so it takes a new incarnation (n1
survives); n1 still follows n0, its log `[1]` is not a prefix of n0's empty log, and n0
no longer counts it, so n1 resyncs to the empty log. n1 is still eligible with its
recorded incarnation, so it is authoritative and lacks the committed write.

The resync source n0 is still the configuration's primary but no longer thinks it is
primary (its recorded incarnation is stale); the model's Resync does not ask the source
to think it is primary. So the run shows that some guard is needed, not that it must be
this one: Resync requiring a source that thinks it is primary, with no eligibility
guard, also keeps every theorem (a scratch build, not in the repository), at the cost of one more invariant
conjunct (a deposed primary's configuration records the current incarnation of each
authoritative eligible replica that follows it).
-/

open Cslib

namespace SyncReplication

/-- `Step`, plus Resync of a replica its primary lists as eligible. -/
inductive StepResyncEligible (m : Nat) : State N → Action N → State N → Prop
  /-- Every step of the model. -/
  | step {s μ s'} : Step m s μ s' → StepResyncEligible m s μ s'
  /-- Resync without `(s.localCfg (primaryOf s r)).eligible r = false`. -/
  | resync (s : State N) (r : N) : primaryOf s r ≠ r → ¬ (s.log r <+: s.log (primaryOf s r)) →
      s.sync (primaryOf s r) r = false → StepResyncEligible m s (.resync r) (resync s r)

/-- The weakened protocol as a transition system. -/
def transitionSystemResyncEligible (m : Nat) : LTS (State N) (Action N) where
  Tr := StepResyncEligible m

def re7 := restartPartialFresh c6 0 0   -- n0 restarts from an empty file: new incarnation, empty log
def re8 := resync re7 1                  -- n1, eligible, resyncs to n0's empty log

/-- The run; the label list is its trace. Only `resync 1` is the weakened action. -/
theorem resyncEligible_run : (transitionSystemResyncEligible 1).MTr c0
    [.addToSyncSet 0 1, .makeEligible 0 1, .append 0, .replicate 1, .ack 1, .commit 0,
     .restartPartial 0 0, .resync 1] re8 :=
  LTS.MTr.comp (transitionSystemResyncEligible 1) (mtr_of_step StepResyncEligible.step committed_run) <|
  .stepL (.step (Step.restartPartialFresh c6 0 0 (by decide) (by decide) (by decide)
    ⟨1, by decide, by decide⟩)) <|
  .stepL (StepResyncEligible.resync re7 1 (by decide) (by decide) (by decide)) <|
  .refl

/-- Resync must exclude eligible replicas: without the guard a reachable state has an
authoritative eligible replica (n1) that lacks the committed history. -/
theorem resyncEligible_unsafe : ∃ s, (transitionSystemResyncEligible 1).CanReach (init 0) s ∧ ¬ Safety s := by
  refine ⟨re8, ⟨_, resyncEligible_run⟩, ?_⟩
  intro ⟨hholds, _⟩
  exact absurd (hholds 1 (by decide)) (by decide)

end SyncReplication
