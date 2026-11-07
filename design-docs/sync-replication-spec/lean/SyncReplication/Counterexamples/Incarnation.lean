import SyncReplication.Counterexamples.Basic

/-!
# A node acts as primary only while its configuration records its incarnation

The takeover compare-and-set checks a replica's incarnation, so a node that came back
empty cannot be promoted. That is not enough: the node may already be the primary. If
it keeps acting as primary on its stale configuration after restarting empty, it can
promote a replica that holds nothing.

`StepNoInc` is `Step` plus Count and MakeEligible guarded by `known[p].primary = p` alone,
without the incarnation half of `ThinksPrimary`. The run: a write commits on n0 and n1,
n0 restarts empty with a new incarnation, and n0 counts the empty n2 and makes it
eligible. n2 is authoritative and lacks the committed write.
-/

open Cslib

namespace SyncReplication

/-- `Step`, plus Count and MakeEligible guarded by `(s.known p).primary = p` alone: the
primary does not check that its own configuration records its current incarnation. -/
inductive StepNoInc (m : Nat) : State N → Action N → State N → Prop
  | step {s μ s'} : Step m s μ s' → StepNoInc m s μ s'
  | count (s : State N) (p r : N) : (s.known p).primary = p → r ≠ p → primaryOf s r = p →
      s.sync p r = false → catchUpPoint s p ≤ s.acked p r →
      StepNoInc m s (.count p r) (count s p r)
  | makeEligible (s : State N) (p r : N) : (s.known p).primary = p → KnowsLatest s p →
      s.sync p r = true → s.cfg.eligible r = false → StepNoInc m s (.makeEligible p r) (makeEligible s p r)

/-- The weakened protocol as a transition system. -/
def ltsNoInc (m : Nat) : LTS (State N) (Action N) where
  Tr := StepNoInc m

def e7 := restartEmpty c6 0        -- n0 restarts empty (n1 survives); new incarnation
def e8 := count e7 0 2             -- n0 still acts as primary: counts the empty n2
def e9 := makeEligible e8 0 2          -- n2 eligible with an empty log

/-- The run; the label list is its trace. After the shared prefix, the last two actions
are the weakened ones. -/
theorem noIncCheck_run : (ltsNoInc 1).MTr c0
    [.count 0 1, .makeEligible 0 1, .append 0, .replicate 1, .ack 1, .commit 0,
     .restartEmpty 0, .count 0 2, .makeEligible 0 2] e9 :=
  LTS.MTr.comp (ltsNoInc 1) (mtr_of_step StepNoInc.step committed_run) <|
  .stepL (.step (Step.restartEmpty c6 0 (by decide) ⟨1, by decide, by decide⟩)) <|
  .stepL (StepNoInc.count e7 0 2 (by decide) (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (StepNoInc.makeEligible e8 0 2 (by decide) (by decide) (by decide) (by decide)) <|
  .refl

/-- The incarnation check in ThinksPrimary is needed: dropping it from Count and
MakeEligible reaches a state where an authoritative eligible replica (n2) lacks the
committed history. -/
theorem noIncCheck_unsafe : ∃ s, (ltsNoInc 1).CanReach (init 0) s ∧ ¬ Safety s := by
  refine ⟨e9, ⟨_, noIncCheck_run⟩, ?_⟩
  intro ⟨hehc, _⟩
  exact absurd (hehc 2 (by decide)) (by decide)

end SyncReplication
