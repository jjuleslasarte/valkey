import SyncReplication.Counterexamples.Basic

/-!
# Early removal only by a primary that knows the latest configuration

Uncount lets a primary drop a counted replica that is not yet eligible, read in the
latest configuration. The model allows it only to a primary that knows that
configuration (`KnowsLatest`). A deposed primary that has not learned of the takeover
still counts the replica that replaced it, and that replica's frozen acknowledgement
is what stops the deposed primary from committing; Takeover drops the new primary from
the eligible set, so the new primary is "counted and not eligible".

`StepUncountDeposed` is `Step` plus Uncount without `KnowsLatest`, keeping the
eligibility guard as the model states it, read in the latest configuration. The run, at
`min-sync-replicas = 0`: n0 counts n1 and makes it eligible; n1 learns and takes over;
n0, deposed, drops n1, writes and commits alone. The committed write is not on n1, the
current primary.

What this shows is narrower than "a deposed primary may not drop members". In n0's own
configuration n1 is eligible (n0 made it so); only the latest configuration, which n0
has not seen, lists n1 as not eligible. A node cannot read a configuration it does not
know, so the run shows that the model's two Uncount guards must go together: the
eligibility check is in the latest configuration only because `KnowsLatest` makes that
configuration the primary's own. Uncount with the eligibility check in the primary's
own configuration and no `KnowsLatest` is the design's own reading; no run is known for
it, and the proof uses `KnowsLatest` there too (`uncount_prim`, and the deposed case of
`failover_uncount`).
-/

open Cslib

namespace SyncReplication

/-- `Step`, plus Uncount by a primary whose configuration may be stale. -/
inductive StepUncountDeposed (m : Nat) : State N → Action N → State N → Prop
  /-- Every step of the model. -/
  | step {s μ s'} : Step m s μ s' → StepUncountDeposed m s μ s'
  /-- Uncount without `KnowsLatest s p`. -/
  | uncount (s : State N) (p r : N) : ThinksPrimary s p → s.sync p r = true →
      s.cfg.eligible r = false → StepUncountDeposed m s (.uncount p r) (uncount s p r)

/-- The weakened protocol as a transition system. -/
def ltsUncountDeposed (m : Nat) : LTS (State N) (Action N) where
  Tr := StepUncountDeposed m

def ud0 : State N := init 0
def ud1 := count ud0 0 1          -- n0 counts n1
def ud2 := makeEligible ud1 0 1   -- n1 eligible (version 2)
def ud3 := learn ud2 1            -- n1 learns version 2
def ud4 := takeover ud3 1         -- n1 takes over (version 3); n0 has not learned
def ud5 := uncount ud4 0 1        -- the deposed n0 drops n1, not eligible in version 3
def ud6 := appendWrite ud5 0      -- n0 writes
def ud7 := commitNext ud6 0       -- n0 commits alone: the history is [1]

/-- The run; the label list is its trace. Only `uncount 0 1` is the weakened action. -/
theorem uncountDeposed_run : (ltsUncountDeposed 0).MTr ud0
    [.count 0 1, .makeEligible 0 1, .learn 1, .takeover 1, .uncount 0 1, .append 0, .commit 0] ud7 :=
  .stepL (.step (Step.count ud0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.makeEligible ud1 0 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.learn ud2 1 (by decide))) <|
  .stepL (.step (Step.takeover ud3 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (StepUncountDeposed.uncount ud4 0 1 (by decide) (by decide) (by decide)) <|
  .stepL (.step (Step.append ud5 0 (by decide) (writable_zero _ _) (by decide))) <|
  .stepL (.step (Step.commit ud6 0 (by decide) (writable_zero _ _) (by decide) (by decide))) <|
  .refl

/-- With the eligibility check read in the latest configuration, Uncount also needs
`KnowsLatest`: otherwise a deposed primary drops the new primary from its sync replica
set and commits a write the new primary, which is authoritative, does not hold. -/
theorem uncountDeposed_unsafe : ∃ s, (ltsUncountDeposed 0).CanReach (init 0) s ∧ ¬ Safety s := by
  refine ⟨ud7, ⟨_, uncountDeposed_run⟩, ?_⟩
  intro ⟨hholds, _⟩
  exact absurd (hholds 1 (by decide)) (by decide)

end SyncReplication
