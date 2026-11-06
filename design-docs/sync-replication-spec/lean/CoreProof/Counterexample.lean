import CoreProof.Model

/-! F1 regression: with ReconcileFirst = FALSE, a concrete 11-step run on 3 nodes
reaches a state violating EligibleHoldsCommitted. n0 = initial primary. -/

open Cslib

namespace CoreProof

abbrev N := Fin 3

instance (s : State N) (p : N) : Decidable (ThinksPrimary s p) :=
  inferInstanceAs (Decidable ((s.known p).prim = p))
instance (s : State N) (p : N) : Decidable (KnowsLatest s p) :=
  inferInstanceAs (Decidable ((s.known p).ver = s.cfg.ver))

def c0 : State N := init 0
def c1 := count c0 0 1          -- n0 counts n1
def c2 := makeElig c1 0 1       -- n1 eligible (ver 2)
def c3 := appendWrite c2 0      -- n0 appends a write
def c4 := learn c3 1            -- n1 learns ver 2
def c5 := replicate c4 1        -- n1 copies the write
def c6 := ack c5 1              -- n1 acks it
def c7 := commitNext c6 0          -- n0 commits it: hist = [1]
def c8 := takeover c7 1         -- n1 takes over (ver 3), commit[n1] = 0
def c9 := learn c8 2            -- n2 learns ver 3 and follows n1
def c10 := count c9 1 2         -- n1 counts empty n2: ack 0 ≥ commit 0 (no reconciliation)
def c11 := makeElig c10 1 2     -- n2 eligible with an empty log

theorem noRec (s : State N) (p : N) : Reconciled false s p := fun h => absurd h (by decide)

/-- The F1 run with ReconcileFirst off; the label list is its trace. -/
theorem noReconcile_run : (lts false false).MTr c0
    [.count 0 1, .makeElig 0 1, .append 0, .learn 1, .replicate 1, .ack 1, .commit 0,
     .takeover 1, .learn 2, .count 1 2, .makeElig 1 2] c11 :=
  .stepL (Step.count c0 0 1 (by decide) (noRec _ _) (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (Step.makeElig c1 0 1 (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (Step.append c2 0 (by decide) (noRec _ _)) <|
  .stepL (Step.learn c3 1 (by decide)) <|
  .stepL (Step.replicate c4 1 (by decide) (by decide) (by decide)) <|
  .stepL (Step.ack c5 1 (by decide) (by decide) (by decide)) <|
  .stepL (Step.commit c6 0 (by decide) (by decide) (by decide)) <|
  .stepL (Step.takeover c7 1 (by decide) (by decide) (by decide)) <|
  .stepL (Step.learn c8 2 (by decide)) <|
  .stepL (Step.count c9 1 2 (by decide) (noRec _ _) (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (Step.makeElig c10 1 2 (by decide) (by decide) (by decide) (by decide)) <|
  .refl

theorem noReconcile_unsafe : ∃ s, Reachable false false (0 : N) s ∧ ¬ Safety s := by
  refine ⟨c11, ⟨_, noReconcile_run⟩, ?_⟩
  intro ⟨hehc, _⟩
  have := hehc 2 (Or.inl (by decide))
  exact absurd this (by decide)

end CoreProof
