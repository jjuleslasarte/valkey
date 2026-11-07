import SyncReplication.Counterexamples.Basic

/-!
# A restart from a stale persistence file must not keep the incarnation

A replica acknowledges a write once it is applied in memory. Without `appendfsync
always` it can restart from a file that predates writes it acknowledged. If it keeps
its incarnation and so its eligibility, it is counted on acknowledgements it no longer
backs.

`StepStaleKeep` is `Step` plus RestartPartial that keeps the incarnation whatever the
file covers. The run: a write commits on n0 and n1, n1 learns the latest
configuration, then restarts from a file holding none of its log. n1 is authoritative
and lacks the committed write.
-/

open Cslib

namespace SyncReplication

/-- `Step`, plus RestartPartial keeping the incarnation for any `k`: the file need not
cover what the node acknowledged. -/
inductive StepStaleKeep (m : Nat) : State N → Action N → State N → Prop
  | step {s μ s'} : Step m s μ s' → StepStaleKeep m s μ s'
  | restartPartial (s : State N) (n : N) (k : Nat) : KnowsLatest s n → k < (s.log n).length →
      StepStaleKeep m s (.restartPartial n k) (restartPartialKeep s n k)

/-- The protocol with that rule, as a transition system. -/
def ltsStaleKeep (m : Nat) : LTS (State N) (Action N) where
  Tr := StepStaleKeep m

def g7 := learn c6 1                  -- n1 learns the latest configuration
def g8 := restartPartialKeep g7 1 0   -- n1 restarts from a file without the write

/-- The run; the label list is its trace. Only the last action is the weakened one. -/
theorem staleRestoreKeepsInc_run : (ltsStaleKeep 1).MTr c0
    [.count 0 1, .makeEligible 0 1, .append 0, .replicate 1, .ack 1, .commit 0,
     .learn 1, .restartPartial 1 0] g8 :=
  LTS.MTr.comp (ltsStaleKeep 1) (mtr_of_step StepStaleKeep.step committed_run) <|
  .stepL (.step (Step.learn c6 1 (by decide))) <|
  .stepL (StepStaleKeep.restartPartial g7 1 0 (by decide) (by decide)) <|
  .refl

/-- The incarnation rule for a stale restore is needed: if a node keeps its incarnation
after restarting from a file that does not cover what it acknowledged, a reachable
state has an authoritative eligible replica (n1) that lacks the committed history. -/
theorem staleRestoreKeepsInc_unsafe :
    ∃ s, (ltsStaleKeep 1).CanReach (init 0) s ∧ ¬ Safety s := by
  refine ⟨g8, ⟨_, staleRestoreKeepsInc_run⟩, ?_⟩
  intro ⟨hehc, _⟩
  exact absurd (hehc 1 (by decide)) (by decide)

def g9 := restartEmpty g8 0   -- n0 restarts empty; allowed, since n1 is still authoritative

/-- One more step: n0 restarts empty. The survival guard is satisfied by n1, which is
authoritative but holds nothing. -/
theorem staleRestoreKeepsInc_loss_run : (ltsStaleKeep 1).MTr c0
    [.count 0 1, .makeEligible 0 1, .append 0, .replicate 1, .ack 1, .commit 0,
     .learn 1, .restartPartial 1 0, .restartEmpty 0] g9 :=
  LTS.MTr.comp (ltsStaleKeep 1) staleRestoreKeepsInc_run <|
  .stepL (.step (Step.restartEmpty g8 0 (by decide) ⟨1, by decide, by decide⟩)) <|
  .refl

/-- The committed write is then gone from every node: the committed history is
non-empty and no node's log holds it. -/
theorem staleRestoreKeepsInc_loses : ∃ s, (ltsStaleKeep 1).CanReach (init 0) s ∧
    s.hist ≠ [] ∧ ∀ n, ¬ s.hist <+: s.log n :=
  ⟨g9, ⟨_, staleRestoreKeepsInc_loss_run⟩, by decide, by decide⟩

end SyncReplication
