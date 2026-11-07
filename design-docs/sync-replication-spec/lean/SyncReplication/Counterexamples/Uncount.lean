import SyncReplication.Counterexamples.Basic

/-!
# A counted replica may be dropped only before it becomes eligible

Design §4 lets a primary that is waiting on a slow replica drop it from the commit
calculation "before step 4", that is, before the replica is committed as eligible.
The qualifier is what makes it safe: once the replica is eligible, the second
ordering rule ("ineligible before any write commits without its acknowledgement")
forbids dropping it from the sync replica set without demoting it first.

`StepUncountElig` is `Step` plus Uncount without the "not yet eligible" condition.
The run, at `min-sync-replicas = 1`: n0 promotes n1 and n2, writes, and gets n2's
acknowledgement. It drops n1 and commits with n2's acknowledgement only. n1 is
eligible and authoritative and lacks the committed write.
-/

open Cslib

namespace SyncReplication

/-- `Step`, plus Uncount of any counted replica, eligible or not. -/
inductive StepUncountElig (m : Nat) : State N → Action N → State N → Prop
  | step {s μ s'} : Step m s μ s' → StepUncountElig m s μ s'
  | uncount (s : State N) (p r : N) : ThinksPrimary s p → KnowsLatest s p → s.sync p r = true →
      StepUncountElig m s (.uncount p r) (uncount s p r)

/-- The weakened protocol as a transition system. -/
def ltsUncountElig (m : Nat) : LTS (State N) (Action N) where
  Tr := StepUncountElig m

def u0 : State N := init 0
def u1 := count u0 0 1             -- n0 counts n1
def u2 := makeEligible u1 0 1          -- n1 eligible
def u3 := count u2 0 2             -- n0 counts n2
def u4 := makeEligible u3 0 2          -- n2 eligible
def u5 := appendWrite u4 0         -- n0 writes at offset 1
def u6 := replicate u5 2           -- n2 copies it
def u7 := ack u6 2                 -- n2 acknowledges
def u8 := uncount u7 0 1           -- n0 drops the eligible n1 from its sync set
def u9 := commitNext u8 0          -- n0 commits with n2's acknowledgement only

/-- The run; the label list is its trace. Only `uncount 0 1` is the weakened action:
n1 is already eligible. -/
theorem uncountElig_run : (ltsUncountElig 1).MTr u0
    [.count 0 1, .makeEligible 0 1, .count 0 2, .makeEligible 0 2, .append 0, .replicate 2, .ack 2,
     .uncount 0 1, .commit 0] u9 :=
  .stepL (.step (Step.count u0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.makeEligible u1 0 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.count u2 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.makeEligible u3 0 2 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.append u4 0 (by decide) (writable_one (r := 1) (by decide) (by decide)
    (by decide)) (by decide))) <|
  .stepL (.step (Step.replicate u5 2 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.ack u6 2 (by decide) (by decide) (by decide))) <|
  .stepL (StepUncountElig.uncount u7 0 1 (by decide) (by decide) (by decide)) <|
  .stepL (.step (Step.commit u8 0 (by decide) (writable_one (r := 2) (by decide) (by decide)
    (by decide)) (by decide) (by decide))) <|
  .refl

/-- "Before step 4" is needed: dropping an eligible replica from the sync replica set
reaches a state where an authoritative eligible replica (n1) lacks the committed
history. -/
theorem uncountElig_unsafe : ∃ s, (ltsUncountElig 1).CanReach (init 0) s ∧ ¬ Safety s := by
  refine ⟨u9, ⟨_, uncountElig_run⟩, ?_⟩
  intro ⟨hehc, _⟩
  exact absurd (hehc 1 (by decide)) (by decide)

end SyncReplication
