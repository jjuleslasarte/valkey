import SyncReplication.Counterexamples.Basic

/-!
# Reconciliation against the inherited log is needed

The design's promotion step 1 waits until a replica has acknowledged up to the
primary's *committed* offset. Right after a failover the new primary's committed
offset is 0, behind writes the old primary already committed. If the new primary
counts replicas against that offset instead of against the log it inherited, it can
promote a replica that holds nothing.

`StepNoReconcile` is `Step` plus Count measured against the primary's own commit
point. The run: n0 commits a write with n1 as its only sync replica; n1 takes over
with commit point 0 and counts the empty n2, then makes it eligible. n2 is
authoritative and lacks the committed write.
-/

open Cslib

namespace SyncReplication

/-- `Step`, plus Count measured against the primary's own commit point instead of
`catchUpPoint`: the design's promotion step 1 as written. -/
inductive StepNoReconcile (m : Nat) : State N → Action N → State N → Prop
  | step {s μ s'} : Step m s μ s' → StepNoReconcile m s μ s'
  | count (s : State N) (p r : N) : ThinksPrimary s p → r ≠ p → primaryOf s r = p →
      s.sync p r = false → s.commit p ≤ s.acked p r →
      StepNoReconcile m s (.count p r) (count s p r)

/-- The weakened protocol as a transition system. -/
def ltsNoReconcile (m : Nat) : LTS (State N) (Action N) where
  Tr := StepNoReconcile m

def r0 : State N := init 0
def r1 := count r0 0 1             -- n0 counts n1
def r2 := makeElig r1 0 1          -- n1 eligible (version 2)
def r3 := appendWrite r2 0         -- n0 writes at offset 1
def r4 := learn r3 1               -- n1 learns version 2
def r5 := replicate r4 1           -- n1 copies the write
def r6 := ack r5 1                 -- n1 acknowledges it
def r7 := commitNext r6 0          -- n0 commits: the history is [1]
def r8 := takeover r7 1            -- n1 takes over (version 3) with commit point 0
def r9 := learn r8 2               -- n2 learns version 3 and follows n1
def r10 := count r9 1 2            -- n1 counts the empty n2: ack 0 ≥ commit 0
def r11 := makeElig r10 1 2        -- n2 eligible with an empty log

/-- The run; the label list is its trace. Only `count 1 2` is the weakened action. -/
theorem noReconcile_run : (ltsNoReconcile 1).MTr r0
    [.count 0 1, .makeElig 0 1, .append 0, .learn 1, .replicate 1, .ack 1, .commit 0,
     .takeover 1, .learn 2, .count 1 2, .makeElig 1 2] r11 :=
  .stepL (.step (Step.count r0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.makeElig r1 0 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.append r2 0 (by decide) (writable_one (r := 1) (by decide) (by decide)
    (by decide)) (by decide))) <|
  .stepL (.step (Step.learn r3 1 (by decide))) <|
  .stepL (.step (Step.replicate r4 1 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.ack r5 1 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.commit r6 0 (by decide) (writable_one (r := 1) (by decide) (by decide)
    (by decide)) (by decide) (by decide))) <|
  .stepL (.step (Step.takeover r7 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.learn r8 2 (by decide))) <|
  .stepL (StepNoReconcile.count r9 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (.step (Step.makeElig r10 1 2 (by decide) (by decide) (by decide) (by decide))) <|
  .refl

/-- Reconciliation is needed: without it a reachable state has an authoritative
eligible replica (n2) that lacks the committed history. -/
theorem noReconcile_unsafe : ∃ s, (ltsNoReconcile 1).CanReach (init 0) s ∧ ¬ Safety s := by
  refine ⟨r11, ⟨_, noReconcile_run⟩, ?_⟩
  intro ⟨hehc, _⟩
  exact absurd (hehc 2 (by decide)) (by decide)

end SyncReplication
