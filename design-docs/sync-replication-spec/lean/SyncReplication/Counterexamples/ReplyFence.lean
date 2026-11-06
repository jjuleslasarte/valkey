import SyncReplication.Counterexamples.Basic

/-!
# The reply fence is needed

A held reply must not be released as OK merely because the committed offset has
passed its offset: the offset can be reused by a later primaryship. If the release
does not also check that the primaryship that accepted the write is still current,
a client can get OK for a write that was replaced.

`AStepNoFence` is `AStep` plus Release on the committed offset alone. The run, at
min-sync-replicas = 0: n0 writes at offset 1 and holds the reply; n1 takes over with
an empty log and n0 is fully resynced to it; n0 is promoted, takes over again, writes
different data at offset 1 and commits it; the old reply is released as OK.
-/

open Cslib

namespace SyncReplication

/-- `AStep`, plus Release on the committed offset alone. -/
inductive AStepNoFence (m : Nat) : AState N → AAction N → AState N → Prop
  | step {a μ a'} : AStep m a μ a' → AStepNoFence m a μ a'
  | release (a : AState N) (h : Held N) : h ∈ a.held → h.2.1 ≤ a.core.commit h.1 →
      AStepNoFence m a (.release h) (release a h)

/-- The weakened layer as a transition system. -/
def altsNoFence (m : Nat) : LTS (AState N) (AAction N) where
  Tr := AStepNoFence m

def b0 : AState N := ainit 0
def b1 : AState N := ⟨count b0.core 0 1, b0.held, b0.okd⟩       -- n0 counts n1
def b2 : AState N := ⟨makeElig b1.core 0 1, b1.held, b1.okd⟩    -- n1 eligible (version 2)
def b3 : AState N := write b2 0                                 -- n0 writes at offset 1; reply (n0, 1, 1) held
def b4 : AState N := ⟨learn b3.core 1, b3.held, b3.okd⟩         -- n1 learns version 2
def b5 : AState N := ⟨takeover b4.core 1, b4.held, b4.okd⟩      -- n1 takes over (version 3), empty log
def b6 : AState N := ⟨learn b5.core 0, b5.held, b5.okd⟩         -- n0 learns it is deposed
def b7 : AState N := ⟨resync b6.core 0, b6.held, b6.okd⟩        -- n0 resynced to the empty log
def b8 : AState N := ⟨count b7.core 1 0, b7.held, b7.okd⟩       -- n1 counts n0
def b9 : AState N := ⟨makeElig b8.core 1 0, b8.held, b8.okd⟩    -- n0 eligible (version 4)
def b10 : AState N := ⟨learn b9.core 0, b9.held, b9.okd⟩        -- n0 learns version 4
def b11 : AState N := ⟨takeover b10.core 0, b10.held, b10.okd⟩  -- n0 takes over (version 5)
def b12 : AState N := write b11 0                               -- n0 writes term 5 at offset 1
def b13 : AState N := ⟨commitNext b12.core 0, b12.held, b12.okd⟩   -- commits alone: the history is [5]
def b14 : AState N := release b13 (0, 1, 1)                     -- the old reply is released as OK

/-- The run; the label list is its trace. Only the final Release is the weakened
action: the primaryship that held the reply ended at n1's takeover. -/
theorem noReplyFence_run : (altsNoFence 0).MTr b0
    [.core (.count 0 1), .core (.makeElig 0 1), .write 0, .core (.learn 1), .core (.takeover 1),
     .core (.learn 0), .core (.resync 0), .core (.count 1 0), .core (.makeElig 1 0),
     .core (.learn 0), .core (.takeover 0), .write 0, .core (.commit 0), .release (0, 1, 1)] b14 :=
  .stepL (.step (AStep.core b0 _ _ (Step.count b0.core 0 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) rfl)) <|
  .stepL (.step (AStep.core b1 _ _ (Step.makeElig b1.core 0 1 (by decide) (by decide) (by decide)
    (by decide)) rfl)) <|
  .stepL (.step (AStep.write b2 0 (by decide) (writable_zero _ _) (by decide))) <|
  .stepL (.step (AStep.core b3 _ _ (Step.learn b3.core 1 (by decide)) rfl)) <|
  .stepL (.step (AStep.core b4 _ _ (Step.takeover b4.core 1 (by decide) (by decide) (by decide)
    (by decide)) rfl)) <|
  .stepL (.step (AStep.core b5 _ _ (Step.learn b5.core 0 (by decide)) rfl)) <|
  .stepL (.step (AStep.core b6 _ _ (Step.resync b6.core 0 (by decide) (by decide) (by decide)
    (by decide)) rfl)) <|
  .stepL (.step (AStep.core b7 _ _ (Step.count b7.core 1 0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) rfl)) <|
  .stepL (.step (AStep.core b8 _ _ (Step.makeElig b8.core 1 0 (by decide) (by decide) (by decide)
    (by decide)) rfl)) <|
  .stepL (.step (AStep.core b9 _ _ (Step.learn b9.core 0 (by decide)) rfl)) <|
  .stepL (.step (AStep.core b10 _ _ (Step.takeover b10.core 0 (by decide) (by decide) (by decide)
    (by decide)) rfl)) <|
  .stepL (.step (AStep.write b11 0 (by decide) (writable_zero _ _) (by decide))) <|
  .stepL (.step (AStep.core b12 _ _ (Step.commit b12.core 0 (by decide) (writable_zero _ _)
    (by decide) (by decide)) rfl)) <|
  .stepL (AStepNoFence.release b13 (0, 1, 1) (by decide) (by decide)) <|
  .refl

/-- The fence is needed: without it a reachable state has acknowledged `(1, 1)` while
the committed history holds `[5]` at offset 1. -/
theorem noReplyFence_unsafe : ∃ a, (altsNoFence 0).CanReach (ainit 0) a ∧ ¬ AckedDurable a := by
  refine ⟨b14, ⟨_, noReplyFence_run⟩, ?_⟩
  intro hd
  have := (hd (1, 1) (by decide)).2.2
  exact absurd this (by decide)

end SyncReplication
