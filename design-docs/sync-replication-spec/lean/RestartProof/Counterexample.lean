import RestartProof.Model

/-!
# Counterexamples for CoreRestart: what breaks without each restart-related check

Three concrete runs on 3 nodes (`Fin 3`, node 0 the initial primary). Each run is a
CSLib multi-step transition (`LTS.MTr`) whose label list is the trace, so the sequence of
actions can be read off the theorem statement. Every guard is evaluated by `decide`, so
each run is a genuine execution of the model.

- `noRebuild_unsafe` (F5): with RebuildSync = FALSE, a primary that restarts with its
  data starts from an empty sync replica set and commits without the eligible replica
  it was counting. That replica is authoritative and lacks the committed write. This
  run uses the model's own `Step` with the F5 switch off.
- `noIncCheck_unsafe`: with every fix on, but with the incarnation part of
  ThinksPrimary removed from Count and MakeEligible, a primary that restarted empty
  keeps acting as primary and promotes an empty replica. `StepNoInc` is `Step` plus
  those two weakened actions.
- `noSurvivor_loses`: with the survival guard removed from RestartEmpty, both copies of
  a committed write restart empty and no node holds it. No node is authoritative
  either, so EligibleHoldsCommitted holds vacuously; the theorem states the loss
  directly. `StepNoSurv` is `Step` plus RestartEmpty without its guard.

These mirror TLC's `CoreRestart_noRebuildMin1`, `CoreRestart_noIncMin1` and
`CoreRestart_noSurvivorMin1`, with all runs at min-sync-replicas = 1.
-/

open Cslib

namespace RestartProof

abbrev N := Fin 3

instance (s : State N) (p : N) : Decidable (ThinksPrimary s p) := by
  unfold ThinksPrimary; infer_instance
instance (s : State N) (p : N) : Decidable (KnowsLatest s p) := by
  unfold KnowsLatest; infer_instance
instance (s : State N) (n : N) : Decidable (IsAuthoritative s n) := by
  unfold IsAuthoritative; infer_instance
instance (rf : Bool) (s : State N) (p : N) : Decidable (Reconciled rf s p) := by
  unfold Reconciled; infer_instance

/-- `Writable 1` from one counted replica. -/
theorem writable_one {s : State N} {p r : N} (hs : s.sync p r = true)
    (he : (s.known p).elig r = true) (hi : (s.known p).inc r = s.inc r) : Writable 1 s p :=
  (writable_iff_list 1 s p).2 ⟨[r], List.nodup_singleton r, by simp, by simp [hs, he, hi]⟩

/-! ## F5: a restarted primary that does not rebuild its sync replica set -/

def d0 : State N := init 0
def d1 := count d0 0 1             -- n0 counts n1
def d2 := makeElig d1 0 1          -- n1 eligible
def d3 := appendWrite d2 0         -- n0 writes at offset 1
def d4 := restartKeep false d3 0   -- n0 restarts with its data; sync set empty (no F5)
def d5 := replicate d4 2           -- n2 copies the write
def d6 := ack d5 2                 -- n2 acknowledges it
def d7 := count d6 0 2             -- n0 counts n2
def d8 := makeElig d7 0 2          -- n2 eligible
def d9 := commitNext d8 0          -- n0 commits with n2's ack only; n1 lacks the write

/-- The F5 run, with RebuildSync off. The label list is its trace. -/
theorem noRebuild_run : (lts 1 true false).MTr d0
    [.count 0 1, .makeElig 0 1, .append 0, .restartKeep 0, .replicate 2, .ack 2,
     .count 0 2, .makeElig 0 2, .commit 0] d9 :=
  .stepL (Step.count d0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (Step.makeElig d1 0 1 (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (Step.append d2 0 (by decide) (writable_one (r := 1) (by decide) (by decide) (by decide))
    (by decide)) <|
  .stepL (Step.restartKeep d3 0 (by decide)) <|
  .stepL (Step.replicate d4 2 (by decide) (by decide) (by decide)) <|
  .stepL (Step.ack d5 2 (by decide) (by decide) (by decide)) <|
  .stepL (Step.count d6 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (Step.makeElig d7 0 2 (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (Step.commit d8 0 (by decide) (writable_one (r := 2) (by decide) (by decide) (by decide))
    (by decide) (by decide)) <|
  .refl

/-- F5 is needed: without RebuildSync, a reachable state at min-sync-replicas = 1 has an
authoritative eligible replica (n1) that lacks the committed history. -/
theorem noRebuild_unsafe : ∃ s, Reachable 1 true false (0 : N) s ∧ ¬ Safety s := by
  refine ⟨d9, ⟨_, noRebuild_run⟩, ?_⟩
  intro ⟨hehc, _⟩
  exact absurd (hehc 1 (by decide)) (by decide)

/-! ## The incarnation check in ThinksPrimary -/

/-- `Step`, plus Count and MakeEligible guarded by `(s.known p).prim = p` alone: the
primary does not check that its own configuration records its current incarnation. -/
inductive StepNoInc (m : Nat) (rf rb : Bool) : State N → Action N → State N → Prop
  | step {s μ s'} : Step m rf rb s μ s' → StepNoInc m rf rb s μ s'
  | count (s : State N) (p r : N) : (s.known p).prim = p → r ≠ p → primaryOf s r = p →
      ((s.known p).elig r = true → (s.known p).inc r = s.inc r) → s.sync p r = false →
      catchUpPoint rf s p ≤ s.acked p r → StepNoInc m rf rb s (.count p r) (count s p r)
  | makeElig (s : State N) (p r : N) : (s.known p).prim = p → KnowsLatest s p →
      s.sync p r = true → s.cfg.elig r = false → StepNoInc m rf rb s (.makeElig p r) (makeElig s p r)

/-- The weakened protocol as a transition system. -/
def ltsNoInc (m : Nat) (rf rb : Bool) : LTS (State N) (Action N) where
  Tr := StepNoInc m rf rb

def e0 : State N := init 0
def e1 := count e0 0 1             -- n0 counts n1
def e2 := makeElig e1 0 1          -- n1 eligible
def e3 := appendWrite e2 0         -- n0 writes
def e4 := replicate e3 1           -- n1 copies it
def e5 := ack e4 1                 -- n1 acknowledges
def e6 := commitNext e5 0          -- committed on n0 and n1
def e7 := restartEmpty e6 0        -- n0 restarts empty (n1 survives); new incarnation
def e8 := count e7 0 2             -- n0 still acts as primary: counts empty n2
def e9 := makeElig e8 0 2          -- n2 eligible with an empty log

/-- The run: a write commits on n0 and n1, n0 restarts empty, and the unchecked n0 keeps
acting as primary. The last two actions are the weakened ones. -/
theorem noIncCheck_run : (ltsNoInc 1 true true).MTr e0
    [.count 0 1, .makeElig 0 1, .append 0, .replicate 1, .ack 1, .commit 0,
     .restartEmpty 0, .count 0 2, .makeElig 0 2] e9 :=
  .stepL (.step (Step.count e0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide))) <|
  .stepL (.step (Step.makeElig e1 0 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.append e2 0 (by decide) (writable_one (r := 1) (by decide) (by decide)
    (by decide)) (by decide))) <|
  .stepL (.step (Step.replicate e3 1 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.ack e4 1 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.commit e5 0 (by decide) (writable_one (r := 1) (by decide) (by decide)
    (by decide)) (by decide) (by decide))) <|
  .stepL (.step (Step.restartEmpty e6 0 (by decide) ⟨1, by decide, by decide⟩)) <|
  .stepL (StepNoInc.count e7 0 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) <|
  .stepL (StepNoInc.makeElig e8 0 2 (by decide) (by decide) (by decide) (by decide)) <|
  .refl

/-- The incarnation check in ThinksPrimary is needed: with every fix on, dropping it from
Count and MakeEligible reaches a state where an authoritative eligible replica (n2)
lacks the committed history. -/
theorem noIncCheck_unsafe : ∃ s, (ltsNoInc 1 true true).CanReach (init 0) s ∧ ¬ Safety s := by
  refine ⟨e9, ⟨_, noIncCheck_run⟩, ?_⟩
  intro ⟨hehc, _⟩
  exact absurd (hehc 2 (by decide)) (by decide)

/-! ## The survival condition -/

/-- `Step`, plus RestartEmpty without the survival guard. -/
inductive StepNoSurv (m : Nat) (rf rb : Bool) : State N → Action N → State N → Prop
  | step {s μ s'} : Step m rf rb s μ s' → StepNoSurv m rf rb s μ s'
  | restartEmpty (s : State N) (n : N) : KnowsLatest s n →
      StepNoSurv m rf rb s (.restartEmpty n) (restartEmpty s n)

/-- The protocol without the survival guard, as a transition system. -/
def ltsNoSurv (m : Nat) (rf rb : Bool) : LTS (State N) (Action N) where
  Tr := StepNoSurv m rf rb

def f7 := learn e6 1               -- n1 learns the latest configuration
def f8 := restartEmpty f7 1        -- n1 restarts empty (n0 survives)
def f9 := restartEmpty f8 0        -- n0 restarts empty: no other authoritative node

/-- The run: the committed write's two holders both restart empty. Only the last action
is unguarded. -/
theorem noSurvivor_run : (ltsNoSurv 1 true true).MTr e0
    [.count 0 1, .makeElig 0 1, .append 0, .replicate 1, .ack 1, .commit 0,
     .learn 1, .restartEmpty 1, .restartEmpty 0] f9 :=
  .stepL (.step (Step.count e0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide))) <|
  .stepL (.step (Step.makeElig e1 0 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.append e2 0 (by decide) (writable_one (r := 1) (by decide) (by decide)
    (by decide)) (by decide))) <|
  .stepL (.step (Step.replicate e3 1 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.ack e4 1 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.commit e5 0 (by decide) (writable_one (r := 1) (by decide) (by decide)
    (by decide)) (by decide) (by decide))) <|
  .stepL (.step (Step.learn e6 1 (by decide))) <|
  .stepL (.step (Step.restartEmpty f7 1 (by decide) ⟨0, by decide, by decide⟩)) <|
  .stepL (StepNoSurv.restartEmpty f8 0 (by decide)) <|
  .refl

/-- The survival condition is needed: without it, a reachable state has a non-empty
committed history that no node's log holds. No node is authoritative there, so
EligibleHoldsCommitted holds only vacuously; this statement names the loss itself. -/
theorem noSurvivor_loses : ∃ s, (ltsNoSurv 1 true true).CanReach (init 0) s ∧
    s.hist ≠ [] ∧ (∀ n, ¬ s.hist <+: s.log n) ∧ (∀ n, ¬ IsAuthoritative s n) :=
  ⟨f9, ⟨_, noSurvivor_run⟩, by decide, by decide, by decide⟩

end RestartProof
