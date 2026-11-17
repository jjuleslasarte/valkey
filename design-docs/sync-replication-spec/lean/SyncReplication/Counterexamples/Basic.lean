import SyncReplication.Replies

/-!
# Counterexamples: shared setup

Every counterexample is a concrete run on three nodes (`Fin 3`, node 0 the initial
primary) in a *weakened* protocol: the model's `Step`, with replication delayed under
Valkey's PSYNC check, plus one action with a rule removed. The weakened relation is named in the theorem, so the statement says exactly
which rule the run does without. Each run is a CSLib multi-step transition
(`LTS.MTr`) whose label list is the trace, so the sequence of actions can be read
off the theorem statement, and every guard is evaluated by `decide`, so each run is
a genuine execution.

This file has the decidability instances the runs need, the one-replica witness for
`Writable 1`, the lemma that lifts a run of the model into any weakening of it, and
the prefix shared by three of the runs: a write that commits on n0 and n1.
-/

open Cslib

namespace SyncReplication

abbrev N := Fin 3

instance (s : State N) (p : N) : Decidable (ThinksPrimary s p) := by
  unfold ThinksPrimary; infer_instance
instance (s : State N) (p : N) : Decidable (KnowsLatest s p) := by
  unfold KnowsLatest; infer_instance
instance (s : State N) (n : N) : Decidable (IsAuthoritative s n) := by
  unfold IsAuthoritative; infer_instance

/-- `Writable 1` from one counted replica. -/
theorem writable_one {s : State N} {p r : N} (hs : s.sync p r = true)
    (he : (s.localCfg p).eligible r = true) (hi : (s.localCfg p).incarnation r = s.incarnation r) : Writable 1 s p :=
  (writable_iff_list 1 s p).2 ⟨[r], List.nodup_singleton r, by simp, by simp [hs, he, hi]⟩

/-- `Writable 0` always holds. -/
theorem writable_zero (s : State N) (p : N) : Writable 0 s p := by simp [Writable]

/-- A run of the model is a run of any weakening of it: a weakening admits every
step of the model (`hL`). -/
theorem mtr_of_step {L : LTS (State N) (Action N)} {m : Nat}
    (hL : ∀ {s μ s'}, Step m s μ s' → L.Tr s μ s') {s t : State N} {μs : List (Action N)}
    (h : (transitionSystem m).MTr s μs t) : L.MTr s μs t := by
  induction h with
  | refl => exact .refl
  | stepL hs _ ih => exact .stepL (hL hs) ih

/-! ## A write commits on n0 and n1

n0 promotes n1, writes; n1 reconnects with PSYNC (ID 1, offset 0), n0 streams the
write, n1 applies and acknowledges it; n0 commits. Afterwards the write is on n0 and n1,
both authoritative, and the committed history is `[1]`. -/

def c0 : State N := init 0
def c1 := addToSyncSet c0 0 1             -- n0 counts n1
def c2 := makeEligible c1 0 1          -- n1 eligible
def c3 := appendWrite c2 0         -- n0 writes at offset 1
def c4 := applyData (streamNext (reconnect c3 1) 0 1 0) (.data 0 1 1 1 1) 1 1 1   -- n1 copies it
def c5 := recordAck (sendAckMsg c4 1) (.ack 1 0 1 1) 0 1 1                        -- n1 acknowledges
def c6 := commitNext c5 0          -- committed on n0 and n1

/-- The shared prefix, at min-sync-replicas = 1. -/
theorem committed_run : (transitionSystem 1).MTr c0
    [.addToSyncSet 0 1, .makeEligible 0 1, .append 0, .psync 1, .sendData 0 1, .deliver (.data 0 1 1 1 1),
     .sendAck 1, .deliver (.ack 1 0 1 1), .commit 0] c6 :=
  .stepL (Step.addToSyncSet c0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (Step.makeEligible c1 0 1 (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (Step.append c2 0 (by decide) (writable_one (r := 1) (by decide) (by decide)
    (by decide))) <|
  .stepL (Step.psync c3 1 (by decide) (by decide) (by decide)) <|
  .stepL (Step.sendData _ 0 1 0 (by decide) (by decide)) <|
  .stepL (Step.deliverData _ 0 1 1 1 1 (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (Step.sendAck _ 1 (by decide)) <|
  .stepL (Step.deliverAck _ 1 0 1 1 1 (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (Step.commit c5 0 (by decide) (writable_one (r := 1) (by decide) (by decide)
    (by decide)) (by decide) (by decide)) <|
  .refl

end SyncReplication
