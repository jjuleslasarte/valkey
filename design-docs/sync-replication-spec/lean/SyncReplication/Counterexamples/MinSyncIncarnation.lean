import SyncReplication.Counterexamples.Basic

/-!
# `min-sync-replicas` must count only replicas with a matching incarnation

`Writable` counts the sync members that are eligible *with the incarnation the
configuration records for them*. If the incarnation is not checked, a replica that
restarted empty, is still listed as eligible, and has caught up again satisfies
`min-sync-replicas = 1` on its own. The primary then commits with that replica as its
only sync member, and the committed write is on no authoritative node but the
primary: the restarted replica cannot take over (its incarnation does not match), so
the design's "two copies" promise does not hold.

`StepNoIncWritable` is `Step` plus AppendWrite and Commit guarded by `WritableNoInc`,
which drops the incarnation condition. The run: a write commits on n0 and n1; n1
learns the latest configuration and restarts empty (n0 survives); n1 catches up and
is counted again; n0 writes, n1 replicates and acknowledges, and n0 may commit. The
theorem mirrors `commit_two_copies`: in the pre-state its hypotheses hold (with the
weakened `Writable`), and after the commit no node other than the primary is
authoritative.
-/

open Cslib

namespace SyncReplication

/-- `Writable` without the incarnation check: `m ≤ |sync[p] ∩ known[p].elig|`. -/
def WritableNoInc (m : Nat) (s : State N) (p : N) : Prop :=
  (m : ℕ∞) ≤ {r | s.sync p r = true ∧ (s.known p).elig r = true}.encard

/-- `Step`, with AppendWrite and Commit guarded by `WritableNoInc`. -/
inductive StepNoIncWritable (m : Nat) : State N → Action N → State N → Prop
  | step {s μ s'} : Step m s μ s' → StepNoIncWritable m s μ s'
  | append (s : State N) (p : N) : ThinksPrimary s p → WritableNoInc m s p → Reconciled s p →
      StepNoIncWritable m s (.append p) (appendWrite s p)
  | commit (s : State N) (p : N) : ThinksPrimary s p → WritableNoInc m s p →
      s.commit p < (s.log p).length → (∀ r, s.sync p r = true → s.commit p < s.acked p r) →
      StepNoIncWritable m s (.commit p) (commitNext s p)

/-- The weakened protocol as a transition system. -/
def ltsNoIncWritable (m : Nat) : LTS (State N) (Action N) where
  Tr := StepNoIncWritable m

/-- `WritableNoInc 1` from one counted eligible replica. -/
theorem writableNoInc_one {s : State N} {p r : N} (hs : s.sync p r = true)
    (he : (s.known p).elig r = true) : WritableNoInc 1 s p :=
  (le_encard_iff_list 1 {r | s.sync p r = true ∧ (s.known p).elig r = true}).2
    ⟨[r], List.nodup_singleton r, by simp, by simp [hs, he]⟩

def w7 := learn c6 1               -- n1 learns the latest configuration
def w8 := restartEmpty w7 1        -- n1 restarts empty (n0 survives); still listed as eligible
def w9 := replicate w8 1           -- n1 copies the committed write back
def w10 := ack w9 1                -- n1 acknowledges it
def w11 := count w10 0 1           -- n0 counts n1 again
def w12 := appendWrite w11 0       -- n0 writes at offset 2 (WritableNoInc: n1 is eligible)
def w13 := replicate w12 1         -- n1 copies it
def w14 := ack w13 1               -- n1 acknowledges it

/-- The run up to the commit. The append is the weakened action; so is the commit
whose guard the theorem states. -/
theorem noIncWritable_run : (ltsNoIncWritable 1).MTr c0
    [.count 0 1, .makeElig 0 1, .append 0, .replicate 1, .ack 1, .commit 0,
     .learn 1, .restartEmpty 1, .replicate 1, .ack 1, .count 0 1, .append 0, .replicate 1,
     .ack 1] w14 :=
  LTS.MTr.comp (ltsNoIncWritable 1) (mtr_of_step StepNoIncWritable.step committed_run) <|
  .stepL (.step (Step.learn c6 1 (by decide))) <|
  .stepL (.step (Step.restartEmpty w7 1 (by decide) ⟨0, by decide, by decide⟩)) <|
  .stepL (.step (Step.replicate w8 1 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.ack w9 1 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.count w10 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (StepNoIncWritable.append w11 0 (by decide)
    (writableNoInc_one (s := w11) (r := 1) (by decide) (by decide)) (by decide)) <|
  .stepL (.step (Step.replicate w12 1 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.ack w13 1 (by decide) (by decide) (by decide))) <|
  .refl

/-- The incarnation check in `Writable` is needed for the two-copies property: at
`min-sync-replicas = 1`, a reachable state satisfies every hypothesis of
`commit_two_copies` except that `Writable` is replaced by `WritableNoInc`, and after
the commit the primary is the only authoritative node. -/
theorem noIncWritable_oneCopy : ∃ s : State N, (ltsNoIncWritable 1).CanReach (init 0) s ∧
    ThinksPrimary s 0 ∧ (0 : N) = s.cfg.prim ∧ WritableNoInc 1 s 0 ∧
    s.commit 0 < (s.log 0).length ∧ (∀ r, s.sync 0 r = true → s.commit 0 < s.acked 0 r) ∧
    ∀ e, e ≠ (0 : N) → ¬ IsAuthoritative (commitNext s 0) e :=
  ⟨w14, ⟨_, noIncWritable_run⟩, by decide, by decide,
    writableNoInc_one (s := w14) (p := 0) (r := 1) (by decide) (by decide), by decide, by decide,
    by decide⟩

end SyncReplication
