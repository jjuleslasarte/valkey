import CoreProof.Lists
import CoreProof.Model

/-! The inductive invariant. Proven for ReconcileFirst = TRUE, EarlyDrop = FALSE. -/

namespace CoreProof

variable {Node : Type} [DecidableEq Node]

/-- `w` witnesses that the stale primary `p` cannot commit anything unsafe:
`w` is in `sync[p]`, no longer follows `p` (so `acked[p][w]` is frozen), has the least
ack among the frozen members, and the first `acked[p][w]` entries of `p` are held by
the current primary (within its reconciliation point) and by every eligible replica
except those still acking `p` as sync members. -/
def Wit (s : State Node) (p w : Node) : Prop :=
  s.sync p w = true ∧ (s.known w).prim ≠ p ∧
  (∀ r, s.sync p r = true → (s.known r).prim ≠ p → s.acked p w ≤ s.acked p r) ∧
  s.acked p w ≤ s.recon s.cfg.prim ∧
  (s.log p).take (s.acked p w) <+: s.log s.cfg.prim ∧
  ∀ m, s.cfg.elig m = true →
    ((s.log p).take (s.acked p w) <+: s.log m ∨ (s.sync p m = true ∧ (s.known m).prim = p))

structure Inv (s : State Node) : Prop where
  /-- Safety part 1 (EligibleHoldsCommitted). -/
  ehc        : ∀ n, (s.cfg.elig n = true ∨ n = s.cfg.prim) → s.hist <+: s.log n
  /-- Safety part 2 (CommittedAgree), split in three. -/
  caLen      : ∀ p, s.commit p ≤ (s.log p).length
  caHist     : ∀ p, s.commit p ≤ s.hist.length
  caEq       : ∀ p, (s.log p).take (s.commit p) = s.hist.take (s.commit p)
  /-- Known configs are past configs; versions identify them. -/
  knownLe    : ∀ n, (s.known n).ver ≤ s.cfg.ver
  knownEq    : ∀ n, (s.known n).ver = s.cfg.ver → s.known n = s.cfg
  primKnows  : s.known s.cfg.prim = s.cfg
  /-- O1 consequence: a primary counts every replica eligible in its config. -/
  eligSync   : ∀ p r, tp s p → (s.known p).elig r = true → s.sync p r = true
  noSelfSync : ∀ p, s.sync p p = false
  /-- The current primary has no ack from a node that does not follow it. -/
  ackedPrim  : ∀ r, (s.known r).prim ≠ s.cfg.prim → s.acked s.cfg.prim r = 0
  ackedLe    : ∀ p r, tp s p → s.acked p r ≤ (s.log p).length
  /-- A follower holds the acked prefix of its primary. -/
  ackHolds   : ∀ p n, tp s p → n ≠ p → (s.known n).prim = p →
                 (s.log p).take (s.acked p n) <+: s.log n
  /-- Counted but not yet eligible replicas follow the current primary, which is reconciled. -/
  syncNew    : ∀ r, s.sync s.cfg.prim r = true → s.cfg.elig r = false →
                 (s.known r).prim = s.cfg.prim ∧ s.recon s.cfg.prim ≤ s.commit s.cfg.prim
  syncCommit : ∀ q r, tp s q → s.sync q r = true → s.commit q ≤ s.acked q r
  /-- An eligible replica following a stale primary is eligible in that primary's config. -/
  eligFol    : ∀ m, s.cfg.elig m = true → (s.known m).prim ≠ s.cfg.prim →
                 (s.known (s.known m).prim).elig m = true
  /-- The history is within the current primary's commit or reconciliation point. -/
  histLe     : s.hist.length ≤ s.commit s.cfg.prim ∨ s.hist.length ≤ s.recon s.cfg.prim
  /-- Stale primaries are fenced by a frozen witness. -/
  stale      : ∀ p, tp s p → (s.known p).ver < s.cfg.ver → ∃ w, Wit s p w

theorem inv_safety {s : State Node} (h : Inv s) : Safety s :=
  ⟨h.ehc, fun p => ⟨h.caLen p, h.caEq p⟩⟩

theorem inv_init (i : Node) : Inv (init i) where
  ehc := by intro n _; simp [init]
  caLen := by intro p; simp [init]
  caHist := by intro p; simp [init]
  caEq := by intro p; simp [init]
  knownLe := by intro n; simp [init]
  knownEq := by intro n _; rfl
  primKnows := rfl
  eligSync := by intro p r _ h; simp [init, cfg0] at h
  noSelfSync := by intro p; rfl
  ackedPrim := by intro r _; rfl
  ackedLe := by intro p r _; simp [init]
  ackHolds := by intro p n _ _ _; simp [init]
  syncNew := by intro r h; simp [init] at h
  syncCommit := by intro q r _ _; simp [init]
  eligFol := by intro m h; simp [init, cfg0] at h
  histLe := by simp [init]
  stale := by intro p _ h; simp [init, cfg0] at h

/-! ### Derived facts -/

section
variable {s : State Node} (h : Inv s)
include h

theorem tp_prim : tp s s.cfg.prim := by
  unfold tp; rw [h.primKnows]

theorem tp_kl {p : Node} (hp : tp s p) (hk : kl s p) : s.known p = s.cfg ∧ s.cfg.prim = p := by
  have e := h.knownEq p hk
  refine ⟨e, ?_⟩
  unfold tp at hp; rw [e] at hp; exact hp

theorem tp_cases {p : Node} (hp : tp s p) :
    (p = s.cfg.prim ∧ s.known p = s.cfg) ∨ (s.known p).ver < s.cfg.ver := by
  rcases Nat.lt_or_ge (s.known p).ver s.cfg.ver with hl | hg
  · exact Or.inr hl
  · have hk : kl s p := Nat.le_antisymm (h.knownLe p) hg
    have := tp_kl h hp hk
    exact Or.inl ⟨this.2.symm, this.1⟩

theorem stale_ne_prim {p : Node} (hv : (s.known p).ver < s.cfg.ver) : p ≠ s.cfg.prim := by
  intro e; subst e; rw [h.primKnows] at hv; omega

theorem kl_iff_prim {p : Node} (hp : tp s p) (hk : kl s p) : p = s.cfg.prim :=
  (tp_kl h hp hk).2.symm

/-- Followers of the current primary hold its acked prefix; non-followers have ack 0. -/
theorem prim_holds_sync {m : Node} (hs : s.sync s.cfg.prim m = true) :
    (s.log s.cfg.prim).take (s.acked s.cfg.prim m) <+: s.log m := by
  by_cases hf : (s.known m).prim = s.cfg.prim
  · have hne : m ≠ s.cfg.prim := by
      intro e; rw [e, h.noSelfSync] at hs; exact Bool.false_ne_true hs
    exact h.ackHolds _ _ (tp_prim h) hne hf
  · rw [h.ackedPrim m hf]; simp

/-- Core commit fact: if `p` may commit offset `c` by the commit rule, every eligible
replica and the current primary hold the first `c+1` entries of `p`. -/
theorem commit_holds {p : Node} (hp : tp s p) (hlen : s.commit p < (s.log p).length)
    (hcap : ∀ r, s.sync p r = true → s.commit p < s.acked p r) :
    ∀ m, (s.cfg.elig m = true ∨ m = s.cfg.prim) → (s.log p).take (s.commit p + 1) <+: s.log m := by
  intro m hm
  rcases tp_cases h hp with ⟨rfl, hk⟩ | hv
  · rcases hm with he | rfl
    · have hs : s.sync s.cfg.prim m = true := h.eligSync _ _ hp (by rw [hk]; exact he)
      exact take_mono_prefix (hcap m hs) (prim_holds_sync h hs)
    · exact List.take_prefix _ _
  · obtain ⟨w, hw1, _, _, _, hwp, hwe⟩ := h.stale p hp hv
    have hcw := hcap w hw1
    rcases hm with he | rfl
    · rcases hwe m he with hd | ⟨hs, hf⟩
      · exact take_mono_prefix hcw hd
      · by_cases hmp : m = p
        · subst hmp; exact List.take_prefix _ _
        · exact take_mono_prefix (hcap m hs) (h.ackHolds _ _ hp hmp hf)
    · exact take_mono_prefix hcw hwp

end

end CoreProof
