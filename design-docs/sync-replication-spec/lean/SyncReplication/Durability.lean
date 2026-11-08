import SyncReplication.Replies

/-! # No acknowledged write is lost

`ackSafety`: every write released as OK is in the committed history at its offset,
and `ackedHeld`: every authoritative node holds it. For every `min-sync-replicas`,
with node restarts with, without and with stale data, under the survival assumption.
The proof extends the replication invariant with three facts about held replies
(`ReplyInvariant`). -/

open Cslib

namespace SyncReplication


variable {Node : Type} [DecidableEq Node]

theorem getD_prefix {l l' : List Nat} (h : l <+: l') {i : Nat} (hi : i < l.length) :
    l'.getD i 0 = l.getD i 0 := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_take {l : List Nat} {i k : Nat} (hi : i < k) :
    (l.take k).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- Held-reply invariant: a reply whose primaryship is current points at its own
entry in that primary's log. -/
def HeldInvariant (s : State Node) (held : List (Held Node)) : Prop :=
  ∀ x ∈ held, x.term ≤ s.cfg.version ∧
    (ReplyFenced s x → 1 ≤ x.offset ∧ x.offset ≤ (s.log x.primary).length ∧
      (s.log x.primary).getD (x.offset - 1) 0 = x.term)

def TermLe (s : State Node) : Prop := ∀ n, s.term n ≤ s.cfg.version

structure ReplyInvariant (a : ReplyState Node) : Prop where
  core  : Invariant a.core
  term  : TermLe a.core
  held  : HeldInvariant a.core a.held
  acked : AckedDurable a

theorem replyInvariant_init (i : Node) : ReplyInvariant (replyInit i) where
  core := invariant_init i
  term := by intro n; simp only [replyInit, init, initCfg]; split <;> omega
  held := by intro x hx; simp [replyInit] at hx
  acked := by intro x hx; simp [replyInit] at hx

/-- What a replication step other than a restart does to the parts the reply
invariants read. -/
theorem step_facts {s s' : State Node} (h : Invariant s) (ht : TermLe s) {m : Nat} {μ : Action Node}
    (hs : Step m s μ s') (hμ : μ.isRestart = false) :
    s.hist <+: s'.hist ∧ s.cfg.version ≤ s'.cfg.version ∧ TermLe s' ∧
    ∀ x t, t ≤ s.cfg.version → ThinksPrimary s' x → s'.term x = t →
      ThinksPrimary s x ∧ s.term x = t ∧ s.log x <+: s'.log x := by
  cases hs with
  | append p _ _ =>
    exact ⟨List.prefix_refl _, Nat.le_refl _, ht, fun x _ _ hp e =>
      ⟨hp, e, grow_upd s.log p _ x⟩⟩
  | replicate r _ _ _ =>
    exact ⟨List.prefix_refl _, Nat.le_refl _, ht, fun x _ _ hp e =>
      ⟨hp, e, grow_upd s.log r _ x⟩⟩
  | ack r _ _ _ =>
    exact ⟨List.prefix_refl _, Nat.le_refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | commit p _ _ _ _ =>
    refine ⟨?_, Nat.le_refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
    show s.hist <+: (if s.commit p = s.hist.length then _ else _)
    split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  | uncount p r _ _ _ =>
    exact ⟨List.prefix_refl _, Nat.le_refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | count p r _ _ _ _ _ =>
    exact ⟨List.prefix_refl _, Nat.le_refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | makeEligible p r hp hkl _ _ =>
    refine ⟨List.prefix_refl _, Nat.le_succ _, fun n => Nat.le_succ_of_le (ht n), ?_⟩
    intro x _ _ hx e
    refine ⟨?_, e, List.prefix_refl _⟩
    by_cases hxp : x = p
    · subst hxp; exact hp
    · unfold ThinksPrimary at hx ⊢; simpa [makeEligible, update_of_ne _ _ hxp] using hx
  | makeIneligible p r hp hkl _ =>
    refine ⟨List.prefix_refl _, Nat.le_succ _, fun n => Nat.le_succ_of_le (ht n), ?_⟩
    intro x _ _ hx e
    refine ⟨?_, e, List.prefix_refl _⟩
    by_cases hxp : x = p
    · subst hxp; exact hp
    · unfold ThinksPrimary at hx ⊢; simpa [makeIneligible, update_of_ne _ _ hxp] using hx
  | learn n hnkl =>
    refine ⟨List.prefix_refl _, Nat.le_refl _, ht, ?_⟩
    intro x _ _ hx e
    refine ⟨?_, e, List.prefix_refl _⟩
    by_cases hxn : x = n
    · exfalso; apply hnkl
      have hx' : s.cfg.primary = x := by have := hx.1; simpa [learn, hxn] using this
      unfold KnowsLatest; rw [← hxn, ← hx', h.primKnows]
    · unfold ThinksPrimary at hx ⊢; simpa [learn, update_of_ne _ _ hxn] using hx
  | takeover n _ _ _ _ =>
    refine ⟨List.prefix_refl _, Nat.le_succ _, ?_, ?_⟩
    · intro x
      show update s.term n (s.cfg.version + 1) x ≤ s.cfg.version + 1
      by_cases hxn : x = n
      · subst hxn; simp
      · rw [update_of_ne _ _ hxn]; exact Nat.le_succ_of_le (ht x)
    · intro x t htv hx e
      by_cases hxn : x = n
      · subst hxn
        have : s.cfg.version + 1 = t := by simpa [takeover] using e
        omega
      · refine ⟨?_, ?_, List.prefix_refl _⟩
        · unfold ThinksPrimary at hx ⊢; simpa [takeover, update_of_ne _ _ hxn] using hx
        · simpa [takeover, update_of_ne _ _ hxn] using e
  | resync r hne _ _ _ =>
    refine ⟨List.prefix_refl _, Nat.le_refl _, ht, ?_⟩
    intro x _ _ hx e
    have hxr : x ≠ r := by
      intro hxr; subst hxr; exact hne hx.1
    refine ⟨hx, e, ?_⟩
    show s.log x <+: update s.log r _ x
    rw [update_of_ne _ _ hxr]
  | restartEmpty n hkl _ =>
    refine ⟨List.prefix_refl _, Nat.le_refl _, ht, ?_⟩
    intro x _ _ hx e
    have hxn : x ≠ n := by
      intro c; subst c
      have h2 := hx.2
      change (s.known x).incarnation x = update s.incarnation x (s.incarnation x + 1) x at h2
      rw [h.knownEq x hkl, update_self] at h2; have := h.incLe x; omega
    have hI : (restartEmpty s n).incarnation x = s.incarnation x := update_of_ne _ _ hxn
    refine ⟨⟨hx.1, ?_⟩, e, ?_⟩
    · have h2 := hx.2; rw [hI] at h2; exact h2
    · show s.log x <+: update s.log n [] x
      rw [update_of_ne _ _ hxn]
  | restartKeep n _ =>
    exact ⟨List.prefix_refl _, Nat.le_refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | restartPartialKeep n k _ _ _ => exact absurd hμ (by simp [Action.isRestart])
  | restartPartialFresh n k _ _ _ _ => exact absurd hμ (by simp [Action.isRestart])

theorem replyInvariant_core {a : ReplyState Node} {c : State Node} (h : ReplyInvariant a) {m : Nat} {μ : Action Node}
    (hs : Step m a.core μ c) (hμ : μ.isRestart = false) :
    ReplyInvariant ⟨c, a.held, a.acknowledged⟩ := by
  obtain ⟨hh, hv, ht', hx⟩ := step_facts h.core h.term hs hμ
  refine ⟨invariant_step h.core hs, ht', ?_, ?_⟩
  · intro x hm
    obtain ⟨hb, hf⟩ := h.held x hm
    refine ⟨Nat.le_trans hb hv, fun hf' => ?_⟩
    obtain ⟨htp, hte, hpre⟩ := hx x.primary x.term hb hf'.1 hf'.2
    obtain ⟨h1, h2, h3⟩ := hf ⟨htp, hte⟩
    exact ⟨h1, Nat.le_trans h2 hpre.length_le, by rw [getD_prefix hpre (by omega)]; exact h3⟩
  · intro x hm
    obtain ⟨h1, h2, h3⟩ := h.acked x hm
    exact ⟨h1, Nat.le_trans h2 hh.length_le, by rw [getD_prefix hh (by omega)]; exact h3⟩

theorem replyInvariant_write {a : ReplyState Node} (h : ReplyInvariant a) (p : Node) : ReplyInvariant (write a p) := by
  have hlog : ∀ x, a.core.log x <+: (appendWrite a.core p).log x := grow_upd a.core.log p _
  refine ⟨invariant_append h.core p, h.term, ?_, h.acked⟩
  intro x hm
  rcases List.mem_cons.mp hm with rfl | hm
  · refine ⟨h.term p, fun _ => ⟨by simp, ?_, ?_⟩⟩
    · simp [write, appendWrite]
    · simp [write, appendWrite, List.getD_eq_getElem?_getD]
  · obtain ⟨hb, hf⟩ := h.held x hm
    refine ⟨hb, fun hf' => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hf hf'
    exact ⟨h1, Nat.le_trans h2 (hlog x.primary).length_le,
      by show ((appendWrite a.core p).log x.primary).getD _ 0 = _
         rw [getD_prefix (hlog x.primary) (by omega)]; exact h3⟩

theorem replyInvariant_release {a : ReplyState Node} (h : ReplyInvariant a) (x : Held Node) (hm : x ∈ a.held)
    (hc : x.offset ≤ a.core.commit x.primary) (hf : ReplyFenced a.core x) : ReplyInvariant (release a x) := by
  refine ⟨h.core, h.term, fun y hy => h.held y (List.mem_of_mem_erase hy), ?_⟩
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · obtain ⟨_, hfx⟩ := h.held x hm
    obtain ⟨h1, _, h3⟩ := hfx hf
    have hhist := h.core.commitWithinHistory x.primary
    have heq := h.core.committedIsHistoryPrefix x.primary
    refine ⟨h1, Nat.le_trans hc hhist, ?_⟩
    show a.core.hist.getD (x.offset - 1) 0 = x.term
    rw [← getD_take (k := a.core.commit x.primary) (by omega), ← heq, getD_take (by omega)]
    exact h3
  · exact h.acked y hy

theorem replyInvariant_abort {a : ReplyState Node} (h : ReplyInvariant a) (x : Held Node) : ReplyInvariant (abort a x) :=
  ⟨h.core, h.term, fun y hy => h.held y (List.mem_of_mem_erase hy), h.acked⟩

/-- A restart of `n` keeps the layer invariant once `n`'s held replies are dropped: the
surviving replies are on other nodes, whose logs, primaryship and terms it leaves alone,
and it changes neither the history nor the configuration version. -/
theorem replyInvariant_restart {a : ReplyState Node} {c : State Node} (h : ReplyInvariant a) (hc : Invariant c) (n : Node)
    (hhist : c.hist = a.core.hist) (hver : c.cfg.version = a.core.cfg.version) (hterm : c.term = a.core.term)
    (hlog : ∀ x, x ≠ n → c.log x = a.core.log x)
    (htp : ∀ x, x ≠ n → ThinksPrimary c x → ThinksPrimary a.core x) :
    ReplyInvariant ⟨c, dropHeld a.held n, a.acknowledged⟩ := by
  refine ⟨hc, fun x => by rw [hterm, hver]; exact h.term x, ?_, ?_⟩
  · intro x hx
    obtain ⟨hm, hxn⟩ := List.mem_filter.mp hx
    have hxn' : x.primary ≠ n := by simpa using hxn
    obtain ⟨hb, hf⟩ := h.held x hm
    refine ⟨by rw [hver]; exact hb, fun hf' => ?_⟩
    have : ReplyFenced a.core x := ⟨htp x.primary hxn' hf'.1, by rw [← hterm]; exact hf'.2⟩
    obtain ⟨h1, h2, h3⟩ := hf this
    rw [hlog x.primary hxn']; exact ⟨h1, h2, h3⟩
  · intro x hx; show _ ∧ x.1 ≤ c.hist.length ∧ c.hist.getD _ 0 = _; rw [hhist]; exact h.acked x hx

theorem replyInvariant_step {a a' : ReplyState Node} (h : ReplyInvariant a) {m : Nat}
    {μ : ReplyAction Node} (hs : ReplyStep m a μ a') : ReplyInvariant a' := by
  cases hs with
  | core _ c hc hμ => exact replyInvariant_core h hc hμ
  | write p _ _ => exact replyInvariant_write h p
  | release x hm hc hf => exact replyInvariant_release h x hm hc hf
  | abort x _ _ => exact replyInvariant_abort h x
  | restartEmpty n hkl hsurv =>
    exact replyInvariant_restart h (invariant_step h.core (Step.restartEmpty (m := m) _ n hkl hsurv)) n rfl rfl rfl
      (fun _ e => restartEmpty_log_other e)
      (fun _ _ hx => (restartEmpty_thinksPrimary (h.core.knownEq n hkl) (h.core.incLe n) hx).2)
  | restartKeep n hkl =>
    exact replyInvariant_restart h (invariant_step h.core (Step.restartKeep (m := m) _ n hkl)) n rfl rfl rfl
      (fun _ _ => rfl) (fun _ _ hx => hx)
  | restartPartialKeep n k hkl hk hkeep =>
    exact replyInvariant_restart h (invariant_step h.core (Step.restartPartialKeep (m := m) _ n k hkl hk hkeep)) n
      rfl rfl rfl (fun _ e => restartPartialKeep_log_other e) (fun _ _ hx => hx)
  | restartPartialFresh n k hkl hk hfresh hsurv =>
    exact replyInvariant_restart h (invariant_step h.core (Step.restartPartialFresh (m := m) _ n k hkl hk hfresh hsurv)) n
      rfl rfl rfl (fun _ e => restartPartialFresh_log_other e)
      (fun _ _ hx => (restartPartialFresh_thinksPrimary (h.core.knownEq n hkl) (h.core.incLe n) hx).2)

theorem replyInvariant_reachable {i : Node} {a : ReplyState Node} {m : Nat} (h : ReplyReachable m i a) :
    ReplyInvariant a :=
  let ⟨_, run⟩ := h
  LTS.mtrInv_of_trInv (p := ReplyInvariant) (fun _ _ _ hs h => replyInvariant_step h hs) _ _ _ run (replyInvariant_init i)

/-- No acknowledged write is lost, for any number of nodes, log length, configuration
changes and restarts, and EVERY min-sync-replicas value `m`, as long as no restart
without data removes the last authoritative node (survival assumption). -/
theorem ackSafety {i : Node} {a : ReplyState Node} {m : Nat} (h : ReplyReachable m i a) :
    AckedDurable a ∧ Safety a.core :=
  let hi := replyInvariant_reachable h
  ⟨hi.acked, invariant_safety hi.core⟩

/-- Every authoritative node holds every acknowledged write. -/
theorem ackedHeld {i : Node} {a : ReplyState Node} {m : Nat} (h : ReplyReachable m i a) :
    AckedHeld a := by
  obtain ⟨hd, he, _⟩ := ackSafety h
  intro x hx n hn
  obtain ⟨h1, h2, h3⟩ := hd x hx
  have hp := he n hn
  exact ⟨Nat.le_trans h2 hp.length_le, by rw [getD_prefix hp (by omega)]; exact h3⟩

end SyncReplication
