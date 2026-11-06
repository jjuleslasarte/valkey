import RestartProof.AckModel

/-! Unbounded proof that no acknowledged write is lost in CoreRestart, for every
MinSync (ReconcileFirst = TRUE, NoReplyFence = FALSE, RebuildSync = TRUE), with node
restarts with and without data under the survival assumption. Adapted from
`ReconProof.AckProof`. -/

open Cslib

namespace RestartProof


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
def HeldInv (s : State Node) (held : List (Held Node)) : Prop :=
  ∀ x ∈ held, x.2.2 ≤ s.cfg.ver ∧
    (fenced s x → 1 ≤ x.2.1 ∧ x.2.1 ≤ (s.log x.1).length ∧ (s.log x.1).getD (x.2.1 - 1) 0 = x.2.2)

def TermLe (s : State Node) : Prop := ∀ n, s.term n ≤ s.cfg.ver

structure AInv (a : AState Node) : Prop where
  core  : Inv a.core
  term  : TermLe a.core
  held  : HeldInv a.core a.held
  acked : AckedDurable a

theorem ainv_init (i : Node) : AInv (ainit i) where
  core := inv_init i
  term := by intro n; simp only [ainit, init, initCfg]; split <;> omega
  held := by intro x hx; simp [ainit] at hx
  acked := by intro x hx; simp [ainit] at hx

/-- What a Core step other than a restart does to the parts the reply invariants read. -/
theorem step_facts {s s' : State Node} (h : Inv s) (ht : TermLe s) {m : Nat} {μ : Action Node}
    (hs : Step m true true s μ s') (hμ : μ.isRestart = false) :
    s.hist <+: s'.hist ∧ s.cfg.ver ≤ s'.cfg.ver ∧ TermLe s' ∧
    ∀ x t, t ≤ s.cfg.ver → ThinksPrimary s' x → s'.term x = t →
      ThinksPrimary s x ∧ s.term x = t ∧ s.log x <+: s'.log x := by
  cases hs with
  | append p _ _ _ =>
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
  | count p r _ _ _ _ _ _ =>
    exact ⟨List.prefix_refl _, Nat.le_refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | makeElig p r hp hk _ _ =>
    refine ⟨List.prefix_refl _, Nat.le_succ _, fun n => Nat.le_succ_of_le (ht n), ?_⟩
    intro x _ _ hx e
    refine ⟨?_, e, List.prefix_refl _⟩
    by_cases hxp : x = p
    · subst hxp; exact hp
    · unfold ThinksPrimary at hx ⊢; simpa [makeElig, upd_ne _ _ hxp] using hx
  | makeInelig p r hp hk _ =>
    refine ⟨List.prefix_refl _, Nat.le_succ _, fun n => Nat.le_succ_of_le (ht n), ?_⟩
    intro x _ _ hx e
    refine ⟨?_, e, List.prefix_refl _⟩
    by_cases hxp : x = p
    · subst hxp; exact hp
    · unfold ThinksPrimary at hx ⊢; simpa [makeInelig, upd_ne _ _ hxp] using hx
  | learn n hk =>
    refine ⟨List.prefix_refl _, Nat.le_refl _, ht, ?_⟩
    intro x _ _ hx e
    refine ⟨?_, e, List.prefix_refl _⟩
    by_cases hxn : x = n
    · exfalso; apply hk
      have hx' : s.cfg.prim = x := by have := hx.1; simpa [learn, hxn] using this
      unfold KnowsLatest; rw [← hxn, ← hx', h.primKnows]
    · unfold ThinksPrimary at hx ⊢; simpa [learn, upd_ne _ _ hxn] using hx
  | takeover n _ _ _ _ =>
    refine ⟨List.prefix_refl _, Nat.le_succ _, ?_, ?_⟩
    · intro x
      show upd s.term n (s.cfg.ver + 1) x ≤ s.cfg.ver + 1
      by_cases hxn : x = n
      · subst hxn; simp
      · rw [upd_ne _ _ hxn]; exact Nat.le_succ_of_le (ht x)
    · intro x t htv hx e
      by_cases hxn : x = n
      · subst hxn
        have : s.cfg.ver + 1 = t := by simpa [takeover] using e
        omega
      · refine ⟨?_, ?_, List.prefix_refl _⟩
        · unfold ThinksPrimary at hx ⊢; simpa [takeover, upd_ne _ _ hxn] using hx
        · simpa [takeover, upd_ne _ _ hxn] using e
  | resync r hne _ _ _ =>
    refine ⟨List.prefix_refl _, Nat.le_refl _, ht, ?_⟩
    intro x _ _ hx e
    have hxr : x ≠ r := by
      intro hxr; subst hxr; exact hne hx.1
    refine ⟨hx, e, ?_⟩
    show s.log x <+: upd s.log r _ x
    rw [upd_ne _ _ hxr]
  | restartEmpty n hk _ =>
    refine ⟨List.prefix_refl _, Nat.le_refl _, ht, ?_⟩
    intro x _ _ hx e
    have hxn : x ≠ n := by
      intro c; subst c
      have h2 := hx.2
      change (s.known x).inc x = upd s.inc x (s.inc x + 1) x at h2
      rw [h.knownEq x hk, upd_same] at h2; have := h.incLe x; omega
    have hI : (restartEmpty s n).inc x = s.inc x := upd_ne _ _ hxn
    refine ⟨⟨hx.1, ?_⟩, e, ?_⟩
    · have h2 := hx.2; rw [hI] at h2; exact h2
    · show s.log x <+: upd s.log n [] x
      rw [upd_ne _ _ hxn]
  | restartKeep n _ =>
    exact ⟨List.prefix_refl _, Nat.le_refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | restartPartialKeep n k _ _ _ => exact absurd hμ (by simp [Action.isRestart])
  | restartPartialFresh n k _ _ _ _ => exact absurd hμ (by simp [Action.isRestart])

theorem ainv_core {a : AState Node} {c : State Node} (h : AInv a) {m : Nat} {μ : Action Node}
    (hs : Step m true true a.core μ c) (hμ : μ.isRestart = false) :
    AInv ⟨c, a.held, a.okd⟩ := by
  obtain ⟨hh, hv, ht', hx⟩ := step_facts h.core h.term hs hμ
  refine ⟨inv_step h.core hs, ht', ?_, ?_⟩
  · intro x hm
    obtain ⟨hb, hf⟩ := h.held x hm
    refine ⟨Nat.le_trans hb hv, fun hf' => ?_⟩
    obtain ⟨htp, hte, hpre⟩ := hx x.1 x.2.2 hb hf'.1 hf'.2
    obtain ⟨h1, h2, h3⟩ := hf ⟨htp, hte⟩
    exact ⟨h1, Nat.le_trans h2 hpre.length_le, by rw [getD_prefix hpre (by omega)]; exact h3⟩
  · intro x hm
    obtain ⟨h1, h2, h3⟩ := h.acked x hm
    exact ⟨h1, Nat.le_trans h2 hh.length_le, by rw [getD_prefix hh (by omega)]; exact h3⟩

theorem ainv_write {a : AState Node} (h : AInv a) (p : Node) : AInv (write a p) := by
  have hlog : ∀ x, a.core.log x <+: (appendWrite a.core p).log x := grow_upd a.core.log p _
  refine ⟨inv_append h.core p, h.term, ?_, h.acked⟩
  intro x hm
  rcases List.mem_cons.mp hm with rfl | hm
  · refine ⟨h.term p, fun _ => ⟨by simp, ?_, ?_⟩⟩
    · simp [write, appendWrite]
    · simp [write, appendWrite, List.getD_eq_getElem?_getD]
  · obtain ⟨hb, hf⟩ := h.held x hm
    refine ⟨hb, fun hf' => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hf hf'
    exact ⟨h1, Nat.le_trans h2 (hlog x.1).length_le,
      by show ((appendWrite a.core p).log x.1).getD _ 0 = _
         rw [getD_prefix (hlog x.1) (by omega)]; exact h3⟩

theorem ainv_release {a : AState Node} (h : AInv a) (x : Held Node) (hm : x ∈ a.held)
    (hc : x.2.1 ≤ a.core.commit x.1) (hf : fenced a.core x) : AInv (release a x) := by
  refine ⟨h.core, h.term, fun y hy => h.held y (List.mem_of_mem_erase hy), ?_⟩
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · obtain ⟨_, hfx⟩ := h.held x hm
    obtain ⟨h1, _, h3⟩ := hfx hf
    have hhist := h.core.caHist x.1
    have heq := h.core.caEq x.1
    refine ⟨h1, Nat.le_trans hc hhist, ?_⟩
    show a.core.hist.getD (x.2.1 - 1) 0 = x.2.2
    rw [← getD_take (k := a.core.commit x.1) (by omega), ← heq, getD_take (by omega)]
    exact h3
  · exact h.acked y hy

theorem ainv_abort {a : AState Node} (h : AInv a) (x : Held Node) : AInv (abort a x) :=
  ⟨h.core, h.term, fun y hy => h.held y (List.mem_of_mem_erase hy), h.acked⟩

/-- A restart of `n` keeps the layer invariant once `n`'s held replies are dropped: the
surviving replies are on other nodes, whose logs, primaryship and terms it leaves alone,
and it changes neither the history nor the configuration version. -/
theorem ainv_restart {a : AState Node} {c : State Node} (h : AInv a) (hc : Inv c) (n : Node)
    (hhist : c.hist = a.core.hist) (hver : c.cfg.ver = a.core.cfg.ver) (hterm : c.term = a.core.term)
    (hlog : ∀ x, x ≠ n → c.log x = a.core.log x)
    (htp : ∀ x, x ≠ n → ThinksPrimary c x → ThinksPrimary a.core x) :
    AInv ⟨c, dropHeld a.held n, a.okd⟩ := by
  refine ⟨hc, fun x => by rw [hterm, hver]; exact h.term x, ?_, ?_⟩
  · intro x hx
    obtain ⟨hm, hxn⟩ := List.mem_filter.mp hx
    have hxn' : x.1 ≠ n := by simpa using hxn
    obtain ⟨hb, hf⟩ := h.held x hm
    refine ⟨by rw [hver]; exact hb, fun hf' => ?_⟩
    have : fenced a.core x := ⟨htp x.1 hxn' hf'.1, by rw [← hterm]; exact hf'.2⟩
    obtain ⟨h1, h2, h3⟩ := hf this
    rw [hlog x.1 hxn']; exact ⟨h1, h2, h3⟩
  · intro x hx; show _ ∧ x.1 ≤ c.hist.length ∧ c.hist.getD _ 0 = _; rw [hhist]; exact h.acked x hx

theorem ainv_step {a a' : AState Node} (h : AInv a) {m : Nat}
    {μ : AAction Node} (hs : AStep m true false true a μ a') : AInv a' := by
  cases hs with
  | core _ c hc hμ => exact ainv_core h hc hμ
  | write p _ _ _ => exact ainv_write h p
  | release x hm hc hf => exact ainv_release h x hm hc (hf rfl)
  | abort x _ _ => exact ainv_abort h x
  | restartE n hk hsv =>
    exact ainv_restart h (inv_step h.core (Step.restartEmpty (m := m) _ n hk hsv)) n rfl rfl rfl
      (fun _ e => restartEmpty_log_other e)
      (fun _ _ hx => (restartEmpty_thinksPrimary (h.core.knownEq n hk) (h.core.incLe n) hx).2)
  | restartK n hk =>
    exact ainv_restart h (inv_step h.core (Step.restartKeep (m := m) _ n hk)) n rfl rfl rfl
      (fun _ _ => rfl) (fun _ _ hx => hx)
  | restartPK n k hkl hk hkeep =>
    exact ainv_restart h (inv_step h.core (Step.restartPartialKeep (m := m) _ n k hkl hk hkeep)) n
      rfl rfl rfl (fun _ e => restartPartialKeep_log_other e) (fun _ _ hx => hx)
  | restartPF n k hkl hk hfresh hsv =>
    exact ainv_restart h (inv_step h.core (Step.restartPartialFresh (m := m) _ n k hkl hk hfresh hsv)) n
      rfl rfl rfl (fun _ e => restartPartialFresh_log_other e)
      (fun _ _ hx => (restartPartialFresh_thinksPrimary (h.core.knownEq n hkl) (h.core.incLe n) hx).2)

theorem ainv_reachable {i : Node} {a : AState Node} {m : Nat} (h : AReachable m true false true i a) :
    AInv a :=
  let ⟨_, run⟩ := h
  LTS.mtrInv_of_trInv (p := AInv) (fun _ _ _ hs h => ainv_step h hs) _ _ _ run (ainv_init i)

/-- No acknowledged write is lost, for any number of nodes, log length, configuration
changes and restarts, and EVERY min-sync-replicas value `m`; with reconciliation
against the inherited log (A1), the F2 fix (reply fence) and the F5 fix (a primary
that restarts with its data rebuilds its sync set), as long as no restart without
data removes the last authoritative node (survival assumption). -/
theorem ackSafety {i : Node} {a : AState Node} {m : Nat} (h : AReachable m true false true i a) :
    AckedDurable a ∧ Safety a.core :=
  let hi := ainv_reachable h
  ⟨hi.acked, inv_safety hi.core⟩

/-- Every authoritative node holds every acknowledged write. -/
theorem ackedHeld {i : Node} {a : AState Node} {m : Nat} (h : AReachable m true false true i a) :
    AckedHeld a := by
  obtain ⟨hd, he, _⟩ := ackSafety h
  intro x hx n hn
  obtain ⟨h1, h2, h3⟩ := hd x hx
  have hp := he n hn
  exact ⟨Nat.le_trans h2 hp.length_le, by rw [getD_prefix hp (by omega)]; exact h3⟩

end RestartProof
