import ReconProof.AckModel

/-! Unbounded proof that no acknowledged write is lost in CoreRecon, for every MinSync
(ReconcileFirst = TRUE, NoReplyFence = FALSE). No lease or `cfg.prim = p` fence.
Adapted from `AckProof.Proof`. -/

namespace ReconProof


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
  term := by intro n; simp only [ainit, init, cfg0]; split <;> omega
  held := by intro x hx; simp [ainit] at hx
  acked := by intro x hx; simp [ainit] at hx

/-- What a Core step does to the parts the reply invariants read. -/
theorem step_facts {s s' : State Node} (h : Inv s) (ht : TermLe s) {m : Nat} (hs : Step m true s s') :
    s.hist <+: s'.hist ∧ s.cfg.ver ≤ s'.cfg.ver ∧ TermLe s' ∧
    ∀ x t, t ≤ s.cfg.ver → tp s' x → s'.term x = t →
      tp s x ∧ s.term x = t ∧ s.log x <+: s'.log x := by
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
  | count p r _ _ _ _ _ =>
    exact ⟨List.prefix_refl _, Nat.le_refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | makeElig p r hp hk _ _ =>
    refine ⟨List.prefix_refl _, Nat.le_succ _, fun n => Nat.le_succ_of_le (ht n), ?_⟩
    intro x _ _ hx e
    refine ⟨?_, e, List.prefix_refl _⟩
    by_cases hxp : x = p
    · subst hxp; exact hp
    · unfold tp at hx ⊢; simpa [makeElig, upd_ne _ _ hxp] using hx
  | makeInelig p r hp hk _ =>
    refine ⟨List.prefix_refl _, Nat.le_succ _, fun n => Nat.le_succ_of_le (ht n), ?_⟩
    intro x _ _ hx e
    refine ⟨?_, e, List.prefix_refl _⟩
    by_cases hxp : x = p
    · subst hxp; exact hp
    · unfold tp at hx ⊢; simpa [makeInelig, upd_ne _ _ hxp] using hx
  | learn n hk =>
    refine ⟨List.prefix_refl _, Nat.le_refl _, ht, ?_⟩
    intro x _ _ hx e
    refine ⟨?_, e, List.prefix_refl _⟩
    by_cases hxn : x = n
    · exfalso; apply hk
      have hx' : s.cfg.prim = x := by unfold tp at hx; simpa [learn, hxn] using hx
      unfold kl; rw [← hxn, ← hx', h.primKnows]
    · unfold tp at hx ⊢; simpa [learn, upd_ne _ _ hxn] using hx
  | takeover n _ _ _ =>
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
        · unfold tp at hx ⊢; simpa [takeover, upd_ne _ _ hxn] using hx
        · simpa [takeover, upd_ne _ _ hxn] using e
  | resync r hne _ _ _ =>
    refine ⟨List.prefix_refl _, Nat.le_refl _, ht, ?_⟩
    intro x _ _ hx e
    have hxr : x ≠ r := by
      intro hxr; subst hxr; exact hne hx
    refine ⟨hx, e, ?_⟩
    show s.log x <+: upd s.log r _ x
    rw [upd_ne _ _ hxr]; exact List.prefix_refl _

theorem ainv_core {a : AState Node} {c : State Node} (h : AInv a) {m : Nat} (hs : Step m true a.core c) :
    AInv ⟨c, a.held, a.okd⟩ := by
  obtain ⟨hh, hv, ht', hx⟩ := step_facts h.core h.term hs
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

theorem ainv_step {a a' : AState Node} (h : AInv a) {m : Nat} (hs : AStep m true false a a') :
    AInv a' := by
  cases hs with
  | core c hc => exact ainv_core h hc
  | write p _ _ _ => exact ainv_write h p
  | release x hm hc hf => exact ainv_release h x hm hc (hf rfl)
  | abort x _ _ => exact ainv_abort h x

theorem ainv_reachable {i : Node} {a : AState Node} {m : Nat} (h : AReachable m true false i a) :
    AInv a := by
  induction h with
  | init => exact ainv_init i
  | step _ hs ih => exact ainv_step ih hs

/-- No acknowledged write is lost, for any number of nodes, log length and
configuration changes and EVERY min-sync-replicas value `m`; with reconciliation
against the inherited log (A1) and the F2 fix (reply fence), without any lease or
`cfg.prim = p` fence (F8). -/
theorem ackSafety {i : Node} {a : AState Node} {m : Nat} (h : AReachable m true false i a) :
    AckedDurable a ∧ Safety a.core :=
  let hi := ainv_reachable h
  ⟨hi.acked, inv_safety hi.core⟩

/-- The primary and every eligible replica hold every acknowledged write. -/
theorem ackedHeld {i : Node} {a : AState Node} {m : Nat} (h : AReachable m true false i a) :
    AckedHeld a := by
  obtain ⟨hd, he, _⟩ := ackSafety h
  intro x hx n hn
  obtain ⟨h1, h2, h3⟩ := hd x hx
  have hp := he n hn
  exact ⟨Nat.le_trans h2 hp.length_le, by rw [getD_prefix hp (by omega)]; exact h3⟩

end ReconProof
