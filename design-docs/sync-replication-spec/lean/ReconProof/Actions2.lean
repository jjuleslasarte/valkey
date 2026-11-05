import ReconProof.Actions1

/-! Preservation for Learn, MakeEligible, MakeIneligible, Takeover, Resync. -/

namespace ReconProof

variable {Node : Type} [DecidableEq Node]

theorem upd_eq_ite {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) (x : α) :
    upd f a b x = if x = a then b else f x := rfl

/-! ### Learn -/

theorem inv_learn {s : State Node} (h : Inv s) (n : Node) (hk : ¬ kl s n) : Inv (learn s n) := by
  have hnp : n ≠ s.cfg.prim := by
    intro e; apply hk; unfold kl; rw [e, h.primKnows]
  have hK : ∀ x, (learn s n).known x = if x = n then s.cfg else s.known x := fun _ => rfl
  have hSn : (learn s n).sync n = fun _ => false := by
    simp [learn, upd, Ne.symm hnp]
  have hS : ∀ x, x ≠ n → (learn s n).sync x = s.sync x := by
    intro x hx; simp [learn, upd, hx]
  have htp : ∀ x, tp (learn s n) x → x ≠ n ∧ tp s x := by
    intro x hx
    unfold tp at hx; rw [hK] at hx
    by_cases e : x = n
    · rw [if_pos e] at hx; exact absurd (hx.trans e).symm hnp
    · rw [if_neg e] at hx; exact ⟨e, hx⟩
  exact {
  ehc := h.ehc, caLen := h.caLen, caHist := h.caHist, caEq := h.caEq
  knownLe := by
    intro x; show ((learn s n).known x).ver ≤ s.cfg.ver; rw [hK]; split
    · exact Nat.le_refl _
    · exact h.knownLe x
  knownEq := by
    intro x hx; show (learn s n).known x = s.cfg; rw [hK] at hx ⊢; split
    · rfl
    · rename_i e; rw [if_neg e] at hx; exact h.knownEq x hx
  primKnows := by show (learn s n).known s.cfg.prim = s.cfg; rw [hK, if_neg (Ne.symm hnp)]; exact h.primKnows
  eligSync := by
    intro p r hp he
    obtain ⟨hpn, hp'⟩ := htp p hp
    rw [hS p hpn]; rw [hK, if_neg hpn] at he; exact h.eligSync p r hp' he
  noSelfSync := by
    intro p; by_cases e : p = n
    · subst e; rw [hSn]
    · rw [hS p e]; exact h.noSelfSync p
  ackedPrim := by
    intro r hr; change (if r = n then s.cfg else s.known r).prim ≠ s.cfg.prim at hr
    show s.acked s.cfg.prim r = 0
    split at hr
    · exact absurd rfl hr
    · exact h.ackedPrim r hr
  ackedLe := by intro p r hp; exact h.ackedLe p r (htp p hp).2
  ackHolds := by
    intro p m hp hm hf
    obtain ⟨hpn, hp'⟩ := htp p hp
    change (if m = n then s.cfg else s.known m).prim = p at hf
    show (s.log p).take (s.acked p m) <+: s.log m
    split at hf
    · rename_i e; subst e
      by_cases hf0 : (s.known m).prim = p
      · exact h.ackHolds p m hp' hm hf0
      · rw [← hf] at hf0 ⊢; rw [h.ackedPrim m hf0]; simp
    · exact h.ackHolds p m hp' hm hf
  syncNew := by
    intro r hs he
    have hs0 : (learn s n).sync s.cfg.prim r = true := hs
    rw [hS _ (Ne.symm hnp)] at hs0
    have hs := hs0
    show _ ∧ s.recon s.cfg.prim ≤ s.acked s.cfg.prim r
    obtain ⟨a, b⟩ := h.syncNew r hs he
    refine ⟨?_, b⟩
    show (if r = n then s.cfg else s.known r).prim = s.cfg.prim
    split
    · rfl
    · exact a
  reconLen := h.reconLen
  syncCommit := by
    intro q r hq hs
    obtain ⟨hqn, hq'⟩ := htp q hq
    rw [hS q hqn] at hs; exact h.syncCommit q r hq' hs
  eligFol := by
    intro m he hf
    change (if m = n then s.cfg else s.known m).prim ≠ s.cfg.prim at hf
    show ((learn s n).known ((learn s n).known m).prim).elig m = true
    rw [hK m]
    split at hf
    · exact absurd rfl hf
    · rename_i e
      rw [if_neg e, hK]
      split
      · exact he
      · exact h.eligFol m he hf
  histLe := h.histLe
  stale := by
    intro p hp hv
    obtain ⟨hpn, hp'⟩ := htp p hp
    have hv' : (s.known p).ver < s.cfg.ver := by
      have := hv; change ((if p = n then s.cfg else s.known p).ver < s.cfg.ver) at this
      rwa [if_neg hpn] at this
    have hprim := stale_ne_prim h hv'
    obtain ⟨w, hw1, hw2, hw3, hw4, hw5, hw6⟩ := h.stale p hp' hv'
    -- frozen in the post-state
    have hfz : ∀ r, ((learn s n).known r).prim ≠ p ↔ (r = n ∨ (s.known r).prim ≠ p) := by
      intro r; rw [hK]; by_cases e : r = n
      · subst e; simp; exact fun x => hprim x.symm
      · simp [e]
    have hSp : (learn s n).sync p = s.sync p := hS p hpn
    by_cases hsw : s.sync p n = true ∧ (s.known n).prim = p ∧ s.acked p n < s.acked p w
    · obtain ⟨hs1, hs2, hs3⟩ := hsw
      have hnp' : n ≠ p := fun e => hpn e.symm
      refine ⟨n, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hSp]; exact hs1
      · exact (hfz n).2 (Or.inl rfl)
      · intro r hr hf
        rw [hSp] at hr
        rcases (hfz r).1 hf with e | hf'
        · subst e; exact Nat.le_refl _
        · exact Nat.le_trans (Nat.le_of_lt hs3) (hw3 r hr hf')
      · show s.acked p n ≤ s.recon s.cfg.prim; omega
      · exact take_mono_prefix (Nat.le_of_lt hs3) hw5
      · intro m hm
        rcases hw6 m hm with d | ⟨d1, d2⟩
        · exact Or.inl (take_mono_prefix (Nat.le_of_lt hs3) d)
        · by_cases e : m = n
          · subst e; exact Or.inl (h.ackHolds p m hp' hnp' hs2)
          · right; rw [hSp]; refine ⟨d1, ?_⟩
            show (if m = n then s.cfg else s.known m).prim = p; rw [if_neg e]; exact d2
    · refine ⟨w, ?_, ?_, ?_, hw4, hw5, ?_⟩
      · rw [hSp]; exact hw1
      · exact (hfz w).2 (Or.inr hw2)
      · intro r hr hf
        rw [hSp] at hr
        show s.acked p w ≤ s.acked p r
        rcases (hfz r).1 hf with e | hf'
        · subst e
          by_cases hf0 : (s.known r).prim = p
          · exact Nat.le_of_not_lt (fun hl => hsw ⟨hr, hf0, hl⟩)
          · exact hw3 r hr hf0
        · exact hw3 r hr hf'
      · intro m hm
        rcases hw6 m hm with d | ⟨d1, d2⟩
        · exact Or.inl d
        · by_cases e : m = n
          · subst e
            have hnp' : m ≠ p := fun e => hpn e.symm
            have hle : s.acked p w ≤ s.acked p m :=
              Nat.le_of_not_lt (fun hl => hsw ⟨d1, d2, hl⟩)
            exact Or.inl (take_mono_prefix hle (h.ackHolds p m hp' hnp' d2))
          · right; rw [hSp]; refine ⟨d1, ?_⟩
            show (if m = n then s.cfg else s.known m).prim = p; rw [if_neg e]; exact d2 }

/-! ### A witness survives steps that leave the stale primary's row alone. -/

theorem wit_transfer {s s' : State Node} {x w : Node} (hw : Wit s x w)
    (hsync : s'.sync x = s.sync x) (hkn : ∀ y, (s'.known y).prim = (s.known y).prim)
    (hack : s'.acked x w = s.acked x w)
    (hack' : ∀ r, s.sync x r = true → s'.acked x r = s.acked x r)
    (hlog : s'.log x = s.log x) (hprim : s'.cfg.prim = s.cfg.prim)
    (hrec : s'.recon s.cfg.prim = s.recon s.cfg.prim)
    (hlp : s'.log s.cfg.prim = s.log s.cfg.prim)
    (hcov : ∀ m, s'.cfg.elig m = true →
      (s.cfg.elig m = true ∧ s'.log m = s.log m) ∨ (s.log x).take (s.acked x w) <+: s'.log m) :
    Wit s' x w := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  refine ⟨by rw [hsync]; exact h1, by rw [hkn]; exact h2, ?_, ?_, ?_, ?_⟩
  · intro r hr hf; rw [hsync] at hr; rw [hkn] at hf
    rw [hack, hack' r hr]; exact h3 r hr hf
  · rw [hack, hprim, hrec]; exact h4
  · rw [hack, hlog, hprim, hlp]; exact h5
  · intro m hm
    rcases hcov m hm with ⟨he, hl⟩ | d
    · rcases h6 m he with d | ⟨d1, d2⟩
      · left; rw [hack, hlog, hl]; exact d
      · right; rw [hsync, hkn]; exact ⟨d1, d2⟩
    · left; rw [hack, hlog]; exact d

/-! ### MakeEligible / MakeIneligible -/

section cas
variable {s : State Node} (h : Inv s) {p r : Node} (hp : tp s p) (hkl : kl s p)
include h hp hkl

theorem inv_makeElig (hs : s.sync p r = true) (he : s.cfg.elig r = false) :
    Inv (makeElig s p r) := by
  obtain ⟨hkp, hpp⟩ := tp_kl h hp hkl
  subst hpp
  have hK : ∀ x, (makeElig s s.cfg.prim r).known x =
      if x = s.cfg.prim then eligCfg s r true else s.known x := fun _ => rfl
  have hKp : ∀ x, ((makeElig s s.cfg.prim r).known x).prim = (s.known x).prim := by
    intro x; rw [hK]; split
    · rename_i e; subst e; rw [hkp]; rfl
    · rfl
  have hE : ∀ x, (makeElig s s.cfg.prim r).cfg.elig x = if x = r then true else s.cfg.elig x :=
    fun _ => rfl
  have hrp : r ≠ s.cfg.prim := by
    intro e; rw [e, h.noSelfSync] at hs; exact Bool.false_ne_true hs
  obtain ⟨hrf, hrec⟩ := h.syncNew r hs he
  -- the new eligible replica holds the history: it acked at least the history's
  -- length (the primary's commit or its reconciliation point) of the primary's log
  have hra : (s.log s.cfg.prim).take (s.acked s.cfg.prim r) <+: s.log r :=
    h.ackHolds _ _ (tp_prim h) hrp hrf
  have hsc := h.syncCommit _ _ (tp_prim h) hs
  have hhl : s.hist.length ≤ s.acked s.cfg.prim r := by
    rcases h.histLe with a | a <;> omega
  have hhist : s.hist <+: s.log r := by
    have hp0 := h.ehc s.cfg.prim (Or.inr rfl)
    have e := prefix_take_eq hp0 (Nat.le_refl s.hist.length)
    rw [List.take_length] at e
    rw [e]; exact take_mono_prefix hhl hra
  have htp : ∀ x, tp (makeElig s s.cfg.prim r) x ↔ tp s x := by
    intro x; unfold tp; rw [hKp]
  exact {
  ehc := by
    intro n hn
    change (if n = r then true else s.cfg.elig n) = true ∨ n = s.cfg.prim at hn
    by_cases e : n = r
    · subst e; exact hhist
    · rw [if_neg e] at hn; exact h.ehc n hn
  caLen := h.caLen, caHist := h.caHist, caEq := h.caEq
  knownLe := by
    intro x; show ((makeElig s s.cfg.prim r).known x).ver ≤ s.cfg.ver + 1; rw [hK]; split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (h.knownLe x)
  knownEq := by
    intro x hx; change ((makeElig s s.cfg.prim r).known x).ver = s.cfg.ver + 1 at hx
    show (makeElig s s.cfg.prim r).known x = eligCfg s r true
    rw [hK] at hx ⊢; split
    · rfl
    · rename_i e; rw [if_neg e] at hx; have := h.knownLe x; omega
  primKnows := by show (makeElig s s.cfg.prim r).known s.cfg.prim = _; rw [hK, if_pos rfl]; rfl
  eligSync := by
    intro x y hx hy
    show s.sync x y = true
    rw [hK] at hy
    split at hy
    · rename_i e; subst e
      change (if y = r then true else s.cfg.elig y) = true at hy
      by_cases ey : y = r
      · subst ey; exact hs
      · rw [if_neg ey] at hy; exact h.eligSync _ y (tp_prim h) (by rw [h.primKnows]; exact hy)
    · exact h.eligSync x y ((htp x).1 hx) hy
  noSelfSync := h.noSelfSync
  ackedPrim := by intro x hx; rw [hKp] at hx; exact h.ackedPrim x hx
  ackedLe := by intro x y hx; exact h.ackedLe x y ((htp x).1 hx)
  ackHolds := by intro x y hx hy hf; rw [hKp] at hf; exact h.ackHolds x y ((htp x).1 hx) hy hf
  syncNew := by
    intro x hx hxe
    rw [hE] at hxe
    split at hxe
    · exact absurd hxe (by decide)
    · obtain ⟨a, b⟩ := h.syncNew x hx hxe; rw [hKp]; exact ⟨a, b⟩
  syncCommit := by intro x y hx; exact h.syncCommit x y ((htp x).1 hx)
  eligFol := by
    intro m hm hf
    rw [hKp] at hf
    change (s.known m).prim ≠ s.cfg.prim at hf
    rw [hE] at hm
    split at hm
    · rename_i e; subst e; exact absurd hrf hf
    · rw [hKp, hK, if_neg hf]; exact h.eligFol m hm hf
  histLe := h.histLe
  reconLen := h.reconLen
  stale := by
    intro x hx hv
    have hx' := (htp x).1 hx
    have hxp : x ≠ s.cfg.prim := by
      intro e; subst e; rw [hK, if_pos rfl] at hv; exact Nat.lt_irrefl _ hv
    have hv' : (s.known x).ver < s.cfg.ver := by
      rw [hK, if_neg hxp] at hv
      rcases Nat.lt_or_ge (s.known x).ver s.cfg.ver with a | a
      · exact a
      · exfalso; have := h.knownEq x (Nat.le_antisymm (h.knownLe x) a)
        exact hxp (tp_kl h hx' (by unfold kl; rw [this])).2.symm
    obtain ⟨w, hw⟩ := h.stale x hx' hv'
    refine ⟨w, wit_transfer hw rfl hKp rfl (fun _ _ => rfl) rfl rfl rfl rfl ?_⟩
    intro m hm
    rw [hE] at hm
    split at hm
    · rename_i e; subst e; right
      obtain ⟨_, _, _, hw4, hw5, _⟩ := hw
      exact take_transfer (Nat.le_trans hw4 hrec) (h.ackedLe x w hx') hw5 hra
    · left; exact ⟨hm, rfl⟩ }

theorem inv_makeInelig (he : s.cfg.elig r = true) : Inv (makeInelig s p r) := by
  obtain ⟨hkp, hpp⟩ := tp_kl h hp hkl
  subst hpp
  have hK : ∀ x, (makeInelig s s.cfg.prim r).known x =
      if x = s.cfg.prim then eligCfg s r false else s.known x := fun _ => rfl
  have hKp : ∀ x, ((makeInelig s s.cfg.prim r).known x).prim = (s.known x).prim := by
    intro x; rw [hK]; split
    · rename_i e; subst e; rw [hkp]; rfl
    · rfl
  have hE : ∀ x, (makeInelig s s.cfg.prim r).cfg.elig x = if x = r then false else s.cfg.elig x :=
    fun _ => rfl
  have hS : ∀ x y, (makeInelig s s.cfg.prim r).sync x y =
      if x = s.cfg.prim ∧ y = r then false else s.sync x y := by
    intro x y
    by_cases ex : x = s.cfg.prim
    · subst ex; by_cases ey : y = r
      · subst ey; simp [makeInelig, upd]
      · simp [makeInelig, upd, ey]
    · simp [makeInelig, upd, ex]
  have hSle : ∀ x y, (makeInelig s s.cfg.prim r).sync x y = true → s.sync x y = true := by
    intro x y hxy; rw [hS] at hxy; split at hxy
    · exact absurd hxy Bool.false_ne_true
    · exact hxy
  have htp : ∀ x, tp (makeInelig s s.cfg.prim r) x ↔ tp s x := by
    intro x; unfold tp; rw [hKp]
  have hEle : ∀ m, (makeInelig s s.cfg.prim r).cfg.elig m = true → m ≠ r ∧ s.cfg.elig m = true := by
    intro m hm; rw [hE] at hm; split at hm
    · exact absurd hm Bool.false_ne_true
    · rename_i e; exact ⟨e, hm⟩
  exact {
  ehc := by
    intro n hn
    rcases hn with hn | hn
    · exact h.ehc n (Or.inl (hEle n hn).2)
    · exact h.ehc n (Or.inr hn)
  caLen := h.caLen, caHist := h.caHist, caEq := h.caEq
  knownLe := by
    intro x; show ((makeInelig s s.cfg.prim r).known x).ver ≤ s.cfg.ver + 1; rw [hK]; split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (h.knownLe x)
  knownEq := by
    intro x hx; change ((makeInelig s s.cfg.prim r).known x).ver = s.cfg.ver + 1 at hx
    show (makeInelig s s.cfg.prim r).known x = eligCfg s r false
    rw [hK] at hx ⊢; split
    · rfl
    · rename_i e; rw [if_neg e] at hx; have := h.knownLe x; omega
  primKnows := by show (makeInelig s s.cfg.prim r).known s.cfg.prim = _; rw [hK, if_pos rfl]; rfl
  eligSync := by
    intro x y hx hy
    rw [hS]
    rw [hK] at hy
    split at hy
    · rename_i e; subst e
      change (if y = r then false else s.cfg.elig y) = true at hy
      split at hy
      · exact absurd hy Bool.false_ne_true
      · rename_i ey
        rw [if_neg (fun c => ey c.2)]
        exact h.eligSync _ y (tp_prim h) (by rw [h.primKnows]; exact hy)
    · rename_i e; rw [if_neg (fun c => e c.1)]; exact h.eligSync x y ((htp x).1 hx) hy
  noSelfSync := by
    intro x; rw [hS]; split
    · rfl
    · exact h.noSelfSync x
  ackedPrim := by intro x hx; rw [hKp] at hx; exact h.ackedPrim x hx
  ackedLe := by intro x y hx; exact h.ackedLe x y ((htp x).1 hx)
  ackHolds := by intro x y hx hy hf; rw [hKp] at hf; exact h.ackHolds x y ((htp x).1 hx) hy hf
  syncNew := by
    intro x hx hxe
    have hx0 := hSle _ _ hx
    rw [hS] at hx
    rw [hE] at hxe
    split at hxe
    · rename_i e; subst e; rw [if_pos ⟨rfl, rfl⟩] at hx; exact absurd hx Bool.false_ne_true
    · obtain ⟨a, b⟩ := h.syncNew x hx0 hxe; rw [hKp]; exact ⟨a, b⟩
  syncCommit := by intro x y hx hxy; exact h.syncCommit x y ((htp x).1 hx) (hSle x y hxy)
  eligFol := by
    intro m hm hf
    obtain ⟨_, hm'⟩ := hEle m hm
    rw [hKp] at hf
    change (s.known m).prim ≠ s.cfg.prim at hf
    rw [hKp, hK, if_neg hf]; exact h.eligFol m hm' hf
  histLe := h.histLe
  reconLen := h.reconLen
  stale := by
    intro x hx hv
    have hx' := (htp x).1 hx
    have hxp : x ≠ s.cfg.prim := by
      intro e; subst e; rw [hK, if_pos rfl] at hv; exact Nat.lt_irrefl _ hv
    have hv' : (s.known x).ver < s.cfg.ver := by
      rw [hK, if_neg hxp] at hv
      rcases Nat.lt_or_ge (s.known x).ver s.cfg.ver with a | a
      · exact a
      · exfalso; have := h.knownEq x (Nat.le_antisymm (h.knownLe x) a)
        exact hxp (tp_kl h hx' (by unfold kl; rw [this])).2.symm
    obtain ⟨w, hw⟩ := h.stale x hx' hv'
    have hSx : (makeInelig s s.cfg.prim r).sync x = s.sync x := by
      funext y; rw [hS, if_neg (fun c => hxp c.1)]
    exact ⟨w, wit_transfer hw hSx hKp rfl (fun _ _ => rfl) rfl rfl rfl rfl
      (fun m hm => Or.inl ⟨(hEle m hm).2, rfl⟩)⟩ }

end cas

end ReconProof
