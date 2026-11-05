import CoreProof.Inv

/-! Preservation for AppendWrite, Replicate, Ack, Commit, Count, EarlyUncount. -/

namespace CoreProof

variable {Node : Type} [DecidableEq Node]

theorem wit_mono {s s' : State Node} {p w : Node} (hw : Wit s p w)
    (hcfg : s'.cfg = s.cfg) (hknown : s'.known = s.known) (hrecon : s'.recon = s.recon)
    (hgrow : ∀ x, s.log x <+: s'.log x) (hlp : s.acked p w ≤ (s.log p).length)
    (hsync : ∀ r, s.sync p r = true → s'.sync p r = true)
    (hsync' : ∀ r, s'.sync p r = true → s.sync p r = true ∨ (s.known r).prim = p)
    (hacked : ∀ r, (s.known r).prim ≠ p → s'.acked p r = s.acked p r) : Wit s' p w := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  have e : (s'.log p).take (s'.acked p w) = (s.log p).take (s.acked p w) := by
    rw [hacked w h2]; exact (prefix_take_eq (hgrow p) hlp).symm
  refine ⟨hsync w h1, by rw [hknown]; exact h2, ?_, ?_, ?_, ?_⟩
  · intro r hr hf
    rw [hknown] at hf
    rcases hsync' r hr with hr' | hr'
    · rw [hacked w h2, hacked r hf]; exact h3 r hr' hf
    · exact absurd hr' hf
  · rw [hacked w h2, hrecon, hcfg]; exact h4
  · rw [e, hcfg]; exact h5.trans (hgrow _)
  · intro m hm
    rw [hcfg] at hm
    rcases h6 m hm with d | ⟨d1, d2⟩
    · left; rw [e]; exact d.trans (hgrow m)
    · right; exact ⟨hsync m d1, by rw [hknown]; exact d2⟩

/-- Any step that only extends logs preserves the invariant (AppendWrite, Replicate). -/
theorem inv_grow {s : State Node} (h : Inv s) (L : Node → List Nat)
    (hL : ∀ x, s.log x <+: L x) : Inv { s with log := L } where
  ehc := fun n hn => (h.ehc n hn).trans (hL n)
  caLen := fun p => Nat.le_trans (h.caLen p) (hL p).length_le
  caHist := h.caHist
  caEq := by
    intro p
    show (L p).take (s.commit p) = _
    rw [← prefix_take_eq (hL p) (h.caLen p)]; exact h.caEq p
  knownLe := h.knownLe
  knownEq := h.knownEq
  primKnows := h.primKnows
  eligSync := h.eligSync
  noSelfSync := h.noSelfSync
  ackedPrim := h.ackedPrim
  ackedLe := fun p r hp => Nat.le_trans (h.ackedLe p r hp) (hL p).length_le
  ackHolds := by
    intro p n hp hn hf
    show (L p).take (s.acked p n) <+: L n
    rw [← prefix_take_eq (hL p) (h.ackedLe p n hp)]
    exact (h.ackHolds p n hp hn hf).trans (hL n)
  syncNew := h.syncNew
  syncCommit := h.syncCommit
  eligFol := h.eligFol
  histLe := h.histLe
  stale := by
    intro p hp hv
    obtain ⟨w, hw⟩ := h.stale p hp hv
    exact ⟨w, wit_mono hw rfl rfl rfl hL (h.ackedLe p w hp) (fun _ x => x)
      (fun _ x => Or.inl x) (fun _ _ => rfl)⟩

theorem grow_upd (L : Node → List Nat) (p : Node) (m : List Nat) :
    ∀ x, L x <+: upd L p (L p ++ m) x := by
  intro x; by_cases hx : x = p
  · subst hx; simp [List.prefix_append]
  · rw [upd_ne _ _ hx]; exact List.prefix_refl _

theorem inv_append {s : State Node} (h : Inv s) (p : Node) : Inv (appendWrite s p) :=
  inv_grow h _ (grow_upd s.log p _)

theorem inv_replicate {s : State Node} (h : Inv s) (r : Node) : Inv (replicate s r) :=
  inv_grow h _ (grow_upd s.log r _)

theorem inv_ack {s : State Node} (h : Inv s) (r : Node) (hne : pof s r ≠ r)
    (hpre : s.log r <+: s.log (pof s r)) (hlt : s.acked (pof s r) r < (s.log r).length) :
    Inv (ack s r) := by
  -- the only changed entry is acked[p][r]
  have hA : ∀ q x, (ack s r).acked q x =
      if q = pof s r ∧ x = r then (s.log r).length else s.acked q x := by
    intro q x
    by_cases hq : q = pof s r
    · subst hq; by_cases hx : x = r
      · subst hx; simp [ack, upd]
      · simp [ack, upd, hx]
    · simp [ack, upd, hq]
  have hfol : (s.known r).prim = pof s r := rfl
  exact {
  ehc := h.ehc, caLen := h.caLen, caHist := h.caHist, caEq := h.caEq,
  knownLe := h.knownLe, knownEq := h.knownEq, primKnows := h.primKnows,
  eligSync := h.eligSync, noSelfSync := h.noSelfSync
  ackedPrim := by
    intro x hx
    show (ack s r).acked s.cfg.prim x = 0
    rw [hA]; split
    · rename_i hc; obtain ⟨h1, rfl⟩ := hc; exact absurd (h1 ▸ hfol) hx
    · exact h.ackedPrim x hx
  ackedLe := by
    intro q x hq
    show (ack s r).acked q x ≤ _
    rw [hA]; split
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; exact hpre.length_le
    · exact h.ackedLe q x hq
  ackHolds := by
    intro q n hq hn hf
    show (s.log q).take ((ack s r).acked q n) <+: s.log n
    rw [hA]; split
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc
      rw [← prefix_take_eq hpre (Nat.le_refl _), List.take_length]; exact List.prefix_refl _
    · exact h.ackHolds q n hq hn hf
  syncNew := h.syncNew
  syncCommit := by
    intro q x hq hs
    show _ ≤ (ack s r).acked q x
    rw [hA]; split
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; exact Nat.le_trans (h.syncCommit _ _ hq hs) (Nat.le_of_lt hlt)
    · exact h.syncCommit q x hq hs
  eligFol := h.eligFol, histLe := h.histLe
  stale := by
    intro p hp hv
    obtain ⟨w, hw⟩ := h.stale p hp hv
    refine ⟨w, wit_mono hw rfl rfl rfl (fun _ => List.prefix_refl _) (h.ackedLe p w hp)
      (fun _ x => x) (fun _ x => Or.inl x) ?_⟩
    intro x hx
    show (ack s r).acked p x = s.acked p x
    rw [hA]; split
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; exact absurd hfol hx
    · rfl }

theorem inv_commit {s : State Node} (h : Inv s) (p : Node) (hp : tp s p)
    (hlen : s.commit p < (s.log p).length)
    (hcap : ∀ r, s.sync p r = true → s.commit p < s.acked p r) : Inv (commitA s p) := by
  have hold := commit_holds h hp hlen hcap
  have hC : ∀ x, (commitA s p).commit x = if x = p then s.commit p + 1 else s.commit x := by
    intro x; by_cases hx : x = p
    · subst hx; simp [commitA, upd]
    · simp [commitA, upd, hx]
  -- the committed entry agrees with the history when it is already in it
  have hsucc := take_succ_getD hlen
  have hcaEqP := h.caEq p
  have hcl := h.caLen p
  have hch := h.caHist p
  -- new history
  have hH : (commitA s p).hist.take (s.commit p + 1) = (s.log p).take (s.commit p + 1) ∧
      s.hist <+: (commitA s p).hist ∧ (commitA s p).hist.length ≤ s.hist.length + 1 ∧
      ((commitA s p).hist.length = s.hist.length + 1 → s.commit p = s.hist.length) := by
    by_cases he : s.commit p = s.hist.length
    · have hh : (commitA s p).hist = s.hist ++ [(s.log p).getD (s.commit p) 0] := by
        simp [commitA, he]
      rw [hh]
      refine ⟨?_, List.prefix_append _ _, by simp, fun _ => he⟩
      rw [hsucc, hcaEqP, he, List.take_length, List.take_of_length_le (by simp)]
    · have hh : (commitA s p).hist = s.hist := by simp [commitA, he]
      rw [hh]
      refine ⟨?_, List.prefix_refl _, by omega, fun e => by omega⟩
      have hlt : s.commit p + 1 ≤ s.hist.length := by omega
      -- both are prefixes of the current primary's log
      have h1 := hold s.cfg.prim (Or.inr rfl)
      have h2 := h.ehc s.cfg.prim (Or.inr rfl)
      have hl1 : s.commit p + 1 ≤ ((s.log p).take (s.commit p + 1)).length := by
        rw [length_take_of_le hlen]; exact Nat.le_refl _
      have := prefixes_agree h2 h1 (k := s.commit p + 1) hlt hl1
      rw [this, List.take_take]; simp
  obtain ⟨hH1, hH2, hH3, hH4⟩ := hH
  exact {
  ehc := by
    intro n hn
    show (commitA s p).hist <+: s.log n
    by_cases he : s.commit p = s.hist.length
    · have hh : (commitA s p).hist = s.hist ++ [(s.log p).getD (s.commit p) 0] := by
        simp [commitA, he]
      rw [hh]
      have := hold n hn
      rw [hsucc, hcaEqP, he, List.take_length] at this
      rw [he]; exact this
    · have hh : (commitA s p).hist = s.hist := by simp [commitA, he]
      rw [hh]; exact h.ehc n hn
  caLen := by
    intro x; show (commitA s p).commit x ≤ _; rw [hC]; split
    · rename_i hx; subst hx; exact hlen
    · exact h.caLen x
  caHist := by
    intro x; show (commitA s p).commit x ≤ (commitA s p).hist.length; rw [hC]; split
    · rename_i hx; subst hx
      have := hH1; have hl := congrArg List.length this
      rw [length_take_of_le hlen] at hl
      simp [List.length_take] at hl; omega
    · exact Nat.le_trans (h.caHist x) hH2.length_le
  caEq := by
    intro x; show (s.log x).take ((commitA s p).commit x) = (commitA s p).hist.take _; rw [hC]
    split
    · rename_i hx; subst hx; exact hH1.symm
    · rw [h.caEq x]; exact prefix_take_eq hH2 (h.caHist x)
  knownLe := h.knownLe, knownEq := h.knownEq, primKnows := h.primKnows,
  eligSync := h.eligSync, noSelfSync := h.noSelfSync, ackedPrim := h.ackedPrim,
  ackedLe := h.ackedLe, ackHolds := h.ackHolds
  syncNew := by
    intro r hs he
    obtain ⟨a, b⟩ := h.syncNew r hs he
    refine ⟨a, ?_⟩
    show _ ≤ (commitA s p).commit s.cfg.prim
    rw [hC]; split
    · rename_i hx; show s.recon s.cfg.prim ≤ s.commit p + 1; rw [hx] at b; rw [hx]; omega
    · exact b
  syncCommit := by
    intro q r hq hs
    show (commitA s p).commit q ≤ _
    rw [hC]; split
    · rename_i hx; subst hx; exact hcap r hs
    · exact h.syncCommit q r hq hs
  eligFol := h.eligFol
  histLe := by
    show (commitA s p).hist.length ≤ (commitA s p).commit s.cfg.prim ∨
      (commitA s p).hist.length ≤ s.recon s.cfg.prim
    rw [hC]
    rcases tp_cases h hp with ⟨hpe, _⟩ | hv
    · rw [if_pos hpe.symm]
      have hl0 := h.histLe
      rw [← hpe] at hl0
      rcases Nat.lt_or_ge s.hist.length ((commitA s p).hist.length) with hl | hl
      · left; have := hH4 (by omega); omega
      · rcases hl0 with a | a
        · left; omega
        · right; rw [← hpe]; omega
    · have hne := stale_ne_prim h hv
      rw [if_neg (fun e => hne e.symm)]
      rcases Nat.lt_or_ge s.hist.length ((commitA s p).hist.length) with hl | hl
      · right
        have e := hH4 (by omega)
        obtain ⟨w, hw1, _, _, hw4, _⟩ := h.stale p hp hv
        have := hcap w hw1; omega
      · rcases h.histLe with a | a
        · left; omega
        · right; omega
  stale := h.stale }

theorem inv_count {s : State Node} (h : Inv s) (rf : Bool) (hrf : rf = true) (p r : Node)
    (hp : tp s p) (hrec : reconciled rf s p) (hrp : r ≠ p) (hf : pof s r = p)
    (hle : s.commit p ≤ s.acked p r) : Inv (count s p r) := by
  have hS : ∀ q x, (count s p r).sync q x = (s.sync q x || (q = p ∧ x = r)) := by
    intro q x
    by_cases hq : q = p
    · subst hq; by_cases hx : x = r
      · subst hx; simp [count, upd]
      · simp [count, upd, hx]
    · simp [count, upd, hq]
  exact {
  ehc := h.ehc, caLen := h.caLen, caHist := h.caHist, caEq := h.caEq,
  knownLe := h.knownLe, knownEq := h.knownEq, primKnows := h.primKnows
  eligSync := by intro q x hq he; show (count s p r).sync q x = true; rw [hS]; simp [h.eligSync q x hq he]
  noSelfSync := by intro q; show (count s p r).sync q q = false; rw [hS]; simp [h.noSelfSync q]; intro e; subst e; exact fun e => hrp e.symm
  ackedPrim := h.ackedPrim, ackedLe := h.ackedLe, ackHolds := h.ackHolds
  syncNew := by
    intro x hs he
    change (count s p r).sync s.cfg.prim x = true at hs
    rw [hS] at hs
    simp at hs
    rcases hs with hs | ⟨hq, rfl⟩
    · exact h.syncNew x hs he
    · subst hq; exact ⟨hf, hrec hrf⟩
  syncCommit := by
    intro q x hq hs
    change (count s p r).sync q x = true at hs
    rw [hS] at hs; simp at hs
    rcases hs with hs | ⟨rfl, rfl⟩
    · exact h.syncCommit q x hq hs
    · exact hle
  eligFol := h.eligFol, histLe := h.histLe
  stale := by
    intro q hq hv
    obtain ⟨w, hw⟩ := h.stale q hq hv
    refine ⟨w, wit_mono hw rfl rfl rfl (fun _ => List.prefix_refl _) (h.ackedLe q w hq)
      ?_ ?_ (fun _ _ => rfl)⟩
    · intro x hx; show (count s p r).sync q x = true; rw [hS]; simp [hx]
    · intro x hx; change (count s p r).sync q x = true at hx; rw [hS] at hx; simp at hx
      rcases hx with hx | ⟨rfl, rfl⟩
      · exact Or.inl hx
      · exact Or.inr hf }

end CoreProof
