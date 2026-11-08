import SyncReplication.Invariant
import SyncReplication.Contracts

/-!
# Preservation: the commit rule (design §2; promotion step 2)

Commit (a primary advances its committed offset once every sync replica has
acknowledged) and Count (a primary starts counting a caught-up replica).
-/

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

-- Every layer lemma takes the action's whole guard, so some take a part they
-- do not use.
set_option linter.unusedSectionVars false

section commit

variable {s : State Node} (h : Invariant s) (p : Node) (hp : ThinksPrimary s p) (hlen : s.commit p < (s.log p).length) (hcap : ∀ r, s.sync p r = true → s.commit p < s.acked p r)

include h hp hlen hcap

/-- Commit changes no configuration. -/
theorem config_commit : ConfigInvariant (commitNext s p) :=
  (h.toConfigInvariant).frame rfl rfl rfl

/-- The commit guard requires every sync replica to have acknowledged past the new commit point. -/
theorem repl_commit : ReplInvariant (commitNext s p) := by
  have hold := commit_holds h hp hlen hcap
  have hC := commitNext_commit (s := s) p
  have hsucc := take_succ_getD hlen
  have hprefixP := h.committedIsHistoryPrefix p
  have hcl := h.commitWithinLog p
  have hch := h.commitWithinHistory p
  have hH : (commitNext s p).hist.take (s.commit p + 1) = (s.log p).take (s.commit p + 1) ∧
      s.hist <+: (commitNext s p).hist ∧ (commitNext s p).hist.length ≤ s.hist.length + 1 ∧
      ((commitNext s p).hist.length = s.hist.length + 1 → s.commit p = s.hist.length) := by
    by_cases he : s.commit p = s.hist.length
    · have hh := commitNext_hist_new (s := s) he
      rw [hh]
      refine ⟨?_, List.prefix_append _ _, by simp, fun _ => he⟩
      rw [hsucc, hprefixP, he, List.take_length, List.take_of_length_le (by simp)]
    · have hh := commitNext_hist_old (s := s) he
      rw [hh]
      refine ⟨?_, List.prefix_refl _, by omega, fun e => by omega⟩
      have hlt : s.commit p + 1 ≤ s.hist.length := by omega
      -- both are prefixes of the log of an authoritative node
      obtain ⟨a, ha⟩ := h.authEx
      have h1 := hold a ha
      have h2 := h.eligibleHoldsCommitted a ha
      have hl1 : s.commit p + 1 ≤ ((s.log p).take (s.commit p + 1)).length := by
        rw [List.length_take_of_le hlen]
      have := prefixes_agree h2 h1 (k := s.commit p + 1) hlt hl1
      rw [this, List.take_take]; simp
  obtain ⟨hH1, hH2, hH3, hH4⟩ := hH
  exact {
  noSelfSync := h.noSelfSync
  ackedPrim := h.ackedPrim
  ackedLe := h.ackedLe
  ackHolds := h.ackHolds
  ackedHigh := fun q n hq hn hf => Nat.le_trans (h.ackedHigh q n hq hn hf) (commitNext_ackHigh_le p n)
  syncCommit := by
    intro q r hq hs
    show (commitNext s p).commit q ≤ _
    rw [hC]; split_ifs with hx
    · subst hx; exact hcap r hs
    · exact h.syncCommit q r hq hs }

/-- Commit changes no sync replica set or eligibility. -/
theorem membership_commit : MembershipInvariant (commitNext s p) :=
  (h.toMembershipInvariant).frame rfl rfl rfl rfl rfl rfl

/-- The newly committed entry is the history's entry at that offset, or extends the history by one. -/
theorem commit_commit : CommitInvariant (commitNext s p) := by
  have hold := commit_holds h hp hlen hcap
  have hC := commitNext_commit (s := s) p
  have hsucc := take_succ_getD hlen
  have hprefixP := h.committedIsHistoryPrefix p
  have hcl := h.commitWithinLog p
  have hch := h.commitWithinHistory p
  have hH : (commitNext s p).hist.take (s.commit p + 1) = (s.log p).take (s.commit p + 1) ∧
      s.hist <+: (commitNext s p).hist ∧ (commitNext s p).hist.length ≤ s.hist.length + 1 ∧
      ((commitNext s p).hist.length = s.hist.length + 1 → s.commit p = s.hist.length) := by
    by_cases he : s.commit p = s.hist.length
    · have hh := commitNext_hist_new (s := s) he
      rw [hh]
      refine ⟨?_, List.prefix_append _ _, by simp, fun _ => he⟩
      rw [hsucc, hprefixP, he, List.take_length, List.take_of_length_le (by simp)]
    · have hh := commitNext_hist_old (s := s) he
      rw [hh]
      refine ⟨?_, List.prefix_refl _, by omega, fun e => by omega⟩
      have hlt : s.commit p + 1 ≤ s.hist.length := by omega
      -- both are prefixes of the log of an authoritative node
      obtain ⟨a, ha⟩ := h.authEx
      have h1 := hold a ha
      have h2 := h.eligibleHoldsCommitted a ha
      have hl1 : s.commit p + 1 ≤ ((s.log p).take (s.commit p + 1)).length := by
        rw [List.length_take_of_le hlen]
      have := prefixes_agree h2 h1 (k := s.commit p + 1) hlt hl1
      rw [this, List.take_take]; simp
  obtain ⟨hH1, hH2, hH3, hH4⟩ := hH
  exact {
  commitWithinLog := by
    intro x; show (commitNext s p).commit x ≤ _; rw [hC]; split_ifs with hx
    · subst hx; exact hlen
    · exact h.commitWithinLog x
  committedIsHistoryPrefix := by
    intro x; show (s.log x).take ((commitNext s p).commit x) = (commitNext s p).hist.take _; rw [hC]
    split_ifs with hx
    · subst hx; exact hH1.symm
    · rw [h.committedIsHistoryPrefix x]; exact prefix_take_eq hH2 (h.commitWithinHistory x)
  histAck := by
    -- If the history grows, the new entry is at `p`'s commit point, which every other
    -- authoritative node has acknowledged (`commit_ackHigh`) and `p` now has too.
    intro n hn
    have hn' : IsAuthoritative s n := hn
    have hle := commitNext_ackHigh_le (s := s) p n
    rcases Nat.lt_or_ge (commitNext s p).hist.length (s.hist.length + 1) with hl | hg
    · exact Nat.le_trans (Nat.le_trans (Nat.le_of_lt_succ hl) (h.histAck n hn')) hle
    · have he := hH4 (Nat.le_antisymm hH3 hg)
      have hlen' : (commitNext s p).hist.length = s.commit p + 1 := by omega
      rw [hlen']
      by_cases hnp : n = p
      · subst hnp; exact commitNext_ackHigh_self _
      · exact Nat.le_trans (commit_ackHigh h hp hcap n hn' hnp) hle
  inheritedEndWithinLog := h.inheritedEndWithinLog
  historyWithinCommitOrInherited := by
    intro hpa
    have hpa' : PrimaryAuthoritative s := hpa
    show (commitNext s p).hist.length ≤ (commitNext s p).commit s.cfg.primary ∨
      (commitNext s p).hist.length ≤ s.inheritedEnd s.cfg.primary
    rw [hC]
    rcases thinksPrimary_cases h hp with ⟨hpe, _⟩ | hv
    · rw [if_pos hpe.symm]
      have hl0 := h.historyWithinCommitOrInherited hpa'
      rw [← hpe] at hl0
      rcases Nat.lt_or_ge s.hist.length ((commitNext s p).hist.length) with hl | hl
      · left; have := hH4 (by omega); omega
      · rcases hl0 with a | a
        · left; omega
        · right; rw [← hpe]; omega
    · have hne := stale_ne_prim h hv
      rw [if_neg (fun e => hne e.symm)]
      rcases Nat.lt_or_ge s.hist.length ((commitNext s p).hist.length) with hl | hl
      · right
        have e := hH4 (by omega)
        -- a deposed primary commits below its fence, which is below the reconciliation point
        have hF := h.stale p hp hv
        obtain ⟨w, ⟨hw1, _⟩, hwF⟩ := hF.attained
        have := hF.fenceLeInheritedEnd hpa'
        have := hcap w hw1; omega
      · rcases h.historyWithinCommitOrInherited hpa' with a | a
        · left; omega
        · right; omega }

/-- Fences do not mention commit points. -/
theorem failover_commit : FailoverInvariant (commitNext s p) := by
  have hold := commit_holds h hp hlen hcap
  have hsucc := take_succ_getD hlen
  have hprefixP := h.committedIsHistoryPrefix p
  have hcl := h.commitWithinLog p
  have hch := h.commitWithinHistory p
  have hH : (commitNext s p).hist.take (s.commit p + 1) = (s.log p).take (s.commit p + 1) ∧
      s.hist <+: (commitNext s p).hist ∧ (commitNext s p).hist.length ≤ s.hist.length + 1 ∧
      ((commitNext s p).hist.length = s.hist.length + 1 → s.commit p = s.hist.length) := by
    by_cases he : s.commit p = s.hist.length
    · have hh := commitNext_hist_new (s := s) he
      rw [hh]
      refine ⟨?_, List.prefix_append _ _, by simp, fun _ => he⟩
      rw [hsucc, hprefixP, he, List.take_length, List.take_of_length_le (by simp)]
    · have hh := commitNext_hist_old (s := s) he
      rw [hh]
      refine ⟨?_, List.prefix_refl _, by omega, fun e => by omega⟩
      have hlt : s.commit p + 1 ≤ s.hist.length := by omega
      -- both are prefixes of the log of an authoritative node
      obtain ⟨a, ha⟩ := h.authEx
      have h1 := hold a ha
      have h2 := h.eligibleHoldsCommitted a ha
      have hl1 : s.commit p + 1 ≤ ((s.log p).take (s.commit p + 1)).length := by
        rw [List.length_take_of_le hlen]
      have := prefixes_agree h2 h1 (k := s.commit p + 1) hlt hl1
      rw [this, List.take_take]; simp
  obtain ⟨hH1, hH2, hH3, hH4⟩ := hH
  exact {
  -- Commit moves only commit points and the history, which the fence does not mention.
  stale := fun q hq hv => (h.stale q hq hv).mono rfl rfl rfl rfl (fun _ => List.prefix_refl _)
    (commitNext_ackHigh_le p) (fun x => h.ackedLe q x hq) (fun _ x => x) (fun _ _ => rfl)
  authEx := h.authEx }

/-- Every authoritative node already holds the newly committed entry (`commit_holds`). -/
theorem eligibleHoldsCommitted_commit : EligibleHoldsCommitted (commitNext s p) := by
  have hold := commit_holds h hp hlen hcap
  have hsucc := take_succ_getD hlen
  have hprefixP := h.committedIsHistoryPrefix p
  have hcl := h.commitWithinLog p
  have hch := h.commitWithinHistory p
  have hH : (commitNext s p).hist.take (s.commit p + 1) = (s.log p).take (s.commit p + 1) ∧
      s.hist <+: (commitNext s p).hist ∧ (commitNext s p).hist.length ≤ s.hist.length + 1 ∧
      ((commitNext s p).hist.length = s.hist.length + 1 → s.commit p = s.hist.length) := by
    by_cases he : s.commit p = s.hist.length
    · have hh := commitNext_hist_new (s := s) he
      rw [hh]
      refine ⟨?_, List.prefix_append _ _, by simp, fun _ => he⟩
      rw [hsucc, hprefixP, he, List.take_length, List.take_of_length_le (by simp)]
    · have hh := commitNext_hist_old (s := s) he
      rw [hh]
      refine ⟨?_, List.prefix_refl _, by omega, fun e => by omega⟩
      have hlt : s.commit p + 1 ≤ s.hist.length := by omega
      -- both are prefixes of the log of an authoritative node
      obtain ⟨a, ha⟩ := h.authEx
      have h1 := hold a ha
      have h2 := h.eligibleHoldsCommitted a ha
      have hl1 : s.commit p + 1 ≤ ((s.log p).take (s.commit p + 1)).length := by
        rw [List.length_take_of_le hlen]
      have := prefixes_agree h2 h1 (k := s.commit p + 1) hlt hl1
      rw [this, List.take_take]; simp
  obtain ⟨hH1, hH2, hH3, hH4⟩ := hH
  intro n hn
  show (commitNext s p).hist <+: s.log n
  by_cases he : s.commit p = s.hist.length
  · have hh := commitNext_hist_new (s := s) he
    rw [hh]
    have := hold n hn
    rw [hsucc, hprefixP, he, List.take_length] at this
    rw [he]; exact this
  · have hh := commitNext_hist_old (s := s) he
    rw [hh]; exact h.eligibleHoldsCommitted n hn

theorem invariant_commit : Invariant (commitNext s p) where
  toConfigInvariant := config_commit h p hp hlen hcap
  toReplInvariant := repl_commit h p hp hlen hcap
  toMembershipInvariant := membership_commit h p hp hlen hcap
  toCommitInvariant := commit_commit h p hp hlen hcap
  toFailoverInvariant := failover_commit h p hp hlen hcap
  eligibleHoldsCommitted := eligibleHoldsCommitted_commit h p hp hlen hcap

end commit

section count

variable {s : State Node} (h : Invariant s) (p r : Node) (hp : ThinksPrimary s p) (hrp : r ≠ p) (hf : primaryOf s r = p) (hcup : catchUpPoint s p ≤ s.acked p r)

include h r hp hrp hf hcup

/-- Count changes no configuration. -/
theorem config_count : ConfigInvariant (count s p r) :=
  (h.toConfigInvariant).frame rfl rfl rfl

/-- `r` has acknowledged up to the catch-up point, which is at least `p`'s commit point, so `p` still never commits past a sync replica's acknowledgement. -/
theorem repl_count : ReplInvariant (count s p r) := by
  have hle : s.commit p ≤ s.acked p r := Nat.le_trans (commit_le_catchUpPoint h p) hcup
  have hS := count_sync (s := s) p r
  exact {
  noSelfSync := by intro q; show (count s p r).sync q q = false; rw [hS, h.noSelfSync q]; simp only [Bool.false_or, decide_eq_false_iff_not]; exact fun ⟨e1, e2⟩ => hrp (e2.symm.trans e1)
  ackedPrim := h.ackedPrim
  ackedLe := h.ackedLe
  ackHolds := h.ackHolds
  ackedHigh := h.ackedHigh
  syncCommit := by
    intro q x hq hs
    change (count s p r).sync q x = true at hs
    rw [hS] at hs; simp at hs
    rcases hs with hs | ⟨rfl, rfl⟩
    · exact h.syncCommit q x hq hs
    · exact hle }

/-- A newly counted ineligible replica follows `p` and has acknowledged past the reconciliation point (promotion steps 1-2). -/
theorem membership_count : MembershipInvariant (count s p r) := by
  have h0 := h
  have hS := count_sync (s := s) p r
  exact {
  eligibleCounted := by intro q x hq he hi; show (count s p r).sync q x = true; rw [hS]; simp [h.eligibleCounted q x hq he hi]
  syncNew := by
    intro x hs he
    change (count s p r).sync s.cfg.primary x = true at hs
    rw [hS] at hs
    simp at hs
    rcases hs with hs | ⟨hq, rfl⟩
    · exact h.syncNew x hs he
    · subst hq
      have := Nat.le_trans (inheritedEnd_le_catchUpPoint (s := s) h0) hcup
      exact ⟨hf, this⟩
  eligibleInOldConfig := h.eligibleInOldConfig }

/-- Count changes no commit point, catch-up point or history. -/
theorem commit_count : CommitInvariant (count s p r) :=
  (h.toCommitInvariant).frame rfl rfl rfl rfl rfl rfl rfl

/-- Adding a sync replica does not move a fence. -/
theorem failover_count : FailoverInvariant (count s p r) := by
  have hS := count_sync (s := s) p r
  exact {
  stale := by
    -- Count only adds a replica to a sync replica set.
    intro q hq hv
    refine (h.stale q hq hv).mono rfl rfl rfl rfl (fun _ => List.prefix_refl _) (fun _ => Nat.le_refl _)
      (fun x => h.ackedLe q x hq) ?_ (fun _ _ => rfl)
    intro x hx; show (count s p r).sync q x = true; rw [hS]; simp [hx]
  authEx := h.authEx }

/-- Count moves no log. -/
theorem eligibleHoldsCommitted_count : EligibleHoldsCommitted (count s p r) := by
  exact h.eligibleHoldsCommitted

theorem invariant_count : Invariant (count s p r) where
  toConfigInvariant := config_count h p r hp hrp hf hcup
  toReplInvariant := repl_count h p r hp hrp hf hcup
  toMembershipInvariant := membership_count h p r hp hrp hf hcup
  toCommitInvariant := commit_count h p r hp hrp hf hcup
  toFailoverInvariant := failover_count h p r hp hrp hf hcup
  eligibleHoldsCommitted := eligibleHoldsCommitted_count h p r hp hrp hf hcup

end count

section uncount

variable {s : State Node} (h : Invariant s) (p r : Node) (hp : ThinksPrimary s p)
  (hs : s.sync p r = true) (hel : (s.known p).eligible r = false)

include h hp hs hel

/-- Uncount changes no configuration. -/
theorem config_uncount : ConfigInvariant (uncount s p r) :=
  (h.toConfigInvariant).frame rfl rfl rfl

/-- Removing a sync replica only weakens the commit rule's obligation. -/
theorem repl_uncount : ReplInvariant (uncount s p r) := by
  have hS := uncount_sync (s := s) p r
  exact {
  noSelfSync := by intro q; show (uncount s p r).sync q q = false; rw [hS, h.noSelfSync q]; simp
  ackedPrim := h.ackedPrim
  ackedLe := h.ackedLe
  ackHolds := h.ackHolds
  ackedHigh := h.ackedHigh
  syncCommit := by
    intro q x hq hx
    change (uncount s p r).sync q x = true at hx
    rw [hS] at hx; simp at hx
    exact h.syncCommit q x hq hx.1 }

/-- `r` was not eligible in `p`'s configuration, so no eligible replica stops being
counted. -/
theorem membership_uncount : MembershipInvariant (uncount s p r) := by
  have hS := uncount_sync (s := s) p r
  exact {
  eligibleCounted := by
    intro q x hq hex hi
    change (s.known q).eligible x = true at hex
    change (s.known q).incarnation x = s.incarnation x at hi
    show (uncount s p r).sync q x = true
    rw [hS]; simp only [Bool.and_eq_true, h.eligibleCounted q x hq hex hi, Bool.not_eq_true', decide_eq_false_iff_not, true_and]
    rintro ⟨e1, e2⟩; subst e1; subst e2
    rw [hex] at hel; exact absurd hel (by decide)
  syncNew := by
    intro x hx hex
    change (uncount s p r).sync s.cfg.primary x = true at hx
    rw [hS] at hx; simp at hx
    exact h.syncNew x hx.1 hex
  eligibleInOldConfig := h.eligibleInOldConfig }

/-- Uncount changes no commit point, catch-up point or history. -/
theorem commit_uncount : CommitInvariant (uncount s p r) :=
  (h.toCommitInvariant).frame rfl rfl rfl rfl rfl rfl rfl

/-- A deposed primary may drop members, but only ones it does not list as eligible, and
only those it lists as eligible fence it: the member that sets its fence stays. An
eligible member that still follows it is not the dropped one either
(`eligibleInOldConfig`). -/
theorem failover_uncount : FailoverInvariant (uncount s p r) := by
  have hS := uncount_sync (s := s) p r
  exact {
  stale := by
    intro q hq hv
    have hv' : (s.known q).version < s.cfg.version := hv
    have hF := h.stale q hq hv'
    obtain ⟨w, ⟨hw1, hw2⟩, hwF⟩ := hF.attained
    have hwr : ¬ (q = p ∧ w = r) := by
      rintro ⟨e1, e2⟩; subst e1; subst e2
      rw [hel] at hw2; exact absurd hw2.2 (by decide)
    refine DeposedFenced.of_left (w := w) ⟨by rw [hS, hw1]; simp only [Bool.true_and, Bool.not_eq_true', decide_eq_false_iff_not]; exact hwr, hw2⟩ ?_ ?_ ?_ ?_
    · intro hpa; show s.acked q w ≤ s.inheritedEnd s.cfg.primary; rw [hwF]; exact hF.fenceLeInheritedEnd hpa
    · intro hpa; show (s.log q).take (s.acked q w) <+: s.log s.cfg.primary; rw [hwF]; exact hF.primHolds hpa
    · intro hpa; show s.acked q w ≤ s.ackHigh s.cfg.primary; rw [hwF]; exact hF.primAck hpa
    · intro m hm hi
      show ((s.log q).take (s.acked q w) <+: s.log m ∧ s.acked q w ≤ s.ackHigh m) ∨
        ((uncount s p r).sync q m = true ∧ (s.known m).primary = q)
      rw [hwF]
      rcases hF.eligHolds m hm hi with d | ⟨d1, d2⟩
      · exact Or.inl d
      · right; refine ⟨?_, d2⟩
        rw [hS, d1]; simp only [Bool.true_and, Bool.not_eq_true', decide_eq_false_iff_not]
        rintro ⟨e1, e2⟩; subst e1; subst e2
        have hold := h.eligibleInOldConfig m hm (by rw [d2]; exact stale_ne_prim h hv')
        rw [d2, hel] at hold; exact absurd hold (by decide)
  authEx := h.authEx }

/-- Uncount moves no log. -/
theorem eligibleHoldsCommitted_uncount : EligibleHoldsCommitted (uncount s p r) := h.eligibleHoldsCommitted

theorem invariant_uncount : Invariant (uncount s p r) where
  toConfigInvariant := config_uncount h p r hp hs hel
  toReplInvariant := repl_uncount h p r hp hs hel
  toMembershipInvariant := membership_uncount h p r hp hs hel
  toCommitInvariant := commit_uncount h p r hp hs hel
  toFailoverInvariant := failover_uncount h p r hp hs hel
  eligibleHoldsCommitted := eligibleHoldsCommitted_uncount h p r hp hs hel

end uncount

end SyncReplication
