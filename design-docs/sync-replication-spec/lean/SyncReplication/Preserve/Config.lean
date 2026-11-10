import SyncReplication.Invariant
import SyncReplication.Contracts

/-!
# Preservation: shard configuration (design §4 promotion and demotion; §6 Cluster V2)

Learn (a node adopts the latest configuration), MakeEligible (promotion step 4) and
MakeIneligible (demotion).
-/

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

-- Every layer lemma takes the action's guard; a lemma that does not use part of it
-- says so with `omit ... in`.

theorem upd_eq_ite {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) (x : α) :
    update f a b x = if x = a then b else f x := rfl

/-! ### Learn -/

section learn
variable {s : State Node} (h : Invariant s) (n : Node) (hnkl : ¬ KnowsLatest s n)
include h hnkl

/-- `n`'s copy of the configuration becomes the latest one; no recorded incarnation changes. -/
theorem config_learn : ConfigInvariant (learn s n) := by
  have hnp : n ≠ s.cfg.primary := by
    intro e; apply hnkl; unfold KnowsLatest; rw [e, h.primKnows]
  have hK := learn_localCfg (s := s) (n := n)
  exact {
  localCfgLe := by
    intro x; show ((learn s n).localCfg x).epoch ≤ s.cfg.epoch; rw [hK]; split
    · exact Nat.le_refl _
    · exact h.localCfgLe x
  localCfgEq := by
    intro x hx; show (learn s n).localCfg x = s.cfg; rw [hK] at hx ⊢; split_ifs with e
    · rfl
    · rw [if_neg e] at hx; exact h.localCfgEq x hx
  primKnows := by show (learn s n).localCfg s.cfg.primary = s.cfg; rw [hK, if_neg (Ne.symm hnp)]; exact h.primKnows
  localCfgIncLe := by
    intro x y; rw [hK]; split
    · exact h.incLe y
    · exact h.localCfgIncLe x y }

/-- `n`, which is not the primary, drops its sync replica set; no log or acknowledgement moves. -/
theorem repl_learn : ReplInvariant (learn s n) := by
  have hnp : n ≠ s.cfg.primary := by
    intro e; apply hnkl; unfold KnowsLatest; rw [e, h.primKnows]
  have hSn : (learn s n).sync n = fun _ => false := learn_sync_self hnp
  have hS : ∀ x, x ≠ n → (learn s n).sync x = s.sync x := fun _ => learn_sync_other
  have htp : ∀ x, ThinksPrimary (learn s n) x → x ≠ n ∧ ThinksPrimary s x :=
    fun _ => learn_thinksPrimary hnp
  exact {
  noSelfSync := by
    intro p; by_cases e : p = n
    · subst e; rw [hSn]
    · rw [hS p e]; exact h.noSelfSync p
  ackedPrim := by
    intro r hr; change (if r = n then s.cfg else s.localCfg r).primary ≠ s.cfg.primary at hr
    show s.acked s.cfg.primary r = 0
    split at hr
    · exact absurd rfl hr
    · exact h.ackedPrim r hr
  ackedLe := by intro p r hp; exact h.ackedLe p r (htp p hp).2
  ackHolds := by
    intro p m hp hm hf
    obtain ⟨hpn, hp'⟩ := htp p hp
    change (if m = n then s.cfg else s.localCfg m).primary = p at hf
    show (s.log p).take (s.acked p m) <+: s.log m
    split_ifs at hf with e
    · subst e
      by_cases hf0 : (s.localCfg m).primary = p
      · exact h.ackHolds p m hp' hm hf0
      · rw [← hf] at hf0 ⊢; rw [h.ackedPrim m hf0]; simp
    · exact h.ackHolds p m hp' hm hf
  ackedHigh := by
    intro p m hp hm hf
    obtain ⟨hpn, hp'⟩ := htp p hp
    change (if m = n then s.cfg else s.localCfg m).primary = p at hf
    show s.acked p m ≤ s.ackHigh m
    split_ifs at hf with e
    · subst e
      by_cases hf0 : (s.localCfg m).primary = p
      · exact h.ackedHigh p m hp' hm hf0
      · rw [← hf] at hf0 ⊢; rw [h.ackedPrim m hf0]; exact Nat.zero_le _
    · exact h.ackedHigh p m hp' hm hf
  syncCommit := by
    intro q r hq hs
    obtain ⟨hqn, hq'⟩ := htp q hq
    rw [hS q hqn] at hs; exact h.syncCommit q r hq' hs }

/-- Learning never makes a node primary, and eligibility does not change. -/
theorem membership_learn : MembershipInvariant (learn s n) := by
  have hnp : n ≠ s.cfg.primary := by
    intro e; apply hnkl; unfold KnowsLatest; rw [e, h.primKnows]
  have hK := learn_localCfg (s := s) (n := n)
  have hS : ∀ x, x ≠ n → (learn s n).sync x = s.sync x := fun _ => learn_sync_other
  have htp : ∀ x, ThinksPrimary (learn s n) x → x ≠ n ∧ ThinksPrimary s x :=
    fun _ => learn_thinksPrimary hnp
  exact {
  eligibleCounted := by
    intro p r hp he hi
    obtain ⟨hpn, hp'⟩ := htp p hp
    rw [hS p hpn]; rw [hK, if_neg hpn] at he hi; exact h.eligibleCounted p r hp' he hi
  syncNew := by
    intro r hs he
    have hs0 : (learn s n).sync s.cfg.primary r = true := hs
    rw [hS _ (Ne.symm hnp)] at hs0
    have hs := hs0
    show _ ∧ s.inheritedEnd s.cfg.primary ≤ s.acked s.cfg.primary r
    obtain ⟨a, b⟩ := h.syncNew r hs he
    refine ⟨?_, b⟩
    show (if r = n then s.cfg else s.localCfg r).primary = s.cfg.primary
    split
    · rfl
    · exact a
  eligibleInOldConfig := by
    intro m he hf
    change (if m = n then s.cfg else s.localCfg m).primary ≠ s.cfg.primary at hf
    show ((learn s n).localCfg ((learn s n).localCfg m).primary).eligible m = true
    rw [hK m]
    split_ifs at hf with e
    · exact absurd rfl hf
    · rw [if_neg e, hK]
      split
      · exact he
      · exact h.eligibleInOldConfig m he hf }

omit hnkl in
/-- Learn changes no commit point, catch-up point or history. -/
theorem commit_learn : CommitInvariant (learn s n) :=
  (h.toCommitInvariant).frame
    (hcommit := rfl) (hinherited := rfl) (hlog := rfl) (hhist := rfl) (hcfg := rfl) (hinc := rfl) (hah := rfl)

/-- A deposed primary stays fenced. If `n` leaves it with an acknowledgement below the old fence, that acknowledgement is the new fence. -/
theorem failover_learn : FailoverInvariant (learn s n) := by
  have hnp : n ≠ s.cfg.primary := by
    intro e; apply hnkl; unfold KnowsLatest; rw [e, h.primKnows]
  have hK := learn_localCfg (s := s) (n := n)
  have hS : ∀ x, x ≠ n → (learn s n).sync x = s.sync x := fun _ => learn_sync_other
  have htp : ∀ x, ThinksPrimary (learn s n) x → x ≠ n ∧ ThinksPrimary s x :=
    fun _ => learn_thinksPrimary hnp
  exact {
  stale := by
    intro p hp hv
    obtain ⟨hpn, hp'⟩ := htp p hp
    have hv' : (s.localCfg p).epoch < s.cfg.epoch := by
      have := hv; change ((if p = n then s.cfg else s.localCfg p).epoch < s.cfg.epoch) at this
      rwa [if_neg hpn] at this
    have hprim := stale_ne_prim h hv'
    have hF := h.stale p hp' hv'
    obtain ⟨w, ⟨hw1, hw2⟩, hwF⟩ := hF.attained
    -- Learn moves no log, acknowledgement or configuration; only whom n follows.
    have hfz : ∀ r, ((learn s n).localCfg r).primary ≠ p ↔ (r = n ∨ (s.localCfg r).primary ≠ p) := by
      intro r; rw [hK]; by_cases e : r = n
      · subst e; simp; exact fun x => hprim x.symm
      · simp [e]
    have hSp : (learn s n).sync p = s.sync p := hS p hpn
    by_cases hsw : s.sync p n = true ∧ (s.localCfg n).primary = p ∧ s.acked p n < fence s p ∧
        (s.localCfg p).eligible n = true
    · -- n followed p with an acknowledgement below the fence. Having learned the new
      -- configuration it has left p, and its acknowledgement is the new fence.
      obtain ⟨hs1, hs2, hs3, hs4⟩ := hsw
      have hnp' : n ≠ p := fun e => hpn e.symm
      refine DeposedFenced.of_left (w := n) ⟨by rw [hSp]; exact hs1, (hfz n).2 (Or.inl rfl), by rw [hK, if_neg hpn]; exact hs4⟩ ?_ ?_ ?_ ?_
      · intro hpa; show s.acked p n ≤ s.inheritedEnd s.cfg.primary; have := hF.fenceLeInheritedEnd hpa; omega
      · intro hpa; exact take_mono_prefix (Nat.le_of_lt hs3) (hF.primHolds hpa)
      · intro hpa; show s.acked p n ≤ s.ackHigh s.cfg.primary; have := hF.primAck hpa; omega
      · intro m hm hi
        rcases hF.eligHolds m hm hi with ⟨d, da⟩ | ⟨d1, d2⟩
        · exact Or.inl ⟨take_mono_prefix (Nat.le_of_lt hs3) d, (Nat.le_of_lt hs3).trans da⟩
        · by_cases e : m = n
          · subst e; exact Or.inl ⟨h.ackHolds p m hp' hnp' hs2, h.ackedHigh p m hp' hnp' hs2⟩
          · right; rw [hSp]; refine ⟨d1, ?_⟩
            show (if m = n then s.cfg else s.localCfg m).primary = p; rw [if_neg e]; exact d2
    · -- Otherwise the old fence still holds.
      refine DeposedFenced.of_left (w := w) ⟨by rw [hSp]; exact hw1, (hfz w).2 (Or.inr hw2.1), by rw [hK, if_neg hpn]; exact hw2.2⟩ ?_ ?_ ?_ ?_
      · intro hpa; show s.acked p w ≤ s.inheritedEnd s.cfg.primary; rw [hwF]; exact hF.fenceLeInheritedEnd hpa
      · intro hpa
        show (s.log p).take (s.acked p w) <+: s.log s.cfg.primary; rw [hwF]; exact hF.primHolds hpa
      · intro hpa; show s.acked p w ≤ s.ackHigh s.cfg.primary; rw [hwF]; exact hF.primAck hpa
      · intro m hm hi
        show ((s.log p).take (s.acked p w) <+: s.log m ∧ s.acked p w ≤ s.ackHigh m) ∨ _
        rw [hwF]
        rcases hF.eligHolds m hm hi with d | ⟨d1, d2⟩
        · exact Or.inl d
        · by_cases e : m = n
          · subst e
            have hnp' : m ≠ p := fun e => hpn e.symm
            have hel : (s.localCfg p).eligible m = true := by
              have := h.eligibleInOldConfig m hm (by rw [d2]; exact hprim)
              rwa [d2] at this
            have hle : fence s p ≤ s.acked p m := Nat.le_of_not_lt (fun hl => hsw ⟨d1, d2, hl, hel⟩)
            exact Or.inl ⟨take_mono_prefix hle (h.ackHolds p m hp' hnp' d2),
              hle.trans (h.ackedHigh p m hp' hnp' d2)⟩
          · right; rw [hSp]; refine ⟨d1, ?_⟩
            show (if m = n then s.cfg else s.localCfg m).primary = p; rw [if_neg e]; exact d2
  authEx := h.authEx }

omit hnkl in
/-- Learn moves no log and changes no authoritative node. -/
theorem eligibleHoldsCommitted_learn : EligibleHoldsCommitted (learn s n) :=
  h.eligibleHoldsCommitted

theorem invariant_learn : Invariant (learn s n) where
  toConfigInvariant := config_learn h n hnkl
  toReplInvariant := repl_learn h n hnkl
  toMembershipInvariant := membership_learn h n hnkl
  toCommitInvariant := commit_learn h n
  toFailoverInvariant := failover_learn h n hnkl
  eligibleHoldsCommitted := eligibleHoldsCommitted_learn h n

end learn

/-! ### MakeEligible / MakeIneligible -/

section cas
variable {s : State Node} (h : Invariant s) {p r : Node} (hp : ThinksPrimary s p) (hkl : KnowsLatest s p)
include h hp hkl

/-- The new epoch records `r` as eligible with its current incarnation, and the primary's copy is that epoch. -/
theorem config_makeEligible (hs : s.sync p r = true) (hel : s.cfg.eligible r = false) :
    ConfigInvariant (makeEligible s p r) := by
  obtain ⟨hkp, hpp⟩ := thinksPrimary_knowsLatest h hp hkl
  have hpa : PrimaryAuthoritative s := (thinksPrimary_primaryAuthoritative hp hkp).2
  subst hpp
  have hK := makeEligible_localCfg (s := s) (r := r)
  have hI := makeEligible_inc (s := s) (r := r)
  have hrp : r ≠ s.cfg.primary := by
    intro e; rw [e, h.noSelfSync] at hs; exact Bool.false_ne_true hs
  have hKi := makeEligible_localCfg_inc (s := s) hkp hrp
  obtain ⟨hrf, hrec⟩ := h.syncNew r hs hel
  have hsc := h.syncCommit _ _ (thinksPrimary_prim h hpa) hs
  exact {
  localCfgLe := by
    intro x; show ((makeEligible s s.cfg.primary r).localCfg x).epoch ≤ s.cfg.epoch + 1; rw [hK]; split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (h.localCfgLe x)
  localCfgEq := by
    intro x hx; change ((makeEligible s s.cfg.primary r).localCfg x).epoch = s.cfg.epoch + 1 at hx
    show (makeEligible s s.cfg.primary r).localCfg x = makeEligibleCfg s r
    rw [hK] at hx ⊢; split_ifs with e
    · rfl
    · rw [if_neg e] at hx; have := h.localCfgLe x; omega
  primKnows := by show (makeEligible s s.cfg.primary r).localCfg s.cfg.primary = _; rw [hK, if_pos rfl]; rfl
  localCfgIncLe := by
    intro x y; rw [hK]; split
    · show update s.cfg.incarnation r (s.incarnation r) y ≤ s.incarnation y
      by_cases ey : y = r
      · subst ey; simp
      · rw [update_of_ne _ _ ey]; exact h.incLe y
    · exact h.localCfgIncLe x y }

/-- Promotion step 4 moves no log, sync replica set or acknowledgement. -/
theorem repl_makeEligible (hs : s.sync p r = true) (hel : s.cfg.eligible r = false) :
    ReplInvariant (makeEligible s p r) := by
  obtain ⟨hkp, hpp⟩ := thinksPrimary_knowsLatest h hp hkl
  have hpa : PrimaryAuthoritative s := (thinksPrimary_primaryAuthoritative hp hkp).2
  subst hpp
  have hKp := makeEligible_localCfg_prim (s := s) (r := r) hkp
  have hrp : r ≠ s.cfg.primary := by
    intro e; rw [e, h.noSelfSync] at hs; exact Bool.false_ne_true hs
  have hKi := makeEligible_localCfg_inc (s := s) hkp hrp
  obtain ⟨hrf, hrec⟩ := h.syncNew r hs hel
  have hsc := h.syncCommit _ _ (thinksPrimary_prim h hpa) hs
  have htp := makeEligible_thinksPrimary (s := s) hkp hrp
  exact {
  noSelfSync := h.noSelfSync
  ackedPrim := by intro x hx; rw [hKp] at hx; exact h.ackedPrim x hx
  ackedLe := by intro x y hx; exact h.ackedLe x y ((htp x).1 hx)
  ackHolds := by intro x y hx hy hf; rw [hKp] at hf; exact h.ackHolds x y ((htp x).1 hx) hy hf
  ackedHigh := by intro x y hx hy hf; rw [hKp] at hf; exact h.ackedHigh x y ((htp x).1 hx) hy hf
  syncCommit := by intro x y hx; exact h.syncCommit x y ((htp x).1 hx) }

/-- `r` was already counted (step 2 comes before step 4), so every eligible replica is still counted. -/
theorem membership_makeEligible (hs : s.sync p r = true) (hel : s.cfg.eligible r = false) :
    MembershipInvariant (makeEligible s p r) := by
  obtain ⟨hkp, hpp⟩ := thinksPrimary_knowsLatest h hp hkl
  have hpa : PrimaryAuthoritative s := (thinksPrimary_primaryAuthoritative hp hkp).2
  subst hpp
  have hK := makeEligible_localCfg (s := s) (r := r)
  have hKp := makeEligible_localCfg_prim (s := s) (r := r) hkp
  have hE := makeEligible_elig (s := s) (r := r)
  have hrp : r ≠ s.cfg.primary := by
    intro e; rw [e, h.noSelfSync] at hs; exact Bool.false_ne_true hs
  have hKi := makeEligible_localCfg_inc (s := s) hkp hrp
  obtain ⟨hrf, hrec⟩ := h.syncNew r hs hel
  have hsc := h.syncCommit _ _ (thinksPrimary_prim h hpa) hs
  have htp := makeEligible_thinksPrimary (s := s) hkp hrp
  exact {
  eligibleCounted := by
    intro x y hx hy hi
    show s.sync x y = true
    rw [hK] at hy hi
    split_ifs at hy with e
    · subst e
      change (if y = r then true else s.cfg.eligible y) = true at hy
      rw [if_pos rfl] at hi
      change update s.cfg.incarnation r (s.incarnation r) y = s.incarnation y at hi
      by_cases ey : y = r
      · subst ey; exact hs
      · rw [if_neg ey] at hy; rw [update_of_ne _ _ ey] at hi
        exact h.eligibleCounted _ y (thinksPrimary_prim h hpa) (by rw [h.primKnows]; exact hy)
          (by rw [h.primKnows]; exact hi)
    · rw [if_neg e] at hi; exact h.eligibleCounted x y ((htp x).1 hx) hy hi
  syncNew := by
    intro x hx hxe
    rw [hE] at hxe
    split at hxe
    · exact absurd hxe (by decide)
    · obtain ⟨a, b⟩ := h.syncNew x hx hxe; rw [hKp]; exact ⟨a, b⟩
  eligibleInOldConfig := by
    intro m hm hf
    rw [hKp] at hf
    change (s.localCfg m).primary ≠ s.cfg.primary at hf
    rw [hE] at hm
    split_ifs at hm with e
    · subst e; exact absurd hrf hf
    · rw [hKp, hK, if_neg hf]; exact h.eligibleInOldConfig m hm hf }

/-- MakeEligible changes no commit point, catch-up point or history. -/
theorem commit_makeEligible (hs : s.sync p r = true) (hel : s.cfg.eligible r = false) :
    CommitInvariant (makeEligible s p r) := by
  obtain ⟨hkp, hpp⟩ := thinksPrimary_knowsLatest h hp hkl
  have hpa : PrimaryAuthoritative s := (thinksPrimary_primaryAuthoritative hp hkp).2
  subst hpp
  have hrp : r ≠ s.cfg.primary := by
    intro e; rw [e, h.noSelfSync] at hs; exact Bool.false_ne_true hs
  have hKi := makeEligible_localCfg_inc (s := s) hkp hrp
  obtain ⟨hrf, hrec⟩ := h.syncNew r hs hel
  have hsc := h.syncCommit _ _ (thinksPrimary_prim h hpa) hs
  exact {
  commitWithinLog := h.commitWithinLog
  committedIsHistoryPrefix := h.committedIsHistoryPrefix
  inheritedEndWithinLog := h.inheritedEndWithinLog
  historyWithinCommitOrInherited := fun _ => h.historyWithinCommitOrInherited hpa
  histAck := by
    -- `r` acknowledged past the primary's commit and reconciliation points, which
    -- cover the history (`historyWithinCommitOrInherited`).
    intro n hn
    rcases makeEligible_isAuthoritative hn with rfl | hn'
    · have hhl : s.hist.length ≤ s.acked s.cfg.primary n := by
        rcases h.historyWithinCommitOrInherited hpa with a | a <;> omega
      exact hhl.trans (h.ackedHigh _ n (thinksPrimary_prim h hpa) hrp hrf)
    · exact h.histAck n hn' }

/-- Fences do not move. `r` holds a deposed primary's log up to its fence, because `r` acknowledged past the reconciliation point, which is past the fence. -/
theorem failover_makeEligible (hs : s.sync p r = true) (hel : s.cfg.eligible r = false) :
    FailoverInvariant (makeEligible s p r) := by
  obtain ⟨hkp, hpp⟩ := thinksPrimary_knowsLatest h hp hkl
  have hpa : PrimaryAuthoritative s := (thinksPrimary_primaryAuthoritative hp hkp).2
  subst hpp
  have hK := makeEligible_localCfg (s := s) (r := r)
  have hKp := makeEligible_localCfg_prim (s := s) (r := r) hkp
  have hI := makeEligible_inc (s := s) (r := r)
  have hrp : r ≠ s.cfg.primary := by
    intro e; rw [e, h.noSelfSync] at hs; exact Bool.false_ne_true hs
  have hKi := makeEligible_localCfg_inc (s := s) hkp hrp
  obtain ⟨hrf, hrec⟩ := h.syncNew r hs hel
  have hra : (s.log s.cfg.primary).take (s.acked s.cfg.primary r) <+: s.log r :=
    h.ackHolds _ _ (thinksPrimary_prim h hpa) hrp hrf
  have hsc := h.syncCommit _ _ (thinksPrimary_prim h hpa) hs
  have htp := makeEligible_thinksPrimary (s := s) hkp hrp
  exact {
  stale := by
    intro x hx hv
    have hx' := (htp x).1 hx
    have hxp : x ≠ s.cfg.primary := by
      intro e; subst e; rw [hK, if_pos rfl] at hv; exact Nat.lt_irrefl _ hv
    have hv' : (s.localCfg x).epoch < s.cfg.epoch := by
      rw [hK, if_neg hxp] at hv
      rcases Nat.lt_or_ge (s.localCfg x).epoch s.cfg.epoch with a | a
      · exact a
      · exfalso; have := h.localCfgEq x (Nat.le_antisymm (h.localCfgLe x) a)
        exact hxp (thinksPrimary_knowsLatest h hx' (by unfold KnowsLatest; rw [this])).2.symm
    -- The fence does not move; the newly eligible r holds x's log up to it because r
    -- caught up past the reconciliation point, which is past the fence.
    have hF := h.stale x hx' hv'
    refine hF.transfer (hsync := rfl) (hkn := hKp) (hke := by rw [hK, if_neg hxp])
      (hack := fun _ _ => rfl) (hlog := rfl) (hprim := rfl) (fun _ => hpa)
      (fun _ => hF.fenceLeInheritedEnd hpa) (fun _ => hF.primHolds hpa) (fun _ => hF.primAck hpa) ?_
    intro m hm hi
    by_cases e : m = r
    · subst e; right
      refine ⟨take_transfer (Nat.le_trans (hF.fenceLeInheritedEnd hpa) hrec)
        (hF.le_len (fun y => h.ackedLe x y hx')) (hF.primHolds hpa) hra, ?_⟩
      exact Nat.le_trans (Nat.le_trans (hF.fenceLeInheritedEnd hpa) hrec)
        (h.ackedHigh _ m (thinksPrimary_prim h hpa) hrp hrf)
    · left
      change (if m = r then true else s.cfg.eligible m) = true at hm
      change (if m = r then s.incarnation r else s.cfg.incarnation m) = s.incarnation m at hi
      rw [if_neg e] at hm hi; exact ⟨hm, hi, rfl, Nat.le_refl _⟩
  authEx := by
    refine ⟨s.cfg.primary, Or.inr rfl, ?_⟩
    show (makeEligible s s.cfg.primary r).cfg.incarnation s.cfg.primary = s.incarnation s.cfg.primary
    rw [hI, if_neg (Ne.symm hrp)]; exact hpa }

/-- `r` is the only node that can become authoritative, and it holds the history: it acknowledged past the reconciliation point, which covers the history. -/
theorem eligibleHoldsCommitted_makeEligible (hs : s.sync p r = true) (hel : s.cfg.eligible r = false) :
    EligibleHoldsCommitted (makeEligible s p r) := by
  obtain ⟨hkp, hpp⟩ := thinksPrimary_knowsLatest h hp hkl
  have hpa : PrimaryAuthoritative s := (thinksPrimary_primaryAuthoritative hp hkp).2
  subst hpp
  have hrp : r ≠ s.cfg.primary := by
    intro e; rw [e, h.noSelfSync] at hs; exact Bool.false_ne_true hs
  have hKi := makeEligible_localCfg_inc (s := s) hkp hrp
  obtain ⟨hrf, hrec⟩ := h.syncNew r hs hel
  have hra : (s.log s.cfg.primary).take (s.acked s.cfg.primary r) <+: s.log r :=
    h.ackHolds _ _ (thinksPrimary_prim h hpa) hrp hrf
  have hsc := h.syncCommit _ _ (thinksPrimary_prim h hpa) hs
  have hhl : s.hist.length ≤ s.acked s.cfg.primary r := by
    rcases h.historyWithinCommitOrInherited hpa with a | a <;> omega
  have hhist : s.hist <+: s.log r := by
    have hp0 := h.eligibleHoldsCommitted s.cfg.primary ⟨Or.inr rfl, hpa⟩
    have e := prefix_take_eq hp0 (Nat.le_refl s.hist.length)
    rw [List.take_length] at e
    rw [e]; exact take_mono_prefix hhl hra
  have hauth : ∀ n, IsAuthoritative (makeEligible s s.cfg.primary r) n → n = r ∨ IsAuthoritative s n :=
    fun _ => makeEligible_isAuthoritative
  exact by
    intro n hn
    rcases hauth n hn with rfl | hn
    · exact hhist
    · exact h.eligibleHoldsCommitted n hn

theorem invariant_makeEligible (hs : s.sync p r = true) (hel : s.cfg.eligible r = false) :
    Invariant (makeEligible s p r) where
  toConfigInvariant := config_makeEligible h hp hkl hs hel
  toReplInvariant := repl_makeEligible h hp hkl hs hel
  toMembershipInvariant := membership_makeEligible h hp hkl hs hel
  toCommitInvariant := commit_makeEligible h hp hkl hs hel
  toFailoverInvariant := failover_makeEligible h hp hkl hs hel
  eligibleHoldsCommitted := eligibleHoldsCommitted_makeEligible h hp hkl hs hel

/-- The new epoch drops `r` from the eligible set; only the primary's copy changes. -/
theorem config_makeIneligible (_he : s.cfg.eligible r = true) :
    ConfigInvariant (makeIneligible s p r) := by
  obtain ⟨hkp, hpp⟩ := thinksPrimary_knowsLatest h hp hkl
  subst hpp
  have hK := makeIneligible_localCfg (s := s) (r := r)
  have hKi := makeIneligible_localCfg_inc (s := s) (r := r) hkp
  exact {
  localCfgLe := by
    intro x; show ((makeIneligible s s.cfg.primary r).localCfg x).epoch ≤ s.cfg.epoch + 1; rw [hK]; split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (h.localCfgLe x)
  localCfgEq := by
    intro x hx; change ((makeIneligible s s.cfg.primary r).localCfg x).epoch = s.cfg.epoch + 1 at hx
    show (makeIneligible s s.cfg.primary r).localCfg x = makeIneligibleCfg s r
    rw [hK] at hx ⊢; split_ifs with e
    · rfl
    · rw [if_neg e] at hx; have := h.localCfgLe x; omega
  primKnows := by show (makeIneligible s s.cfg.primary r).localCfg s.cfg.primary = _; rw [hK, if_pos rfl]; rfl
  localCfgIncLe := by
    intro x y; rw [hK]; split
    · exact h.incLe y
    · exact h.localCfgIncLe x y }

/-- The primary stops counting `r`; no log or other acknowledgement moves. -/
theorem repl_makeIneligible (_he : s.cfg.eligible r = true) :
    ReplInvariant (makeIneligible s p r) := by
  obtain ⟨hkp, hpp⟩ := thinksPrimary_knowsLatest h hp hkl
  subst hpp
  have hKp := makeIneligible_localCfg_prim (s := s) (r := r) hkp
  have hKi := makeIneligible_localCfg_inc (s := s) (r := r) hkp
  have hS := makeIneligible_sync (s := s) (r := r)
  have hSle : ∀ x y, (makeIneligible s s.cfg.primary r).sync x y = true → s.sync x y = true :=
    fun _ _ => makeIneligible_sync_le
  have htp := makeIneligible_thinksPrimary (s := s) (r := r) hkp
  exact {
  noSelfSync := by
    intro x; rw [hS]; split
    · rfl
    · exact h.noSelfSync x
  ackedPrim := by intro x hx; rw [hKp] at hx; exact h.ackedPrim x hx
  ackedLe := by intro x y hx; exact h.ackedLe x y ((htp x).1 hx)
  ackHolds := by intro x y hx hy hf; rw [hKp] at hf; exact h.ackHolds x y ((htp x).1 hx) hy hf
  ackedHigh := by intro x y hx hy hf; rw [hKp] at hf; exact h.ackedHigh x y ((htp x).1 hx) hy hf
  syncCommit := by intro x y hx hxy; exact h.syncCommit x y ((htp x).1 hx) (hSle x y hxy) }

/-- `r` is ineligible before any write commits without it (demotion ordering rule). -/
theorem membership_makeIneligible (hel : s.cfg.eligible r = true) :
    MembershipInvariant (makeIneligible s p r) := by
  obtain ⟨hkp, hpp⟩ := thinksPrimary_knowsLatest h hp hkl
  have hpa : PrimaryAuthoritative s := (thinksPrimary_primaryAuthoritative hp hkp).2
  subst hpp
  have hK := makeIneligible_localCfg (s := s) (r := r)
  have hKp := makeIneligible_localCfg_prim (s := s) (r := r) hkp
  have hKi := makeIneligible_localCfg_inc (s := s) (r := r) hkp
  have hE := makeIneligible_elig (s := s) (r := r)
  have hS := makeIneligible_sync (s := s) (r := r)
  have hSle : ∀ x y, (makeIneligible s s.cfg.primary r).sync x y = true → s.sync x y = true :=
    fun _ _ => makeIneligible_sync_le
  have htp := makeIneligible_thinksPrimary (s := s) (r := r) hkp
  have hEle : ∀ m, (makeIneligible s s.cfg.primary r).cfg.eligible m = true → m ≠ r ∧ s.cfg.eligible m = true :=
    fun _ => makeIneligible_elig_true
  exact {
  eligibleCounted := by
    intro x y hx hy hi
    rw [hS]
    rw [hK] at hy hi
    split_ifs at hy with e
    · subst e
      rw [if_pos rfl] at hi
      change (if y = r then false else s.cfg.eligible y) = true at hy
      change s.cfg.incarnation y = s.incarnation y at hi
      split_ifs at hy with ey
      rw [if_neg (fun c => ey c.2)]
      exact h.eligibleCounted _ y (thinksPrimary_prim h hpa) (by rw [h.primKnows]; exact hy)
        (by rw [h.primKnows]; exact hi)
    · rw [if_neg e] at hi; rw [if_neg (fun c => e c.1)]
      exact h.eligibleCounted x y ((htp x).1 hx) hy hi
  syncNew := by
    intro x hx hxe
    have hx0 := hSle _ _ hx
    rw [hS] at hx
    rw [hE] at hxe
    split_ifs at hxe with e
    · subst e; rw [if_pos ⟨rfl, rfl⟩] at hx; exact absurd hx Bool.false_ne_true
    · obtain ⟨a, b⟩ := h.syncNew x hx0 hxe; rw [hKp]; exact ⟨a, b⟩
  eligibleInOldConfig := by
    intro m hm hf
    obtain ⟨_, hm'⟩ := hEle m hm
    rw [hKp] at hf
    change (s.localCfg m).primary ≠ s.cfg.primary at hf
    rw [hKp, hK, if_neg hf]; exact h.eligibleInOldConfig m hm' hf }

/-- MakeIneligible changes no commit point, catch-up point, history or primary, and the
commit facts only mention the current primary. -/
theorem commit_makeIneligible (_he : s.cfg.eligible r = true) : CommitInvariant (makeIneligible s p r) := by
  obtain ⟨_, hpp⟩ := thinksPrimary_knowsLatest h hp hkl
  subst hpp
  exact { commitWithinLog := h.commitWithinLog, committedIsHistoryPrefix := h.committedIsHistoryPrefix, inheritedEndWithinLog := h.inheritedEndWithinLog,
          historyWithinCommitOrInherited := h.historyWithinCommitOrInherited, histAck := fun n hn => h.histAck n (makeIneligible_isAuthoritative hn) }

/-- Fences do not move, and no node becomes authoritative. -/
theorem failover_makeIneligible (_he : s.cfg.eligible r = true) :
    FailoverInvariant (makeIneligible s p r) := by
  obtain ⟨hkp, hpp⟩ := thinksPrimary_knowsLatest h hp hkl
  have hpa : PrimaryAuthoritative s := (thinksPrimary_primaryAuthoritative hp hkp).2
  subst hpp
  have hK := makeIneligible_localCfg (s := s) (r := r)
  have hKp := makeIneligible_localCfg_prim (s := s) (r := r) hkp
  have hKi := makeIneligible_localCfg_inc (s := s) (r := r) hkp
  have hS := makeIneligible_sync (s := s) (r := r)
  have htp := makeIneligible_thinksPrimary (s := s) (r := r) hkp
  have hEle : ∀ m, (makeIneligible s s.cfg.primary r).cfg.eligible m = true → m ≠ r ∧ s.cfg.eligible m = true :=
    fun _ => makeIneligible_elig_true
  exact {
  stale := by
    intro x hx hv
    have hx' := (htp x).1 hx
    have hxp : x ≠ s.cfg.primary := by
      intro e; subst e; rw [hK, if_pos rfl] at hv; exact Nat.lt_irrefl _ hv
    have hv' : (s.localCfg x).epoch < s.cfg.epoch := by
      rw [hK, if_neg hxp] at hv
      rcases Nat.lt_or_ge (s.localCfg x).epoch s.cfg.epoch with a | a
      · exact a
      · exfalso; have := h.localCfgEq x (Nat.le_antisymm (h.localCfgLe x) a)
        exact hxp (thinksPrimary_knowsLatest h hx' (by unfold KnowsLatest; rw [this])).2.symm
    have hSx : (makeIneligible s s.cfg.primary r).sync x = s.sync x := by
      funext y; rw [hS, if_neg (fun c => hxp c.1)]
    have hF := h.stale x hx' hv'
    exact hF.transfer (hsync := hSx) (hkn := hKp) (hke := by rw [hK, if_neg hxp])
      (hack := fun _ _ => rfl) (hlog := rfl) (hprim := rfl) (fun _ => hpa)
      (fun _ => hF.fenceLeInheritedEnd hpa) (fun _ => hF.primHolds hpa) (fun _ => hF.primAck hpa)
      (fun m hm hi => Or.inl ⟨(hEle m hm).2, hi, rfl, Nat.le_refl _⟩)
  authEx := ⟨s.cfg.primary, Or.inr rfl, hpa⟩ }

/-- No node becomes authoritative. -/
theorem eligibleHoldsCommitted_makeIneligible (_he : s.cfg.eligible r = true) :
    EligibleHoldsCommitted (makeIneligible s p r) := by
  obtain ⟨hkp, hpp⟩ := thinksPrimary_knowsLatest h hp hkl
  subst hpp
  have hKi := makeIneligible_localCfg_inc (s := s) (r := r) hkp
  have hauth : ∀ n, IsAuthoritative (makeIneligible s s.cfg.primary r) n → IsAuthoritative s n :=
    fun _ => makeIneligible_isAuthoritative
  exact fun n hn => h.eligibleHoldsCommitted n (hauth n hn)

theorem invariant_makeIneligible (hel : s.cfg.eligible r = true) :
    Invariant (makeIneligible s p r) where
  toConfigInvariant := config_makeIneligible h hp hkl hel
  toReplInvariant := repl_makeIneligible h hp hkl hel
  toMembershipInvariant := membership_makeIneligible h hp hkl hel
  toCommitInvariant := commit_makeIneligible h hp hkl hel
  toFailoverInvariant := failover_makeIneligible h hp hkl hel
  eligibleHoldsCommitted := eligibleHoldsCommitted_makeIneligible h hp hkl hel

end cas

end SyncReplication
