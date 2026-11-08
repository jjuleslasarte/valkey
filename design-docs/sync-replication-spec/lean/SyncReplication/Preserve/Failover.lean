import SyncReplication.Invariant
import SyncReplication.Contracts

/-!
# Preservation: failover (design §5)

Takeover: an eligible replica becomes primary in a new configuration. The old primary
is not stopped; it is fenced (`DeposedFenced`).
-/

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

section takeover

/-! Every lemma below takes the takeover's guard as hypotheses: `n` knows the latest
configuration, is eligible in it, is not its primary, and its recorded incarnation
matches. A lemma that does not use part of it says so with `omit ... in`. -/

variable {s : State Node} (h : Invariant s) (n : Node) (hkl : KnowsLatest s n)
    (hel : s.cfg.eligible n = true) (hnp : n ≠ s.cfg.primary) (hin : s.cfg.incarnation n = s.incarnation n)
include h hkl hel hnp hin

omit hkl hel hnp hin in
/-- Configuration: the takeover's configuration becomes the latest one, `n`'s copy is it,
and recorded incarnations do not change. -/
theorem config_takeover : ConfigInvariant (takeover s n) := by
  have hK : ∀ x, (takeover s n).known x = if x = n then takeoverCfg s n else s.known x :=
    takeover_known
  exact {
  knownLe := by
    intro x; show ((takeover s n).known x).version ≤ s.cfg.version + 1; rw [hK]; split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (h.knownLe x)
  knownEq := by
    intro x hx; change ((takeover s n).known x).version = s.cfg.version + 1 at hx
    show (takeover s n).known x = takeoverCfg s n
    rw [hK] at hx ⊢; split_ifs with e
    · rfl
    · rw [if_neg e] at hx; have := h.knownLe x; omega
  primKnows := by show (takeover s n).known n = takeoverCfg s n; rw [hK, if_pos rfl]
  knownIncLe := by
    intro x y; rw [hK]; split
    · exact h.incLe y
    · exact h.knownIncLe x y }

/-- Replication: `n` starts its primaryship with no acknowledgements recorded; every other
node's records are unchanged, and no log moves. -/
theorem repl_takeover : ReplInvariant (takeover s n) := by
  have hK : ∀ x, (takeover s n).known x = if x = n then takeoverCfg s n else s.known x :=
    takeover_known
  have hKo : ∀ x, x ≠ n → (takeover s n).known x = s.known x := fun _ => takeover_known_other
  have hSn : (takeover s n).sync n = takeoverSync s n := takeover_sync_self
  have hSo : ∀ x, x ≠ n → (takeover s n).sync x = s.sync x := fun _ => takeover_sync_other
  have hAn : (takeover s n).acked n = fun _ => 0 := takeover_acked_self
  have hAo : ∀ x, x ≠ n → (takeover s n).acked x = s.acked x := fun _ => takeover_acked_other
  have hCn : (takeover s n).commit n = 0 := takeover_commit_self
  have hCo : ∀ x, x ≠ n → (takeover s n).commit x = s.commit x := fun _ => takeover_commit_other
  have htp := takeover_thinksPrimary hin
  exact {
  noSelfSync := by
    intro x; by_cases e : x = n
    · subst e; rw [hSn]; exact takeoverSync_self
    · rw [hSo x e]; exact h.noSelfSync x
  ackedPrim := by intro r _; show (takeover s n).acked n r = 0; rw [hAn]
  ackedLe := by
    intro x y hx
    rcases (htp x).1 hx with rfl | ⟨e, hx'⟩
    · rw [hAn]; exact Nat.zero_le _
    · rw [hAo x e]; exact h.ackedLe x y hx'
  ackHolds := by
    intro x y hx hy hf
    rcases (htp x).1 hx with rfl | ⟨e, hx'⟩
    · rw [hAn]; simp
    · by_cases ey : y = n
      · subst ey; rw [hK, if_pos rfl] at hf; exact absurd hf.symm e
      · rw [hKo y ey] at hf; rw [hAo x e]; exact h.ackHolds x y hx' hy hf
  ackedHigh := by
    intro x y hx hy hf
    rcases (htp x).1 hx with rfl | ⟨e, hx'⟩
    · rw [hAn]; exact Nat.zero_le _
    · by_cases ey : y = n
      · subst ey; rw [hK, if_pos rfl] at hf; exact absurd hf.symm e
      · rw [hKo y ey] at hf; rw [hAo x e]; exact h.ackedHigh x y hx' hy hf
  syncCommit := by
    intro x y hx hs
    rcases (htp x).1 hx with rfl | ⟨e, hx'⟩
    · rw [hCn]; exact Nat.zero_le _
    · rw [hCo x e, hAo x e]; rw [hSo x e] at hs; exact h.syncCommit x y hx' hs }

/-- Membership: `n` counts exactly the eligible replicas of the new configuration whose
recorded incarnation matches, and counts no ineligible replica. -/
theorem membership_takeover : MembershipInvariant (takeover s n) := by
  have hK : ∀ x, (takeover s n).known x = if x = n then takeoverCfg s n else s.known x :=
    takeover_known
  have hKo : ∀ x, x ≠ n → (takeover s n).known x = s.known x := fun _ => takeover_known_other
  have hSn : (takeover s n).sync n = takeoverSync s n := takeover_sync_self
  have hSo : ∀ x, x ≠ n → (takeover s n).sync x = s.sync x := fun _ => takeover_sync_other
  have hNE := takeoverEligible_iff (s := s) (n := n)
  have htp := takeover_thinksPrimary hin
  exact {
  eligibleCounted := by
    intro x y hx hy hi
    rcases (htp x).1 hx with rfl | ⟨e, hx'⟩
    · rw [hSn]; rw [hK, if_pos rfl] at hy
      change takeoverEligible s x y = true at hy
      exact (takeoverSync_iff y).2 hy
    · rw [hSo x e]; rw [hKo x e] at hy hi; exact h.eligibleCounted x y hx' hy hi
  syncNew := by
    intro r hs he
    change (takeover s n).sync n r = true at hs
    rw [hSn] at hs
    change takeoverEligible s n r = false at he
    rw [takeoverSync_iff, he] at hs; exact absurd hs (by decide)
  eligibleInOldConfig := by
    intro m hm hf
    change takeoverEligible s n m = true at hm
    obtain ⟨hm1, hm2, hm3⟩ := (hNE m).1 hm
    rw [hKo m hm3] at hf ⊢
    change (s.known m).primary ≠ n at hf
    rw [hKo _ hf]
    by_cases hq : (s.known m).primary = s.cfg.primary
    · rw [hq, h.primKnows]; exact hm1
    · exact h.eligibleInOldConfig m hm1 hq }

/-- Commit: `n`'s commit point is 0 and its catch-up point is the end of its log. As an
eligible replica it held the whole committed history, so the history is below its
catch-up point: it reconciles before it serves. -/
theorem commit_takeover : CommitInvariant (takeover s n) := by
  have hCn : (takeover s n).commit n = 0 := takeover_commit_self
  have hCo : ∀ x, x ≠ n → (takeover s n).commit x = s.commit x := fun _ => takeover_commit_other
  have hRn : (takeover s n).inheritedEnd n = (s.log n).length := takeover_inheritedEnd_self
  have hehn : s.hist <+: s.log n := h.eligibleHoldsCommitted n ⟨Or.inl hel, hin⟩
  have hNE := takeoverEligible_iff (s := s) (n := n)
  exact {
  commitWithinLog := by
    intro x; by_cases e : x = n
    · subst e; rw [hCn]; exact Nat.zero_le _
    · rw [hCo x e]; exact h.commitWithinLog x
  committedIsHistoryPrefix := by
    intro x; by_cases e : x = n
    · subst e; rw [hCn]; rfl
    · rw [hCo x e]; exact h.committedIsHistoryPrefix x
  inheritedEndWithinLog := by show (takeover s n).inheritedEnd n ≤ (s.log n).length; rw [hRn]
  historyWithinCommitOrInherited := by intro _; right; show s.hist.length ≤ (takeover s n).inheritedEnd n; rw [hRn]; exact hehn.length_le
  histAck := by
    intro m ⟨hm, hi⟩
    change takeoverEligible s n m = true ∨ m = n at hm
    change s.cfg.incarnation m = s.incarnation m at hi
    rcases hm with hm | rfl
    · exact h.histAck m ⟨Or.inl ((hNE m).1 hm).1, hi⟩
    · exact h.histAck m ⟨Or.inl hel, hin⟩ }

/-- Failover: every deposed primary is fenced, including the one `n` replaced, and `n`
itself is authoritative. -/
theorem failover_takeover : FailoverInvariant (takeover s n) := by
  have hkn : s.known n = s.cfg := h.knownEq n hkl
  have hfn : (s.known n).primary = s.cfg.primary := by rw [hkn]
  have hK : ∀ x, (takeover s n).known x = if x = n then takeoverCfg s n else s.known x :=
    takeover_known
  have hKo : ∀ x, x ≠ n → (takeover s n).known x = s.known x := fun _ => takeover_known_other
  have hSo : ∀ x, x ≠ n → (takeover s n).sync x = s.sync x := fun _ => takeover_sync_other
  have hAo : ∀ x, x ≠ n → (takeover s n).acked x = s.acked x := fun _ => takeover_acked_other
  have hRn : (takeover s n).inheritedEnd n = (s.log n).length := takeover_inheritedEnd_self
  have hNE := takeoverEligible_iff (s := s) (n := n)
  have htp := takeover_thinksPrimary hin
  exact {
  stale := by
    -- Every node that still thinks it is primary under an old configuration is fenced.
    intro x hx hv
    rcases (htp x).1 hx with rfl | ⟨e, hx'⟩
    · rw [hK, if_pos rfl] at hv; exact absurd hv (Nat.lt_irrefl _)
    -- x keeps its log, sync replica set and acknowledgements.
    have hSx := hSo x e
    have hAx := hAo x e
    have hL : (takeover s n).log = s.log := rfl
    have hleft : ∀ r, s.sync x r = true → ((takeover s n).known r).primary ≠ x →
        (s.known x).eligible r = true → r ∈ leftSync (takeover s n) x :=
      fun r hr hf he => ⟨by rw [hSx]; exact hr, hf, by rw [hKo x e]; exact he⟩
    by_cases hxq : x = s.cfg.primary
    · -- x is the primary n took over from. n was eligible, so x counts n, and n now
      -- follows itself: n has left x.
      subst hxq
      have hpa : PrimaryAuthoritative s := (thinksPrimary_primaryAuthoritative hx' h.primKnows).2
      have hxp := thinksPrimary_prim h hpa
      by_cases hex : ∃ r, s.sync s.cfg.primary r = true ∧ (s.known r).primary ≠ s.cfg.primary ∧
          s.cfg.eligible r = true ∧ r ≠ n
      · -- Another sync replica had already left x. The current primary records no
        -- acknowledgement from such a replica, so the fence is 0.
        obtain ⟨r, hr1, hr2, hr4, hr3⟩ := hex
        have h0 : (takeover s n).acked s.cfg.primary r = 0 := by rw [hAx]; exact h.ackedPrim r hr2
        refine DeposedFenced.of_left (hleft r hr1 (by rw [hKo r hr3]; exact hr2) (by rw [h.primKnows]; exact hr4)) ?_ ?_ ?_ ?_ <;> simp [h0]
      · -- n is the only replica that left x: the fence is n's acknowledgement, and n
        -- holds x's log up to it.
        have hsn : s.sync s.cfg.primary n = true :=
          h.eligibleCounted _ n hxp (by rw [h.primKnows]; exact hel) (by rw [h.primKnows]; exact hin)
        have hhold := h.ackHolds _ _ hxp hnp hfn
        have hlen := h.ackedLe s.cfg.primary n hxp
        have hnx : ((takeover s n).known n).primary ≠ s.cfg.primary := by
          rw [hK, if_pos rfl]; exact hnp
        refine DeposedFenced.of_left (hleft n hsn hnx (by rw [h.primKnows]; exact hel)) ?_ ?_ ?_ ?_
        · intro _
          change (takeover s n).acked s.cfg.primary n ≤ (takeover s n).inheritedEnd n
          rw [hAx, hRn]
          have := hhold.length_le; rw [List.length_take_of_le hlen] at this; exact this
        · intro _
          change ((takeover s n).log s.cfg.primary).take ((takeover s n).acked s.cfg.primary n) <+:
            (takeover s n).log n
          rw [hAx, hL]; exact hhold
        · intro _
          change (takeover s n).acked s.cfg.primary n ≤ s.ackHigh n
          rw [hAx]; exact h.ackedHigh _ _ hxp hnp hfn
        · -- Every other eligible replica is counted by x and still follows it.
          intro m hm hi
          change takeoverEligible s n m = true at hm
          change s.cfg.incarnation m = s.incarnation m at hi
          obtain ⟨hm1, _, hm3⟩ := (hNE m).1 hm
          have hsm := h.eligibleCounted _ m hxp (by rw [h.primKnows]; exact hm1) (by rw [h.primKnows]; exact hi)
          right
          refine ⟨by rw [hSx]; exact hsm, ?_⟩
          rw [hKo m hm3]
          by_cases hf : (s.known m).primary = s.cfg.primary
          · exact hf
          · exact absurd ⟨m, hsm, hf, hm1, hm3⟩ hex
    · -- x was already deposed. Its old fence still works: the replica that set it has
      -- still left x, and n, being eligible, already held x's log up to the fence.
      have hv' : (s.known x).version < s.cfg.version := by
        rw [hKo x e] at hv
        rcases Nat.lt_or_ge (s.known x).version s.cfg.version with a | a
        · exact a
        · exfalso; have := h.knownEq x (Nat.le_antisymm (h.knownLe x) a)
          exact hxq (thinksPrimary_knowsLatest h hx' (by unfold KnowsLatest; rw [this])).2.symm
      have hF := h.stale x hx' hv'
      obtain ⟨w, ⟨hw1, hw2⟩, hwF⟩ := hF.attained
      have hn6 : (s.log x).take (fence s x) <+: s.log n ∧ fence s x ≤ s.ackHigh n := by
        rcases hF.eligHolds n hel hin with d | ⟨_, d2⟩
        · exact d
        · rw [hfn] at d2; exact absurd d2.symm hxq
      have hw' : w ∈ leftSync (takeover s n) x := hleft w hw1 (by
        rw [hK]; split
        · show n ≠ x; exact fun c => e c.symm
        · exact hw2.1) hw2.2
      refine DeposedFenced.of_left hw' ?_ ?_ ?_ ?_
      · intro _
        change (takeover s n).acked x w ≤ (takeover s n).inheritedEnd n
        rw [hAx, hwF, hRn]
        have := hn6.1.length_le
        rw [List.length_take_of_le (hwF ▸ h.ackedLe x w hx')] at this; exact this
      · intro _
        change ((takeover s n).log x).take ((takeover s n).acked x w) <+: (takeover s n).log n
        rw [hAx, hwF, hL]; exact hn6.1
      · intro _
        change (takeover s n).acked x w ≤ s.ackHigh n
        rw [hAx, hwF]; exact hn6.2
      · intro m hm hi
        change takeoverEligible s n m = true at hm
        change s.cfg.incarnation m = s.incarnation m at hi
        obtain ⟨hm1, _, hm3⟩ := (hNE m).1 hm
        show ((s.log x).take ((takeover s n).acked x w) <+: s.log m ∧
            (takeover s n).acked x w ≤ s.ackHigh m) ∨
          ((takeover s n).sync x m = true ∧ ((takeover s n).known m).primary = x)
        rw [hAx, hwF, hSx, hKo m hm3]
        exact hF.eligHolds m hm1 hi
  authEx := ⟨n, Or.inr rfl, hin⟩ }

/-- Goal: `n` held the committed history as an eligible replica, and the new eligible
set is part of the old one, so every authoritative node still holds it. -/
theorem eligibleHoldsCommitted_takeover :
    ∀ m, IsAuthoritative (takeover s n) m → (takeover s n).hist <+: (takeover s n).log m := by
  have hNE := takeoverEligible_iff (s := s) (n := n)
  have hehn : s.hist <+: s.log n := h.eligibleHoldsCommitted n ⟨Or.inl hel, hin⟩
  intro m ⟨hm, hi⟩
  change takeoverEligible s n m = true ∨ m = n at hm
  change s.cfg.incarnation m = s.incarnation m at hi
  rcases hm with hm | rfl
  · exact h.eligibleHoldsCommitted m ⟨Or.inl ((hNE m).1 hm).1, hi⟩
  · exact hehn
/-- Takeover preserves the invariant, layer by layer. -/
theorem invariant_takeover : Invariant (takeover s n) where
  toConfigInvariant := config_takeover h n
  toReplInvariant := repl_takeover h n hkl hel hnp hin
  toMembershipInvariant := membership_takeover h n hkl hel hnp hin
  toCommitInvariant := commit_takeover h n hkl hel hnp hin
  toFailoverInvariant := failover_takeover h n hkl hel hnp hin
  eligibleHoldsCommitted := eligibleHoldsCommitted_takeover h n hkl hel hnp hin

end takeover

end SyncReplication
