import SyncReplication.Invariant
import SyncReplication.Contracts

/-!
# Preservation: replication (design §2 write path; full resync)

Steps that move data between a primary and its replicas: AppendWrite and Replicate
(logs only grow, `invariant_grow`), Ack (a primary records how far a replica holds its log)
and Resync (a diverged, uncounted, ineligible replica is reset to a prefix of its
primary's log).
-/

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

-- Every layer lemma takes the action's guard; a lemma that does not use part of it
-- says so with `omit ... in`.

/-- Any step that only extends logs preserves the invariant (AppendWrite, Replicate). -/
theorem invariant_grow {s : State Node} (h : Invariant s) (L : Node → List Nat)
    (hL : ∀ x, s.log x <+: L x) : Invariant { s with log := L } where
  eligibleHoldsCommitted := fun n hn => (h.eligibleHoldsCommitted n hn).trans (hL n)
  commitWithinLog := fun p => Nat.le_trans (h.commitWithinLog p) (hL p).length_le
  committedIsHistoryPrefix := by
    intro p
    show (L p).take (s.commit p) = _
    rw [← prefix_take_eq (hL p) (h.commitWithinLog p)]; exact h.committedIsHistoryPrefix p
  knownLe := h.knownLe
  knownEq := h.knownEq
  primKnows := h.primKnows
  eligibleCounted := h.eligibleCounted
  noSelfSync := h.noSelfSync
  ackedPrim := h.ackedPrim
  ackedLe := fun p r hp => Nat.le_trans (h.ackedLe p r hp) (hL p).length_le
  ackHolds := by
    intro p n hp hn hf
    show (L p).take (s.acked p n) <+: L n
    rw [← prefix_take_eq (hL p) (h.ackedLe p n hp)]
    exact (h.ackHolds p n hp hn hf).trans (hL n)
  ackedHigh := h.ackedHigh
  histAck := h.histAck
  syncNew := h.syncNew
  inheritedEndWithinLog := Nat.le_trans h.inheritedEndWithinLog (hL _).length_le
  syncCommit := h.syncCommit
  eligibleInOldConfig := h.eligibleInOldConfig
  knownIncLe := h.knownIncLe
  authEx := h.authEx
  historyWithinCommitOrInherited := h.historyWithinCommitOrInherited
  stale := fun p hp hv => (h.stale p hp hv).mono (hcfg := rfl) (hknown := rfl) (hinherited := rfl) (hinc := rfl)
      hL (fun _ => Nat.le_refl _)
    (fun r => h.ackedLe p r hp) (fun _ x => x) (fun _ _ => rfl)

theorem grow_upd (L : Node → List Nat) (p : Node) (m : List Nat) :
    ∀ x, L x <+: update L p (L p ++ m) x := by
  intro x; by_cases hx : x = p
  · subst hx; simp [List.prefix_append]
  · rw [update_of_ne _ _ hx]

theorem invariant_append {s : State Node} (h : Invariant s) (p : Node) : Invariant (appendWrite s p) :=
  invariant_grow h _ (grow_upd s.log p _)

theorem invariant_replicate {s : State Node} (h : Invariant s) (r : Node) : Invariant (replicate s r) :=
  (invariant_grow h _ (grow_upd s.log r _)).term_frame _ _

section ack

variable {s : State Node} (h : Invariant s) (r : Node) (hne : primaryOf s r ≠ r) (hpre : s.log r <+: s.log (primaryOf s r)) (hlt : s.acked (primaryOf s r) r < (s.log r).length)

include h hne hpre hlt

omit hne hpre hlt in
/-- Ack changes no configuration. -/
theorem config_ack : ConfigInvariant (ack s r) :=
  (h.toConfigInvariant).frame (hcfg := rfl) (hknown := rfl) (hinc := rfl)

/-- The recorded acknowledgement becomes the replica's log length, and the replica's log is a prefix of its primary's, so the record is real. -/
theorem repl_ack : ReplInvariant (ack s r) := by
  have hA := ack_acked (s := s) r
  have hfol : (s.known r).primary = primaryOf s r := rfl
  exact {
  noSelfSync := h.noSelfSync
  ackedPrim := by
    intro x hx
    show (ack s r).acked s.cfg.primary x = 0
    rw [hA]; split_ifs with hc
    · obtain ⟨h1, rfl⟩ := hc; exact absurd (h1 ▸ hfol) hx
    · exact h.ackedPrim x hx
  ackedLe := by
    intro q x hq
    show (ack s r).acked q x ≤ _
    rw [hA]; split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact hpre.length_le
    · exact h.ackedLe q x hq
  ackHolds := by
    intro q n hq hn hf
    show (s.log q).take ((ack s r).acked q n) <+: s.log n
    rw [hA]; split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      rw [← prefix_take_eq hpre (Nat.le_refl _), List.take_length]
    · exact h.ackHolds q n hq hn hf
  ackedHigh := by
    intro q n hq hn hf
    show (ack s r).acked q n ≤ (ack s r).ackHigh n
    rw [hA]; split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact ack_ackHigh_self _
    · exact Nat.le_trans (h.ackedHigh q n hq hn hf) (ack_ackHigh_le _ n)
  syncCommit := by
    intro q x hq hs
    show _ ≤ (ack s r).acked q x
    rw [hA]; split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact Nat.le_trans (h.syncCommit _ _ hq hs) (Nat.le_of_lt hlt)
    · exact h.syncCommit q x hq hs }

/-- Acknowledgements only grow, so a counted replica stays caught up. -/
theorem membership_ack : MembershipInvariant (ack s r) := by
  have hA := ack_acked (s := s) r
  exact {
  eligibleCounted := h.eligibleCounted
  syncNew := by
    intro x hs he
    obtain ⟨a, b⟩ := h.syncNew x hs he
    refine ⟨a, ?_⟩
    show _ ≤ (ack s r).acked s.cfg.primary x
    rw [hA]; split_ifs with hc
    · obtain ⟨h1, rfl⟩ := hc
      show s.inheritedEnd s.cfg.primary ≤ _; have := hlt; rw [← h1] at this; omega
    · exact b
  eligibleInOldConfig := h.eligibleInOldConfig }

omit hne hpre hlt in
/-- Ack changes no commit point, catch-up point or history, and only raises a high-water mark. -/
theorem commit_ack : CommitInvariant (ack s r) where
  commitWithinLog := h.commitWithinLog
  committedIsHistoryPrefix := h.committedIsHistoryPrefix
  inheritedEndWithinLog := h.inheritedEndWithinLog
  historyWithinCommitOrInherited := h.historyWithinCommitOrInherited
  histAck := fun n hn => Nat.le_trans (h.histAck n hn) (ack_ackHigh_le r n)

/-- Only the acknowledgement of a replica that still follows its primary moves, so no fence moves. -/
theorem failover_ack : FailoverInvariant (ack s r) := by
  have hA := ack_acked (s := s) r
  have hfol : (s.known r).primary = primaryOf s r := rfl
  exact {
  stale := by
    -- Ack moves only the acknowledgement of a replica that follows its primary.
    intro p hp hv
    refine (h.stale p hp hv).mono (hcfg := rfl) (hknown := rfl) (hinherited := rfl) (hinc := rfl)
      (fun _ => List.prefix_refl _) (ack_ackHigh_le r)
      (fun x => h.ackedLe p x hp) (fun _ x => x) ?_
    intro x hx
    show (ack s r).acked p x = s.acked p x
    rw [hA]; split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact absurd hfol hx
    · rfl
  authEx := h.authEx }

omit hne hpre hlt in
/-- Ack moves no log. -/
theorem eligibleHoldsCommitted_ack : EligibleHoldsCommitted (ack s r) := by
  exact h.eligibleHoldsCommitted

theorem invariant_ack : Invariant (ack s r) where
  toConfigInvariant := config_ack h r
  toReplInvariant := repl_ack h r hne hpre hlt
  toMembershipInvariant := membership_ack h r hne hpre hlt
  toCommitInvariant := commit_ack h r
  toFailoverInvariant := failover_ack h r hne hpre hlt
  eligibleHoldsCommitted := eligibleHoldsCommitted_ack h r

end ack

section resync

variable {s : State Node} (h : Invariant s) (r : Node) (hne : primaryOf s r ≠ r) (hsy : s.sync (primaryOf s r) r = false) (hke : (s.known (primaryOf s r)).eligible r = false)

include h hne hsy hke

/-- What the Resync guard says about `r` in the latest configuration. The guard only
says `r` is uncounted and ineligible *in its primary's copy* of the configuration;
`eligibleInOldConfig` lifts that to the latest one, so `r` is neither the current primary nor
eligible, and no node that thinks it is primary is `r`. -/
theorem resync_facts :
    r ≠ s.cfg.primary ∧ s.cfg.eligible r = false ∧ (∀ x, ThinksPrimary s x → x ≠ r) := by
  have hrprim : r ≠ s.cfg.primary := by
    intro e; apply hne; show (s.known r).primary = r; rw [e, h.primKnows]
  refine ⟨hrprim, ?_, fun x hx e => by subst e; exact hne hx.1⟩
  cases hc : s.cfg.eligible r
  · rfl
  · exfalso
    by_cases hf : (s.known r).primary = s.cfg.primary
    · have : primaryOf s r = s.cfg.primary := hf
      rw [this, h.primKnows, hc] at hke; exact absurd hke (by decide)
    · have := h.eligibleInOldConfig r hc hf
      change (s.known (primaryOf s r)).eligible r = true at this
      rw [hke] at this; exact absurd this (by decide)

omit hne hsy hke in
/-- Resync changes no configuration. -/
theorem config_resync : ConfigInvariant (resync s r) :=
  (h.toConfigInvariant).frame (hcfg := rfl) (hknown := rfl) (hinc := rfl)

/-- `r`'s log becomes a prefix of its primary's and its acknowledgement is reset to 0, so recorded acknowledgements stay real. -/
theorem repl_resync : ReplInvariant (resync s r) := by
  obtain ⟨hrprim, hrel, htpne⟩ := resync_facts h r hne hsy hke
  have hcl := commit_le_catchUpPoint h (primaryOf s r)
  have hLo : ∀ x, x ≠ r → (resync s r).log x = s.log x := fun _ => resync_log_other
  have hCo : ∀ x, x ≠ r → (resync s r).commit x = s.commit x := fun _ => resync_commit_other
  have hA := resync_acked (s := s) (r := r)
  have hAle := resync_acked_le (s := s) (r := r)
  have hAs : ∀ q x, s.sync q x = true → (resync s r).acked q x = s.acked q x :=
    fun _ _ => resync_acked_sync hsy
  exact {
  noSelfSync := h.noSelfSync
  ackedPrim := by intro x hx; show (resync s r).acked s.cfg.primary x = 0; have := hAle s.cfg.primary x; rw [h.ackedPrim x hx] at this; omega
  ackedLe := by
    intro p x hp
    show (resync s r).acked p x ≤ ((resync s r).log p).length
    rw [hLo p (htpne p hp)]; exact Nat.le_trans (hAle p x) (h.ackedLe p x hp)
  ackHolds := by
    intro p m hp hm hf
    show ((resync s r).log p).take ((resync s r).acked p m) <+: (resync s r).log m
    rw [hLo p (htpne p hp), hA]
    split_ifs with c
    · simp
    · by_cases em : m = r
      · subst em; exact absurd ⟨hf.symm, rfl⟩ c
      · rw [hLo m em]; exact h.ackHolds p m hp hm hf
  ackedHigh := by
    intro p m hp hm hf
    show (resync s r).acked p m ≤ s.ackHigh m
    rw [hA]; split_ifs with c
    · exact Nat.zero_le _
    · exact h.ackedHigh p m hp hm hf
  syncCommit := by
    intro q x hq hs
    rw [hCo q (htpne q hq), hAs q x hs]; exact h.syncCommit q x hq hs }

omit hne hke in
/-- `r` was not counted, so the acknowledgements primaries count are untouched and every
counted replica stays caught up. -/
theorem membership_resync : MembershipInvariant (resync s r) := by
  have hcl := commit_le_catchUpPoint h (primaryOf s r)
  have hAs : ∀ q x, s.sync q x = true → (resync s r).acked q x = s.acked q x :=
    fun _ _ => resync_acked_sync hsy
  exact {
  eligibleCounted := h.eligibleCounted
  syncNew := by
    intro x hs he
    obtain ⟨a, b⟩ := h.syncNew x hs he
    refine ⟨a, ?_⟩
    show s.inheritedEnd s.cfg.primary ≤ (resync s r).acked s.cfg.primary x
    rw [hAs _ _ (show s.sync s.cfg.primary x = true from hs)]; exact b
  eligibleInOldConfig := h.eligibleInOldConfig }

/-- `r`'s commit point is capped at its primary's, so its committed prefix is still a prefix of the history. -/
theorem commit_resync : CommitInvariant (resync s r) := by
  obtain ⟨hrprim, hrel, htpne⟩ := resync_facts h r hne hsy hke
  have hcl := commit_le_catchUpPoint h (primaryOf s r)
  have hcu := catchUpPoint_le_len h (primaryOf s r)
  have hLr := resync_log_self (s := s) (r := r)
  have hLo : ∀ x, x ≠ r → (resync s r).log x = s.log x := fun _ => resync_log_other
  have hCr := resync_commit_self (s := s) (r := r)
  have hCo : ∀ x, x ≠ r → (resync s r).commit x = s.commit x := fun _ => resync_commit_other
  exact {
  commitWithinLog := by
    intro x; by_cases e : x = r
    · subst e; rw [hCr, hLr, List.length_take_of_le hcu]; omega
    · rw [hCo x e, hLo x e]; exact h.commitWithinLog x
  committedIsHistoryPrefix := by
    intro x; by_cases e : x = r
    · subst e
      show ((resync s x).log x).take ((resync s x).commit x) = s.hist.take ((resync s x).commit x)
      rw [hCr, hLr, List.take_take]
      have hk0 : min (min (s.commit x) (s.commit (primaryOf s x))) (catchUpPoint s (primaryOf s x)) =
          min (s.commit x) (s.commit (primaryOf s x)) := by omega
      have hk : min (min (s.commit x) (s.commit (primaryOf s x))) (s.commit (primaryOf s x)) =
          min (s.commit x) (s.commit (primaryOf s x)) := by omega
      rw [hk0]
      rw [show (s.log (primaryOf s x)).take (min (s.commit x) (s.commit (primaryOf s x))) =
          ((s.log (primaryOf s x)).take (s.commit (primaryOf s x))).take (min (s.commit x) (s.commit (primaryOf s x)))
          by rw [List.take_take]; congr 1; omega]
      rw [h.committedIsHistoryPrefix (primaryOf s x), List.take_take, hk]
    · rw [hCo x e, hLo x e]; exact h.committedIsHistoryPrefix x
  inheritedEndWithinLog := by
    show _ ≤ ((resync s r).log s.cfg.primary).length
    rw [hLo _ (Ne.symm hrprim)]; exact h.inheritedEndWithinLog
  historyWithinCommitOrInherited := by
    intro hpa
    show s.hist.length ≤ (resync s r).commit s.cfg.primary ∨ _
    rw [hCo _ (Ne.symm hrprim)]; exact h.historyWithinCommitOrInherited hpa
  histAck := h.histAck }

/-- `r` is neither a primary nor eligible (`resync_facts`), and no counted acknowledgement
moves, so every fence and everything it covers is unchanged. -/
theorem failover_resync : FailoverInvariant (resync s r) := by
  obtain ⟨hrprim, hrel, htpne⟩ := resync_facts h r hne hsy hke
  have hcl := commit_le_catchUpPoint h (primaryOf s r)
  have hLo : ∀ x, x ≠ r → (resync s r).log x = s.log x := fun _ => resync_log_other
  have hAs : ∀ q x, s.sync q x = true → (resync s r).acked q x = s.acked q x :=
    fun _ _ => resync_acked_sync hsy
  have hnotr : ∀ x, (s.cfg.eligible x = true ∨ x = s.cfg.primary) → x ≠ r := by
    intro x hx e; subst e
    rcases hx with hx | hx
    · rw [hrel] at hx; exact absurd hx (by decide)
    · exact hrprim hx
  exact {
  stale := by
    intro x hx hv
    have hxr := htpne x hx
    have hF := h.stale x hx hv
    exact hF.transfer (hsync := rfl) (hkn := fun _ => rfl) (hke := rfl)
      (hack := (hAs x)) (hlog := (hLo x hxr)) (hprim := rfl) id
      (fun hq => hF.fenceLeInheritedEnd hq) (fun hq => by rw [hLo _ (Ne.symm hrprim)]; exact hF.primHolds hq)
      (fun hq => hF.primAck hq)
      (fun m hm hi => Or.inl ⟨hm, hi, hLo m (hnotr m (Or.inl hm)), Nat.le_refl _⟩)
  authEx := h.authEx }

/-- `r` is not authoritative (`resync_facts`), and no authoritative node's log moves. -/
theorem eligibleHoldsCommitted_resync : EligibleHoldsCommitted (resync s r) := by
  obtain ⟨hrprim, hrel, htpne⟩ := resync_facts h r hne hsy hke
  have hcl := commit_le_catchUpPoint h (primaryOf s r)
  have hLo : ∀ x, x ≠ r → (resync s r).log x = s.log x := fun _ => resync_log_other
  have hnotr : ∀ x, (s.cfg.eligible x = true ∨ x = s.cfg.primary) → x ≠ r := by
    intro x hx e; subst e
    rcases hx with hx | hx
    · rw [hrel] at hx; exact absurd hx (by decide)
    · exact hrprim hx
  intro x hx; rw [hLo x (hnotr x hx.1)]; exact h.eligibleHoldsCommitted x hx

/-- Resync copies the primary's log up to its CatchUpPoint (the inherited log while it
is unreconciled). -/
theorem invariant_resync : Invariant (resync s r) where
  toConfigInvariant := config_resync h r
  toReplInvariant := repl_resync h r hne hsy hke
  toMembershipInvariant := membership_resync h r hsy
  toCommitInvariant := commit_resync h r hne hsy hke
  toFailoverInvariant := failover_resync h r hne hsy hke
  eligibleHoldsCommitted := eligibleHoldsCommitted_resync h r hne hsy hke

end resync

end SyncReplication
