import SyncReplication.Invariant
import SyncReplication.Contracts

/-!
# Preservation: restarts (design §6, incarnations)

RestartEmpty (under the survival assumption), RestartKeep (the restarted primary
rebuilds its sync replica set), and RestartPartial, a restart from a persistence file that
holds only a prefix of the log: keeping the incarnation when the prefix covers the
node's high-water mark `ackHigh`, otherwise behaving as RestartEmpty.
-/

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

-- Every layer lemma takes the action's whole guard, so some take a part they
-- do not use.
set_option linter.unusedSectionVars false

section restartEmpty

variable {s : State Node} (h : Invariant s) (n : Node) (hkl : KnowsLatest s n) (hsurv : ∃ m, m ≠ n ∧ IsAuthoritative s m)

include h hkl hsurv

/-- `n`'s incarnation goes up, so recorded incarnations stay at or below the real ones. -/
theorem config_restartEmpty : ConfigInvariant (restartEmpty s n) := by
  have hI := restartEmpty_inc (s := s) (n := n)
  have hnauth : ¬ (s.cfg.incarnation n = s.incarnation n + 1) := by have := h.incLe n; omega
  exact {
  knownLe := h.knownLe
  knownEq := h.knownEq
  primKnows := h.primKnows
  incLe := by
    intro x; show s.cfg.incarnation x ≤ (restartEmpty s n).incarnation x; rw [hI]; split_ifs with e
    · subst e; have := h.incLe x; omega
    · exact h.incLe x
  knownIncLe := by
    intro x y; show (s.known x).incarnation y ≤ (restartEmpty s n).incarnation y; rw [hI]; split_ifs with e
    · subst e; have := h.knownIncLe x y; omega
    · exact h.knownIncLe x y }

/-- `n` loses its acknowledgements and sync replica set, and the current primary forgets `n`'s acknowledgement. -/
theorem repl_restartEmpty : ReplInvariant (restartEmpty s n) := by
  have hkn : s.known n = s.cfg := h.knownEq n hkl
  have hLo : ∀ x, x ≠ n → (restartEmpty s n).log x = s.log x := fun _ => restartEmpty_log_other
  have hCo : ∀ x, x ≠ n → (restartEmpty s n).commit x = s.commit x := fun _ => restartEmpty_commit_other
  have hS := restartEmpty_sync (s := s) (n := n)
  have hA := restartEmpty_acked (s := s) (n := n)
  have hAle := restartEmpty_acked_le (s := s) (n := n)
  have hnauth : ¬ (s.cfg.incarnation n = s.incarnation n + 1) := by have := h.incLe n; omega
  have htp : ∀ x, ThinksPrimary (restartEmpty s n) x → x ≠ n ∧ ThinksPrimary s x :=
    fun _ => restartEmpty_thinksPrimary hkn (h.incLe n)
  exact {
  noSelfSync := by
    intro p; rw [hS]; split
    · rfl
    · split
      · rfl
      · exact h.noSelfSync p
  ackedPrim := by
    intro r hr
    show (restartEmpty s n).acked s.cfg.primary r = 0
    have := hAle s.cfg.primary r; rw [h.ackedPrim r hr] at this; omega
  ackedLe := by
    intro p r hp
    obtain ⟨hpn, hp'⟩ := htp p hp
    rw [hLo p hpn]; exact Nat.le_trans (hAle p r) (h.ackedLe p r hp')
  ackHolds := by
    intro p m hp hm hf
    obtain ⟨hpn, hp'⟩ := htp p hp
    rw [hLo p hpn]
    by_cases emn : m = n
    · subst emn
      have hpp : p = s.cfg.primary := by rw [← hf]; show (s.known m).primary = s.cfg.primary; rw [hkn]
      rw [hA, if_neg hpn, if_pos ⟨hpp, rfl⟩]; simp
    · rw [hLo m emn, hA, if_neg hpn, if_neg (fun c => emn c.2)]
      exact h.ackHolds p m hp' hm hf
  ackedHigh := by
    intro p m hp hm hf
    obtain ⟨hpn, hp'⟩ := htp p hp
    show (restartEmpty s n).acked p m ≤ (restartEmpty s n).ackHigh m
    rw [restartEmpty_ackHigh]
    by_cases emn : m = n
    · subst emn
      have hpp : p = s.cfg.primary := by rw [← hf]; show (s.known m).primary = s.cfg.primary; rw [hkn]
      rw [hA, if_neg hpn, if_pos ⟨hpp, rfl⟩, if_pos rfl]
    · rw [hA, if_neg hpn, if_neg (fun c => emn c.2), if_neg emn]
      exact h.ackedHigh p m hp' hm hf
  syncCommit := by
    intro q r hq hs
    obtain ⟨hqn, hq'⟩ := htp q hq
    rw [hCo q hqn]
    have hs' := hS q r; rw [hs, if_neg hqn] at hs'
    rw [hA, if_neg hqn]
    split_ifs with c
    · rw [if_pos c] at hs'; exact absurd hs' (by decide)
    · rw [if_neg c] at hs'; exact h.syncCommit q r hq' hs'.symm }

/-- `n` no longer matches its recorded incarnation, so no primary has to count it. -/
theorem membership_restartEmpty : MembershipInvariant (restartEmpty s n) := by
  have hkn : s.known n = s.cfg := h.knownEq n hkl
  have hIo : ∀ x, x ≠ n → (restartEmpty s n).incarnation x = s.incarnation x := fun _ => restartEmpty_inc_other
  have hIn := restartEmpty_inc_self (s := s) (n := n)
  have hRo : ∀ x, x ≠ n → (restartEmpty s n).recon x = s.recon x := fun _ => restartEmpty_recon_other
  have hS := restartEmpty_sync (s := s) (n := n)
  have hA := restartEmpty_acked (s := s) (n := n)
  have hSle : ∀ p r, (restartEmpty s n).sync p r = true → s.sync p r = true :=
    fun _ _ => restartEmpty_sync_le
  have hnauth : ¬ (s.cfg.incarnation n = s.incarnation n + 1) := by have := h.incLe n; omega
  have htp : ∀ x, ThinksPrimary (restartEmpty s n) x → x ≠ n ∧ ThinksPrimary s x :=
    fun _ => restartEmpty_thinksPrimary hkn (h.incLe n)
  exact {
  eligibleCounted := by
    intro p r hp he hi
    obtain ⟨hpn, hp'⟩ := htp p hp
    have hrn : r ≠ n := by
      intro e; subst e
      change (s.known p).incarnation r = (restartEmpty s r).incarnation r at hi
      rw [hIn] at hi; have := h.knownIncLe p r; omega
    change (s.known p).incarnation r = (restartEmpty s n).incarnation r at hi
    rw [hIo r hrn] at hi
    rw [hS, if_neg hpn, if_neg (fun c => hrn c.2)]
    exact h.eligibleCounted p r hp' he hi
  syncNew := by
    intro r hs he
    change (restartEmpty s n).sync s.cfg.primary r = true at hs
    by_cases ep : s.cfg.primary = n
    · rw [hS, if_pos ep] at hs; exact absurd hs (by decide)
    · have hrn : r ≠ n := by
        intro e; rw [hS, if_neg ep, if_pos ⟨rfl, e⟩] at hs; exact absurd hs (by decide)
      obtain ⟨a, b⟩ := h.syncNew r (hSle _ _ hs) he
      refine ⟨a, ?_⟩
      show (restartEmpty s n).recon s.cfg.primary ≤ (restartEmpty s n).acked s.cfg.primary r
      rw [hRo _ ep, hA, if_neg ep, if_neg (fun c => hrn c.2)]; exact b
  eligibleInOldConfig := h.eligibleInOldConfig }

/-- `n`'s commit and catch-up points go to 0; if `n` was the primary it is no longer authoritative, and the commit facts about the current primary are conditional on that. -/
theorem commit_restartEmpty : CommitInvariant (restartEmpty s n) := by
  have hLo : ∀ x, x ≠ n → (restartEmpty s n).log x = s.log x := fun _ => restartEmpty_log_other
  have hCo : ∀ x, x ≠ n → (restartEmpty s n).commit x = s.commit x := fun _ => restartEmpty_commit_other
  have hCn := restartEmpty_commit_self (s := s) (n := n)
  have hRo : ∀ x, x ≠ n → (restartEmpty s n).recon x = s.recon x := fun _ => restartEmpty_recon_other
  have hRn := restartEmpty_recon_self (s := s) (n := n)
  have hnauth : ¬ (s.cfg.incarnation n = s.incarnation n + 1) := by have := h.incLe n; omega
  have hpa : PrimaryAuthoritative (restartEmpty s n) → s.cfg.primary ≠ n ∧ PrimaryAuthoritative s :=
    restartEmpty_primaryAuthoritative (h.incLe n)
  exact {
  caLen := by
    intro x; by_cases e : x = n
    · subst e; rw [hCn]; exact Nat.zero_le _
    · rw [hCo x e, hLo x e]; exact h.caLen x
  caHist := by
    intro x; by_cases e : x = n
    · subst e; rw [hCn]; exact Nat.zero_le _
    · rw [hCo x e]; exact h.caHist x
  caEq := by
    intro x; by_cases e : x = n
    · subst e; rw [hCn]; rfl
    · rw [hCo x e, hLo x e]; exact h.caEq x
  reconLen := by
    show (restartEmpty s n).recon s.cfg.primary ≤ ((restartEmpty s n).log s.cfg.primary).length
    by_cases ep : s.cfg.primary = n
    · rw [ep, hRn]; exact Nat.zero_le _
    · rw [hRo _ ep, hLo _ ep]; exact h.reconLen
  histLe := by
    intro hp
    obtain ⟨hpn, hp'⟩ := hpa hp
    show s.hist.length ≤ (restartEmpty s n).commit s.cfg.primary ∨
      s.hist.length ≤ (restartEmpty s n).recon s.cfg.primary
    rw [hCo _ hpn, hRo _ hpn]; exact h.histLe hp'
  histAck := by
    intro m hm
    obtain ⟨hmn, hm'⟩ := restartEmpty_isAuthoritative (h.incLe n) hm
    show s.hist.length ≤ (restartEmpty s n).ackHigh m
    rw [restartEmpty_ackHigh_other hmn]; exact h.histAck m hm' }

/-- Other nodes' fences do not move, and the survival guard keeps some other node authoritative. -/
theorem failover_restartEmpty : FailoverInvariant (restartEmpty s n) := by
  have hkn : s.known n = s.cfg := h.knownEq n hkl
  have hIo : ∀ x, x ≠ n → (restartEmpty s n).incarnation x = s.incarnation x := fun _ => restartEmpty_inc_other
  have hLo : ∀ x, x ≠ n → (restartEmpty s n).log x = s.log x := fun _ => restartEmpty_log_other
  have hRo : ∀ x, x ≠ n → (restartEmpty s n).recon x = s.recon x := fun _ => restartEmpty_recon_other
  have hS := restartEmpty_sync (s := s) (n := n)
  have hA := restartEmpty_acked (s := s) (n := n)
  have hnauth : ¬ (s.cfg.incarnation n = s.incarnation n + 1) := by have := h.incLe n; omega
  have htp : ∀ x, ThinksPrimary (restartEmpty s n) x → x ≠ n ∧ ThinksPrimary s x :=
    fun _ => restartEmpty_thinksPrimary hkn (h.incLe n)
  have hauth : ∀ x, IsAuthoritative (restartEmpty s n) x → x ≠ n ∧ IsAuthoritative s x :=
    fun _ => restartEmpty_isAuthoritative (h.incLe n)
  have hpa : PrimaryAuthoritative (restartEmpty s n) → s.cfg.primary ≠ n ∧ PrimaryAuthoritative s :=
    restartEmpty_primaryAuthoritative (h.incLe n)
  exact {
  stale := by
    intro p hp hv
    obtain ⟨hpn, hp'⟩ := htp p hp
    have hpp := stale_ne_prim h hv
    have hSp : (restartEmpty s n).sync p = s.sync p := by
      funext r; rw [hS, if_neg hpn, if_neg (fun c => hpp c.1)]
    have hAp : ∀ r, (restartEmpty s n).acked p r = s.acked p r := by
      intro r; rw [hA, if_neg hpn, if_neg (fun c => hpp c.1)]
    have hF := h.stale p hp' hv
    refine hF.transfer hSp (fun _ => rfl) (fun r _ => hAp r) (hLo p hpn) rfl
      (fun hq => (hpa hq).2) (fun hq => by rw [hRo _ (hpa hq).1]; exact hF.reconLe (hpa hq).2)
      (fun hq => by rw [hLo _ (hpa hq).1]; exact hF.primHolds (hpa hq).2)
      (fun hq => by rw [restartEmpty_ackHigh_other (hpa hq).1]; exact hF.primAck (hpa hq).2) ?_
    intro m hm hi
    have hmn : m ≠ n := (hauth m ⟨Or.inl hm, hi⟩).1
    left
    refine ⟨hm, ?_, hLo m hmn, by rw [restartEmpty_ackHigh_other hmn]⟩
    change s.cfg.incarnation m = (restartEmpty s n).incarnation m at hi
    rw [hIo m hmn] at hi; exact hi
  authEx := by
    obtain ⟨m, hmn, hm1, hm2⟩ := hsurv
    refine ⟨m, hm1, ?_⟩
    show s.cfg.incarnation m = (restartEmpty s n).incarnation m; rw [hIo m hmn]; exact hm2 }

/-- `n` stops being authoritative, and every other node keeps its log. -/
theorem ehc_restartEmpty : EligibleHoldsCommitted (restartEmpty s n) := by
  have hLo : ∀ x, x ≠ n → (restartEmpty s n).log x = s.log x := fun _ => restartEmpty_log_other
  have hnauth : ¬ (s.cfg.incarnation n = s.incarnation n + 1) := by have := h.incLe n; omega
  have hauth : ∀ x, IsAuthoritative (restartEmpty s n) x → x ≠ n ∧ IsAuthoritative s x :=
    fun _ => restartEmpty_isAuthoritative (h.incLe n)
  intro x hx
  obtain ⟨hxn, hx'⟩ := hauth x hx
  rw [hLo x hxn]; exact h.ehc x hx'

theorem invariant_restartEmpty : Invariant (restartEmpty s n) where
  toConfigInvariant := config_restartEmpty h n hkl hsurv
  toReplInvariant := repl_restartEmpty h n hkl hsurv
  toMembershipInvariant := membership_restartEmpty h n hkl hsurv
  toCommitInvariant := commit_restartEmpty h n hkl hsurv
  toFailoverInvariant := failover_restartEmpty h n hkl hsurv
  ehc := ehc_restartEmpty h n hkl hsurv

end restartEmpty

section restartKeep

variable {s : State Node} (h : Invariant s) (n : Node) (hkl : KnowsLatest s n)

include h hkl

/-- RestartKeep changes no configuration or incarnation. -/
theorem config_restartKeep : ConfigInvariant (restartKeep s n) :=
  (h.toConfigInvariant).frame rfl rfl rfl

/-- `n`'s acknowledgements are reset and its commit point is 0, so it is below every acknowledgement. -/
theorem repl_restartKeep : ReplInvariant (restartKeep s n) := by
  have hCo : ∀ x, x ≠ n → (restartKeep s n).commit x = s.commit x := fun _ => restartKeep_commit_other
  have hCn := restartKeep_commit_self (s := s) (n := n)
  have hAo : ∀ x, x ≠ n → (restartKeep s n).acked x = s.acked x := fun _ => restartKeep_acked_other
  have hAn := restartKeep_acked_self (s := s) (n := n)
  have hSo : ∀ x, x ≠ n → (restartKeep s n).sync x = s.sync x := fun _ => restartKeep_sync_other
  have hSn := restartKeep_sync_self (s := s) (n := n)
  have htp := restartKeep_thinksPrimary (s := s) (n := n)
  exact {
  noSelfSync := by
    intro p; by_cases e : p = n
    · subst e; rw [hSn]; split
      · simp [rebuiltSync]
      · rfl
    · rw [hSo p e]; exact h.noSelfSync p
  ackedPrim := by
    intro r hr
    show (restartKeep s n).acked s.cfg.primary r = 0
    by_cases e : s.cfg.primary = n
    · rw [e, hAn]
    · rw [hAo _ e]; exact h.ackedPrim r hr
  ackedLe := by
    intro p r hp
    by_cases e : p = n
    · subst e; rw [hAn]; exact Nat.zero_le _
    · rw [hAo p e]; exact h.ackedLe p r hp
  ackHolds := by
    intro p m hp hm hf
    by_cases e : p = n
    · subst e; rw [hAn]; simp
    · rw [hAo p e]; exact h.ackHolds p m hp hm hf
  ackedHigh := by
    intro p m hp hm hf
    show (restartKeep s n).acked p m ≤ s.ackHigh m
    by_cases e : p = n
    · subst e; rw [hAn]; exact Nat.zero_le _
    · rw [hAo p e]; exact h.ackedHigh p m hp hm hf
  syncCommit := by
    intro q r hq hs
    by_cases e : q = n
    · subst e; rw [hCn]; exact Nat.zero_le _
    · rw [hCo q e, hAo q e]; rw [hSo q e] at hs; exact h.syncCommit q r hq hs }

/-- A restarted primary counts every matching eligible replica again. -/
theorem membership_restartKeep : MembershipInvariant (restartKeep s n) := by
  have hkn : s.known n = s.cfg := h.knownEq n hkl
  have hRo : ∀ x, x ≠ n → (restartKeep s n).recon x = s.recon x := fun _ => restartKeep_recon_other
  have hAo : ∀ x, x ≠ n → (restartKeep s n).acked x = s.acked x := fun _ => restartKeep_acked_other
  have hSo : ∀ x, x ≠ n → (restartKeep s n).sync x = s.sync x := fun _ => restartKeep_sync_other
  have hSn := restartKeep_sync_self (s := s) (n := n)
  have hnse : ThinksPrimary s n → (s.known n).eligible n = true → (s.known n).incarnation n = s.incarnation n → False := by
    intro hp he hi; have := h.eligibleCounted n n hp he hi; rw [h.noSelfSync] at this
    exact absurd this (by decide)
  have htp := restartKeep_thinksPrimary (s := s) (n := n)
  exact {
  eligibleCounted := by
    intro p r hp he hi
    by_cases e : p = n
    · subst e
      have hc : (s.known p).primary = p ∧ (s.known p).incarnation p = s.incarnation p := hp
      rw [hSn, if_pos hc]
      have hrp : r ≠ p := by
        intro c; subst c; exact hnse hp he hi
      simp only [rebuiltSync, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨he, hi⟩, hrp⟩
    · rw [hSo p e]; exact h.eligibleCounted p r hp he hi
  syncNew := by
    intro r hs he
    by_cases e : s.cfg.primary = n
    · exfalso
      have hs' : (restartKeep s n).sync n r = true := by
        have := hs; change (restartKeep s n).sync s.cfg.primary r = true at this
        rw [e] at this; exact this
      change s.cfg.eligible r = false at he
      rw [hSn] at hs'
      split at hs'
      · simp only [rebuiltSync, hkn, Bool.and_eq_true] at hs'
        have := hs'.1.1; rw [he] at this; exact absurd this (by decide)
      · exact Bool.false_ne_true hs'
    · have hs' : s.sync s.cfg.primary r = true := by rw [← hSo _ e]; exact hs
      obtain ⟨a, b⟩ := h.syncNew r hs' he
      refine ⟨a, ?_⟩
      show (restartKeep s n).recon s.cfg.primary ≤ (restartKeep s n).acked s.cfg.primary r
      rw [hRo _ e, hAo _ e]; exact b
  eligibleInOldConfig := h.eligibleInOldConfig }

/-- `n` must re-commit its whole log: its commit point is 0 and its catch-up point is the end of its log. -/
theorem commit_restartKeep : CommitInvariant (restartKeep s n) := by
  have hCo : ∀ x, x ≠ n → (restartKeep s n).commit x = s.commit x := fun _ => restartKeep_commit_other
  have hCn := restartKeep_commit_self (s := s) (n := n)
  have hRo : ∀ x, x ≠ n → (restartKeep s n).recon x = s.recon x := fun _ => restartKeep_recon_other
  have hRn := restartKeep_recon_self (s := s) (n := n)
  have htp := restartKeep_thinksPrimary (s := s) (n := n)
  exact {
  caLen := by
    intro x; by_cases e : x = n
    · subst e; rw [hCn]; exact Nat.zero_le _
    · rw [hCo x e]; exact h.caLen x
  caHist := by
    intro x; by_cases e : x = n
    · subst e; rw [hCn]; exact Nat.zero_le _
    · rw [hCo x e]; exact h.caHist x
  caEq := by
    intro x; by_cases e : x = n
    · subst e; rw [hCn]; rfl
    · rw [hCo x e]; exact h.caEq x
  reconLen := by
    show (restartKeep s n).recon s.cfg.primary ≤ (s.log s.cfg.primary).length
    by_cases e : s.cfg.primary = n
    · rw [e, hRn]
    · rw [hRo _ e]; exact h.reconLen
  histLe := by
    intro hp
    show s.hist.length ≤ (restartKeep s n).commit s.cfg.primary ∨
      s.hist.length ≤ (restartKeep s n).recon s.cfg.primary
    by_cases e : s.cfg.primary = n
    · right; rw [e, hRn]; rw [← e]; exact (h.ehc _ ⟨Or.inr rfl, hp⟩).length_le
    · rw [hCo _ e, hRo _ e]; exact h.histLe hp
  histAck := h.histAck }

/-- `n` knows the latest configuration, so it is not deposed; other primaries' fences do not move. -/
theorem failover_restartKeep : FailoverInvariant (restartKeep s n) := by
  have hRo : ∀ x, x ≠ n → (restartKeep s n).recon x = s.recon x := fun _ => restartKeep_recon_other
  have hRn := restartKeep_recon_self (s := s) (n := n)
  have hAo : ∀ x, x ≠ n → (restartKeep s n).acked x = s.acked x := fun _ => restartKeep_acked_other
  have hSo : ∀ x, x ≠ n → (restartKeep s n).sync x = s.sync x := fun _ => restartKeep_sync_other
  have htp := restartKeep_thinksPrimary (s := s) (n := n)
  exact {
  stale := by
    intro p hp hv
    have hpn : p ≠ n := by
      intro c
      have hv' : (s.known p).version < s.cfg.version := hv
      rw [c] at hv'; unfold KnowsLatest at hkl; omega
    have hF := h.stale p hp hv
    refine hF.transfer (hSo p hpn) (fun _ => rfl)
      (fun r _ => by rw [hAo p hpn]) rfl rfl id ?_ (fun hq => hF.primHolds hq) (fun hq => hF.primAck hq)
      (fun m hm hi => Or.inl ⟨hm, hi, rfl, Nat.le_refl _⟩)
    -- the primary's catch-up point only moves up, to the end of its log
    intro hq
    show fence s p ≤ (restartKeep s n).recon s.cfg.primary
    by_cases e : s.cfg.primary = n
    · have h1 := hF.reconLe hq; have h2 := h.reconLen; rw [e] at h1 h2 ⊢; rw [hRn]; omega
    · rw [hRo _ e]; exact hF.reconLe hq
  authEx := h.authEx }

/-- No log or incarnation changes. -/
theorem ehc_restartKeep : EligibleHoldsCommitted (restartKeep s n) := by
  have htp := restartKeep_thinksPrimary (s := s) (n := n)
  exact h.ehc

theorem invariant_restartKeep : Invariant (restartKeep s n) where
  toConfigInvariant := config_restartKeep h n hkl
  toReplInvariant := repl_restartKeep h n hkl
  toMembershipInvariant := membership_restartKeep h n hkl
  toCommitInvariant := commit_restartKeep h n hkl
  toFailoverInvariant := failover_restartKeep h n hkl
  ehc := ehc_restartKeep h n hkl

end restartKeep

section restartPartialKeep

variable {s : State Node} (h : Invariant s) (n : Node) (k : Nat) (hkl : KnowsLatest s n)
    (hk : k < (s.log n).length) (hkeep : s.ackHigh n ≤ k)

include h hkl hk hkeep

/-! `n` keeps its incarnation, so it may still be authoritative, or primary. What makes
the truncated log safe is that it covers `n`'s high-water mark: everything `n`'s primary
recorded as acknowledged (`ackedHigh`), the whole committed history (`histAck`), and
every deposed primary's fence (`Fenced.eligHolds`, `Fenced.primAck`). -/

/-- RestartPartial changes no configuration or incarnation. -/
theorem config_restartPartialKeep : ConfigInvariant (restartPartialKeep s n k) :=
  (h.toConfigInvariant).frame rfl rfl rfl

/-- `n`'s acknowledgements are reset. The acknowledgement its primary recorded from it is
within `n`'s high-water mark, which the kept prefix covers, so it is still real. -/
theorem repl_restartPartialKeep : ReplInvariant (restartPartialKeep s n k) := by
  have hLo : ∀ x, x ≠ n → (restartPartialKeep s n k).log x = s.log x := fun _ => restartPartialKeep_log_other
  have hLn := restartPartialKeep_log_self (s := s) (n := n) (k := k)
  have hCo : ∀ x, x ≠ n → (restartPartialKeep s n k).commit x = s.commit x := fun _ => restartPartialKeep_commit_other
  have hCn := restartPartialKeep_commit_self (s := s) (n := n) (k := k)
  have hAo : ∀ x, x ≠ n → (restartPartialKeep s n k).acked x = s.acked x := fun _ => restartPartialKeep_acked_other
  have hAn := restartPartialKeep_acked_self (s := s) (n := n) (k := k)
  have hSo : ∀ x, x ≠ n → (restartPartialKeep s n k).sync x = s.sync x := fun _ => restartPartialKeep_sync_other
  have hSn := restartPartialKeep_sync_self (s := s) (n := n) (k := k)
  exact {
  noSelfSync := by
    intro p; by_cases e : p = n
    · subst e; rw [hSn]; split
      · simp [rebuiltSync]
      · rfl
    · rw [hSo p e]; exact h.noSelfSync p
  ackedPrim := by
    intro r hr
    show (restartPartialKeep s n k).acked s.cfg.primary r = 0
    by_cases e : s.cfg.primary = n
    · rw [e, hAn]
    · rw [hAo _ e]; exact h.ackedPrim r hr
  ackedLe := by
    intro p r hp
    show (restartPartialKeep s n k).acked p r ≤ ((restartPartialKeep s n k).log p).length
    by_cases e : p = n
    · subst e; rw [hAn]; exact Nat.zero_le _
    · rw [hAo p e, hLo p e]; exact h.ackedLe p r hp
  ackHolds := by
    intro p m hp hm hf
    show ((restartPartialKeep s n k).log p).take ((restartPartialKeep s n k).acked p m) <+:
      (restartPartialKeep s n k).log m
    by_cases e : p = n
    · subst e; rw [hAn]; simp
    · rw [hAo p e, hLo p e]
      by_cases em : m = n
      · subst em; rw [hLn]
        have hle : s.acked p m ≤ k := Nat.le_trans (h.ackedHigh p m hp hm hf) hkeep
        exact prefix_take_of_length_le (h.ackHolds p m hp hm hf) (by rw [List.length_take]; omega)
      · rw [hLo m em]; exact h.ackHolds p m hp hm hf
  ackedHigh := by
    intro p m hp hm hf
    show (restartPartialKeep s n k).acked p m ≤ s.ackHigh m
    by_cases e : p = n
    · subst e; rw [hAn]; exact Nat.zero_le _
    · rw [hAo p e]; exact h.ackedHigh p m hp hm hf
  syncCommit := by
    intro q r hq hs
    by_cases e : q = n
    · subst e; rw [hCn]; exact Nat.zero_le _
    · rw [hCo q e, hAo q e]; rw [hSo q e] at hs; exact h.syncCommit q r hq hs }

/-- As for RestartKeep: a restarted primary counts every matching eligible replica. -/
theorem membership_restartPartialKeep : MembershipInvariant (restartPartialKeep s n k) := by
  have hkn : s.known n = s.cfg := h.knownEq n hkl
  have hRo : ∀ x, x ≠ n → (restartPartialKeep s n k).recon x = s.recon x := fun _ => restartPartialKeep_recon_other
  have hAo : ∀ x, x ≠ n → (restartPartialKeep s n k).acked x = s.acked x := fun _ => restartPartialKeep_acked_other
  have hSo : ∀ x, x ≠ n → (restartPartialKeep s n k).sync x = s.sync x := fun _ => restartPartialKeep_sync_other
  have hSn := restartPartialKeep_sync_self (s := s) (n := n) (k := k)
  have hnse : ThinksPrimary s n → (s.known n).eligible n = true → (s.known n).incarnation n = s.incarnation n → False := by
    intro hp he hi; have := h.eligibleCounted n n hp he hi; rw [h.noSelfSync] at this
    exact absurd this (by decide)
  exact {
  eligibleCounted := by
    intro p r hp he hi
    by_cases e : p = n
    · subst e
      have hc : (s.known p).primary = p ∧ (s.known p).incarnation p = s.incarnation p := hp
      rw [hSn, if_pos hc]
      have hrp : r ≠ p := by
        intro c; subst c; exact hnse hp he hi
      simp only [rebuiltSync, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨he, hi⟩, hrp⟩
    · rw [hSo p e]; exact h.eligibleCounted p r hp he hi
  syncNew := by
    intro r hs he
    by_cases e : s.cfg.primary = n
    · exfalso
      have hs' : (restartPartialKeep s n k).sync n r = true := by
        have := hs; change (restartPartialKeep s n k).sync s.cfg.primary r = true at this
        rw [e] at this; exact this
      change s.cfg.eligible r = false at he
      rw [hSn] at hs'
      split at hs'
      · simp only [rebuiltSync, hkn, Bool.and_eq_true] at hs'
        have := hs'.1.1; rw [he] at this; exact absurd this (by decide)
      · exact Bool.false_ne_true hs'
    · have hs' : s.sync s.cfg.primary r = true := by rw [← hSo _ e]; exact hs
      obtain ⟨a, b⟩ := h.syncNew r hs' he
      refine ⟨a, ?_⟩
      show (restartPartialKeep s n k).recon s.cfg.primary ≤ (restartPartialKeep s n k).acked s.cfg.primary r
      rw [hRo _ e, hAo _ e]; exact b
  eligibleInOldConfig := h.eligibleInOldConfig }

/-- `n` must re-commit what it kept: its commit point is 0 and its catch-up point is the
end of the kept prefix. If `n` is the primary, the whole history is below that, because
`n` had acknowledged all of it (`histAck`). -/
theorem commit_restartPartialKeep : CommitInvariant (restartPartialKeep s n k) := by
  have hLo : ∀ x, x ≠ n → (restartPartialKeep s n k).log x = s.log x := fun _ => restartPartialKeep_log_other
  have hLn := restartPartialKeep_log_self (s := s) (n := n) (k := k)
  have hCo : ∀ x, x ≠ n → (restartPartialKeep s n k).commit x = s.commit x := fun _ => restartPartialKeep_commit_other
  have hCn := restartPartialKeep_commit_self (s := s) (n := n) (k := k)
  have hRo : ∀ x, x ≠ n → (restartPartialKeep s n k).recon x = s.recon x := fun _ => restartPartialKeep_recon_other
  have hRn := restartPartialKeep_recon_self (s := s) (n := n) (k := k)
  exact {
  caLen := by
    intro x; by_cases e : x = n
    · subst e; rw [hCn]; exact Nat.zero_le _
    · rw [hCo x e, hLo x e]; exact h.caLen x
  caHist := by
    intro x; by_cases e : x = n
    · subst e; rw [hCn]; exact Nat.zero_le _
    · rw [hCo x e]; exact h.caHist x
  caEq := by
    intro x; by_cases e : x = n
    · subst e; rw [hCn]; rfl
    · rw [hCo x e, hLo x e]; exact h.caEq x
  reconLen := by
    show (restartPartialKeep s n k).recon s.cfg.primary ≤ ((restartPartialKeep s n k).log s.cfg.primary).length
    by_cases e : s.cfg.primary = n
    · rw [e, hRn, hLn, List.length_take]; omega
    · rw [hRo _ e, hLo _ e]; exact h.reconLen
  histLe := by
    intro hp
    show s.hist.length ≤ (restartPartialKeep s n k).commit s.cfg.primary ∨
      s.hist.length ≤ (restartPartialKeep s n k).recon s.cfg.primary
    by_cases e : s.cfg.primary = n
    · right; rw [e, hRn]
      have hpa : PrimaryAuthoritative s := hp
      have := h.histAck n ⟨Or.inr e.symm, by rw [← e]; exact hpa⟩
      omega
    · rw [hCo _ e, hRo _ e]; exact h.histLe hp
  histAck := h.histAck }

/-- `n` knows the latest configuration, so it is not deposed. Every deposed primary's
fence is within `n`'s high-water mark, so the kept prefix still holds its log up to
the fence, whether `n` is the current primary or an eligible replica. -/
theorem failover_restartPartialKeep : FailoverInvariant (restartPartialKeep s n k) := by
  have hkn : s.known n = s.cfg := h.knownEq n hkl
  have hLo : ∀ x, x ≠ n → (restartPartialKeep s n k).log x = s.log x := fun _ => restartPartialKeep_log_other
  have hLn := restartPartialKeep_log_self (s := s) (n := n) (k := k)
  have hRo : ∀ x, x ≠ n → (restartPartialKeep s n k).recon x = s.recon x := fun _ => restartPartialKeep_recon_other
  have hRn := restartPartialKeep_recon_self (s := s) (n := n) (k := k)
  have hAo : ∀ x, x ≠ n → (restartPartialKeep s n k).acked x = s.acked x := fun _ => restartPartialKeep_acked_other
  have hSo : ∀ x, x ≠ n → (restartPartialKeep s n k).sync x = s.sync x := fun _ => restartPartialKeep_sync_other
  exact {
  stale := by
    intro p hp hv
    have hpn : p ≠ n := by
      intro c
      have hv' : (s.known p).version < s.cfg.version := hv
      rw [c] at hv'; unfold KnowsLatest at hkl; omega
    have hF := h.stale p hp hv
    have hpp := stale_ne_prim h hv
    refine hF.transfer (hSo p hpn) (fun _ => rfl) (fun r _ => by rw [hAo p hpn]) (hLo p hpn) rfl id
      ?_ ?_ (fun hq => hF.primAck hq) ?_
    · -- the fence is within the primary's high-water mark, hence within the kept prefix
      intro hq
      show fence s p ≤ (restartPartialKeep s n k).recon s.cfg.primary
      by_cases e : s.cfg.primary = n
      · rw [e, hRn]; have := hF.primAck hq; rw [e] at this; omega
      · rw [hRo _ e]; exact hF.reconLe hq
    · intro hq
      show (s.log p).take (fence s p) <+: (restartPartialKeep s n k).log s.cfg.primary
      by_cases e : s.cfg.primary = n
      · rw [e, hLn]
        have hfk : fence s p ≤ k := by have := hF.primAck hq; rw [e] at this; omega
        have := hF.primHolds hq; rw [e] at this
        exact prefix_take_of_length_le this (by rw [List.length_take]; omega)
      · rw [hLo _ e]; exact hF.primHolds hq
    · intro m hm hi
      by_cases em : m = n
      · subst em
        -- m knows the latest configuration, so it does not follow the deposed p; it holds
        -- and has acknowledged p's log up to the fence, and the kept prefix covers that
        have hd : (s.log p).take (fence s p) <+: s.log m ∧ fence s p ≤ s.ackHigh m := by
          rcases hF.eligHolds m hm hi with d | ⟨_, d2⟩
          · exact d
          · exfalso; rw [hkn] at d2; exact hpp d2.symm
        have hfk : fence s p ≤ k := hd.2.trans hkeep
        right
        refine ⟨?_, hd.2⟩
        rw [hLn]; exact prefix_take_of_length_le hd.1 (by rw [List.length_take]; omega)
      · left; exact ⟨hm, hi, hLo m em, Nat.le_refl _⟩
  authEx := h.authEx }

/-- `n` had acknowledged the whole committed history, so the kept prefix holds it. -/
theorem ehc_restartPartialKeep : EligibleHoldsCommitted (restartPartialKeep s n k) := by
  intro x hx
  have hx' : IsAuthoritative s x := hx
  by_cases e : x = n
  · subst e
    show s.hist <+: (restartPartialKeep s x k).log x
    rw [restartPartialKeep_log_self]
    exact prefix_take_of_length_le (h.ehc x hx') ((h.histAck x hx').trans hkeep)
  · show s.hist <+: (restartPartialKeep s n k).log x
    rw [restartPartialKeep_log_other e]; exact h.ehc x hx'

theorem invariant_restartPartialKeep : Invariant (restartPartialKeep s n k) where
  toConfigInvariant := config_restartPartialKeep h n k hkl hk hkeep
  toReplInvariant := repl_restartPartialKeep h n k hkl hk hkeep
  toMembershipInvariant := membership_restartPartialKeep h n k hkl hk hkeep
  toCommitInvariant := commit_restartPartialKeep h n k hkl hk hkeep
  toFailoverInvariant := failover_restartPartialKeep h n k hkl hk hkeep
  ehc := ehc_restartPartialKeep h n k hkl hk hkeep

end restartPartialKeep

section restartPartialFresh

variable {s : State Node} (h : Invariant s) (n : Node) (k : Nat) (hkl : KnowsLatest s n)
    (hsurv : ∃ m, m ≠ n ∧ IsAuthoritative s m) (hk : k < (s.log n).length) (hfresh : k < s.ackHigh n)

include h hkl hsurv hk hfresh

/-! The incarnation changes and the kept entries play no part: every proof is the
RestartEmpty proof, which never used `log n = []`. -/

/-- `n`'s incarnation goes up, so recorded incarnations stay at or below the real ones. -/
theorem config_restartPartialFresh : ConfigInvariant (restartPartialFresh s n k) := by
  have hI := restartPartialFresh_inc (s := s) (n := n) (k := k)
  have hnauth : ¬ (s.cfg.incarnation n = s.incarnation n + 1) := by have := h.incLe n; omega
  exact {
  knownLe := h.knownLe
  knownEq := h.knownEq
  primKnows := h.primKnows
  incLe := by
    intro x; show s.cfg.incarnation x ≤ (restartPartialFresh s n k).incarnation x; rw [hI]; split_ifs with e
    · subst e; have := h.incLe x; omega
    · exact h.incLe x
  knownIncLe := by
    intro x y; show (s.known x).incarnation y ≤ (restartPartialFresh s n k).incarnation y; rw [hI]; split_ifs with e
    · subst e; have := h.knownIncLe x y; omega
    · exact h.knownIncLe x y }

/-- `n` loses its acknowledgements and sync replica set, and the current primary forgets `n`'s acknowledgement. -/
theorem repl_restartPartialFresh : ReplInvariant (restartPartialFresh s n k) := by
  have hkn : s.known n = s.cfg := h.knownEq n hkl
  have hLo : ∀ x, x ≠ n → (restartPartialFresh s n k).log x = s.log x := fun _ => restartPartialFresh_log_other
  have hCo : ∀ x, x ≠ n → (restartPartialFresh s n k).commit x = s.commit x := fun _ => restartPartialFresh_commit_other
  have hS := restartPartialFresh_sync (s := s) (n := n) (k := k)
  have hA := restartPartialFresh_acked (s := s) (n := n) (k := k)
  have hAle := restartPartialFresh_acked_le (s := s) (n := n) (k := k)
  have hnauth : ¬ (s.cfg.incarnation n = s.incarnation n + 1) := by have := h.incLe n; omega
  have htp : ∀ x, ThinksPrimary (restartPartialFresh s n k) x → x ≠ n ∧ ThinksPrimary s x :=
    fun _ => restartPartialFresh_thinksPrimary hkn (h.incLe n)
  exact {
  noSelfSync := by
    intro p; rw [hS]; split
    · rfl
    · split
      · rfl
      · exact h.noSelfSync p
  ackedPrim := by
    intro r hr
    show (restartPartialFresh s n k).acked s.cfg.primary r = 0
    have := hAle s.cfg.primary r; rw [h.ackedPrim r hr] at this; omega
  ackedLe := by
    intro p r hp
    obtain ⟨hpn, hp'⟩ := htp p hp
    rw [hLo p hpn]; exact Nat.le_trans (hAle p r) (h.ackedLe p r hp')
  ackHolds := by
    intro p m hp hm hf
    obtain ⟨hpn, hp'⟩ := htp p hp
    rw [hLo p hpn]
    by_cases emn : m = n
    · subst emn
      have hpp : p = s.cfg.primary := by rw [← hf]; show (s.known m).primary = s.cfg.primary; rw [hkn]
      rw [hA, if_neg hpn, if_pos ⟨hpp, rfl⟩]; simp
    · rw [hLo m emn, hA, if_neg hpn, if_neg (fun c => emn c.2)]
      exact h.ackHolds p m hp' hm hf
  ackedHigh := by
    intro p m hp hm hf
    obtain ⟨hpn, hp'⟩ := htp p hp
    show (restartPartialFresh s n k).acked p m ≤ (restartPartialFresh s n k).ackHigh m
    rw [restartPartialFresh_ackHigh]
    by_cases emn : m = n
    · subst emn
      have hpp : p = s.cfg.primary := by rw [← hf]; show (s.known m).primary = s.cfg.primary; rw [hkn]
      rw [hA, if_neg hpn, if_pos ⟨hpp, rfl⟩, if_pos rfl]
    · rw [hA, if_neg hpn, if_neg (fun c => emn c.2), if_neg emn]
      exact h.ackedHigh p m hp' hm hf
  syncCommit := by
    intro q r hq hs
    obtain ⟨hqn, hq'⟩ := htp q hq
    rw [hCo q hqn]
    have hs' := hS q r; rw [hs, if_neg hqn] at hs'
    rw [hA, if_neg hqn]
    split_ifs with c
    · rw [if_pos c] at hs'; exact absurd hs' (by decide)
    · rw [if_neg c] at hs'; exact h.syncCommit q r hq' hs'.symm }

/-- `n` no longer matches its recorded incarnation, so no primary has to count it. -/
theorem membership_restartPartialFresh : MembershipInvariant (restartPartialFresh s n k) := by
  have hkn : s.known n = s.cfg := h.knownEq n hkl
  have hIo : ∀ x, x ≠ n → (restartPartialFresh s n k).incarnation x = s.incarnation x := fun _ => restartPartialFresh_inc_other
  have hIn := restartPartialFresh_inc_self (s := s) (n := n) (k := k)
  have hRo : ∀ x, x ≠ n → (restartPartialFresh s n k).recon x = s.recon x := fun _ => restartPartialFresh_recon_other
  have hS := restartPartialFresh_sync (s := s) (n := n) (k := k)
  have hA := restartPartialFresh_acked (s := s) (n := n) (k := k)
  have hSle : ∀ p r, (restartPartialFresh s n k).sync p r = true → s.sync p r = true :=
    fun _ _ => restartPartialFresh_sync_le
  have hnauth : ¬ (s.cfg.incarnation n = s.incarnation n + 1) := by have := h.incLe n; omega
  have htp : ∀ x, ThinksPrimary (restartPartialFresh s n k) x → x ≠ n ∧ ThinksPrimary s x :=
    fun _ => restartPartialFresh_thinksPrimary hkn (h.incLe n)
  exact {
  eligibleCounted := by
    intro p r hp he hi
    obtain ⟨hpn, hp'⟩ := htp p hp
    have hrn : r ≠ n := by
      intro e; subst e
      change (s.known p).incarnation r = (restartPartialFresh s r k).incarnation r at hi
      rw [hIn] at hi; have := h.knownIncLe p r; omega
    change (s.known p).incarnation r = (restartPartialFresh s n k).incarnation r at hi
    rw [hIo r hrn] at hi
    rw [hS, if_neg hpn, if_neg (fun c => hrn c.2)]
    exact h.eligibleCounted p r hp' he hi
  syncNew := by
    intro r hs he
    change (restartPartialFresh s n k).sync s.cfg.primary r = true at hs
    by_cases ep : s.cfg.primary = n
    · rw [hS, if_pos ep] at hs; exact absurd hs (by decide)
    · have hrn : r ≠ n := by
        intro e; rw [hS, if_neg ep, if_pos ⟨rfl, e⟩] at hs; exact absurd hs (by decide)
      obtain ⟨a, b⟩ := h.syncNew r (hSle _ _ hs) he
      refine ⟨a, ?_⟩
      show (restartPartialFresh s n k).recon s.cfg.primary ≤ (restartPartialFresh s n k).acked s.cfg.primary r
      rw [hRo _ ep, hA, if_neg ep, if_neg (fun c => hrn c.2)]; exact b
  eligibleInOldConfig := h.eligibleInOldConfig }

/-- `n`'s commit and catch-up points go to 0; if `n` was the primary it is no longer authoritative, and the commit facts about the current primary are conditional on that. -/
theorem commit_restartPartialFresh : CommitInvariant (restartPartialFresh s n k) := by
  have hLo : ∀ x, x ≠ n → (restartPartialFresh s n k).log x = s.log x := fun _ => restartPartialFresh_log_other
  have hCo : ∀ x, x ≠ n → (restartPartialFresh s n k).commit x = s.commit x := fun _ => restartPartialFresh_commit_other
  have hCn := restartPartialFresh_commit_self (s := s) (n := n) (k := k)
  have hRo : ∀ x, x ≠ n → (restartPartialFresh s n k).recon x = s.recon x := fun _ => restartPartialFresh_recon_other
  have hRn := restartPartialFresh_recon_self (s := s) (n := n) (k := k)
  have hnauth : ¬ (s.cfg.incarnation n = s.incarnation n + 1) := by have := h.incLe n; omega
  have hpa : PrimaryAuthoritative (restartPartialFresh s n k) → s.cfg.primary ≠ n ∧ PrimaryAuthoritative s :=
    restartPartialFresh_primaryAuthoritative (h.incLe n)
  exact {
  caLen := by
    intro x; by_cases e : x = n
    · subst e; rw [hCn]; exact Nat.zero_le _
    · rw [hCo x e, hLo x e]; exact h.caLen x
  caHist := by
    intro x; by_cases e : x = n
    · subst e; rw [hCn]; exact Nat.zero_le _
    · rw [hCo x e]; exact h.caHist x
  caEq := by
    intro x; by_cases e : x = n
    · subst e; rw [hCn]; rfl
    · rw [hCo x e, hLo x e]; exact h.caEq x
  reconLen := by
    show (restartPartialFresh s n k).recon s.cfg.primary ≤ ((restartPartialFresh s n k).log s.cfg.primary).length
    by_cases ep : s.cfg.primary = n
    · rw [ep, hRn]; exact Nat.zero_le _
    · rw [hRo _ ep, hLo _ ep]; exact h.reconLen
  histLe := by
    intro hp
    obtain ⟨hpn, hp'⟩ := hpa hp
    show s.hist.length ≤ (restartPartialFresh s n k).commit s.cfg.primary ∨
      s.hist.length ≤ (restartPartialFresh s n k).recon s.cfg.primary
    rw [hCo _ hpn, hRo _ hpn]; exact h.histLe hp'
  histAck := by
    intro m hm
    obtain ⟨hmn, hm'⟩ := restartPartialFresh_isAuthoritative (h.incLe n) hm
    show s.hist.length ≤ (restartPartialFresh s n k).ackHigh m
    rw [restartPartialFresh_ackHigh_other hmn]; exact h.histAck m hm' }

/-- Other nodes' fences do not move, and the survival guard keeps some other node authoritative. -/
theorem failover_restartPartialFresh : FailoverInvariant (restartPartialFresh s n k) := by
  have hkn : s.known n = s.cfg := h.knownEq n hkl
  have hIo : ∀ x, x ≠ n → (restartPartialFresh s n k).incarnation x = s.incarnation x := fun _ => restartPartialFresh_inc_other
  have hLo : ∀ x, x ≠ n → (restartPartialFresh s n k).log x = s.log x := fun _ => restartPartialFresh_log_other
  have hRo : ∀ x, x ≠ n → (restartPartialFresh s n k).recon x = s.recon x := fun _ => restartPartialFresh_recon_other
  have hS := restartPartialFresh_sync (s := s) (n := n) (k := k)
  have hA := restartPartialFresh_acked (s := s) (n := n) (k := k)
  have hnauth : ¬ (s.cfg.incarnation n = s.incarnation n + 1) := by have := h.incLe n; omega
  have htp : ∀ x, ThinksPrimary (restartPartialFresh s n k) x → x ≠ n ∧ ThinksPrimary s x :=
    fun _ => restartPartialFresh_thinksPrimary hkn (h.incLe n)
  have hauth : ∀ x, IsAuthoritative (restartPartialFresh s n k) x → x ≠ n ∧ IsAuthoritative s x :=
    fun _ => restartPartialFresh_isAuthoritative (h.incLe n)
  have hpa : PrimaryAuthoritative (restartPartialFresh s n k) → s.cfg.primary ≠ n ∧ PrimaryAuthoritative s :=
    restartPartialFresh_primaryAuthoritative (h.incLe n)
  exact {
  stale := by
    intro p hp hv
    obtain ⟨hpn, hp'⟩ := htp p hp
    have hpp := stale_ne_prim h hv
    have hSp : (restartPartialFresh s n k).sync p = s.sync p := by
      funext r; rw [hS, if_neg hpn, if_neg (fun c => hpp c.1)]
    have hAp : ∀ r, (restartPartialFresh s n k).acked p r = s.acked p r := by
      intro r; rw [hA, if_neg hpn, if_neg (fun c => hpp c.1)]
    have hF := h.stale p hp' hv
    refine hF.transfer hSp (fun _ => rfl) (fun r _ => hAp r) (hLo p hpn) rfl
      (fun hq => (hpa hq).2) (fun hq => by rw [hRo _ (hpa hq).1]; exact hF.reconLe (hpa hq).2)
      (fun hq => by rw [hLo _ (hpa hq).1]; exact hF.primHolds (hpa hq).2)
      (fun hq => by rw [restartPartialFresh_ackHigh_other (hpa hq).1]; exact hF.primAck (hpa hq).2) ?_
    intro m hm hi
    have hmn : m ≠ n := (hauth m ⟨Or.inl hm, hi⟩).1
    left
    refine ⟨hm, ?_, hLo m hmn, by rw [restartPartialFresh_ackHigh_other hmn]⟩
    change s.cfg.incarnation m = (restartPartialFresh s n k).incarnation m at hi
    rw [hIo m hmn] at hi; exact hi
  authEx := by
    obtain ⟨m, hmn, hm1, hm2⟩ := hsurv
    refine ⟨m, hm1, ?_⟩
    show s.cfg.incarnation m = (restartPartialFresh s n k).incarnation m; rw [hIo m hmn]; exact hm2 }

/-- `n` stops being authoritative, and every other node keeps its log. -/
theorem ehc_restartPartialFresh : EligibleHoldsCommitted (restartPartialFresh s n k) := by
  have hLo : ∀ x, x ≠ n → (restartPartialFresh s n k).log x = s.log x := fun _ => restartPartialFresh_log_other
  have hnauth : ¬ (s.cfg.incarnation n = s.incarnation n + 1) := by have := h.incLe n; omega
  have hauth : ∀ x, IsAuthoritative (restartPartialFresh s n k) x → x ≠ n ∧ IsAuthoritative s x :=
    fun _ => restartPartialFresh_isAuthoritative (h.incLe n)
  intro x hx
  obtain ⟨hxn, hx'⟩ := hauth x hx
  rw [hLo x hxn]; exact h.ehc x hx'

theorem invariant_restartPartialFresh : Invariant (restartPartialFresh s n k) where
  toConfigInvariant := config_restartPartialFresh h n k hkl hsurv hk hfresh
  toReplInvariant := repl_restartPartialFresh h n k hkl hsurv hk hfresh
  toMembershipInvariant := membership_restartPartialFresh h n k hkl hsurv hk hfresh
  toCommitInvariant := commit_restartPartialFresh h n k hkl hsurv hk hfresh
  toFailoverInvariant := failover_restartPartialFresh h n k hkl hsurv hk hfresh
  ehc := ehc_restartPartialFresh h n k hkl hsurv hk hfresh

end restartPartialFresh

end SyncReplication
