import SyncReplication.InstantLeases

/-!
# A restart need not clear the node's grantor rows

A restart clears four lease rows of the restarted node `n` (`leaseRestart`): its read
lease as a holder, and, as a grantor, its primary leases (`primaryLease n`), the times
it last heard from each replica (`ackReceived n`) and the acknowledgements it last
echoed (`ackEcho n`). The model keeps all four clears, because a real restart forgets
this in-memory state. This file shows that the three grantor rows need not be
cleared for `NoStaleRead`.

`LeaseStepKeepGrantorRows` is `LeaseStep` plus the four restarts with those three rows
kept. `noStaleRead_keepGrantorRows` proves `NoStaleRead` in every state it reaches.
Kept rows are older than any the node would build afresh, so each errs on the safe
side, and the restart's demotion wait (`oldEligible n := fun _ => true`) covers every
replica whatever `ackReceived n` says. (Keeping the holder's read lease is not safe:
`restartKeepsReadLease_stale`.)
-/

open Cslib

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-- `leaseRestart`, except that `n`'s grantor rows (`primaryLease`, `ackReceived`,
`ackEcho`) are kept. -/
def leaseRestartKeepGrantorRows (a : LeaseState Node) (n : Node) (c : State Node) : LeaseState Node :=
  { leaseRestart a n c with primaryLease := a.primaryLease, ackReceived := a.ackReceived,
                            ackEcho := a.ackEcho }

/-- `LeaseStep`, plus the restarts that keep the restarted node's grantor rows. -/
inductive LeaseStepKeepGrantorRows (m : Nat) (P : LeaseParams) :
    LeaseState Node → LeaseAction Node → LeaseState Node → Prop
  | step (a μ a') (hs : LeaseStep m P a μ a') : LeaseStepKeepGrantorRows m P a μ a'
  | restartEmpty (a n) : (hKnowsLatest : KnowsLatest a.core n) →
      (hSurvivor : ∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      LeaseStepKeepGrantorRows m P a (.restartEmpty n) (leaseRestartKeepGrantorRows a n (restartEmpty a.core n))
  | restartKeep (a n) : (hKnowsLatest : KnowsLatest a.core n) →
      LeaseStepKeepGrantorRows m P a (.restartKeep n) (leaseRestartKeepGrantorRows a n (restartKeep a.core n))
  | restartPartialKeep (a n k) : (hKnowsLatest : KnowsLatest a.core n) →
      (hFileShorter : k < (a.core.log n).length) → (hCoversAcks : a.core.ackHigh n ≤ k) →
      LeaseStepKeepGrantorRows m P a (.restartPartial n k)
        (leaseRestartKeepGrantorRows a n (restartPartialKeep a.core n k))
  | restartPartialFresh (a n k) : (hKnowsLatest : KnowsLatest a.core n) →
      (hFileShorter : k < (a.core.log n).length) → (hMissesAcks : k < a.core.ackHigh n) →
      (hSurvivor : ∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      LeaseStepKeepGrantorRows m P a (.restartPartial n k)
        (leaseRestartKeepGrantorRows a n (restartPartialFresh a.core n k))

/-- The lease layer with grantor rows kept across restarts, as a labelled transition
system. -/
def leaseTransitionSystemKeepGrantorRows (m : Nat) (P : LeaseParams) :
    LTS (LeaseState Node) (LeaseAction Node) where
  Tr := LeaseStepKeepGrantorRows m P

/-- The restart lemma (`leaseInvariant_restart`) with `n`'s grantor rows kept. The only
conjunct that reads them across the restart is `primarySinceAck`: `n`'s kept
acknowledgements predate its new primaryship, and the restart marks every replica old,
which is the second disjunct. -/
theorem leaseInvariant_restartKeepGrantorRows {P : LeaseParams} {a : LeaseState Node}
    (h : LeaseInvariant P a) {n : Node} {c : State Node} (hc : Invariant c)
    (hkl : KnowsLatest a.core n)
    (hcfg : c.cfg = a.core.cfg) (hlocalCfg : c.localCfg = a.core.localCfg)
    (hinc : ∀ x, x ≠ n → c.incarnation x = a.core.incarnation x)
    (hlog : ∀ x, x ≠ n → c.log x = a.core.log x) (hhist : c.hist = a.core.hist)
    (hcommit : ∀ x, x ≠ n → c.commit x = a.core.commit x) :
    LeaseInvariant P (leaseRestartKeepGrantorRows a n c) := by
  have hPT := primaryTraffic_bump h n
  have hPS : ∀ p T, update a.primarySince n (some a.now) p = some T → T ≤ a.now := by
    intro q T hT; by_cases e : q = n
    · subst e; rw [update_self] at hT; cases hT; exact Nat.le_refl _
    · rw [update_of_ne _ _ e] at hT; exact h.primarySinceLe q T hT
  have hPA : ∀ p r T b, update a.primarySince n (some a.now) p = some T → a.ackReceived p r = some b →
      T ≤ b ∨ update a.oldEligible n (fun _ => true) p r = true := by
    intro q x T b hT hb; by_cases e : q = n
    · subst e; right; rw [update_self]
    · rw [update_of_ne _ _ e] at hT; rw [update_of_ne _ _ e]; exact h.primarySinceAck q x T b hT hb
  obtain ⟨hCV, hCH⟩ := committedView_reset h n hlog hhist
  obtain ⟨_, hcb, hgle⟩ := bump_facts h (a' := leaseRestartKeepGrantorRows a n c) (n := n) rfl rfl
  have hLS : ∀ r x, LeaseStart (leaseRestartKeepGrantorRows a n c) r x → r ≠ n ∧ LeaseStart a r x := by
    intro r x hx
    rcases hx with hx | ⟨msg, hm, hc, hd, he⟩
    · obtain ⟨hrn, hx⟩ := update_none_some _ _ _ hx; exact ⟨hrn, Or.inl hx⟩
    · obtain ⟨hc', _, hdn⟩ := hcb msg hm hc
      exact ⟨hd ▸ hdn, Or.inr ⟨msg, hm, hc', hd, he⟩⟩
  have hPLS : ∀ p r x, PrimStart (leaseRestartKeepGrantorRows a n c) p r x → PrimStart a p r x := by
    intro p r x hx
    rcases hx with hx | ⟨msg, hm, hc, hd, hs, he⟩
    · exact Or.inl hx
    · exact Or.inr ⟨msg, hm, (hcb msg hm hc).1, hd, hs, he⟩
  obtain ⟨hS1, hS2, hS3, hS4⟩ := msgs_frame h (a' := leaseRestartKeepGrantorRows a n c) (Nat.le_refl _) (fun _ hm => hm)
    (fun msg hm hc => (hcb msg hm hc).1) hgle
    (fun msg hm hc => (hcommit _ (hcb msg hm hc).2.1).ge)
    (fun msg _ _ => congrArg (fun f => (f msg.dst).primary) hlocalCfg)
  exact {
  core := hc
  primaryTrafficLe := fun x => (hPT x).2
  ackReceivedLe := h.ackReceivedLe, primarySinceLe := hPS, echoLe := h.echoLe, primarySinceAck := hPA
  primaryLeaseLe := fun q x v hv => Nat.le_trans (h.primaryLeaseLe q x v (hPLS q x v hv)) (hPT x).1
  dataSentLe := by
    intro x; show update a.dataSent n a.now x ≤ update a.primaryTraffic n a.now x
    unfold update; split_ifs
    · exact Nat.le_refl _
    · exact h.dataSentLe x
  deposed := by
    intro q hq hv
    -- `n` knew the latest configuration, so it is not the deposed node.
    have hqn : q ≠ n := by
      intro e; subst e; change (c.localCfg q).epoch < c.cfg.epoch at hv
      rw [hlocalCfg, hcfg] at hv; unfold KnowsLatest at hkl; omega
    obtain ⟨t, h1, h2, h3, h4⟩ :=
      deposed_frame h (hcfg := hcfg) (hlocalCfg := hlocalCfg) ((thinksPrimary_congr hlocalCfg (hinc q hqn)).1 hq) hv
    exact ⟨t, h1, h2, h3, fun x hx => h4 x (hPLS q t x hx)⟩
  leaseBound := by
    intro x v hx
    obtain ⟨hxn, hx⟩ := hLS x v hx
    show (∃ b, a.ackReceived c.cfg.primary x = some b ∧ v ≤ b) ∨
      (∃ T, update a.primarySince n (some a.now) c.cfg.primary = some T ∧ v ≤ T ∧
        (update a.oldEligible n (fun _ => true) c.cfg.primary x = true ∨
          ¬ HolderValid P a.now (some v) P.readDur))
    rw [hcfg]
    by_cases hpn : a.core.cfg.primary = n
    · -- the primary restarted: every remaining lease is bounded by its new primaryship.
      rw [hpn, update_self, update_self]
      right; exact ⟨a.now, rfl, h.leaseStartLe x v hx, Or.inl rfl⟩
    · rw [update_of_ne _ _ hpn, update_of_ne _ _ hpn]; exact h.leaseBound x v hx
  leaseAuth := by
    intro x v hx hnp hv
    obtain ⟨ex, hx⟩ := hLS x v hx
    exact (isAuthoritative_congr hcfg (hinc x ex)).2
      (h.leaseAuth x v hx (fun hp => hnp ((thinksPrimary_congr hlocalCfg (hinc x ex)).2 hp)) hv)
  selfPrimNoLease := by
    intro q hq v hx
    obtain ⟨_, hx⟩ := hLS q v hx
    change (c.localCfg q).primary = q at hq; rw [hlocalCfg] at hq; exact h.selfPrimNoLease q hq v hx
  committedViewLen := hCV
  committedViewHist := hCH
  sentLe := hS1, genLe := hS2, commitLe := hS3, follows := hS4 }

/-- Every step of the variant preserves the lease invariant. -/
theorem leaseInvariant_stepKeepGrantorRows {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {m : Nat}
    {a a' : LeaseState Node} {μ : LeaseAction Node} (h : LeaseInvariant P a)
    (hs : LeaseStepKeepGrantorRows m P a μ a') : LeaseInvariant P a' := by
  cases hs with
  | step _ _ hs1 => exact leaseInvariant_step hM h hs1
  | restartEmpty n hkl hsurv =>
    exact leaseInvariant_restartKeepGrantorRows h (invariant_restartEmpty h.core n hkl hsurv) hkl rfl rfl
      (fun _ e => restartEmpty_inc_other e) (fun _ e => restartEmpty_log_other e) rfl
      (fun _ e => restartEmpty_commit_other e)
  | restartKeep n hkl =>
    exact leaseInvariant_restartKeepGrantorRows h (invariant_restartKeep h.core n hkl) hkl rfl rfl
      (fun _ _ => rfl) (fun _ _ => rfl) rfl (fun _ e => restartKeep_commit_other e)
  | restartPartialKeep n k hkl hk hkeep =>
    exact leaseInvariant_restartKeepGrantorRows h (invariant_restartPartialKeep h.core n k hkl hk hkeep)
      hkl rfl rfl (fun _ _ => rfl) (fun _ e => restartPartialKeep_log_other e) rfl
      (fun _ e => restartKeep_commit_other e)
  | restartPartialFresh n k hkl hk hfresh hsurv =>
    exact leaseInvariant_restartKeepGrantorRows h
      (invariant_restartPartialFresh h.core n k hkl hsurv hk hfresh) hkl rfl rfl
      (fun _ e => restartEmpty_inc_other e) (fun _ e => restartPartialFresh_log_other e) rfl
      (fun _ e => restartEmpty_commit_other e)

/-- **Clearing the grantor rows at a restart is not needed for `NoStaleRead`.** With
`margin ≥ 2 · drift`, every state reachable when restarts keep the restarted node's
primary leases, acknowledgement times and echoes satisfies `NoStaleRead`. -/
theorem noStaleRead_keepGrantorRows {P : LeaseParams} (hMargin : 2 * P.drift ≤ P.margin) {m : Nat}
    {i : Node} {a : LeaseState Node}
    (hReachable : (leaseTransitionSystemKeepGrantorRows m P).CanReach (leaseInit i) a) :
    NoStaleRead P a :=
  let ⟨_, run⟩ := hReachable
  leaseInvariant_noStaleRead hMargin
    (LTS.mtrInv_of_trInv (p := LeaseInvariant P)
      (fun _ _ _ hs h => leaseInvariant_stepKeepGrantorRows hMargin h hs) _ _ _ run
      (leaseInvariant_init P i))

end SyncReplication
