import SyncReplication.InstantLeases

/-!
# A restart need not reset the node's committed view

A restart starts the restarted node's committed view at 0 (`leaseRestart`), because a
real node keeps it in memory. This file shows that the reset is not what keeps reads
safe after a restart with data. The read rule is: a replica serves a linearizable read
only when its committed view covers its whole log (`ReplCanRead`), and the view only
ever rises to its primary's committed offset (`recvData`, `deliverData`). So a kept view
never covers an entry that has not committed, whatever the node restored, and every
entry past it stays dirty.

`LeaseStepRestartKeepsView` is `LeaseStep` plus the four restarts with the restarted
node's committed view kept, capped at the length of the log it restores. RestartKeep
restores the whole log, so there the view is kept unchanged. Everything else is
`leaseRestart`'s, including the applied offset capped at the restored log.
`noStaleRead_restartKeepsView` proves `NoStaleRead` in every state it reaches. The
committed-view conjuncts hold because the restored log is a prefix of the old one, and no
other conjunct of the lease invariant reads the view. (Counting the restored log as
committed is not safe: `restartCountsLoaded_stale`.)
-/

open Cslib

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-- `leaseRestart`, except that `n` keeps its committed view, capped at the length of the
log it restores. -/
def leaseRestartKeepView (a : LeaseState Node) (n : Node) (c : State Node) : LeaseState Node :=
  { leaseRestart a n c with
    committedView := update a.committedView n (min (a.committedView n) (c.log n).length) }

/-- `LeaseStep`, plus the restarts that keep the restarted node's committed view. -/
inductive LeaseStepRestartKeepsView (m : Nat) (P : LeaseParams) :
    LeaseState Node → LeaseAction Node → LeaseState Node → Prop
  /-- Every step of the lease layer. -/
  | step (a μ a') (hs : LeaseStep m P a μ a') : LeaseStepRestartKeepsView m P a μ a'
  /-- RestartEmpty, with its guards; the kept view is capped at 0. -/
  | restartEmpty (a n) : (hKnowsLatest : KnowsLatest a.core n) →
      (hSurvivor : ∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      LeaseStepRestartKeepsView m P a (.restartEmpty n) (leaseRestartKeepView a n (restartEmpty a.core n))
  /-- RestartKeep, with its guard; the view is kept unchanged. -/
  | restartKeep (a n) : (hKnowsLatest : KnowsLatest a.core n) →
      LeaseStepRestartKeepsView m P a (.restartKeep n) (leaseRestartKeepView a n (restartKeep a.core n))
  /-- RestartPartial keeping the incarnation, with its guards; the view is capped at `k`. -/
  | restartPartialKeep (a n k) : (hKnowsLatest : KnowsLatest a.core n) →
      (hFileShorter : k < (a.core.log n).length) → (hCoversAcks : a.core.ackHigh n ≤ k) →
      LeaseStepRestartKeepsView m P a (.restartPartial n k)
        (leaseRestartKeepView a n (restartPartialKeep a.core n k))
  /-- RestartPartial taking a new incarnation, with its guards; the view is capped at `k`. -/
  | restartPartialFresh (a n k) : (hKnowsLatest : KnowsLatest a.core n) →
      (hFileShorter : k < (a.core.log n).length) → (hMissesAcks : k < a.core.ackHigh n) →
      (hSurvivor : ∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      LeaseStepRestartKeepsView m P a (.restartPartial n k)
        (leaseRestartKeepView a n (restartPartialFresh a.core n k))

/-- The weakened lease layer as a labelled transition system. -/
def leaseTransitionSystemRestartKeepsView (m : Nat) (P : LeaseParams) :
    LTS (LeaseState Node) (LeaseAction Node) where
  Tr := LeaseStepRestartKeepsView m P

/-- The lease invariant does not read the committed view except in its two committed-view
conjuncts, so it survives replacing the view by one that satisfies them. -/
theorem LeaseInvariant.withCommittedView {P : LeaseParams} {a : LeaseState Node}
    (h : LeaseInvariant P a) (v : Node → Nat)
    (hCV : ∀ x, v x ≤ (a.core.log x).length)
    (hCH : ∀ x, v x ≤ a.core.hist.length ∧ (a.core.log x).take (v x) <+: a.core.hist) :
    LeaseInvariant P { a with committedView := v } :=
  { h with committedViewLen := hCV, committedViewHist := hCH,
           drop := ⟨h.drop.1, h.drop.2, h.drop.3, h.drop.4⟩ }

/-- After a restart that leaves `n` a prefix of its log, `n`'s kept view, capped at that
prefix, still satisfies the committed-view conjuncts. -/
theorem committedView_keep {P : LeaseParams} {a : LeaseState Node} (h : LeaseInvariant P a)
    {c : State Node} (n : Node)
    (hlog : ∀ x, x ≠ n → c.log x = a.core.log x) (hhist : c.hist = a.core.hist)
    (hpre : c.log n <+: a.core.log n) :
    (∀ x, update a.committedView n (min (a.committedView n) (c.log n).length) x ≤ (c.log x).length) ∧
    (∀ x, update a.committedView n (min (a.committedView n) (c.log n).length) x ≤ c.hist.length ∧
      (c.log x).take (update a.committedView n (min (a.committedView n) (c.log n).length) x) <+: c.hist) := by
  rw [hhist]
  refine ⟨fun x => ?_, fun x => ?_⟩ <;> by_cases e : x = n
  · subst e; rw [update_self]; exact Nat.min_le_right _ _
  · rw [update_of_ne _ _ e, hlog x e]; exact h.committedViewLen x
  · subst e; rw [update_self]
    refine ⟨Nat.le_trans (Nat.min_le_left _ _) (h.committedViewHist x).1, ?_⟩
    rw [prefix_take_eq hpre (Nat.min_le_right _ _)]
    exact take_mono_prefix (Nat.min_le_left _ _) (h.committedViewHist x).2
  · rw [update_of_ne _ _ e, hlog x e]; exact h.committedViewHist x

/-- A restart with the view kept preserves the lease invariant. -/
theorem leaseInvariant_restartKeepView {P : LeaseParams} {a : LeaseState Node} {n : Node}
    {c : State Node} (h : LeaseInvariant P a) (h' : LeaseInvariant P (leaseRestart a n c))
    (hlog : ∀ x, x ≠ n → c.log x = a.core.log x) (hhist : c.hist = a.core.hist)
    (hpre : c.log n <+: a.core.log n) :
    LeaseInvariant P (leaseRestartKeepView a n c) :=
  let hv := committedView_keep h n hlog hhist hpre
  h'.withCommittedView _ hv.1 hv.2

/-- Every step of the variant preserves the lease invariant of the atomic model's view. -/
theorem leaseInvariant_stepRestartKeepsView {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {m : Nat}
    {a a' : LeaseState Node} {μ : LeaseAction Node} {L : Node → Cfg Node} (hP : PromSim a.core L)
    (h : LeaseInvariant P (leaseSim a L)) (hs : LeaseStepRestartKeepsView m P a μ a') :
    ∃ L', PromSim a'.core L' ∧ LeaseInvariant P (leaseSim a' L') := by
  have hi : Invariant (simState a.core L) := h.core
  cases hs with
  | step _ _ hs1 => exact leaseInvariant_stepN hM hP h hs1
  | restartEmpty n hkl hsurv =>
    have hkl' := hP.knows hi hkl
    obtain ⟨L', hP', hS | ⟨_, _, hμ⟩⟩ := hP.step hi (Step.restartEmpty (m := m) a.core n hkl hsurv)
    · have e := hS.restartEmpty_inv
      have := leaseInvariant_restartKeepView h (leaseInvariant_restartEmpty h hkl' hsurv)
        (fun _ e => restartEmpty_log_other e) rfl (by simp [restartEmpty])
      have heq : leaseRestartKeepView (leaseSim a L) n (restartEmpty (leaseSim a L).core n) =
          leaseSim (leaseRestartKeepView a n (restartEmpty a.core n)) L' := by
        simp only [leaseRestartKeepView, leaseRestart, leaseSim]; rw [← e]; rfl
      exact ⟨L', hP', heq ▸ this⟩
    · cases hμ
  | restartKeep n hkl =>
    have hkl' := hP.knows hi hkl
    obtain ⟨L', hP', hS | ⟨_, _, hμ⟩⟩ := hP.step hi (Step.restartKeep (m := m) a.core n hkl)
    · have e := hS.restartKeep_inv
      have := leaseInvariant_restartKeepView h (leaseInvariant_restartKeep h hkl')
        (fun _ _ => rfl) rfl (List.prefix_refl _)
      have heq : leaseRestartKeepView (leaseSim a L) n (restartKeep (leaseSim a L).core n) =
          leaseSim (leaseRestartKeepView a n (restartKeep a.core n)) L' := by
        simp only [leaseRestartKeepView, leaseRestart, leaseSim]; rw [← e]; rfl
      exact ⟨L', hP', heq ▸ this⟩
    · cases hμ
  | restartPartialKeep n k hkl hk hkeep =>
    have hkl' := hP.knows hi hkl
    obtain ⟨L', hP', hS | ⟨_, _, hμ⟩⟩ := hP.step hi (Step.restartPartialKeep (m := m) a.core n k hkl hk hkeep)
    · rcases hS.restartPartial_inv with e | e
      · have := leaseInvariant_restartKeepView h (leaseInvariant_restartPartialKeep h hkl' hk hkeep)
          (fun _ e => restartPartialKeep_log_other e) rfl
          (by simp [restartPartialKeep, List.take_prefix])
        have heq : leaseRestartKeepView (leaseSim a L) n (restartPartialKeep (leaseSim a L).core n k) =
            leaseSim (leaseRestartKeepView a n (restartPartialKeep a.core n k)) L' := by
          simp only [leaseRestartKeepView, leaseRestart, leaseSim]; rw [← e]; rfl
        exact ⟨L', hP', heq ▸ this⟩
      · have := congrArg (fun x => x.incarnation n) e
        simp [simState, restartPartialKeep, restartKeep, restartPartialFresh, restartEmpty] at this
    · cases hμ
  | restartPartialFresh n k hkl hk hfresh hsurv =>
    have hkl' := hP.knows hi hkl
    obtain ⟨L', hP', hS | ⟨_, _, hμ⟩⟩ :=
      hP.step hi (Step.restartPartialFresh (m := m) a.core n k hkl hk hfresh hsurv)
    · rcases hS.restartPartial_inv with e | e
      · have := congrArg (fun x => x.incarnation n) e
        simp [simState, restartPartialKeep, restartKeep, restartPartialFresh, restartEmpty] at this
      · have := leaseInvariant_restartKeepView h (leaseInvariant_restartPartialFresh h hkl' hk hfresh hsurv)
          (fun _ e => restartPartialFresh_log_other e) rfl
          (by simp [restartPartialFresh, restartEmpty, List.take_prefix])
        have heq : leaseRestartKeepView (leaseSim a L) n (restartPartialFresh (leaseSim a L).core n k) =
            leaseSim (leaseRestartKeepView a n (restartPartialFresh a.core n k)) L' := by
          simp only [leaseRestartKeepView, leaseRestart, leaseSim]; rw [← e]; rfl
        exact ⟨L', hP', heq ▸ this⟩
    · cases hμ

/-- **Resetting the committed view at a restart is not needed for `NoStaleRead`.** With
`margin ≥ 2 · drift`, every state reachable when restarts keep the restarted node's
committed view (capped at the restored log) satisfies `NoStaleRead`. -/
theorem noStaleRead_restartKeepsView {P : LeaseParams} (hMargin : 2 * P.drift ≤ P.margin) {m : Nat}
    {i : Node} {a : LeaseState Node}
    (hReachable : (leaseTransitionSystemRestartKeepsView m P).CanReach (leaseInit i) a) :
    NoStaleRead P a := by
  obtain ⟨_, run⟩ := hReachable
  obtain ⟨L, hP, h⟩ := LTS.mtrInv_of_trInv (p := fun a => ∃ L, PromSim a.core L ∧ LeaseInvariant P (leaseSim a L))
      (fun _ _ _ hs ⟨_, hP, h⟩ => leaseInvariant_stepRestartKeepsView hMargin hP h hs) _ _ _ run
      ⟨(init i).localCfg, promSim_init i, leaseInvariant_init P i⟩
  have hn := leaseInvariant_noStaleRead hMargin h
  exact ⟨fun p hp => hn.1 p (hP.primCanRead hp), fun r hr => hn.2 r (hP.replCanRead hr)⟩

end SyncReplication
