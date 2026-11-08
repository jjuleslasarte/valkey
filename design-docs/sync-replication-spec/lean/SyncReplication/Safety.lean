import SyncReplication.Preserve

/-! # Main theorem

Every reachable state satisfies Safety, with EligibleHoldsCommitted over authoritative nodes, for EVERY
MinSync `m`, any node type, unbounded logs, versions, incarnations and restarts. -/

open Cslib

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-- Safety for every min-sync-replicas value `m`.

In prose: in every state reachable from `init i`, every authoritative node holds the whole committed history,
and no node has committed an entry that differs from it. This holds for any number
of nodes, log length, configuration changes and restarts, provided each restart
without data leaves some other authoritative node with its data. -/
theorem safety {m : Nat} {i : Node} {s : State Node} (h : Reachable m i s) : Safety s :=
  invariant_safety (invariant_reachable h)

/-- What MinSync >= 1 adds: when the current primary commits, an eligible replica with a
matching incarnation counts toward the commit, so after the commit the history is on
at least two distinct authoritative nodes, the primary and that replica. -/
theorem commit_two_copies {m : Nat} (hm : 1 ≤ m) {i : Node} {s : State Node}
    (h : Reachable m i s) {p : Node} (hp : ThinksPrimary s p) (hpp : p = s.cfg.primary)
    (hw : Writable m s p) (hlen : s.commit p < (s.log p).length)
    (hcap : ∀ r, s.sync p r = true → s.commit p < s.acked p r) :
    ∃ e, e ≠ p ∧ IsAuthoritative (commitNext s p) e ∧ IsAuthoritative (commitNext s p) p ∧
      (commitNext s p).hist <+: (commitNext s p).log e ∧ (commitNext s p).hist <+: (commitNext s p).log p := by
  have hi := invariant_reachable h
  have hs' := (safety (h.stepR (Step.commit s p hp hw hlen hcap))).1
  obtain ⟨r, h1, h2, h3⟩ : (syncEligible s p).Nonempty :=
    Set.one_le_encard_iff_nonempty.mp (le_trans (by exact_mod_cast hm) hw)
  subst hpp
  rw [hi.primKnows] at h2 h3
  have hrp : r ≠ s.cfg.primary := by intro e; rw [e, hi.noSelfSync] at h1; exact absurd h1 (by decide)
  have har : IsAuthoritative (commitNext s s.cfg.primary) r := ⟨Or.inl h2, h3⟩
  have hap : IsAuthoritative (commitNext s s.cfg.primary) s.cfg.primary := by
    refine ⟨Or.inr rfl, ?_⟩
    have := hp.2; rw [hi.primKnows] at this; exact this
  exact ⟨r, hrp, har, hap, hs' r har, hs' _ hap⟩

/-! ## Inherited entries commit first

AppendWrite does not wait for a new primary to commit its inherited log. These lemmas
say why that is safe for the commit order: a node's commit point moves past the end of
its inherited log only one offset at a time, so it reaches that end exactly before it
commits anything after it. -/

/-- One step either leaves `p`'s commit point within its inherited log, or keeps the
inherited end and advances the commit point by at most one. -/
theorem commit_step_le {m : Nat} {s s' : State Node} {μ : Action Node} (hs : Step m s μ s')
    (p : Node) :
    s'.commit p ≤ s'.inheritedEnd p ∨
      (s'.inheritedEnd p = s.inheritedEnd p ∧ s'.commit p ≤ s.commit p + 1) := by
  cases hs <;>
    simp only [appendWrite, replicate, ack, commitNext, count, uncount, makeEligible,
      makeIneligible, learn, takeover, resync, restartEmpty, restartKeep, restartPartialKeep,
      restartPartialFresh, update] <;>
    (try split_ifs) <;> (try subst_vars) <;> (try simp only [true_and]) <;> omega

/-- Along any run that ends with `p` committed past its inherited log, either `p` was
already past it at the start, with the same inherited end, or some state of the run has
`p`'s commit point exactly at the final inherited end. -/
theorem commit_crosses_inheritedEnd {m : Nat} {s t : State Node} {μs : List (Action Node)}
    (h : (lts m).MTr s μs t) (p : Node) :
    t.commit p ≤ t.inheritedEnd p ∨
      (∃ u, (lts m).CanReach s u ∧ (lts m).CanReach u t ∧
        u.commit p = u.inheritedEnd p ∧ u.inheritedEnd p = t.inheritedEnd p) ∨
      (s.inheritedEnd p < s.commit p ∧ s.inheritedEnd p = t.inheritedEnd p) := by
  induction h with
  | refl =>
    exact (le_or_gt _ _).elim Or.inl (fun hlt => Or.inr (Or.inr ⟨hlt, rfl⟩))
  | @stepL s₀ μ s₁ μs' t hs hrun ih =>
    rcases ih with h1 | ⟨u, ⟨l1, r1⟩, r2, hu, he⟩ | ⟨hlt, he⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨u, ⟨μ :: l1, .stepL hs r1⟩, r2, hu, he⟩)
    · rcases commit_step_le hs p with h0 | ⟨hi, hc⟩
      · omega
      · by_cases hs0 : s₀.inheritedEnd p < s₀.commit p
        · exact Or.inr (Or.inr ⟨hs0, hi ▸ he⟩)
        · exact Or.inr (Or.inl ⟨s₀, LTS.CanReach.refl _ _, ⟨_, .stepL hs hrun⟩, by omega,
            hi ▸ he⟩)

/-- Inherited entries commit first. In every reachable state where `p` has committed past
the end of its inherited log, an earlier reachable state had `p`'s commit point exactly at
that end, with the same inherited end: `p` committed every inherited offset before any
offset after them. This is why AppendWrite needs no guard that the primary has committed
its inherited log.

Limits. It is about offsets, not about which writes occupy them: it does not say that a
write appended before reconciling lands above the inherited end. It does whenever the
node's log is at least as long as its inherited end; a deposed node whose log a Resync
truncated below its inherited end is the case not covered. -/
theorem committed_inherited_first {m : Nat} {i : Node} {t : State Node} (ht : Reachable m i t)
    (p : Node) (hpast : t.inheritedEnd p < t.commit p) :
    ∃ u, Reachable m i u ∧ (lts m).CanReach u t ∧
      u.commit p = t.inheritedEnd p ∧ u.inheritedEnd p = t.inheritedEnd p := by
  obtain ⟨_, run⟩ := ht
  rcases commit_crosses_inheritedEnd run p with h1 | ⟨u, hsu, hut, hu, he⟩ | ⟨hlt, _⟩
  · omega
  · exact ⟨u, hsu, hut, hu ▸ he, he⟩
  · simp [init] at hlt

end SyncReplication
