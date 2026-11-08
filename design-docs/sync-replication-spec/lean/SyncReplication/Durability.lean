import SyncReplication.Replies

/-! # No acknowledged write is lost

`ackSafety`: every write released as OK is in the committed history at its offset,
and `ackedHeld`: every authoritative node holds it. For every `min-sync-replicas`,
with node restarts with, without and with stale data, under the survival assumption.
The proof extends the replication invariant with three facts about held replies
(`ReplyInvariant`). -/

open Cslib

namespace SyncReplication


variable {Node : Type} [DecidableEq Node]

theorem getD_prefix {l l' : List Nat} (h : l <+: l') {i : Nat} (hi : i < l.length) :
    l'.getD i 0 = l.getD i 0 := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_take {l : List Nat} {i k : Nat} (hi : i < k) :
    (l.take k).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- Held-reply invariant: a reply whose primaryship is current points at its own
entry in that primary's log. -/
def HeldInvariant (s : State Node) (held : List (Held Node)) : Prop :=
  ∀ x ∈ held, x.replId ∈ s.usedIds ∧
    (ReplyFenced s x → 1 ≤ x.offset ∧ x.offset ≤ (s.log x.primary).length ∧
      (s.log x.primary).getD (x.offset - 1) 0 = x.replId)

/-- Every node's replication ID has been handed out: it is in `usedIds`. A takeover's
fresh ID is therefore different from every ID a node or a held reply already carries. -/
def ReplIdsIssued (s : State Node) : Prop := ∀ n, s.replId n ∈ s.usedIds

structure ReplyInvariant (a : ReplyState Node) : Prop where
  core  : Invariant a.core
  /-- Every node's replication ID has been handed out. -/
  replIdsIssued : ReplIdsIssued a.core
  held  : HeldInvariant a.core a.held
  acked : AckedDurable a

theorem replyInvariant_init (i : Node) : ReplyInvariant (replyInit i) where
  core := invariant_init i
  replIdsIssued := by intro n; simp only [replyInit, init]; split <;> simp
  held := by intro x hx; simp [replyInit] at hx
  acked := by intro x hx; simp [replyInit] at hx

/-- What a replication step other than a restart does to the parts the reply
invariants read. -/
theorem step_facts {s s' : State Node} (h : Invariant s) (ht : ReplIdsIssued s) {m : Nat} {μ : Action Node}
    (hs : Step m s μ s') (hμ : μ.isRestart = false) :
    s.hist <+: s'.hist ∧ s.usedIds ⊆ s'.usedIds ∧ ReplIdsIssued s' ∧
    ∀ x t, t ∈ s.usedIds → ThinksPrimary s' x → s'.replId x = t →
      ThinksPrimary s x ∧ s.replId x = t ∧ s.log x <+: s'.log x := by
  cases hs with
  | append p _ _ =>
    exact ⟨List.prefix_refl _, Finset.Subset.refl _, ht, fun x _ _ hp e =>
      ⟨hp, e, grow_upd s.log p _ x⟩⟩
  | replicate r hne _ _ =>
    refine ⟨List.prefix_refl _, Finset.Subset.refl _, ?_, fun x _ _ hp e => ?_⟩
    · -- the replica adopts its primary's replication ID, which is a used one
      intro x; show update s.replId r (s.replId (primaryOf s r)) x ∈ s.usedIds
      by_cases hxr : x = r
      · subst hxr; rw [update_self]; exact ht _
      · rw [update_of_ne _ _ hxr]; exact ht x
    · -- a node that thinks it is primary is not the adopting replica
      have hxr : x ≠ r := fun hxr => by subst hxr; exact hne hp.1
      refine ⟨hp, ?_, grow_upd s.log r _ x⟩
      change update s.replId r _ x = _ at e; rwa [update_of_ne _ _ hxr] at e
  | ack r _ _ _ =>
    exact ⟨List.prefix_refl _, Finset.Subset.refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | commit p _ _ _ _ =>
    refine ⟨?_, Finset.Subset.refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
    show s.hist <+: (if s.commit p = s.hist.length then _ else _)
    split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  | uncount p r _ _ _ =>
    exact ⟨List.prefix_refl _, Finset.Subset.refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | count p r _ _ _ _ _ =>
    exact ⟨List.prefix_refl _, Finset.Subset.refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | makeEligible p r hp hkl _ _ =>
    refine ⟨List.prefix_refl _, Finset.Subset.refl _, ht, ?_⟩
    intro x _ _ hx e
    refine ⟨?_, e, List.prefix_refl _⟩
    by_cases hxp : x = p
    · subst hxp; exact hp
    · unfold ThinksPrimary at hx ⊢; simpa [makeEligible, update_of_ne _ _ hxp] using hx
  | makeIneligible p r hp hkl _ =>
    refine ⟨List.prefix_refl _, Finset.Subset.refl _, ht, ?_⟩
    intro x _ _ hx e
    refine ⟨?_, e, List.prefix_refl _⟩
    by_cases hxp : x = p
    · subst hxp; exact hp
    · unfold ThinksPrimary at hx ⊢; simpa [makeIneligible, update_of_ne _ _ hxp] using hx
  | learn n hnkl =>
    refine ⟨List.prefix_refl _, Finset.Subset.refl _, ht, ?_⟩
    intro x _ _ hx e
    refine ⟨?_, e, List.prefix_refl _⟩
    by_cases hxn : x = n
    · exfalso; apply hnkl
      have hx' : s.cfg.primary = x := by have := hx.1; simpa [learn, hxn] using this
      unfold KnowsLatest; rw [← hxn, ← hx', h.primKnows]
    · unfold ThinksPrimary at hx ⊢; simpa [learn, update_of_ne _ _ hxn] using hx
  | takeover n _ _ _ _ =>
    refine ⟨List.prefix_refl _, Finset.subset_insert _ _, ?_, ?_⟩
    · intro x
      show update s.replId n (freshId s) x ∈ insert (freshId s) s.usedIds
      by_cases hxn : x = n
      · subst hxn; simp
      · rw [update_of_ne _ _ hxn]; exact Finset.mem_insert_of_mem (ht x)
    · intro x t htv hx e
      by_cases hxn : x = n
      · subst hxn
        have : freshId s = t := by simpa [takeover] using e
        exact absurd (this ▸ htv) (freshId_not_mem s)
      · refine ⟨?_, ?_, List.prefix_refl _⟩
        · unfold ThinksPrimary at hx ⊢; simpa [takeover, update_of_ne _ _ hxn] using hx
        · simpa [takeover, update_of_ne _ _ hxn] using e
  | resync r hne _ _ _ =>
    refine ⟨List.prefix_refl _, Finset.Subset.refl _, ht, ?_⟩
    intro x _ _ hx e
    have hxr : x ≠ r := by
      intro hxr; subst hxr; exact hne hx.1
    refine ⟨hx, e, ?_⟩
    show s.log x <+: update s.log r _ x
    rw [update_of_ne _ _ hxr]
  | restartEmpty n hkl _ =>
    refine ⟨List.prefix_refl _, Finset.Subset.refl _, ht, ?_⟩
    intro x _ _ hx e
    have hxn : x ≠ n := by
      intro c; subst c
      have h2 := hx.2
      change (s.known x).incarnation x = update s.incarnation x (s.incarnation x + 1) x at h2
      rw [h.knownEq x hkl, update_self] at h2; have := h.incLe x; omega
    have hI : (restartEmpty s n).incarnation x = s.incarnation x := update_of_ne _ _ hxn
    refine ⟨⟨hx.1, ?_⟩, e, ?_⟩
    · have h2 := hx.2; rw [hI] at h2; exact h2
    · show s.log x <+: update s.log n [] x
      rw [update_of_ne _ _ hxn]
  | restartKeep n _ =>
    exact ⟨List.prefix_refl _, Finset.Subset.refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | restartPartialKeep n k _ _ _ => exact absurd hμ (by simp [Action.isRestart])
  | restartPartialFresh n k _ _ _ _ => exact absurd hμ (by simp [Action.isRestart])

theorem replyInvariant_core {a : ReplyState Node} {c : State Node} (h : ReplyInvariant a) {m : Nat} {μ : Action Node}
    (hs : Step m a.core μ c) (hμ : μ.isRestart = false) :
    ReplyInvariant ⟨c, a.held, a.acknowledged⟩ := by
  obtain ⟨hh, hv, ht', hx⟩ := step_facts h.core h.replIdsIssued hs hμ
  refine ⟨invariant_step h.core hs, ht', ?_, ?_⟩
  · intro x hm
    obtain ⟨hb, hf⟩ := h.held x hm
    refine ⟨hv hb, fun hf' => ?_⟩
    obtain ⟨htp, hte, hpre⟩ := hx x.primary x.replId hb hf'.1 hf'.2
    obtain ⟨h1, h2, h3⟩ := hf ⟨htp, hte⟩
    exact ⟨h1, Nat.le_trans h2 hpre.length_le, by rw [getD_prefix hpre (by omega)]; exact h3⟩
  · intro x hm
    obtain ⟨h1, h2, h3⟩ := h.acked x hm
    exact ⟨h1, Nat.le_trans h2 hh.length_le, by rw [getD_prefix hh (by omega)]; exact h3⟩

theorem replyInvariant_write {a : ReplyState Node} (h : ReplyInvariant a) (p : Node) : ReplyInvariant (write a p) := by
  have hlog : ∀ x, a.core.log x <+: (appendWrite a.core p).log x := grow_upd a.core.log p _
  refine ⟨invariant_append h.core p, h.replIdsIssued, ?_, h.acked⟩
  intro x hm
  rcases List.mem_cons.mp hm with rfl | hm
  · refine ⟨h.replIdsIssued p, fun _ => ⟨by simp, ?_, ?_⟩⟩
    · simp [write, appendWrite]
    · simp [write, appendWrite, List.getD_eq_getElem?_getD]
  · obtain ⟨hb, hf⟩ := h.held x hm
    refine ⟨hb, fun hf' => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hf hf'
    exact ⟨h1, Nat.le_trans h2 (hlog x.primary).length_le,
      by show ((appendWrite a.core p).log x.primary).getD _ 0 = _
         rw [getD_prefix (hlog x.primary) (by omega)]; exact h3⟩

theorem replyInvariant_release {a : ReplyState Node} (h : ReplyInvariant a) (x : Held Node) (hm : x ∈ a.held)
    (hc : x.offset ≤ a.core.commit x.primary) (hf : ReplyFenced a.core x) : ReplyInvariant (release a x) := by
  refine ⟨h.core, h.replIdsIssued, fun y hy => h.held y (List.mem_of_mem_erase hy), ?_⟩
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · obtain ⟨_, hfx⟩ := h.held x hm
    obtain ⟨h1, _, h3⟩ := hfx hf
    have hhist := h.core.commitWithinHistory x.primary
    have heq := h.core.committedIsHistoryPrefix x.primary
    refine ⟨h1, Nat.le_trans hc hhist, ?_⟩
    show a.core.hist.getD (x.offset - 1) 0 = x.replId
    rw [← getD_take (k := a.core.commit x.primary) (by omega), ← heq, getD_take (by omega)]
    exact h3
  · exact h.acked y hy

theorem replyInvariant_abort {a : ReplyState Node} (h : ReplyInvariant a) (x : Held Node) : ReplyInvariant (abort a x) :=
  ⟨h.core, h.replIdsIssued, fun y hy => h.held y (List.mem_of_mem_erase hy), h.acked⟩

/-- A restart of `n` keeps the layer invariant once `n`'s held replies are dropped: the
surviving replies are on other nodes, whose logs, primaryship and replication IDs it leaves alone,
and it changes neither the history nor the used replication IDs. -/
theorem replyInvariant_restart {a : ReplyState Node} {c : State Node} (h : ReplyInvariant a) (hc : Invariant c) (n : Node)
    (hhist : c.hist = a.core.hist) (hids : c.usedIds = a.core.usedIds) (hreplId : c.replId = a.core.replId)
    (hlog : ∀ x, x ≠ n → c.log x = a.core.log x)
    (htp : ∀ x, x ≠ n → ThinksPrimary c x → ThinksPrimary a.core x) :
    ReplyInvariant ⟨c, dropHeld a.held n, a.acknowledged⟩ := by
  refine ⟨hc, fun x => by rw [hreplId, hids]; exact h.replIdsIssued x, ?_, ?_⟩
  · intro x hx
    obtain ⟨hm, hxn⟩ := List.mem_filter.mp hx
    have hxn' : x.primary ≠ n := by simpa using hxn
    obtain ⟨hb, hf⟩ := h.held x hm
    refine ⟨by rw [hids]; exact hb, fun hf' => ?_⟩
    have : ReplyFenced a.core x := ⟨htp x.primary hxn' hf'.1, by rw [← hreplId]; exact hf'.2⟩
    obtain ⟨h1, h2, h3⟩ := hf this
    rw [hlog x.primary hxn']; exact ⟨h1, h2, h3⟩
  · intro x hx; show _ ∧ x.1 ≤ c.hist.length ∧ c.hist.getD _ 0 = _; rw [hhist]; exact h.acked x hx

/-- A fresh replication ID without a takeover: replies held by `p` stop passing the
fence (they can only be aborted), every other reply is unchanged. -/
theorem replyInvariant_newId {a : ReplyState Node} (h : ReplyInvariant a) (p : Node) :
    ReplyInvariant (newId a p) := by
  refine ⟨h.core.replId_frame _ _, ?_, ?_, h.acked⟩
  · intro x; show update a.core.replId p (freshId a.core) x ∈ insert (freshId a.core) a.core.usedIds
    by_cases hx : x = p
    · subst hx; simp
    · rw [update_of_ne _ _ hx]; exact Finset.mem_insert_of_mem (h.replIdsIssued x)
  · intro x hm
    obtain ⟨hb, hf⟩ := h.held x hm
    refine ⟨Finset.mem_insert_of_mem hb, fun ⟨hp, he⟩ => ?_⟩
    change update a.core.replId p (freshId a.core) x.primary = x.replId at he
    by_cases hx : x.primary = p
    · rw [hx, update_self] at he; exact absurd (he ▸ hb) (freshId_not_mem _)
    · rw [update_of_ne _ _ hx] at he; exact hf ⟨hp, he⟩

theorem replyInvariant_step {a a' : ReplyState Node} (h : ReplyInvariant a) {m : Nat}
    {μ : ReplyAction Node} (hs : ReplyStep m a μ a') : ReplyInvariant a' := by
  cases hs with
  | core _ c hc hμ => exact replyInvariant_core h hc hμ
  | write p _ _ => exact replyInvariant_write h p
  | release x hm hc hf => exact replyInvariant_release h x hm hc hf
  | abort x _ _ => exact replyInvariant_abort h x
  | newId p => exact replyInvariant_newId h p
  | restartEmpty n hkl hsurv =>
    exact replyInvariant_restart h (invariant_step h.core (Step.restartEmpty (m := m) _ n hkl hsurv)) n rfl rfl rfl
      (fun _ e => restartEmpty_log_other e)
      (fun _ _ hx => (restartEmpty_thinksPrimary (h.core.knownEq n hkl) (h.core.incLe n) hx).2)
  | restartKeep n hkl =>
    exact replyInvariant_restart h (invariant_step h.core (Step.restartKeep (m := m) _ n hkl)) n rfl rfl rfl
      (fun _ _ => rfl) (fun _ _ hx => hx)
  | restartPartialKeep n k hkl hk hkeep =>
    exact replyInvariant_restart h (invariant_step h.core (Step.restartPartialKeep (m := m) _ n k hkl hk hkeep)) n
      rfl rfl rfl (fun _ e => restartPartialKeep_log_other e) (fun _ _ hx => hx)
  | restartPartialFresh n k hkl hk hfresh hsurv =>
    exact replyInvariant_restart h (invariant_step h.core (Step.restartPartialFresh (m := m) _ n k hkl hk hfresh hsurv)) n
      rfl rfl rfl (fun _ e => restartPartialFresh_log_other e)
      (fun _ _ hx => (restartPartialFresh_thinksPrimary (h.core.knownEq n hkl) (h.core.incLe n) hx).2)

theorem replyInvariant_reachable {i : Node} {a : ReplyState Node} {m : Nat} (h : ReplyReachable m i a) :
    ReplyInvariant a :=
  let ⟨_, run⟩ := h
  LTS.mtrInv_of_trInv (p := ReplyInvariant) (fun _ _ _ hs h => replyInvariant_step h hs) _ _ _ run (replyInvariant_init i)

/-- No acknowledged write is lost, for any number of nodes, log length, configuration
changes and restarts, and EVERY min-sync-replicas value `m`, as long as no restart
without data removes the last authoritative node (survival assumption). -/
theorem ackSafety {i : Node} {a : ReplyState Node} {m : Nat} (h : ReplyReachable m i a) :
    AckedDurable a ∧ Safety a.core :=
  let hi := replyInvariant_reachable h
  ⟨hi.acked, invariant_safety hi.core⟩

/-- Every authoritative node holds every acknowledged write. -/
theorem ackedHeld {i : Node} {a : ReplyState Node} {m : Nat} (h : ReplyReachable m i a) :
    AckedHeld a := by
  obtain ⟨hd, he, _⟩ := ackSafety h
  intro x hx n hn
  obtain ⟨h1, h2, h3⟩ := hd x hx
  have hp := he n hn
  exact ⟨Nat.le_trans h2 hp.length_le, by rw [getD_prefix hp (by omega)]; exact h3⟩

end SyncReplication
