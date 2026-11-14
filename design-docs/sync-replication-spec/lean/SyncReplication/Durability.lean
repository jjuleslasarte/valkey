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
  /-- The replication-message invariant. -/
  rcore : RInvariant a.core
  held  : HeldInvariant a.core a.held
  acked : AckedDurable a

/-- Every node's replication ID has been handed out: `RInvariant.ids`. -/
theorem ReplyInvariant.replIdsIssued {a : ReplyState Node} (h : ReplyInvariant a) : ReplIdsIssued a.core :=
  h.rcore.ids

theorem replyInvariant_init (i : Node) : ReplyInvariant (replyInit i) where
  core := invariant_init i
  rcore := rInvariant_init i
  held := by intro x hx; simp [replyInit] at hx
  acked := by intro x hx; simp [replyInit] at hx

/-- What a replication step other than a restart does to the parts the reply
invariants read. -/
theorem step_facts {s s' : State Node} (h : Invariant s) (hr : RInvariant s) (ht : ReplIdsIssued s) {m : Nat} {μ : Action Node}
    (hs : Step m s μ s') (hμ : μ.isRestart = false) :
    s.hist <+: s'.hist ∧ s.usedIds ⊆ s'.usedIds ∧ ReplIdsIssued s' ∧
    ∀ x t, t ∈ s.usedIds → ThinksPrimary s' x → s'.replId x = t →
      ThinksPrimary s x ∧ s.replId x = t ∧ s.log x <+: s'.log x := by
  cases hs with
  | append p _ _ =>
    exact ⟨List.prefix_refl _, Finset.Subset.refl _, ht, fun x _ _ hp e =>
      ⟨hp, e, grow_upd s.log p _ x⟩⟩
  | commit p _ _ _ _ =>
    refine ⟨?_, Finset.Subset.refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
    show s.hist <+: (if s.commit p = s.hist.length then _ else _)
    split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  | removeFromSyncSet p r _ _ _ =>
    exact ⟨List.prefix_refl _, Finset.Subset.refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | addToSyncSet p r _ _ _ _ _ =>
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
  | resync r hne _ _ =>
    refine ⟨List.prefix_refl _, Finset.Subset.refl _, ?_, ?_⟩
    · -- the resynced replica takes its primary's replication ID, a used one
      intro x; show update s.replId r (s.replId (primaryOf s r)) x ∈ s.usedIds
      by_cases hxr : x = r
      · subst hxr; rw [update_self]; exact ht _
      · rw [update_of_ne _ _ hxr]; exact ht x
    intro x _ _ hx e
    have hxr : x ≠ r := by
      intro hxr; subst hxr; exact hne hx.1
    refine ⟨hx, ?_, ?_⟩
    · change update s.replId r _ x = _ at e; rwa [update_of_ne _ _ hxr] at e
    · show s.log x <+: update s.log r _ x
      rw [update_of_ne _ _ hxr]
  | restartEmpty n hkl _ => exact absurd hμ (by simp [Action.isRestart])
  | restartKeep n _ => exact absurd hμ (by simp [Action.isRestart])
  | restartPartialKeep n k _ _ _ => exact absurd hμ (by simp [Action.isRestart])
  | restartPartialFresh n k _ _ _ _ => exact absurd hμ (by simp [Action.isRestart])
  | psync r _ _ _ =>
    exact ⟨List.prefix_refl _, Finset.Subset.refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | sendData p r k _ _ =>
    exact ⟨List.prefix_refl _, Finset.Subset.refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | deliverData p r g v rid hin hcur hf hfol =>
    -- the replica takes the ID the entry was streamed under, a used one; it follows
    -- another node, so it does not think it is primary
    obtain ⟨hpr, -, hrid⟩ := hr.deliver_prefix hin hcur hf
    refine ⟨List.prefix_refl _, Finset.Subset.refl _, ?_, ?_⟩
    · intro x; show update s.replId r rid x ∈ s.usedIds
      by_cases hxr : x = r
      · subst hxr; rw [update_self]; exact hrid
      · rw [update_of_ne _ _ hxr]; exact ht x
    · intro x _ _ hx e
      have hxr : x ≠ r := by
        intro hxr; subst hxr; exact hpr (hfol.symm.trans hx.1)
      refine ⟨hx, ?_, ?_⟩
      · change update s.replId r rid x = _ at e; rwa [update_of_ne _ _ hxr] at e
      · show s.log x <+: update s.log r _ x
        rw [update_of_ne _ _ hxr]
  | sendAck r _ =>
    exact ⟨List.prefix_refl _, Finset.Subset.refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | deliverAck r p g off k _ _ _ _ =>
    exact ⟨List.prefix_refl _, Finset.Subset.refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩
  | dropMsg msg _ =>
    exact ⟨List.prefix_refl _, Finset.Subset.refl _, ht, fun x _ _ hp e => ⟨hp, e, List.prefix_refl _⟩⟩

theorem replyInvariant_core {a : ReplyState Node} {c : State Node} (h : ReplyInvariant a) {m : Nat} {μ : Action Node}
    (hs : Step m a.core μ c) (hμ : μ.isRestart = false) :
    ReplyInvariant ⟨c, a.held, a.acknowledged⟩ := by
  obtain ⟨hh, hv, ht', hx⟩ := step_facts h.core h.rcore h.replIdsIssued hs hμ
  obtain ⟨hc, hrc⟩ := invariants_step h.core h.rcore hs
  refine ⟨hc, hrc, ?_, ?_⟩
  · intro x hm
    obtain ⟨hb, hf⟩ := h.held x hm
    refine ⟨hv hb, fun hf' => ?_⟩
    obtain ⟨htp, hte, hpre⟩ := hx x.primary x.replId hb hf'.1 hf'.2
    obtain ⟨h1, h2, h3⟩ := hf ⟨htp, hte⟩
    exact ⟨h1, Nat.le_trans h2 hpre.length_le, by rw [getD_prefix hpre (by omega)]; exact h3⟩
  · intro x hm
    obtain ⟨h1, h2, h3⟩ := h.acked x hm
    exact ⟨h1, Nat.le_trans h2 hh.length_le, by rw [getD_prefix hh (by omega)]; exact h3⟩

theorem replyInvariant_write {a : ReplyState Node} (h : ReplyInvariant a) {p : Node} (hp : ThinksPrimary a.core p) :
    ReplyInvariant (write a p) := by
  have hlog : ∀ x, a.core.log x <+: (appendWrite a.core p).log x := grow_upd a.core.log p _
  refine ⟨invariant_append h.core p, h.rcore.append hp, ?_, h.acked⟩
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
  refine ⟨h.core, h.rcore, fun y hy => h.held y (List.mem_of_mem_erase hy), ?_⟩
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
  ⟨h.core, h.rcore, fun y hy => h.held y (List.mem_of_mem_erase hy), h.acked⟩

/-- A restart of `n` keeps the layer invariant once `n`'s held replies are dropped: the
surviving replies are on other nodes, whose logs, primaryship and replication IDs it leaves alone,
and it changes neither the history nor the used replication IDs. -/
theorem replyInvariant_restart {a : ReplyState Node} {c : State Node} (h : ReplyInvariant a) (hc : Invariant c ∧ RInvariant c) (n : Node)
    (hhist : c.hist = a.core.hist) (hids : a.core.usedIds ⊆ c.usedIds)
    (hreplId : ∀ x, x ≠ n → c.replId x = a.core.replId x) (hn : c.replId n ∈ c.usedIds)
    (hlog : ∀ x, x ≠ n → c.log x = a.core.log x)
    (htp : ∀ x, x ≠ n → ThinksPrimary c x → ThinksPrimary a.core x) :
    ReplyInvariant ⟨c, dropHeld a.held n, a.acknowledged⟩ := by
  refine ⟨hc.1, hc.2, ?_, ?_⟩
  · intro x hx
    obtain ⟨hm, hxn⟩ := List.mem_filter.mp hx
    have hxn' : x.primary ≠ n := by simpa using hxn
    obtain ⟨hb, hf⟩ := h.held x hm
    refine ⟨hids hb, fun hf' => ?_⟩
    have : ReplyFenced a.core x := ⟨htp x.primary hxn' hf'.1, by rw [← hreplId _ hxn']; exact hf'.2⟩
    obtain ⟨h1, h2, h3⟩ := hf this
    rw [hlog x.primary hxn']; exact ⟨h1, h2, h3⟩
  · intro x hx; show _ ∧ x.1 ≤ c.hist.length ∧ c.hist.getD _ 0 = _; rw [hhist]; exact h.acked x hx

/-- `p` takes a fresh ID, its log, secondary ID and connections unchanged: the fresh ID
names `p`'s log, and nothing read before mentions it. -/
theorem RInvariant.newId {s : State Node} (h : RInvariant s) (p : Node) :
    RInvariant { s with replId := update s.replId p (freshId s), usedIds := insert (freshId s) s.usedIds } := by
  have hne : ∀ x, x ≠ p → update s.replId p (freshId s) x = s.replId x := fun x hx => update_of_ne _ _ hx
  have hdata := dataOn_of_rnet (s := s)
    (s' := { s with replId := update s.replId p (freshId s), usedIds := insert (freshId s) s.usedIds }) rfl
  have hpend := pend_of_rnet (s := s)
    (s' := { s with replId := update s.replId p (freshId s), usedIds := insert (freshId s) s.usedIds }) rfl
  exact {
  ackedLeMax := h.ackedLeMax
  ids := fun x => by
    show update s.replId p (freshId s) x ∈ insert (freshId s) s.usedIds
    by_cases hx : x = p
    · subst hx; rw [update_self]; exact Finset.mem_insert_self _ _
    · rw [hne x hx]; exact Finset.mem_insert_of_mem (h.ids x)
  secIds := fun x t o hx => Finset.mem_insert_of_mem (h.secIds x t o hx)
  msgIds := fun m hm hd => Finset.mem_insert_of_mem (h.msgIds m hm hd)
  uniqPrim := by
    intro x y hx hy he
    change update s.replId p (freshId s) x = update s.replId p (freshId s) y at he
    by_cases hxp : x = p
    · by_cases hyp : y = p
      · rw [hxp, hyp]
      · subst hxp; rw [update_self, hne y hyp] at he; exact absurd (he ▸ h.ids y) (freshId_not_mem s)
    · by_cases hyp : y = p
      · subst hyp; rw [update_self, hne x hxp] at he; exact absurd (he ▸ h.ids x) (freshId_not_mem s)
      · rw [hne x hxp, hne y hyp] at he; exact h.uniqPrim x y hx hy he
  genLe := h.genLe
  streamGen := h.streamGen
  stream := fun q r k g hs hgg => by
    simp only [hpend]; exact h.stream q r k g hs hgg
  dataStream := h.dataStream
  ackOk := h.ackOk
  hist := by
    obtain ⟨H, hH⟩ := h.hist
    obtain ⟨hsame, hnew⟩ := fresh_hist h (H := H) (s.log p)
    refine ⟨update H (freshId s) (s.log p), {
      logH := fun x => ?_
      ownH := fun x hx => ?_
      secH := fun x t o hx => ?_
      streamH := fun q r k g hs hgg i hi => ?_ }⟩
    · show s.log x <+: update H (freshId s) (s.log p) (update s.replId p (freshId s) x)
      by_cases hx : x = p
      · subst hx; rw [update_self, hnew]
      · rw [hne x hx, hsame _ (h.ids x)]; exact hH.logH x
    · show update H (freshId s) (s.log p) (update s.replId p (freshId s) x) = s.log x
      by_cases hxp : x = p
      · subst hxp; rw [update_self, hnew]
      · rw [hne x hxp, hsame _ (h.ids x)]; exact hH.ownH x hx
    · show o ≤ (s.log x).length ∧ (s.log x).take o = (update H (freshId s) (s.log p) t).take o
      rw [hsame _ (h.secIds x t o hx)]; exact hH.secH x t o hx
    · simp only [hdata, hpend] at hi ⊢
      have hmem : (dataOn s q r g)[i] ∈ s.rnet := (List.mem_filter.1 (List.getElem_mem hi)).1
      have hdown : ((dataOn s q r g)[i]).down = true := by
        have := (List.mem_filter.1 (List.getElem_mem hi)).2
        simp only [decide_eq_true_eq] at this
        simp [RMsg.down, this]
      show _ <+: update H (freshId s) (s.log p) _
      rw [hsame _ (h.msgIds _ hmem hdown)]; exact hH.streamH q r k g hs hgg i hi }

/-- A fresh replication ID without a takeover: replies held by `p` stop passing the
fence (they can only be aborted), every other reply is unchanged. -/
theorem replyInvariant_newId {a : ReplyState Node} (h : ReplyInvariant a) (p : Node) :
    ReplyInvariant (newId a p) := by
  refine ⟨h.core.replId_frame _ _, h.rcore.newId p, ?_, h.acked⟩
  intro x hm
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
  | write p hp _ => exact replyInvariant_write h hp
  | release x hm hc hf => exact replyInvariant_release h x hm hc hf
  | abort x _ _ => exact replyInvariant_abort h x
  | newId p => exact replyInvariant_newId h p
  | restartEmpty n hkl hsurv =>
    exact replyInvariant_restart h (invariants_step h.core h.rcore (Step.restartEmpty (m := m) _ n hkl hsurv)) n rfl (Finset.subset_insert _ _) (fun _ e => update_of_ne _ _ e) (by show update _ n _ n ∈ insert _ _; rw [update_self]; exact Finset.mem_insert_self _ _)
      (fun _ e => restartEmpty_log_other e)
      (fun _ _ hx => (restartEmpty_thinksPrimary (h.core.localCfgEq n hkl) (h.core.incLe n) hx).2)
  | restartKeep n hkl =>
    exact replyInvariant_restart h (invariants_step h.core h.rcore (Step.restartKeep (m := m) _ n hkl)) n rfl (restartIds_sub _ _ _) (fun _ e => restartIds_other _ _ _ e) (restartIds_mem _ _ _ (h.replIdsIssued n))
      (fun _ _ => rfl) (fun _ _ hx => hx)
  | restartPartialKeep n k hkl hk hkeep =>
    exact replyInvariant_restart h (invariants_step h.core h.rcore (Step.restartPartialKeep (m := m) _ n k hkl hk hkeep)) n
      rfl (restartIds_sub _ _ _) (fun _ e => restartIds_other _ _ _ e) (restartIds_mem _ _ _ (h.replIdsIssued n)) (fun _ e => restartPartialKeep_log_other e) (fun _ _ hx => hx)
  | restartPartialFresh n k hkl hk hfresh hsurv =>
    exact replyInvariant_restart h (invariants_step h.core h.rcore (Step.restartPartialFresh (m := m) _ n k hkl hk hfresh hsurv)) n
      rfl (restartIds_sub _ _ _) (fun _ e => restartIds_other _ _ _ e) (restartIds_mem _ _ _ (h.replIdsIssued n)) (fun _ e => restartPartialFresh_log_other e)
      (fun _ _ hx => (restartPartialFresh_thinksPrimary (h.core.localCfgEq n hkl) (h.core.incLe n) hx).2)

theorem replyInvariant_reachable {i : Node} {a : ReplyState Node} {m : Nat} (h : ReplyReachable m i a) :
    ReplyInvariant a :=
  let ⟨_, run⟩ := h
  LTS.mtrInv_of_trInv (p := ReplyInvariant) (fun _ _ _ hs h => replyInvariant_step h hs) _ _ _ run (replyInvariant_init i)

/-- No acknowledged write is lost, for any number of nodes, log length, configuration
changes and restarts, and EVERY min-sync-replicas value `m`, as long as no restart
without data removes the last authoritative node (survival assumption). -/
theorem ackSafety {i : Node} {a : ReplyState Node} {m : Nat} (hReachable : ReplyReachable m i a) :
    AckedDurable a ∧ Safety a.core :=
  let hi := replyInvariant_reachable hReachable
  ⟨hi.acked, invariant_safety hi.core⟩

/-- Every authoritative node holds every acknowledged write. -/
theorem ackedHeld {i : Node} {a : ReplyState Node} {m : Nat} (hReachable : ReplyReachable m i a) :
    AckedHeld a := by
  obtain ⟨hd, he, _⟩ := ackSafety hReachable
  intro x hx n hn
  obtain ⟨h1, h2, h3⟩ := hd x hx
  have hp := he n hn
  exact ⟨Nat.le_trans h2 hp.length_le, by rw [getD_prefix hp (by omega)]; exact h3⟩

end SyncReplication
