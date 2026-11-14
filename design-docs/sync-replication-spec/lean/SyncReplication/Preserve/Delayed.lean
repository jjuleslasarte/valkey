import SyncReplication.Preserve.Replication
import SyncReplication.Preserve.Commit
import SyncReplication.Preserve.Config
import SyncReplication.Preserve.Failover
import SyncReplication.Preserve.Restart

/-!
# Delayed replication: the invariant over `Step`

`Invariant` reads no replication message, stream position, connection generation or
replication ID, so every action `Step` shares with `InstantStep` keeps it as before.
Delivering a data message is `replicate` with the message's ID, and delivering an
acknowledgement raises the primary's record to at most what the replica holds of its
log. Both need facts about the messages in flight, which `RInvariant` collects: an ID
names one history (`idHist`), every open stream carries the primary's log to the
replica in order, and every open acknowledgement is real.
-/

open Cslib

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-! ## Frames for `Invariant` -/

/-- `Invariant` reads no replication message, stream, generation or ID. -/
theorem Invariant.net_frame {s : State Node} (h : Invariant s) (t : Node → Nat) (u : Finset Nat)
    (w : Node → Option (Nat × Nat)) (net : List (RMsg Node)) (st : Node → Node → Option (Nat × Nat))
    (g : Node → Node → Nat) (ak : Node → Node → Nat) :
    Invariant { s with replId := t, usedIds := u, replId2 := w, rnet := net, stream := st, rgen := g, acked := ak } where
  toConfigInvariant := ⟨h.localCfgLe, h.localCfgEq, h.primKnows, h.localCfgIncLe⟩
  toReplInvariant := ⟨h.noSelfSync, h.ackedPrim, h.ackedLe, h.ackHolds, h.ackedHigh, h.syncCommit⟩
  toMembershipInvariant := ⟨h.eligibleCounted, h.syncNew, h.eligibleInOldConfig⟩
  toCommitInvariant := ⟨h.commitWithinLog, h.committedIsHistoryPrefix, h.inheritedEndWithinLog,
    h.historyWithinCommitOrInherited, h.histAck⟩
  toFailoverInvariant := ⟨fun p hp hv => let hF := h.stale p hp hv
      ⟨hF.left, hF.fenceLeInheritedEnd, hF.primHolds, hF.primAck, hF.eligHolds⟩, h.authEx⟩
  eligibleHoldsCommitted := h.eligibleHoldsCommitted

/-- Raising high-water marks keeps the invariant: every conjunct bounds them below. -/
theorem Invariant.ackHigh_mono {s : State Node} (h : Invariant s) (A : Node → Nat) (hA : ∀ x, s.ackHigh x ≤ A x) :
    Invariant { s with ackHigh := A } where
  toConfigInvariant := ⟨h.localCfgLe, h.localCfgEq, h.primKnows, h.localCfgIncLe⟩
  toReplInvariant := ⟨h.noSelfSync, h.ackedPrim, h.ackedLe, h.ackHolds,
    fun p n hp hn hf => (h.ackedHigh p n hp hn hf).trans (hA n), h.syncCommit⟩
  toMembershipInvariant := ⟨h.eligibleCounted, h.syncNew, h.eligibleInOldConfig⟩
  toCommitInvariant := ⟨h.commitWithinLog, h.committedIsHistoryPrefix, h.inheritedEndWithinLog,
    h.historyWithinCommitOrInherited, fun n hn => (h.histAck n hn).trans (hA n)⟩
  toFailoverInvariant := ⟨fun p hp hv => (h.stale p hp hv).mono (hcfg := rfl) (hlocalCfg := rfl)
      (hinherited := rfl) (hinc := rfl) (fun _ => List.prefix_refl _) hA (fun r => h.ackedLe p r hp)
      (fun _ x => x) (fun _ _ => rfl), h.authEx⟩
  eligibleHoldsCommitted := h.eligibleHoldsCommitted

/-! ## Messages on a link -/

/-- The generation of a message's connection at send. -/
def RMsg.g (m : RMsg Node) : Nat := m.link.2.2.1
/-- Whether a message goes from the primary to the replica (a data message). -/
def RMsg.down (m : RMsg Node) : Bool := m.link.2.2.2

/-- The data messages in flight from `p` to `r` on connection `g`, oldest first. -/
def dataOn (s : State Node) (p r : Node) (g : Nat) : List (RMsg Node) :=
  s.rnet.filter fun m => decide (m.link = (p, r, g, true))

/-- Their entries. -/
def pend (s : State Node) (p r : Node) (g : Nat) : List Nat := (dataOn s p r g).map RMsg.val

/-- A connection that is open after `closeAll` was open before and has neither end at
the node. -/
theorem closeAll_open {G : Node → Node → Nat} {n x y : Node} {g : Nat} (hle : g ≤ G x y)
    (he : closeAll G n x y = g) : x ≠ n ∧ y ≠ n ∧ G x y = g := by
  unfold closeAll at he; split at he
  · omega
  · rename_i hc; exact ⟨fun e => hc (Or.inl e), fun e => hc (Or.inr e), he⟩

theorem le_closeAll (G : Node → Node → Nat) (n x y : Node) : G x y ≤ closeAll G n x y := by
  unfold closeAll; split <;> omega

/-- A connection that is open after `closeLink` was open before and is another one. -/
theorem closeLink_open {G : Node → Node → Nat} {p r x y : Node} {g : Nat} (hle : g ≤ G x y)
    (he : closeLink G p r x y = g) : ¬ (x = p ∧ y = r) ∧ G x y = g := by
  unfold closeLink update at he
  by_cases hx : x = p
  · subst hx; by_cases hy : y = r
    · subst hy; simp at he; omega
    · simp [hy] at he; exact ⟨fun h => hy h.2, he⟩
  · simp [hx] at he; exact ⟨fun h => hx h.1, he⟩

theorem le_closeLink (G : Node → Node → Nat) (p r x y : Node) : G x y ≤ closeLink G p r x y := by
  unfold closeLink update
  by_cases hx : x = p
  · subst hx; by_cases hy : y = r
    · subst hy; simp
    · simp [hy]
  · simp [hx]

theorem closeLink_self (G : Node → Node → Nat) (p r : Node) : closeLink G p r p r = G p r + 1 := by
  simp [closeLink, update]

theorem filter_erase_of_false {α : Type} [DecidableEq α] (P : α → Bool) (l : List α) (a : α) (h : P a = false) :
    (l.erase a).filter P = l.filter P := by
  induction l with
  | nil => simp
  | cons b l ih =>
    by_cases hb : b = a
    · subst hb; simp [h]
    · rw [List.erase_cons_tail (by simpa using hb)]
      by_cases hP : P b = true
      · simp [List.filter_cons, hP, ih]
      · simp [List.filter_cons, hP, ih]

theorem filter_erase_of_head {α : Type} [DecidableEq α] (P : α → Bool) (l : List α) (a : α)
    (h : (l.filter P).head? = some a) : (l.erase a).filter P = (l.filter P).tail := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    by_cases hP : P b = true
    · simp only [List.filter_cons, hP, if_true, List.head?_cons, Option.some.injEq] at h
      subst h; simp [List.filter_cons, hP]
    · simp only [List.filter_cons, hP] at h
      simp only [Bool.false_eq_true, if_false] at h
      have hba : b ≠ a := by
        intro e; subst e
        have := List.mem_of_mem_head? h
        exact hP (List.mem_filter.1 this).2
      rw [List.erase_cons_tail (by simpa using hba)]
      simp [List.filter_cons, hP, ih h]

end SyncReplication

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-! ## Raising an acknowledgement record -/

/-- `p`'s record of `r`'s acknowledgement set to `v`. -/
def setAcked (s : State Node) (p r : Node) (v : Nat) : State Node :=
  { s with ackedMax := update s.ackedMax p (update (s.ackedMax p) r v) }

theorem setAcked_ackedMax (s : State Node) (p r : Node) (v : Nat) (q x : Node) :
    (setAcked s p r v).ackedMax q x = if q = p ∧ x = r then v else s.ackedMax q x := by
  by_cases hq : q = p
  · subst hq; by_cases hx : x = r
    · subst hx; simp [setAcked, update]
    · simp [setAcked, update, hx]
  · simp [setAcked, update, hq]

section raise

variable {s : State Node} (h : Invariant s) {p r : Node} {v : Nat}
  (hfol : (s.localCfg r).primary = p) (hne : p ≠ r) (hv : v ≤ (s.log r).length)
  (hpre : (s.log r).take v <+: s.log p) (hhigh : v ≤ s.ackHigh r) (hgt : s.ackedMax p r < v)

include h hfol hne hv hpre hhigh hgt

/-- A primary's record of a follower's acknowledgement may be raised to any offset up to
which the follower holds the primary's log, within the follower's high-water mark. -/
theorem invariant_raiseAck : Invariant (setAcked s p r v) := by
  have hA := setAcked_ackedMax s p r v
  have hlenp : v ≤ (s.log p).length := by
    have := hpre.length_le; rw [List.length_take, Nat.min_eq_left hv] at this; exact this
  have htake : (s.log p).take v = (s.log r).take v := by
    rw [← prefix_take_eq hpre (by rw [List.length_take, Nat.min_eq_left hv]), List.take_take, Nat.min_self]
  exact {
  toConfigInvariant := (h.toConfigInvariant).frame (hcfg := rfl) (hlocalCfg := rfl) (hinc := rfl)
  toReplInvariant := {
    noSelfSync := h.noSelfSync
    ackedPrim := by
      intro x hx
      show (setAcked s p r v).ackedMax s.cfg.primary x = 0
      rw [hA]; split_ifs with hc
      · obtain ⟨h1, rfl⟩ := hc; exact absurd (h1 ▸ hfol) hx
      · exact h.ackedPrim x hx
    ackedLe := by
      intro q x hq
      show (setAcked s p r v).ackedMax q x ≤ _
      rw [hA]; split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc; exact hlenp
      · exact h.ackedLe q x hq
    ackHolds := by
      intro q n hq hn hf
      show (s.log q).take ((setAcked s p r v).ackedMax q n) <+: s.log n
      rw [hA]; split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc; rw [htake]; exact List.take_prefix _ _
      · exact h.ackHolds q n hq hn hf
    ackedHigh := by
      intro q n hq hn hf
      show (setAcked s p r v).ackedMax q n ≤ s.ackHigh n
      rw [hA]; split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc; exact hhigh
      · exact h.ackedHigh q n hq hn hf
    syncCommit := by
      intro q x hq hs
      show _ ≤ (setAcked s p r v).ackedMax q x
      rw [hA]; split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc; exact Nat.le_trans (h.syncCommit _ _ hq hs) (Nat.le_of_lt hgt)
      · exact h.syncCommit q x hq hs }
  toMembershipInvariant := {
    eligibleCounted := h.eligibleCounted
    syncNew := by
      intro x hs he
      obtain ⟨a, b⟩ := h.syncNew x hs he
      refine ⟨a, ?_⟩
      show _ ≤ (setAcked s p r v).ackedMax s.cfg.primary x
      rw [hA]; split_ifs with hc
      · obtain ⟨h1, rfl⟩ := hc
        show s.inheritedEnd s.cfg.primary ≤ v
        rw [h1] at b ⊢; omega
      · exact b
    eligibleInOldConfig := h.eligibleInOldConfig }
  toCommitInvariant := ⟨h.commitWithinLog, h.committedIsHistoryPrefix, h.inheritedEndWithinLog,
    h.historyWithinCommitOrInherited, h.histAck⟩
  toFailoverInvariant := {
    stale := by
      intro q hq hvq
      refine (h.stale q hq hvq).mono (hcfg := rfl) (hlocalCfg := rfl) (hinherited := rfl) (hinc := rfl)
        (fun _ => List.prefix_refl _) (fun _ => Nat.le_refl _)
        (fun x => h.ackedLe q x hq) (fun _ x => x) ?_
      intro x hx
      show (setAcked s p r v).ackedMax q x = s.ackedMax q x
      rw [hA]; split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc; exact absurd hfol hx
      · rfl
    authEx := h.authEx }
  eligibleHoldsCommitted := h.eligibleHoldsCommitted }

end raise

end SyncReplication

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-! ## The replication-message invariant -/

/-- `H` gives each replication ID the history it names: every node's log is a prefix
of its ID's history, a node that thinks it is primary holds its ID's whole history, a
secondary ID agrees with its history up to its offset, and every entry on an open
stream extends the replica's log within the history of the ID it was sent under. -/
structure HistOk (s : State Node) (H : Nat → List Nat) : Prop where
  logH : ∀ n, s.log n <+: H (s.replId n)
  ownH : ∀ p, ThinksPrimary s p → H (s.replId p) = s.log p
  secH : ∀ n t o, s.replId2 n = some (t, o) → o ≤ (s.log n).length ∧ (s.log n).take o = (H t).take o
  streamH : ∀ p r k g, s.stream p r = some (k, g) → s.rgen p r = g →
    ∀ i (hi : i < (dataOn s p r g).length),
      s.log r ++ (pend s p r g).take (i + 1) <+: H ((dataOn s p r g)[i]).rid

/-- Close a goal `acked q x ≤ ackedMax q x` after a step that resets both records in
the same places (or resets only `acked`), given the bound before. -/
macro "ack_le " h:term:max : tactic =>
  `(tactic| (split_ifs <;> (try simp only [update]) <;> (try split_ifs) <;>
      first | exact Nat.le_refl _ | exact Nat.zero_le _ | exact $h _ _))

/-- The facts about replication IDs, connections and messages in flight. -/
structure RInvariant (s : State Node) : Prop where
  ids : ∀ n, s.replId n ∈ s.usedIds
  secIds : ∀ n t o, s.replId2 n = some (t, o) → t ∈ s.usedIds
  msgIds : ∀ m ∈ s.rnet, m.down = true → m.rid ∈ s.usedIds
  /-- No two nodes that think they are primary share an ID. -/
  uniqPrim : ∀ p q, ThinksPrimary s p → ThinksPrimary s q → s.replId p = s.replId q → p = q
  /-- No message or stream is on a connection newer than now's. -/
  genLe : ∀ m ∈ s.rnet, m.g ≤ s.rgen m.primary m.replica
  streamGen : ∀ p r k g, s.stream p r = some (k, g) → g ≤ s.rgen p r
  /-- An open stream goes from the replica's primary to the replica, and the replica's
  log followed by the entries in flight is a prefix of the primary's log, ending at the
  stream position. -/
  stream : ∀ p r k g, s.stream p r = some (k, g) → s.rgen p r = g →
    p ≠ r ∧ (s.localCfg r).primary = p ∧ s.log r ++ pend s p r g <+: s.log p ∧
    (s.log r).length + (pend s p r g).length = k
  /-- A data message on an open connection belongs to an accepted stream. -/
  dataStream : ∀ m ∈ s.rnet, m.down = true → s.rgen m.primary m.replica = m.g →
    ∃ k, s.stream m.primary m.replica = some (k, m.g)
  /-- An acknowledgement on an open, accepted connection is real: the replica holds the
  primary's log up to it, within its high-water mark. -/
  ackOk : ∀ r p g off, RMsg.ack r p g off ∈ s.rnet → s.rgen p r = g →
    (∃ k, s.stream p r = some (k, g)) →
    off ≤ (s.log r).length ∧ (s.log r).take off <+: s.log p ∧ off ≤ s.ackHigh r
  hist : ∃ H, HistOk s H
  /-- The per-connection acknowledgement record never exceeds the highest one since the
  last reset of the record: a reconnect starts the first again from 0. -/
  ackedLeMax : ∀ p r, s.acked p r ≤ s.ackedMax p r

theorem rInvariant_init (i : Node) : RInvariant (init i) where
  ids := by intro n; simp [init]
  secIds := by intro n t o h; simp [init] at h
  msgIds := by intro m h; simp [init] at h
  uniqPrim := by
    intro p q hp hq _
    have h1 := hp.1; have h2 := hq.1; simp [init, initCfg] at h1 h2; rw [← h1, ← h2]
  genLe := by intro m h; simp [init] at h
  streamGen := by intro p r k g h; simp [init] at h
  stream := by intro p r k g h; simp [init] at h
  dataStream := by intro m h; simp [init] at h
  ackOk := by intro r p g off h; simp [init] at h
  hist := ⟨fun _ => [], {
    logH := by intro n; simp [init]
    ownH := by intro p _; simp [init]
    secH := by intro n t o h; simp [init] at h
    streamH := by intro p r k g h; simp [init] at h }⟩
  ackedLeMax := fun _ _ => Nat.le_refl _

theorem dataOn_of_rnet {s s' : State Node} (h : s'.rnet = s.rnet) (p r : Node) (g : Nat) :
    dataOn s' p r g = dataOn s p r g := by unfold dataOn; rw [h]

theorem pend_of_rnet {s s' : State Node} (h : s'.rnet = s.rnet) (p r : Node) (g : Nat) :
    pend s' p r g = pend s p r g := by unfold pend; rw [dataOn_of_rnet h]

theorem thinks_of_local {s s' : State Node} {x : Node} (hc : s'.localCfg x = s.localCfg x)
    (hi : s'.incarnation x = s.incarnation x) : ThinksPrimary s' x ↔ ThinksPrimary s x := by
  unfold ThinksPrimary; rw [hc, hi]

/-- A step that resets node `n`'s state and closes its connections: everything about
any other node's links is as before, and `n`'s links are closed. -/
theorem RInvariant.reset {s s' : State Node} (h : RInvariant s) (n : Node)
    (hlog : ∀ x, x ≠ n → s'.log x = s.log x) (hrid : ∀ x, x ≠ n → s'.replId x = s.replId x)
    (hrid2 : ∀ x, x ≠ n → s'.replId2 x = s.replId2 x)
    (hcfgx : ∀ x, x ≠ n → s'.localCfg x = s.localCfg x) (hincx : ∀ x, x ≠ n → s'.incarnation x = s.incarnation x)
    (hah : ∀ x, x ≠ n → s.ackHigh x ≤ s'.ackHigh x)
    (hids : s.usedIds ⊆ s'.usedIds) (hidn : s'.replId n ∈ s'.usedIds)
    (hsecn : ∀ t o, s'.replId2 n = some (t, o) → t ∈ s'.usedIds)
    (hg : s'.rgen = closeAll s.rgen n)
    (hnet : s'.rnet = s.rnet) (hst : s'.stream = s.stream)
    (hprimn : ThinksPrimary s' n → (ThinksPrimary s n ∧ s'.replId n = s.replId n) ∨ s'.replId n ∉ s.usedIds)
    (hHn : ∀ H, HistOk s H → ∃ H' : Nat → List Nat, (∀ t ∈ s.usedIds, H' t = H t) ∧ s'.log n <+: H' (s'.replId n) ∧
      (ThinksPrimary s' n → H' (s'.replId n) = s'.log n) ∧
      (∀ t o, s'.replId2 n = some (t, o) → o ≤ (s'.log n).length ∧ (s'.log n).take o = (H' t).take o))
    (hak : ∀ p r, s'.acked p r ≤ s'.ackedMax p r) :
    RInvariant s' := by
  have hrg : ∀ x y, s.rgen x y ≤ s'.rgen x y := fun x y => by rw [hg]; exact le_closeAll _ _ _ _
  have htk : ∀ x, x ≠ n → (ThinksPrimary s' x ↔ ThinksPrimary s x) :=
    fun x hx => thinks_of_local (hcfgx x hx) (hincx x hx)
  -- A connection with `n` at either end that was open before is closed now.
  have hclosed : ∀ x y g, g ≤ s.rgen x y → s'.rgen x y = g → x ≠ n ∧ y ≠ n ∧ s.rgen x y = g := by
    intro x y g hle he; rw [hg] at he; exact closeAll_open hle he
  have hdata := dataOn_of_rnet hnet
  have hpend := pend_of_rnet hnet
  exact {
  ids := fun x => by
    by_cases hx : x = n
    · subst hx; exact hidn
    · rw [hrid x hx]; exact hids (h.ids x)
  secIds := fun x t o hx => by
    by_cases hxn : x = n
    · subst hxn; exact hsecn t o hx
    · rw [hrid2 x hxn] at hx; exact hids (h.secIds x t o hx)
  msgIds := fun m hm hd => hids (h.msgIds m (hnet ▸ hm) hd)
  uniqPrim := by
    intro p q hp hq he
    by_cases hpn : p = n
    · subst hpn
      by_cases hqn : q = p
      · exact hqn.symm
      · have hq0 := (htk q hqn).1 hq
        rcases hprimn hp with ⟨hp0, e⟩ | hfresh
        · exact h.uniqPrim _ _ hp0 hq0 (by rw [← e, he, hrid q hqn])
        · exact absurd (by rw [he, hrid q hqn]; exact h.ids q) hfresh
    · by_cases hqn : q = n
      · subst hqn
        have hp0 := (htk p hpn).1 hp
        rcases hprimn hq with ⟨hq0, e⟩ | hfresh
        · exact h.uniqPrim _ _ hp0 hq0 (by rw [← e, ← he, hrid p hpn])
        · exact absurd (by rw [← he, hrid p hpn]; exact h.ids p) hfresh
      · exact h.uniqPrim _ _ ((htk p hpn).1 hp) ((htk q hqn).1 hq) (by rw [← hrid p hpn, ← hrid q hqn]; exact he)
  genLe := fun m hm => (h.genLe m (hnet ▸ hm)).trans (hrg _ _)
  streamGen := fun p r k g hs => (h.streamGen p r k g (hst ▸ hs)).trans (hrg _ _)
  stream := by
    intro p r k g hs hgg
    rw [hst] at hs
    obtain ⟨hpn, hrn, hg0⟩ := hclosed p r g (h.streamGen p r k g hs) hgg
    obtain ⟨h1, h2, h3, h4⟩ := h.stream p r k g hs hg0
    refine ⟨h1, by rw [hcfgx r hrn]; exact h2, ?_, ?_⟩
    · rw [hlog r hrn, hlog p hpn, hpend]; exact h3
    · rw [hlog r hrn, hpend]; exact h4
  dataStream := by
    intro m hm hd hgg
    rw [hnet] at hm
    obtain ⟨-, -, hg0⟩ := hclosed _ _ _ (h.genLe m hm) hgg
    rw [hst]
    exact h.dataStream m hm hd hg0
  ackOk := by
    intro r p g off hm hgg hk
    rw [hnet] at hm
    obtain ⟨hpn, hrn, hg0⟩ := hclosed p r g (h.genLe _ hm) hgg
    rw [hst] at hk
    obtain ⟨h1, h2, h3⟩ := h.ackOk r p g off hm hg0 hk
    rw [hlog r hrn, hlog p hpn]; exact ⟨h1, h2, h3.trans (hah r hrn)⟩
  hist := by
    obtain ⟨H, hH⟩ := h.hist
    obtain ⟨H', hsame, hl, ho, hsc⟩ := hHn H hH
    refine ⟨H', {
      logH := fun x => by
        by_cases hx : x = n
        · subst hx; exact hl
        · rw [hlog x hx, hrid x hx, hsame _ (h.ids x)]; exact hH.logH x
      ownH := fun p hp => by
        by_cases hpn : p = n
        · subst hpn; exact ho hp
        · rw [hrid p hpn, hsame _ (h.ids p), hlog p hpn]; exact hH.ownH p ((htk p hpn).1 hp)
      secH := fun x t o hx => by
        by_cases hxn : x = n
        · subst hxn; exact hsc t o hx
        · rw [hrid2 x hxn] at hx
          rw [hlog x hxn, hsame _ (h.secIds x t o hx)]; exact hH.secH x t o hx
      streamH := by
        intro p r k g hs hgg i hi
        rw [hst] at hs
        obtain ⟨-, hrn, hg0⟩ := hclosed p r g (h.streamGen p r k g hs) hgg
        have hi' : i < (dataOn s p r g).length := by rw [← hdata]; exact hi
        have := hH.streamH p r k g hs hg0 i hi'
        have hmem : (dataOn s p r g)[i] ∈ s.rnet := (List.mem_filter.1 (List.getElem_mem hi')).1
        have hdown : ((dataOn s p r g)[i]).down = true := by
          have := (List.mem_filter.1 (List.getElem_mem hi')).2
          simp only [decide_eq_true_eq] at this
          simp [RMsg.down, this]
        simp only [hdata, hpend, hlog r hrn]
        rw [hsame _ (h.msgIds _ hmem hdown)]; exact this }⟩
  ackedLeMax := hak }

end SyncReplication

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-- A step that moves no log, ID, message, stream or generation, keeps every node's
primary, creates no node that thinks it is primary, and only raises high-water marks. -/
theorem RInvariant.frame {s s' : State Node} (h : RInvariant s)
    (hlog : s'.log = s.log) (hrid : s'.replId = s.replId) (hrid2 : s'.replId2 = s.replId2)
    (hids : s'.usedIds = s.usedIds) (hg : s'.rgen = s.rgen) (hnet : s'.rnet = s.rnet) (hst : s'.stream = s.stream)
    (hprim : ∀ x, (s'.localCfg x).primary = (s.localCfg x).primary)
    (htp : ∀ x, ThinksPrimary s' x → ThinksPrimary s x) (hah : ∀ x, s.ackHigh x ≤ s'.ackHigh x)
    (hA : s'.acked = s.acked := by rfl) (hAM : s'.ackedMax = s.ackedMax := by rfl) :
    RInvariant s' := by
  have hdata := dataOn_of_rnet hnet
  have hpend := pend_of_rnet hnet
  exact {
  ackedLeMax := fun q x => by rw [hA, hAM]; exact h.ackedLeMax q x
  ids := fun x => by rw [hrid, hids]; exact h.ids x
  secIds := fun x t o hx => by rw [hids]; rw [hrid2] at hx; exact h.secIds x t o hx
  msgIds := fun m hm hd => by rw [hids]; exact h.msgIds m (hnet ▸ hm) hd
  uniqPrim := fun p q hp hq he => h.uniqPrim p q (htp p hp) (htp q hq) (by rw [← hrid]; exact he)
  genLe := fun m hm => by rw [hg]; exact h.genLe m (hnet ▸ hm)
  streamGen := fun p r k g hs => by rw [hg]; exact h.streamGen p r k g (hst ▸ hs)
  stream := fun p r k g hs hgg => by
    rw [hst] at hs; rw [hg] at hgg
    obtain ⟨h1, h2, h3, h4⟩ := h.stream p r k g hs hgg
    exact ⟨h1, by rw [hprim]; exact h2, by rw [hlog, hpend]; exact h3, by rw [hlog, hpend]; exact h4⟩
  dataStream := fun m hm hd hgg => by
    rw [hst]; rw [hg] at hgg; exact h.dataStream m (hnet ▸ hm) hd hgg
  ackOk := fun r p g off hm hgg hk => by
    rw [hst] at hk; rw [hg] at hgg
    obtain ⟨h1, h2, h3⟩ := h.ackOk r p g off (hnet ▸ hm) hgg hk
    rw [hlog]; exact ⟨h1, h2, h3.trans (hah r)⟩
  hist := by
    obtain ⟨H, hH⟩ := h.hist
    exact ⟨H, {
      logH := fun x => by rw [hlog, hrid]; exact hH.logH x
      ownH := fun p hp => by rw [hlog, hrid]; exact hH.ownH p (htp p hp)
      secH := fun x t o hx => by rw [hlog]; rw [hrid2] at hx; exact hH.secH x t o hx
      streamH := fun p r k g hs hgg i hi => by
        rw [hst] at hs; rw [hg] at hgg
        simp only [hdata, hpend, hlog] at hi ⊢
        exact hH.streamH p r k g hs hgg i hi }⟩ }

/-- An append by a node that thinks it is primary: its ID's history grows with its log. -/
theorem RInvariant.append {s : State Node} (h : RInvariant s) {p : Node} (hp : ThinksPrimary s p) :
    RInvariant (appendWrite s p) := by
  have hlog : ∀ x, s.log x <+: (appendWrite s p).log x := grow_upd s.log p _
  have hlogp : (appendWrite s p).log p = s.log p ++ [s.replId p] := by simp [appendWrite]
  have hlogx : ∀ x, x ≠ p → (appendWrite s p).log x = s.log x := fun x hx => by
    simp [appendWrite, update, hx]
  -- No node streams into `p`: `p` follows itself.
  have hnotrep : ∀ q k g, s.stream q p = some (k, g) → s.rgen q p = g → False := by
    intro q k g hs hgg
    obtain ⟨h1, h2, -, -⟩ := h.stream q p k g hs hgg
    exact h1 (h2.symm.trans hp.1)
  exact {
  ackedLeMax := h.ackedLeMax
  ids := h.ids, secIds := h.secIds, msgIds := h.msgIds
  uniqPrim := h.uniqPrim, genLe := h.genLe, streamGen := h.streamGen
  stream := by
    intro q r k g hs hgg
    obtain ⟨h1, h2, h3, h4⟩ := h.stream q r k g hs hgg
    have hrp : r ≠ p := fun e => by subst e; exact hnotrep q k g hs hgg
    refine ⟨h1, h2, ?_, ?_⟩
    · show (appendWrite s p).log r ++ pend s q r g <+: (appendWrite s p).log q
      rw [hlogx r hrp]; exact h3.trans (hlog q)
    · show ((appendWrite s p).log r).length + _ = k; rw [hlogx r hrp]; exact h4
  dataStream := h.dataStream
  ackOk := by
    intro r q g off hm hgg hk
    obtain ⟨h1, h2, h3⟩ := h.ackOk r q g off hm hgg hk
    obtain ⟨k, hk⟩ := hk
    have hrp : r ≠ p := fun e => by subst e; exact hnotrep q k g hk hgg
    show off ≤ ((appendWrite s p).log r).length ∧ ((appendWrite s p).log r).take off <+: (appendWrite s p).log q ∧ _
    rw [hlogx r hrp]; exact ⟨h1, h2.trans (hlog q), h3⟩
  hist := by
    obtain ⟨H, hH⟩ := h.hist
    have hHp := hH.ownH p hp
    refine ⟨update H (s.replId p) (s.log p ++ [s.replId p]), ?_⟩
    have hgrow : ∀ t, H t <+: update H (s.replId p) (s.log p ++ [s.replId p]) t := by
      intro t; by_cases ht : t = s.replId p
      · subst ht; rw [update_self, hHp]; exact List.prefix_append _ _
      · rw [update_of_ne _ _ ht]
    exact {
      logH := fun x => by
        by_cases hx : x = p
        · subst hx; show _ <+: update H (s.replId x) _ (s.replId x); rw [update_self, hlogp]
        · show (appendWrite s p).log x <+: _; rw [hlogx x hx]; exact (hH.logH x).trans (hgrow _)
      ownH := fun q hq => by
        have hq0 : ThinksPrimary s q := hq
        by_cases hqp : q = p
        · subst hqp; show update H (s.replId q) _ (s.replId q) = _; rw [update_self, hlogp]
        · have hne : s.replId q ≠ s.replId p := fun he => hqp (h.uniqPrim q p hq0 hp he)
          show update H (s.replId p) _ (s.replId q) = (appendWrite s p).log q
          rw [update_of_ne _ _ hne, hlogx q hqp]; exact hH.ownH q hq0
      secH := fun x t o hx => by
        obtain ⟨h1, h2⟩ := hH.secH x t o hx
        have hlo : o ≤ (H t).length := by
          have := congrArg List.length h2; rw [List.length_take, List.length_take] at this; omega
        refine ⟨h1.trans (hlog x).length_le, ?_⟩
        rw [← prefix_take_eq (hlog x) h1, h2, prefix_take_eq (hgrow t) hlo]
      streamH := by
        intro q r k g hs hgg i hi
        have hrp : r ≠ p := fun e => by subst e; exact hnotrep q k g hs hgg
        show (appendWrite s p).log r ++ _ <+: _
        rw [hlogx r hrp]
        exact (hH.streamH q r k g hs hgg i hi).trans (hgrow _) } }

end SyncReplication

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-! ## Message lists -/

theorem dataOn_append (s : State Node) (net : List (RMsg Node)) (m : RMsg Node) (p r : Node) (g : Nat)
    (hnet : s.rnet = net ++ [m]) (s0 : State Node) (h0 : s0.rnet = net) :
    dataOn s p r g = dataOn s0 p r g ++ (if m.link = (p, r, g, true) then [m] else []) := by
  unfold dataOn; rw [hnet, h0, List.filter_append]; congr 1; by_cases hm : m.link = (p, r, g, true) <;> simp [hm]

theorem prefix_snoc_of_lt {L M : List Nat} (h : L <+: M) (hl : L.length < M.length) :
    L ++ [M.getD L.length 0] <+: M := by
  obtain ⟨t, rfl⟩ := h
  cases t with
  | nil => simp at hl
  | cons x t => simp [List.getD_eq_getElem?_getD]

theorem closeInto_open {G : Node → Node → Nat} {n x y : Node} {g : Nat} (hle : g ≤ G x y)
    (he : closeInto G n x y = g) : y ≠ n ∧ G x y = g := by
  unfold closeInto at he; split at he
  · omega
  · rename_i hc; exact ⟨hc, he⟩

theorem le_closeInto (G : Node → Node → Nat) (n x y : Node) : G x y ≤ closeInto G n x y := by
  unfold closeInto; split <;> omega

/-- On an open stream the replica's log is a prefix of the primary's. -/
theorem RInvariant.prefix_of_open {s : State Node} (h : RInvariant s) {p r : Node} (ho : StreamOpen s p r) :
    s.log r <+: s.log p := by
  unfold StreamOpen at ho
  cases hs : s.stream p r with
  | none => rw [hs] at ho; cases ho
  | some x =>
    rw [hs] at ho; obtain ⟨k, g⟩ := x
    simp only [Option.map_some, Option.some.injEq] at ho
    obtain ⟨-, -, hpre, -⟩ := h.stream p r k g hs ho.symm
    exact (List.prefix_append _ _).trans hpre

/-- Raising connection generations, so that every connection open afterwards was open
before, keeps the invariant. -/
theorem RInvariant.regen {s : State Node} (h : RInvariant s) (G : Node → Node → Nat)
    (hle : ∀ x y, s.rgen x y ≤ G x y) (hopen : ∀ x y g, g ≤ s.rgen x y → G x y = g → s.rgen x y = g) :
    RInvariant { s with rgen := G } where
  ackedLeMax := h.ackedLeMax
  ids := h.ids
  secIds := h.secIds
  msgIds := h.msgIds
  uniqPrim := h.uniqPrim
  genLe := fun m hm => (h.genLe m hm).trans (hle _ _)
  streamGen := fun p r k g hs => (h.streamGen p r k g hs).trans (hle _ _)
  stream := fun p r k g hs hgg => h.stream p r k g hs (hopen p r g (h.streamGen p r k g hs) hgg)
  dataStream := fun m hm hd hgg => h.dataStream m hm hd (hopen _ _ _ (h.genLe m hm) hgg)
  ackOk := fun r p g off hm hgg hk => h.ackOk r p g off hm (hopen p r g (h.genLe _ hm) hgg) hk
  hist := by
    obtain ⟨H, hH⟩ := h.hist
    exact ⟨H, { logH := hH.logH, ownH := hH.ownH, secH := hH.secH
                streamH := fun p r k g hs hgg =>
                  hH.streamH p r k g hs (hopen p r g (h.streamGen p r k g hs) hgg) }⟩

/-- Close the connection from `p` to `r`. -/
theorem RInvariant.closeOne {s : State Node} (h : RInvariant s) (p r : Node) :
    RInvariant { s with rgen := closeLink s.rgen p r } :=
  h.regen _ (le_closeLink _ _ _) (fun _ _ _ hle he => (closeLink_open hle he).2)

/-- Erase a message on a closed connection. -/
theorem RInvariant.eraseClosed {s : State Node} (h : RInvariant s) {msg : RMsg Node}
    (hc : s.rgen msg.primary msg.replica ≠ msg.g) :
    RInvariant { s with rnet := s.rnet.erase msg } := by
  have hdata : ∀ p r g, s.rgen p r = g →
      dataOn { s with rnet := s.rnet.erase msg } p r g = dataOn s p r g := by
    intro p r g hgg
    unfold dataOn; apply filter_erase_of_false
    simp only [decide_eq_false_iff_not]
    intro he
    apply hc; simp only [RMsg.primary, RMsg.replica, RMsg.g, he]; exact hgg
  have hpend : ∀ p r g, s.rgen p r = g →
      pend { s with rnet := s.rnet.erase msg } p r g = pend s p r g := fun p r g a => by
    unfold pend; rw [hdata p r g a]
  exact {
  ackedLeMax := h.ackedLeMax
  ids := h.ids, secIds := h.secIds
  msgIds := fun m hm => h.msgIds m (List.mem_of_mem_erase hm)
  uniqPrim := h.uniqPrim
  genLe := fun m hm => h.genLe m (List.mem_of_mem_erase hm)
  streamGen := h.streamGen
  stream := fun p r k g hs hgg => by
    have := h.stream p r k g hs hgg; rw [hpend p r g hgg]; exact this
  dataStream := fun m hm => h.dataStream m (List.mem_of_mem_erase hm)
  ackOk := fun r p g off hm => h.ackOk r p g off (List.mem_of_mem_erase hm)
  hist := by
    obtain ⟨H, hH⟩ := h.hist
    exact ⟨H, { logH := hH.logH, ownH := hH.ownH, secH := hH.secH
                streamH := fun p r k g hs hgg i hi => by
                  simp only [hdata p r g hgg, hpend p r g hgg] at hi ⊢
                  exact hH.streamH p r k g hs hgg i hi }⟩ }

/-- A lost message closes its connection, and only that one. -/
theorem RInvariant.lose {s : State Node} (h : RInvariant s) {msg : RMsg Node} (hm : msg ∈ s.rnet) :
    RInvariant (loseMsg s msg) := by
  have h2 := h.closeOne msg.primary msg.replica
  have hc : closeLink s.rgen msg.primary msg.replica msg.primary msg.replica ≠ msg.g := by
    have := h.genLe msg hm; rw [closeLink_self]; omega
  exact h2.eraseClosed (msg := msg) hc

end SyncReplication

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-- Erase an acknowledgement: no data stream changes. -/
theorem dataOn_erase_ack (s : State Node) (r p : Node) (g off : Nat) (q x : Node) (g' : Nat) :
    dataOn { s with rnet := s.rnet.erase (.ack r p g off) } q x g' = dataOn s q x g' := by
  unfold dataOn; apply filter_erase_of_false; simp [RMsg.link]

/-- A primary streams its next entry. -/
theorem RInvariant.sendData {s : State Node} (h : RInvariant s) {p r : Node} {k : Nat}
    (hs : s.stream p r = some (k, s.rgen p r)) (hk : k < (s.log p).length) :
    RInvariant (streamNext s p r k) := by
  set m : RMsg Node := .data p r (s.rgen p r) ((s.log p).getD k 0) (s.replId p) with hm
  have hD : ∀ q x g', dataOn (streamNext s p r k) q x g' =
      dataOn s q x g' ++ (if m.link = (q, x, g', true) then [m] else []) :=
    fun q x g' => dataOn_append _ s.rnet m q x g' rfl s rfl
  have hst : ∀ q x, (streamNext s p r k).stream q x =
      if q = p ∧ x = r then some (k + 1, s.rgen p r) else s.stream q x := by
    intro q x; by_cases hq : q = p
    · subst hq; by_cases hx : x = r
      · subst hx; simp [streamNext]
      · simp [streamNext, update, hx]
    · simp [streamNext, update, hq]
  obtain ⟨hpr, hfol, hpre, hlen⟩ := h.stream p r k _ hs rfl
  have hmlink : m.link = (p, r, s.rgen p r, true) := rfl
  have hnew : ∀ q x g', m.link = (q, x, g', true) → q = p ∧ x = r ∧ g' = s.rgen p r := by
    intro q x g' he; rw [hmlink] at he; simp only [Prod.mk.injEq] at he
    exact ⟨he.1.symm, he.2.1.symm, he.2.2.1.symm⟩
  have hpend : pend (streamNext s p r k) p r (s.rgen p r) = pend s p r (s.rgen p r) ++ [(s.log p).getD k 0] := by
    unfold pend; rw [hD, if_pos hmlink]; simp [m, RMsg.val]
  have hpendo : ∀ q x g', ¬ (q = p ∧ x = r ∧ g' = s.rgen p r) →
      pend (streamNext s p r k) q x g' = pend s q x g' := by
    intro q x g' hn; unfold pend; rw [hD, if_neg (fun he => hn (hnew q x g' he))]; simp
  have hkey : s.log r ++ pend s p r (s.rgen p r) ++ [(s.log p).getD k 0] <+: s.log p := by
    have := prefix_snoc_of_lt hpre (by rw [List.length_append, hlen]; exact hk)
    rwa [List.length_append, hlen] at this
  exact {
  ackedLeMax := h.ackedLeMax
  ids := h.ids, secIds := h.secIds
  msgIds := by
    intro x hx hd
    rcases List.mem_append.1 hx with hx | hx
    · exact h.msgIds x hx hd
    · rw [List.mem_singleton] at hx; subst hx; exact h.ids p
  uniqPrim := h.uniqPrim
  genLe := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact h.genLe x hx
    · rw [List.mem_singleton] at hx; subst hx; exact Nat.le_refl _
  streamGen := by
    intro q x k' g' hs'
    rw [hst] at hs'; split_ifs at hs' with hc
    · obtain ⟨rfl, rfl⟩ := hc; cases hs'; exact Nat.le_refl _
    · exact h.streamGen q x k' g' hs'
  stream := by
    intro q x k' g' hs' hgg
    rw [hst] at hs'; split_ifs at hs' with hc
    · obtain ⟨rfl, rfl⟩ := hc; cases hs'
      refine ⟨hpr, hfol, ?_, ?_⟩
      · show s.log x ++ _ <+: s.log q; rw [hpend, ← List.append_assoc]; exact hkey
      · show (s.log x).length + _ = k + 1; rw [hpend, List.length_append, ← Nat.add_assoc, hlen]; rfl
    · have hn : ¬ (q = p ∧ x = r ∧ g' = s.rgen p r) := fun ⟨a, b, _⟩ => hc ⟨a, b⟩
      rw [hpendo q x g' hn]; exact h.stream q x k' g' hs' hgg
  dataStream := by
    intro x hx hd hgg
    rw [hst]
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨k', hk'⟩ := h.dataStream x hx hd hgg
      split_ifs with hc
      · obtain ⟨hq, hx'⟩ := hc
        rw [hq, hx', hs] at hk'; simp only [Option.some.injEq, Prod.mk.injEq] at hk'
        exact ⟨k + 1, by rw [hk'.2]⟩
      · exact ⟨k', hk'⟩
    · rw [List.mem_singleton] at hx; subst hx
      exact ⟨k + 1, by simp [m, RMsg.primary, RMsg.replica, RMsg.g, RMsg.link]⟩
  ackOk := by
    intro x q g' off hm' hgg hk'
    have hm0 : RMsg.ack x q g' off ∈ s.rnet := by
      rcases List.mem_append.1 hm' with hm' | hm'
      · exact hm'
      · simp [m] at hm'
    apply h.ackOk x q g' off hm0 hgg
    obtain ⟨k', hk'⟩ := hk'
    rw [hst] at hk'; split_ifs at hk' with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact ⟨k, by cases hk'; exact hs⟩
    · exact ⟨k', hk'⟩
  hist := by
    obtain ⟨H, hH⟩ := h.hist
    refine ⟨H, { logH := hH.logH, ownH := hH.ownH, secH := hH.secH, streamH := ?_ }⟩
    intro q x k' g' hs' hgg i hi
    rw [hst] at hs'
    by_cases hc : q = p ∧ x = r ∧ g' = s.rgen p r
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      have hlen' : (dataOn (streamNext s q x k) q x (s.rgen q x)).length =
          (dataOn s q x (s.rgen q x)).length + 1 := by rw [hD, if_pos hmlink]; simp
      rcases Nat.lt_or_ge i (dataOn s q x (s.rgen q x)).length with hlt | hge
      · have hget : (dataOn (streamNext s q x k) q x (s.rgen q x))[i] = (dataOn s q x (s.rgen q x))[i] := by
          simp only [hD, if_pos hmlink]; exact List.getElem_append_left hlt
        rw [hget, hpend, List.take_append_of_le_length (by unfold pend; simp; omega)]
        exact hH.streamH q x k _ hs rfl i hlt
      · have hi' : i = (dataOn s q x (s.rgen q x)).length := by omega
        have hget : (dataOn (streamNext s q x k) q x (s.rgen q x))[i] = m := by
          simp only [hD, if_pos hmlink]; rw [List.getElem_append_right (by omega)]; simp [hi']
        rw [hget, hpend, List.take_of_length_le (by unfold pend; simp; omega), ← List.append_assoc]
        exact hkey.trans (hH.logH q)
    · have hD' : dataOn (streamNext s p r k) q x g' = dataOn s q x g' := by
        rw [hD, if_neg (fun he => hc (hnew q x g' he))]; simp
      have hs0 : s.stream q x = some (k', g') := by
        split_ifs at hs' with hqx
        · obtain ⟨rfl, rfl⟩ := hqx; cases hs'; exact absurd ⟨rfl, rfl, rfl⟩ hc
        · exact hs'
      simp only [hD', hpendo q x g' hc] at hi ⊢
      exact hH.streamH q x k' g' hs0 hgg i hi }

end SyncReplication

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

theorem dataOn_first {s : State Node} {p r : Node} {g v rid : Nat}
    (hf : (RMsg.data p r g v rid).First s) :
    ∃ tl, dataOn s p r g = .data p r g v rid :: tl ∧
      dataOn { s with rnet := s.rnet.erase (.data p r g v rid) } p r g = tl := by
  have he : (s.rnet.filter fun m => decide (m.link = (RMsg.data p r g v rid).link)) =
      dataOn s p r g := rfl
  unfold RMsg.First at hf
  rw [he] at hf
  cases hd : dataOn s p r g with
  | nil => rw [hd] at hf; simp at hf
  | cons a tl =>
    rw [hd] at hf; simp only [List.head?_cons, Option.some.injEq] at hf; subst hf
    refine ⟨tl, rfl, ?_⟩
    have := filter_erase_of_head (fun m => decide (m.link = ((RMsg.data p r g v rid).link))) s.rnet
      (.data p r g v rid) (by rw [he, hd]; rfl)
    show List.filter (fun m => decide (m.link = (RMsg.data p r g v rid).link)) _ = tl
    rw [this, he, hd]; rfl

/-- The next entry of an open stream extends the replica's log within the streaming
primary's log, and was sent under a used ID. -/
theorem RInvariant.deliver_prefix {s : State Node} (h : RInvariant s) {p r : Node} {g v rid : Nat}
    (hin : RMsg.data p r g v rid ∈ s.rnet) (hcur : (RMsg.data p r g v rid).Current s)
    (hf : (RMsg.data p r g v rid).First s) :
    p ≠ r ∧ s.log r ++ [v] <+: s.log p ∧ rid ∈ s.usedIds := by
  have hgg : s.rgen p r = g := hcur
  obtain ⟨k, hk⟩ := h.dataStream _ hin rfl hgg
  obtain ⟨hpr, -, hpre, -⟩ := h.stream p r k g hk hgg
  obtain ⟨tl, hd, -⟩ := dataOn_first hf
  have hpendE : pend s p r g = v :: tl.map RMsg.val := by unfold pend; rw [hd]; rfl
  rw [hpendE] at hpre
  have hv : s.log r ++ [v] <+: s.log r ++ v :: tl.map RMsg.val := ⟨tl.map RMsg.val, by simp⟩
  exact ⟨hpr, List.IsPrefix.trans hv hpre, h.msgIds _ hin rfl⟩

/-- A replica applies the next entry of an open stream. -/
theorem RInvariant.deliverData {s : State Node} (h : RInvariant s) {p r : Node} {g v rid : Nat}
    (hin : RMsg.data p r g v rid ∈ s.rnet) (hcur : (RMsg.data p r g v rid).Current s)
    (hf : (RMsg.data p r g v rid).First s) :
    RInvariant (applyData s (.data p r g v rid) r v rid) := by
  have hgg : s.rgen p r = g := hcur
  obtain ⟨k, hk⟩ := h.dataStream _ hin rfl hgg
  have hk : s.stream p r = some (k, g) := hk
  obtain ⟨hpr, hfol, hpre, hlen⟩ := h.stream p r k g hk hgg
  obtain ⟨tl, hd, hd'⟩ := dataOn_first hf
  have hpendE : pend s p r g = v :: tl.map RMsg.val := by unfold pend; rw [hd]; rfl
  set s' := applyData s (.data p r g v rid) r v rid with hs'
  have hlogr : s'.log r = s.log r ++ [v] := by simp [s', applyData]
  have hlogx : ∀ x, x ≠ r → s'.log x = s.log x := fun x hx => by simp [s', applyData, update, hx]
  have hridx : ∀ x, x ≠ r → s'.replId x = s.replId x := fun x hx => by simp [s', applyData, update, hx]
  have hridr : s'.replId r = rid := by simp [s', applyData]
  have hgrow : ∀ x, s.log x <+: s'.log x := fun x => by
    by_cases hx : x = r
    · subst hx; rw [hlogr]; exact List.prefix_append _ _
    · rw [hlogx x hx]
  have hnotr : ¬ ThinksPrimary s r := fun ht => hpr (hfol.symm.trans ht.1)
  have htp : ∀ x, ThinksPrimary s' x ↔ ThinksPrimary s x := fun x => Iff.rfl
  -- Data on other links is unchanged.
  have hDo : ∀ q x g', (q, x, g') ≠ (p, r, g) → dataOn s' q x g' = dataOn s q x g' := by
    intro q x g' hne
    unfold dataOn; show (s.rnet.erase (.data p r g v rid)).filter _ = _
    apply filter_erase_of_false
    simp only [decide_eq_false_iff_not, RMsg.link, Prod.mk.injEq]
    intro ⟨a, b, c, _⟩; exact hne (by rw [a, b, c])
  have hDs : dataOn s' p r g = tl := hd'
  -- The only open stream into `r` is `p`'s.
  have honly : ∀ q k' g', s.stream q r = some (k', g') → s.rgen q r = g' →
      q = p ∧ k' = k ∧ g' = g := by
    intro q k' g' hs hgq
    obtain ⟨-, hq, -, -⟩ := h.stream q r k' g' hs hgq
    have hqp : q = p := hq.symm.trans hfol
    subst hqp; rw [hk] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs
    exact ⟨rfl, hs.1.symm, hs.2.symm⟩
  exact {
  ackedLeMax := h.ackedLeMax
  ids := fun x => by
    by_cases hx : x = r
    · subst hx; rw [hridr]; exact h.msgIds _ hin rfl
    · rw [hridx x hx]; exact h.ids x
  secIds := h.secIds
  msgIds := fun m hm => h.msgIds m (List.mem_of_mem_erase hm)
  uniqPrim := fun x y hx hy he => by
    have hxr : x ≠ r := fun e => hnotr (e ▸ hx)
    have hyr : y ≠ r := fun e => hnotr (e ▸ hy)
    exact h.uniqPrim x y hx hy (by rw [← hridx x hxr, ← hridx y hyr]; exact he)
  genLe := fun m hm => h.genLe m (List.mem_of_mem_erase hm)
  streamGen := h.streamGen
  stream := by
    intro q x k' g' hs hgq
    have hgq' : s.rgen q x = g' := hgq
    by_cases hxr : x = r
    · subst hxr
      obtain ⟨hq, hk', hg1⟩ := honly q k' g' hs hgq'
      subst hq hk' hg1
      have hpe : pend s' q x g' = tl.map RMsg.val := by unfold pend; rw [hDs]
      refine ⟨hpr, hfol, ?_, ?_⟩
      · rw [hpe, hlogr, hlogx q hpr, List.append_assoc]
        have : [v] ++ tl.map RMsg.val = pend s q x g' := by rw [hpendE]; rfl
        rw [this]; exact hpre
      · rw [hpe, hlogr, ← hlen, hpendE]; simp; omega
    · have hne : (q, x, g') ≠ (p, r, g) := fun e => hxr (by simp only [Prod.mk.injEq] at e; exact e.2.1)
      obtain ⟨h1, h2, h3, h4⟩ := h.stream q x k' g' hs hgq'
      have hpe : pend s' q x g' = pend s q x g' := by unfold pend; rw [hDo q x g' hne]
      exact ⟨h1, h2, by rw [hpe, hlogx x hxr]; exact h3.trans (hgrow q), by rw [hpe, hlogx x hxr]; exact h4⟩
  dataStream := fun m hm => h.dataStream m (List.mem_of_mem_erase hm)
  ackOk := by
    intro x q g' off hm hgg' hk'
    obtain ⟨h1, h2, h3⟩ := h.ackOk x q g' off (List.mem_of_mem_erase hm) hgg' hk'
    refine ⟨h1.trans (hgrow x).length_le, ?_, h3⟩
    rw [← prefix_take_eq (hgrow x) h1]
    exact h2.trans (hgrow q)
  hist := by
    obtain ⟨H, hH⟩ := h.hist
    have h0 : 0 < (dataOn s p r g).length := by rw [hd]; simp
    have hfirst := hH.streamH p r k g hk hgg 0 h0
    simp only [hd, List.getElem_cons_zero, hpendE, List.take_succ_cons, List.take_zero] at hfirst
    refine ⟨H, {
      logH := fun x => by
        by_cases hx : x = r
        · subst hx; rw [hlogr, hridr]; exact hfirst
        · rw [hlogx x hx, hridx x hx]; exact hH.logH x
      ownH := fun x hx => by
        have hxr : x ≠ r := fun e => hnotr (e ▸ hx)
        rw [hridx x hxr, hlogx x hxr]; exact hH.ownH x hx
      secH := fun x t o hx => by
        obtain ⟨h1, h2⟩ := hH.secH x t o hx
        exact ⟨h1.trans (hgrow x).length_le, by rw [← prefix_take_eq (hgrow x) h1]; exact h2⟩
      streamH := ?_ }⟩
    intro q x k' g' hs hgq i hi
    have hgq' : s.rgen q x = g' := hgq
    by_cases hxr : x = r
    · subst hxr
      obtain ⟨hq, hk', hg1⟩ := honly q k' g' hs hgq'
      subst hq hk' hg1
      have hi0 : i < tl.length := by rw [← hDs]; exact hi
      have hi1 : i + 1 < (dataOn s q x g').length := by rw [hd]; simp; exact hi0
      have := hH.streamH q x k' g' hk hgg (i + 1) hi1
      simp only [hd, List.getElem_cons_succ, hpendE, List.take_succ_cons] at this
      have hget : (dataOn s' q x g')[i] = tl[i] := by simp only [hDs]
      have hpe : pend s' q x g' = tl.map RMsg.val := by unfold pend; rw [hDs]
      rw [hget, hpe, hlogr, List.append_assoc, List.singleton_append]
      exact this
    · have hne : (q, x, g') ≠ (p, r, g) := fun e => hxr (by simp only [Prod.mk.injEq] at e; exact e.2.1)
      have hDq := hDo q x g' hne
      unfold pend; simp only [hDq] at hi ⊢; rw [hlogx x hxr]
      have := hH.streamH q x k' g' hs hgq' i hi
      unfold pend at this; exact this }

end SyncReplication

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-- A replica sends an acknowledgement. -/
theorem RInvariant.sendAck {s : State Node} (h : RInvariant s) (r : Node) : RInvariant (sendAckMsg s r) := by
  set p := primaryOf s r with hp
  set m : RMsg Node := .ack r p (s.rgen p r) (s.log r).length with hm
  have hD : ∀ q x g', dataOn (sendAckMsg s r) q x g' = dataOn s q x g' := by
    intro q x g'
    rw [dataOn_append _ s.rnet m q x g' rfl s rfl, if_neg (by simp [m, RMsg.link])]; simp
  have hP : ∀ q x g', pend (sendAckMsg s r) q x g' = pend s q x g' := fun q x g' => by
    unfold pend; rw [hD]
  have hah : ∀ x, s.ackHigh x ≤ (sendAckMsg s r).ackHigh x := fun x => by
    show s.ackHigh x ≤ update s.ackHigh r _ x
    by_cases hx : x = r
    · subst hx; rw [update_self]; exact Nat.le_max_left _ _
    · rw [update_of_ne _ _ hx]
  exact {
  ackedLeMax := h.ackedLeMax
  ids := h.ids, secIds := h.secIds
  msgIds := fun x hx hd => by
    rcases List.mem_append.1 hx with hx | hx
    · exact h.msgIds x hx hd
    · rw [List.mem_singleton] at hx; subst hx; simp [m, RMsg.down, RMsg.link] at hd
  uniqPrim := h.uniqPrim
  genLe := fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · exact h.genLe x hx
    · rw [List.mem_singleton] at hx; subst hx; exact Nat.le_refl _
  streamGen := h.streamGen
  stream := fun q x k g' hs hgq => by
    rw [hP]; exact h.stream q x k g' hs hgq
  dataStream := fun x hx hd => by
    rcases List.mem_append.1 hx with hx | hx
    · exact h.dataStream x hx hd
    · rw [List.mem_singleton] at hx; subst hx; simp [m, RMsg.down, RMsg.link] at hd
  ackOk := by
    intro x q g' off hmem hgg hk
    rcases List.mem_append.1 hmem with hmem | hmem
    · obtain ⟨h1, h2, h3⟩ := h.ackOk x q g' off hmem hgg hk
      exact ⟨h1, h2, h3.trans (hah x)⟩
    · rw [List.mem_singleton] at hmem
      simp only [m, RMsg.ack.injEq] at hmem
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
      obtain ⟨k, hk⟩ := hk
      obtain ⟨-, -, hpre, -⟩ := h.stream _ _ k _ hk rfl
      refine ⟨Nat.le_refl _, ?_, ?_⟩
      · show List.take (s.log x).length (s.log x) <+: s.log (primaryOf s x)
        rw [List.take_length]; exact (List.prefix_append _ _).trans hpre
      · show _ ≤ update s.ackHigh x _ x; rw [update_self]; exact Nat.le_max_right _ _
  hist := by
    obtain ⟨H, hH⟩ := h.hist
    exact ⟨H, { logH := hH.logH, ownH := hH.ownH, secH := hH.secH
                streamH := fun q x k g' hs hgq i hi => by
                  simp only [hD, hP] at hi ⊢; exact hH.streamH q x k g' hs hgq i hi }⟩ }

/-- A primary records an acknowledgement: the message goes, and only the records move,
which this invariant reads only to bound one by the other. -/
theorem RInvariant.recordAck {s : State Node} (h : RInvariant s) (r p : Node) (g off : Nat) :
    RInvariant (SyncReplication.recordAck s (.ack r p g off) p r off) := by
  have hD := dataOn_erase_ack s r p g off
  have hD' : ∀ q x g', dataOn (SyncReplication.recordAck s (.ack r p g off) p r off) q x g' =
      dataOn s q x g' := hD
  have hP : ∀ q x g', pend (SyncReplication.recordAck s (.ack r p g off) p r off) q x g' =
      pend s q x g' := fun q x g' => by unfold pend; rw [hD']
  exact {
  ids := h.ids, secIds := h.secIds
  msgIds := fun m hm => h.msgIds m (List.mem_of_mem_erase hm)
  uniqPrim := h.uniqPrim
  genLe := fun m hm => h.genLe m (List.mem_of_mem_erase hm)
  streamGen := h.streamGen
  stream := fun q x k g' hs hgq => by rw [hP]; exact h.stream q x k g' hs hgq
  dataStream := fun m hm => h.dataStream m (List.mem_of_mem_erase hm)
  ackOk := fun x q g' o hm => h.ackOk x q g' o (List.mem_of_mem_erase hm)
  hist := by
    obtain ⟨H, hH⟩ := h.hist
    exact ⟨H, { logH := hH.logH, ownH := hH.ownH, secH := hH.secH
                streamH := fun q x k g' hs hgq i hi => by
                  simp only [hD', hP] at hi ⊢; exact hH.streamH q x k g' hs hgq i hi }⟩
  ackedLeMax := by
    intro q x
    show update s.acked p (update (s.acked p) r _) q x ≤ update s.ackedMax p (update (s.ackedMax p) r _) q x
    by_cases hq : q = p
    · subst hq; by_cases hx : x = r
      · subst hx; simp only [update, ite_true]; exact max_le_max (h.ackedLeMax _ _) le_rfl
      · simp only [update, ite_true, hx, ite_false]; exact h.ackedLeMax _ _
    · simp only [update, hq, ite_false]; exact h.ackedLeMax _ _ }

/-- PSYNC's check gives what the stream needs: the replica's log is a prefix of the
primary's. The ID and offset name a history (`HistOk`), and the primary holds that
history up to the offset. -/
theorem prefix_of_psyncOk {s : State Node} {H : Nat → List Nat} (hH : HistOk s H) {p r : Node}
    (hok : PsyncOk s p (s.replId r) (s.log r).length) : s.log r <+: s.log p := by
  obtain ⟨hlen, hid | hsec⟩ := hok
  · exact List.prefix_of_prefix_length_le (hH.logH r) (by rw [← hid]; exact hH.logH p) hlen
  · cases h2 : s.replId2 p with
    | none => rw [h2] at hsec; simp at hsec
    | some x =>
      rw [h2] at hsec
      obtain ⟨t, o⟩ := x
      simp only [Option.any_some, decide_eq_true_eq] at hsec
      obtain ⟨rfl, hle⟩ := hsec
      obtain ⟨ho, htake⟩ := hH.secH p _ o h2
      have hr : s.log r = (H (s.replId r)).take (s.log r).length :=
        List.prefix_iff_eq_take.1 (hH.logH r)
      rw [List.prefix_iff_eq_take, hr]
      rw [show (H (s.replId r)).take (s.log r).length = ((H (s.replId r)).take o).take (s.log r).length by
        rw [List.take_take, Nat.min_eq_left hle], ← htake, List.take_take, Nat.min_eq_left hle]
      simp

/-- A replica reconnects and its primary accepts its PSYNC. -/
theorem RInvariant.psync {s : State Node} (h : RInvariant s) {r : Node} (hne : primaryOf s r ≠ r)
    (hok : PsyncOk s (primaryOf s r) (s.replId r) (s.log r).length) : RInvariant (reconnect s r) := by
  set p := primaryOf s r with hp
  have ht := h.closeOne p r
  set t : State Node := { s with rgen := closeLink s.rgen p r } with htdef
  obtain ⟨H, hH⟩ := h.hist
  have hpre : s.log r <+: s.log p := prefix_of_psyncOk hH hok
  have hgr : t.rgen p r = s.rgen p r + 1 := closeLink_self _ _ _
  -- Nothing is in flight on the new connection.
  have hfresh : ∀ m ∈ s.rnet, m.primary = p → m.replica = r → m.g < t.rgen p r := by
    intro m hm h1 h2; have := h.genLe m hm; rw [h1, h2] at this; omega
  have hnil : dataOn t p r (s.rgen p r + 1) = [] := by
    unfold dataOn; rw [List.filter_eq_nil_iff]
    intro m hm; simp only [decide_eq_true_eq]; intro he
    have h1 : m.primary = p := by simp [RMsg.primary, he]
    have h2 : m.replica = r := by simp [RMsg.replica, he]
    have hg' : m.g = s.rgen p r + 1 := by simp [RMsg.g, he]
    have := hfresh m hm h1 h2; rw [hg', hgr] at this; exact Nat.lt_irrefl _ this
  have hst : ∀ q x, (reconnect s r).stream q x =
      if q = p ∧ x = r then some ((s.log r).length, s.rgen p r + 1) else s.stream q x := by
    intro q x
    show update s.stream (primaryOf s r) (update (s.stream (primaryOf s r)) r _) q x = _
    rw [← hp]
    by_cases hq : q = p <;> by_cases hx : x = r <;> simp [update, hq, hx]
  have hD : ∀ q x g', dataOn (reconnect s r) q x g' = dataOn t q x g' := fun _ _ _ => rfl
  have hP : ∀ q x g', pend (reconnect s r) q x g' = pend t q x g' := fun _ _ _ => rfl
  have hpnil : pend t p r (s.rgen p r + 1) = [] := by unfold pend; rw [hnil]; rfl
  have hR : (reconnect s r).rgen = t.rgen := rfl
  exact {
  ackedLeMax := fun q x => by
    show update s.acked p (update (s.acked p) r 0) q x ≤ s.ackedMax q x
    by_cases hq : q = p
    · subst hq; by_cases hx : x = r
      · subst hx; simp only [update, ite_true]; exact Nat.zero_le _
      · simp only [update, ite_true, hx, ite_false]; exact h.ackedLeMax _ _
    · simp only [update, hq, ite_false]; exact h.ackedLeMax _ _
  ids := ht.ids, secIds := ht.secIds, msgIds := ht.msgIds, uniqPrim := ht.uniqPrim, genLe := ht.genLe
  streamGen := by
    intro q x k g' hs
    rw [hst] at hs; split_ifs at hs with hc
    · obtain ⟨hq, hx⟩ := hc; cases hs; rw [hR, hq, hx, hgr]
    · exact ht.streamGen q x k g' hs
  stream := by
    intro q x k g' hs hgg
    rw [hst] at hs; split_ifs at hs with hc
    · obtain ⟨hq, hx⟩ := hc; subst hq hx; cases hs
      refine ⟨hne, rfl, ?_, ?_⟩
      · rw [hP, hpnil, List.append_nil]; exact hpre
      · rw [hP, hpnil]; rfl
    · rw [hP]; exact ht.stream q x k g' hs hgg
  dataStream := by
    intro m hm hd hgg
    rw [hst]; split_ifs with hc
    · obtain ⟨hq, hx⟩ := hc
      have := hfresh m hm hq hx
      have h2 : t.rgen m.primary m.replica = m.g := hgg
      rw [hq, hx] at h2; omega
    · exact ht.dataStream m hm hd hgg
  ackOk := by
    intro x q g' off hm hgg hk
    obtain ⟨k, hk⟩ := hk
    rw [hst] at hk; split_ifs at hk with hc
    · obtain ⟨hq, hx⟩ := hc
      have := hfresh _ hm hq hx
      have h2 : t.rgen q x = g' := hgg
      rw [hq, hx] at h2
      simp only [RMsg.g, RMsg.link] at this; omega
    · exact ht.ackOk x q g' off hm hgg ⟨k, hk⟩
  hist := by
    obtain ⟨H', hH'⟩ := ht.hist
    refine ⟨H', { logH := hH'.logH, ownH := hH'.ownH, secH := hH'.secH, streamH := ?_ }⟩
    intro q x k g' hs hgg i hi
    rw [hst] at hs; split_ifs at hs with hc
    · obtain ⟨hq, hx⟩ := hc; subst hq hx; cases hs
      rw [hD] at hi; rw [hnil] at hi; simp at hi
    · simp only [hD, hP] at hi ⊢; exact hH'.streamH q x k g' hs hgg i hi }

end SyncReplication

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-! ## The other actions -/

theorem RInvariant.commit {s : State Node} (h : RInvariant s) (p : Node) : RInvariant (commitNext s p) :=
  h.frame rfl rfl rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ hx => hx) (fun x => by
    show s.ackHigh x ≤ update s.ackHigh p _ x
    by_cases hx : x = p
    · subst hx; rw [update_self]; exact Nat.le_max_left _ _
    · rw [update_of_ne _ _ hx])

theorem RInvariant.addToSyncSet {s : State Node} (h : RInvariant s) (p r : Node) :
    RInvariant (addToSyncSet s p r) :=
  h.frame rfl rfl rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ hx => hx) (fun _ => Nat.le_refl _)

theorem RInvariant.removeFromSyncSet {s : State Node} (h : RInvariant s) (p r : Node) :
    RInvariant (removeFromSyncSet s p r) :=
  h.frame rfl rfl rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ hx => hx) (fun _ => Nat.le_refl _)

/-- A primary that knows the latest configuration replaces its copy with one that has the
same primary; the incarnation it records for itself does not change. -/
theorem RInvariant.cfgBump {s : State Node} (hi : Invariant s) (h : RInvariant s) {p : Node}
    (hp : ThinksPrimary s p) (hk : KnowsLatest s p) (c : Cfg Node) (hcp : c.primary = s.cfg.primary)
    (hci : c.incarnation p = s.cfg.incarnation p) (sy : Node → Node → Bool) (s' : State Node)
    (hs' : s' = { s with cfg := c, localCfg := update s.localCfg p c, sync := sy }) : RInvariant s' := by
  have hpp := knowsLatest_iff_prim hi hp hk
  have hlc := hi.localCfgEq p hk
  subst hs'
  refine h.frame rfl rfl rfl rfl rfl rfl rfl ?_ ?_ (fun _ => Nat.le_refl _)
  · intro x; show (update s.localCfg p c x).primary = _
    by_cases hx : x = p
    · subst hx; rw [update_self, hcp, hlc]
    · rw [update_of_ne _ _ hx]
  · intro x hx
    by_cases hxp : x = p
    · subst hxp; exact hp
    · unfold ThinksPrimary at hx ⊢; simpa [update_of_ne _ _ hxp] using hx

theorem RInvariant.makeEligible {s : State Node} (hi : Invariant s) (h : RInvariant s) {p r : Node}
    (hp : ThinksPrimary s p) (hk : KnowsLatest s p) (hsy : s.sync p r = true) : RInvariant (makeEligible s p r) := by
  have hrp : r ≠ p := fun e => by subst e; rw [hi.noSelfSync] at hsy; exact absurd hsy (by decide)
  exact h.cfgBump hi hp hk (makeEligibleCfg s r) rfl (by simp [makeEligibleCfg, update, hrp.symm]) _ _ rfl

theorem RInvariant.makeIneligible {s : State Node} (hi : Invariant s) (h : RInvariant s) {p r : Node}
    (hp : ThinksPrimary s p) (hk : KnowsLatest s p) : RInvariant (makeIneligible s p r) :=
  h.cfgBump hi hp hk (makeIneligibleCfg s r) rfl rfl _ _ rfl

/-- Learning the latest configuration makes no node newly think it is primary. -/
theorem thinks_learn {s : State Node} (hi : Invariant s) {n : Node} (hnkl : ¬ KnowsLatest s n) {x : Node}
    (hx : ThinksPrimary (learn s n) x) : ThinksPrimary s x := by
  by_cases hxn : x = n
  · exfalso; apply hnkl
    have hx' : s.cfg.primary = x := by have := hx.1; simpa [learn, hxn] using this
    unfold KnowsLatest; rw [← hxn, ← hx', hi.primKnows]
  · unfold ThinksPrimary at hx ⊢; simpa [learn, update_of_ne _ _ hxn] using hx

/-- A step that moves no log, ID, message or stream, raises generations only so that
every connection open after was open before and none into `n` is open, changes only
`n`'s primary, and creates no node that thinks it is primary. -/
theorem RInvariant.frameInto {s s' : State Node} (h : RInvariant s) (n : Node)
    (hlog : s'.log = s.log) (hrid : s'.replId = s.replId) (hrid2 : s'.replId2 = s.replId2)
    (hids : s'.usedIds = s.usedIds) (hnet : s'.rnet = s.rnet) (hst : s'.stream = s.stream)
    (hg : s'.rgen = closeInto s.rgen n)
    (hprim : ∀ x, x ≠ n → (s'.localCfg x).primary = (s.localCfg x).primary)
    (htp : ∀ x, ThinksPrimary s' x → ThinksPrimary s x) (hah : ∀ x, s.ackHigh x ≤ s'.ackHigh x)
    (hA : s'.acked = s.acked := by rfl) (hAM : s'.ackedMax = s.ackedMax := by rfl) :
    RInvariant s' := by
  have hdata := dataOn_of_rnet hnet
  have hpend := pend_of_rnet hnet
  have hop : ∀ x y g, g ≤ s.rgen x y → s'.rgen x y = g → y ≠ n ∧ s.rgen x y = g :=
    fun x y g hle he => closeInto_open hle (hg ▸ he)
  have hle : ∀ x y, s.rgen x y ≤ s'.rgen x y := fun x y => by rw [hg]; exact le_closeInto _ _ _ _
  exact {
  ackedLeMax := fun q x => by rw [hA, hAM]; exact h.ackedLeMax q x
  ids := fun x => by rw [hrid, hids]; exact h.ids x
  secIds := fun x t o hx => by rw [hids]; rw [hrid2] at hx; exact h.secIds x t o hx
  msgIds := fun m hm hd => by rw [hids]; exact h.msgIds m (hnet ▸ hm) hd
  uniqPrim := fun p q hp hq he => h.uniqPrim p q (htp p hp) (htp q hq) (by rw [← hrid]; exact he)
  genLe := fun m hm => (h.genLe m (hnet ▸ hm)).trans (hle _ _)
  streamGen := fun p r k g hs => (h.streamGen p r k g (hst ▸ hs)).trans (hle _ _)
  stream := fun p r k g hs hgg => by
    rw [hst] at hs
    obtain ⟨hrn, hg0⟩ := hop p r g (h.streamGen p r k g hs) hgg
    obtain ⟨h1, h2, h3, h4⟩ := h.stream p r k g hs hg0
    exact ⟨h1, by rw [hprim r hrn]; exact h2, by rw [hlog, hpend]; exact h3, by rw [hlog, hpend]; exact h4⟩
  dataStream := fun m hm hd hgg => by
    rw [hst]; rw [hnet] at hm
    exact h.dataStream m hm hd (hop _ _ _ (h.genLe m hm) hgg).2
  ackOk := fun r p g off hm hgg hk => by
    rw [hst] at hk; rw [hnet] at hm
    obtain ⟨h1, h2, h3⟩ := h.ackOk r p g off hm (hop p r g (h.genLe _ hm) hgg).2 hk
    rw [hlog]; exact ⟨h1, h2, h3.trans (hah r)⟩
  hist := by
    obtain ⟨H, hH⟩ := h.hist
    exact ⟨H, {
      logH := fun x => by rw [hlog, hrid]; exact hH.logH x
      ownH := fun p hp => by rw [hlog, hrid]; exact hH.ownH p (htp p hp)
      secH := fun x t o hx => by rw [hlog]; rw [hrid2] at hx; exact hH.secH x t o hx
      streamH := fun p r k g hs hgg i hi => by
        rw [hst] at hs
        have hg0 := (hop p r g (h.streamGen p r k g hs) hgg).2
        simp only [hdata, hpend, hlog] at hi ⊢
        exact hH.streamH p r k g hs hg0 i hi }⟩ }

theorem RInvariant.learn {s : State Node} (hi : Invariant s) (h : RInvariant s) {n : Node}
    (hnkl : ¬ KnowsLatest s n) : RInvariant (learn s n) := by
  by_cases hp : s.cfg.primary = (s.localCfg n).primary
  · refine h.frame rfl rfl rfl rfl (by simp [SyncReplication.learn, hp]) rfl rfl ?_ (fun _ hx => thinks_learn hi hnkl hx)
      (fun _ => Nat.le_refl _)
    intro x; by_cases hx : x = n
    · subst hx; simp [SyncReplication.learn, hp]
    · simp [SyncReplication.learn, update, hx]
  · exact h.frameInto n rfl rfl rfl rfl rfl rfl (by simp [SyncReplication.learn, hp])
      (fun x hx => by simp [SyncReplication.learn, update, hx]) (fun _ hx => thinks_learn hi hnkl hx)
      (fun _ => Nat.le_refl _)

/-- A fresh ID for a node: its history is its log, and no fact reads it before. -/
theorem fresh_hist {s : State Node} (h : RInvariant s) {H : Nat → List Nat} (L : List Nat) :
    (∀ t ∈ s.usedIds, update H (freshId s) L t = H t) ∧ update H (freshId s) L (freshId s) = L :=
  ⟨fun t ht => update_of_ne _ _ (fun e => freshId_not_mem s (e ▸ ht)), update_self _ _ _⟩

theorem RInvariant.takeover {s : State Node} (h : RInvariant s) (n : Node) : RInvariant (takeover s n) := by
  have hrid : (SyncReplication.takeover s n).replId n = freshId s := by simp [SyncReplication.takeover]
  exact h.reset n (fun _ _ => rfl) (fun x hx => by simp [SyncReplication.takeover, update, hx])
    (fun x hx => by simp [SyncReplication.takeover, update, hx])
    (fun x hx => by simp [SyncReplication.takeover, update, hx]) (fun _ _ => rfl) (fun _ _ => Nat.le_refl _)
    (Finset.subset_insert _ _) (by rw [hrid]; exact Finset.mem_insert_self _ _)
    (fun t o ht => by
      simp [SyncReplication.takeover] at ht; obtain ⟨rfl, -⟩ := ht; exact Finset.mem_insert_of_mem (h.ids n))
    rfl rfl rfl
    (fun _ => Or.inr (by rw [hrid]; exact freshId_not_mem s))
    (fun H hH => by
      obtain ⟨hsame, hnew⟩ := fresh_hist h (H := H) (s.log n)
      refine ⟨update H (freshId s) (s.log n), hsame, ?_, ?_, ?_⟩
      · show s.log n <+: _; rw [hrid, hnew]
      · intro _; show _ = s.log n; rw [hrid, hnew]
      · intro t o ht
        simp [SyncReplication.takeover] at ht; obtain ⟨rfl, rfl⟩ := ht
        refine ⟨Nat.le_refl _, ?_⟩
        show (s.log n).take _ = _
        rw [hsame _ (h.ids n), List.take_length]
        exact (List.prefix_iff_eq_take.1 (hH.logH n)))
    (fun q x => by simp only [SyncReplication.takeover, update]; ack_le h.ackedLeMax)

theorem RInvariant.resync {s : State Node} (h : RInvariant s) {r : Node} (hne : primaryOf s r ≠ r) :
    RInvariant (resync s r) :=
  h.reset r (fun x hx => by simp [SyncReplication.resync, update, hx])
    (fun x hx => by simp [SyncReplication.resync, update, hx]) (fun x hx => by simp [SyncReplication.resync, update, hx])
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => Nat.le_refl _) (Finset.Subset.refl _)
    (by simp only [SyncReplication.resync, update_self]; exact h.ids _)
    (fun t o ht => by simp [SyncReplication.resync] at ht)
    rfl rfl rfl
    (fun hp => absurd hp.1 hne)
    (fun H hH => ⟨H, fun _ _ => rfl, by
      show update s.log r _ r <+: H (update s.replId r _ r)
      rw [update_self, update_self]
      exact (List.take_prefix _ _).trans (hH.logH _),
      fun hp => absurd hp.1 hne, fun t o ht => by simp [SyncReplication.resync] at ht⟩)
    (fun q x => by simp only [SyncReplication.resync, update]; ack_le h.ackedLeMax)

end SyncReplication

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-- A restart: `n` keeps the first `k` entries of its log, takes a fresh ID with its old
one valid up to `k`, and its connections close; no other node's state that this
invariant reads changes. -/
theorem RInvariant.restart {s s' : State Node} (h : RInvariant s) (n : Node) (k : Nat) (hk : k ≤ (s.log n).length)
    (hlogn : s'.log n = (s.log n).take k) (hlog : ∀ x, x ≠ n → s'.log x = s.log x)
    (hridn : s'.replId n = freshId s) (hrid : ∀ x, x ≠ n → s'.replId x = s.replId x)
    (hsec : ∀ t o, s'.replId2 n = some (t, o) → t = s.replId n ∧ o = k)
    (hrid2 : ∀ x, x ≠ n → s'.replId2 x = s.replId2 x)
    (hids : s'.usedIds = insert (freshId s) s.usedIds)
    (hcfgx : ∀ x, x ≠ n → s'.localCfg x = s.localCfg x) (hincx : ∀ x, x ≠ n → s'.incarnation x = s.incarnation x)
    (hah : ∀ x, x ≠ n → s'.ackHigh x = s.ackHigh x)
    (hg : s'.rgen = closeAll s.rgen n)
    (hnet : s'.rnet = s.rnet) (hst : s'.stream = s.stream)
    (hak : ∀ p r, s'.acked p r ≤ s'.ackedMax p r) : RInvariant s' :=
  h.reset n hlog hrid hrid2 hcfgx hincx (fun x hx => by rw [hah x hx]) (by rw [hids]; exact Finset.subset_insert _ _)
    (by rw [hridn, hids]; exact Finset.mem_insert_self _ _)
    (fun t o ht => by
      obtain ⟨rfl, -⟩ := hsec t o ht; rw [hids]; exact Finset.mem_insert_of_mem (h.ids n))
    hg hnet hst
    (fun _ => Or.inr (by rw [hridn]; exact freshId_not_mem s))
    (fun H hH => by
      obtain ⟨hsame, hnew⟩ := fresh_hist h (H := H) ((s.log n).take k)
      refine ⟨update H (freshId s) ((s.log n).take k), hsame, ?_, ?_, ?_⟩
      · rw [hridn, hnew, hlogn]
      · intro _; rw [hridn, hnew, hlogn]
      · intro t o ht
        obtain ⟨rfl, rfl⟩ := hsec t o ht
        refine ⟨by rw [hlogn, List.length_take, Nat.min_eq_left hk], ?_⟩
        rw [hlogn, List.take_take, Nat.min_self, hsame _ (h.ids n)]
        exact prefix_take_eq (hH.logH n) hk) hak

theorem RInvariant.restartEmpty {s : State Node} (h : RInvariant s) (n : Node) :
    RInvariant (restartEmpty s n) :=
  h.restart n 0 (Nat.zero_le _) (by simp [SyncReplication.restartEmpty])
    (fun x hx => by simp [SyncReplication.restartEmpty, update, hx]) (by simp [SyncReplication.restartEmpty])
    (fun x hx => by simp [SyncReplication.restartEmpty, update, hx])
    (fun t o ht => by simp [SyncReplication.restartEmpty] at ht)
    (fun x hx => by simp [SyncReplication.restartEmpty, update, hx]) rfl (fun _ _ => rfl)
    (fun x hx => by simp [SyncReplication.restartEmpty, update, hx])
    (fun x hx => by simp [SyncReplication.restartEmpty, update, hx])
    rfl rfl rfl (fun q x => by simp only [SyncReplication.restartEmpty, update]; ack_le h.ackedLeMax)

/-- A restart of a replica: `n` keeps the first `k` entries and its ID, drops its
secondary ID, and its connections close. -/
theorem RInvariant.restartKeepId {s s' : State Node} (h : RInvariant s) (n : Node) (k : Nat)
    (hrep : (s.localCfg n).primary ≠ n)
    (hlogn : s'.log n = (s.log n).take k) (hlog : ∀ x, x ≠ n → s'.log x = s.log x)
    (hrid : s'.replId = s.replId) (hsec : s'.replId2 n = none) (hrid2 : ∀ x, x ≠ n → s'.replId2 x = s.replId2 x)
    (hids : s'.usedIds = s.usedIds) (hcfg : s'.localCfg = s.localCfg)
    (hincx : ∀ x, x ≠ n → s'.incarnation x = s.incarnation x)
    (hah : ∀ x, x ≠ n → s'.ackHigh x = s.ackHigh x)
    (hg : s'.rgen = closeAll s.rgen n)
    (hnet : s'.rnet = s.rnet) (hst : s'.stream = s.stream)
    (hak : ∀ p r, s'.acked p r ≤ s'.ackedMax p r) : RInvariant s' :=
  h.reset n hlog (fun _ _ => by rw [hrid]) hrid2 (fun _ _ => by rw [hcfg]) hincx (fun x hx => by rw [hah x hx])
    (by rw [hids]) (by rw [hrid, hids]; exact h.ids n) (fun t o ht => by rw [hsec] at ht; cases ht)
    hg hnet hst
    (fun hp => absurd (by rw [← hcfg]; exact hp.1) hrep)
    (fun H hH => ⟨H, fun _ _ => rfl, by rw [hlogn, hrid]; exact (List.take_prefix _ _).trans (hH.logH n),
      fun hp => absurd (by rw [← hcfg]; exact hp.1) hrep, fun t o ht => by rw [hsec] at ht; cases ht⟩) hak

/-- A restart with `k` entries kept, the IDs from `restartIds`. -/
theorem RInvariant.restartWith {s s' : State Node} (h : RInvariant s) (n : Node) (k : Nat) (hk : k ≤ (s.log n).length)
    (hlogn : s'.log n = (s.log n).take k) (hlog : ∀ x, x ≠ n → s'.log x = s.log x)
    (hR : s'.replId = (restartIds s n k).1) (hU : s'.usedIds = (restartIds s n k).2.1)
    (hR2 : s'.replId2 = (restartIds s n k).2.2) (hcfg : s'.localCfg = s.localCfg)
    (hincx : ∀ x, x ≠ n → s'.incarnation x = s.incarnation x)
    (hah : ∀ x, x ≠ n → s'.ackHigh x = s.ackHigh x)
    (hg : s'.rgen = closeAll s.rgen n)
    (hnet : s'.rnet = s.rnet) (hst : s'.stream = s.stream)
    (hak : ∀ p r, s'.acked p r ≤ s'.ackedMax p r) : RInvariant s' := by
  by_cases hp : (s.localCfg n).primary = n
  · simp only [restartIds, hp, if_true] at hR hU hR2
    exact h.restart n k hk hlogn hlog (by rw [hR]; simp) (fun x hx => by rw [hR]; simp [update, hx])
      (fun t o ht => by rw [hR2] at ht; simp at ht; exact ⟨ht.1.symm, ht.2.symm⟩)
      (fun x hx => by rw [hR2]; simp [update, hx]) hU
      (fun x _ => by rw [hcfg]) hincx hah hg hnet hst hak
  · simp only [restartIds, hp, if_false] at hR hU hR2
    exact h.restartKeepId n k hp hlogn hlog hR (by rw [hR2]; simp) (fun x hx => by rw [hR2]; simp [update, hx])
      hU hcfg hincx hah hg hnet hst hak

theorem RInvariant.restartKeep {s : State Node} (h : RInvariant s) (n : Node) :
    RInvariant (restartKeep s n) :=
  h.restartWith n (s.log n).length (Nat.le_refl _) (by simp [SyncReplication.restartKeep])
    (fun _ _ => rfl) rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    rfl rfl rfl (fun q x => by simp only [SyncReplication.restartKeep, update]; ack_le h.ackedLeMax)

theorem RInvariant.restartPartialKeep {s : State Node} (h : RInvariant s) (n : Node) {k : Nat}
    (hk : k < (s.log n).length) : RInvariant (restartPartialKeep s n k) := by
  have hR : (restartIds s n (s.log n).length).1 = (restartIds s n k).1 := by
    unfold restartIds; split <;> rfl
  have hU : (restartIds s n (s.log n).length).2.1 = (restartIds s n k).2.1 := by
    unfold restartIds; split <;> rfl
  exact h.restartWith n k hk.le (by simp [SyncReplication.restartPartialKeep])
    (fun x hx => by simp [SyncReplication.restartPartialKeep, update, hx]) hR hU rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    rfl rfl rfl (fun q x => by simp only [SyncReplication.restartPartialKeep, SyncReplication.restartKeep, update]; ack_le h.ackedLeMax)

theorem RInvariant.restartPartialFresh {s : State Node} (h : RInvariant s) (n : Node) {k : Nat}
    (hk : k < (s.log n).length) : RInvariant (restartPartialFresh s n k) :=
  h.restartWith n k hk.le (by simp [SyncReplication.restartPartialFresh])
    (fun x hx => by simp [SyncReplication.restartPartialFresh, update, hx]) rfl rfl rfl rfl
    (fun x hx => by simp [SyncReplication.restartPartialFresh, SyncReplication.restartEmpty, update, hx])
    (fun x hx => by simp [SyncReplication.restartPartialFresh, SyncReplication.restartEmpty, update, hx])
    rfl rfl rfl (fun q x => by simp only [SyncReplication.restartPartialFresh, SyncReplication.restartEmpty, update]; ack_le h.ackedLeMax)

end SyncReplication

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-! ## Every step of the delayed model preserves both invariants -/

theorem invariants_step {m : Nat} {s s' : State Node} {μ : Action Node} (hi : Invariant s) (hr : RInvariant s)
    (hs : Step m s μ s') : Invariant s' ∧ RInvariant s' := by
  cases hs with
  | append p hp _ => exact ⟨invariant_append hi p, hr.append hp⟩
  | commit p hp _ hlen hcap =>
    exact ⟨invariant_commit hi p hp hlen (fun r hs => Nat.lt_of_lt_of_le (hcap r hs) (hr.ackedLeMax p r)),
      hr.commit p⟩
  | addToSyncSet p r hp hrp hf _ hle =>
    exact ⟨invariant_addToSyncSet hi p r hp hrp hf (hle.trans (hr.ackedLeMax p r)), hr.addToSyncSet p r⟩
  | removeFromSyncSet p r hp hsy hel => exact ⟨invariant_removeFromSyncSet hi p r hp hsy hel, hr.removeFromSyncSet p r⟩
  | makeEligible p r hp hkl hsy hel => exact ⟨invariant_makeEligible hi hp hkl hsy hel, hr.makeEligible hi hp hkl hsy⟩
  | makeIneligible p r hp hkl hel => exact ⟨invariant_makeIneligible hi hp hkl hel, hr.makeIneligible hi hp hkl⟩
  | learn n hnkl => exact ⟨invariant_learn hi n hnkl, hr.learn hi hnkl⟩
  | takeover n hkl hel hnp hin => exact ⟨invariant_takeover hi n hkl hel hnp hin, hr.takeover n⟩
  | resync r hne hsy hke => exact ⟨invariant_resync hi r hne hsy hke, hr.resync hne⟩
  | restartEmpty n hkl hsurv => exact ⟨invariant_restartEmpty hi n hkl hsurv, hr.restartEmpty n⟩
  | restartKeep n hkl => exact ⟨invariant_restartKeep hi n hkl, hr.restartKeep n⟩
  | restartPartialKeep n k hkl hk hkeep =>
    exact ⟨invariant_restartPartialKeep hi n k hkl hk hkeep, hr.restartPartialKeep n hk⟩
  | restartPartialFresh n k hkl hk hfresh hsurv =>
    exact ⟨invariant_restartPartialFresh hi n k hkl hsurv hk hfresh, hr.restartPartialFresh n hk⟩
  | psync r hne _ hok => exact ⟨hi.net_frame _ _ _ _ _ _ _, hr.psync hne hok⟩
  | sendData p r k hst hk => exact ⟨hi.net_frame _ _ _ _ _ _ _, hr.sendData hst hk⟩
  | deliverData p r g v rid hin hcur hf _ =>
    exact ⟨(invariant_grow hi _ (grow_upd s.log r [v])).net_frame _ _ _ _ _ _ _, hr.deliverData hin hcur hf⟩
  | sendAck r _ =>
    refine ⟨((hi.ackHigh_mono (update s.ackHigh r (max (s.ackHigh r) (s.log r).length)) fun x => ?_).net_frame
      _ _ _ _ _ _ _), hr.sendAck r⟩
    show s.ackHigh x ≤ update s.ackHigh r _ x
    by_cases hx : x = r
    · subst hx; rw [update_self]; exact Nat.le_max_left _ _
    · rw [update_of_ne _ _ hx]
  | deliverAck r p g off k hin hcur _ hst =>
    refine ⟨?_, hr.recordAck r p g off⟩
    have hgg : s.rgen p r = g := hcur
    obtain ⟨h1, h2, h3⟩ := hr.ackOk r p g off hin hgg ⟨k, hst⟩
    obtain ⟨hpr, hfol, -, -⟩ := hr.stream p r k g hst hgg
    set A := update s.acked p (update (s.acked p) r (max (s.acked p r) off))
    by_cases hle : off ≤ s.ackedMax p r
    · have he : update s.ackedMax p (update (s.ackedMax p) r (max (s.ackedMax p r) off)) = s.ackedMax := by
        funext q x
        by_cases hq : q = p
        · subst hq; by_cases hx : x = r
          · subst hx; simp [update, Nat.max_eq_left hle]
          · simp [update, hx]
        · simp [update, hq]
      have := hi.net_frame s.replId s.usedIds s.replId2 (s.rnet.erase (.ack r p g off)) s.stream s.rgen A
      show Invariant { s with rnet := _, acked := _, ackedMax := _ }
      rw [he]; exact this
    · have hm : max (s.ackedMax p r) off = off := Nat.max_eq_right (by omega)
      have := (invariant_raiseAck hi hfol hpr h1 h2 h3 (by omega)).net_frame s.replId s.usedIds s.replId2
        (s.rnet.erase (.ack r p g off)) s.stream s.rgen A
      show Invariant { s with rnet := _, acked := _, ackedMax := _ }
      rw [hm]; exact this
  | dropMsg msg hin => exact ⟨hi.net_frame _ _ _ _ _ _ _, hr.lose hin⟩

end SyncReplication
