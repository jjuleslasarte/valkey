import SyncReplication.Leases
import SyncReplication.Preserve

/-!
# No stale linearizable read

The invariant of the lease layer and the theorem `noStaleRead`: whenever a node may
serve a linearizable read, its log is exactly the committed history.

## The argument

**Primary reads.** A primary that holds a valid lease from every eligible replica it
knows of is the *current* primary. Why: a deposed primary `p` was deposed by a takeover
of some `t`. `p` was current then, so it knew the latest configuration (`primKnows`),
and `t`'s takeover checked `t`'s eligibility in that same configuration: `t` is
eligible in `p`'s configuration. `t` waited until `p`'s lease must have expired,
measured from the last traffic `t` received from `p`, and `p`'s lease from `t` started
no later than that traffic. `t` now follows someone else, so its acknowledgements never
reach `p` again and the lease is never renewed: it is over for good (`deposed`), and
`p` cannot hold a valid lease from every eligible replica it knows. The current primary, by the
replication invariant, has the whole committed history below its committed offset or
its catch-up point; with nothing uncommitted, its log is the history.

**Replica reads.** A read lease is granted only by a primary that holds its own lease,
hence by the current primary, and only to an eligible replica with a matching
incarnation (`leaseAuth`: a valid read lease implies the holder is authoritative).
Demotion waits until the lease must have expired; a new primary waits one read lease
plus the margin after its takeover before demoting anyone, and every lease granted
before the takeover started before it (`leaseBound`). An authoritative node holds the
whole history (`eligibleHoldsCommitted`), and a replica's committed view is a committed prefix of its log
(`committedViewHist`); with nothing uncommitted, its log is the history.

Both arguments need `margin ≥ 2 · drift`. A holder assumes its clock slow and a grantor
assumes its clock fast, each by `drift`, so the two worst cases are `2 · drift` apart;
the margin covers the gap. It is used in exactly two places: `deposed_not_leaseValid`
(the taker's wait makes `p`'s lease from `t` invalid) and the acknowledgement branch of
`lease_over_of_guards` (the demotion wait makes the read lease invalid).

Two conjuncts that look like bookkeeping carry weight. `primarySinceAck` (every
acknowledgement a primary holds arrived during its current primaryship) is what lets a
read lease bounded by the takeover time (`leaseBound`'s second case) be renewed into one
bounded by an acknowledgement. `selfPrimNoLease` (a node whose configuration names it
primary holds no read lease) keeps the deposed primary out of the read-lease holders,
which `leaseAuth` needs to survive a takeover or a Learn.

## Reading the preservation proofs

Most actions move few fields. The frame lemmas say which conjuncts survive which kind
of change: `leaseInvariant_frame` for a replication step that moves no lease state
(data messages, resync, the plain actions), `deposed_frame` and `deposed_cfgBump` for
the deposed primary's witness, `cleared_rows` for a node whose lease rows are cleared
(takeover, restart), `committedView_reset` for a node whose view starts over (resync,
restart), `primaryTraffic_bump` for a node whose traffic timer restarts. Each
preservation proof is then left with the conjuncts its action touches: the renewal of a
read lease in `heartbeatGrant`, the deposed primary's new witness and the bound on
existing read leases in `takeover`, the two demotion waits in `demote`.
-/

open Cslib

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-! ## Facts about updates and about the replication state -/

theorem update2_self {β : Type} (f : Node → Node → β) (p r : Node) (b : β) :
    update2 f p r b p r = b := by simp [update2, update]

theorem update2_of_ne {β : Type} (f : Node → Node → β) {p r q x : Node} (b : β)
    (h : ¬ (q = p ∧ x = r)) : update2 f p r b q x = f q x := by
  unfold update2 update
  by_cases hq : q = p
  · subst hq; have : x ≠ r := fun e => h ⟨rfl, e⟩; simp [this]
  · simp [hq]

/-- After clearing `n`'s entry, any value left is an old one at another node. -/
theorem update_none_some {β : Type} (f : Node → Option β) (n r : Node) {b : β}
    (hb : update f n none r = some b) : r ≠ n ∧ f r = some b := by
  by_cases e : r = n
  · subst e; rw [update_self] at hb; exact absurd hb (by simp)
  · rw [update_of_ne _ _ e] at hb; exact ⟨e, hb⟩

/-- After clearing `n`'s row, any value left is an old one in another row. -/
theorem update_row_some {β : Type} (f : Node → Node → Option β) (n q r : Node) {b : β}
    (hb : update f n (fun _ => none) q r = some b) : q ≠ n ∧ f q r = some b := by
  by_cases e : q = n
  · subst e; rw [update_self] at hb; exact absurd hb (by simp)
  · rw [update_of_ne _ _ e] at hb; exact ⟨e, hb⟩

/-- Whether a node thinks it is primary depends only on its copy of the configuration
and its incarnation. -/
theorem thinksPrimary_congr {s c : State Node} {x : Node} (hlocalCfg : c.localCfg = s.localCfg)
    (hinc : c.incarnation x = s.incarnation x) : ThinksPrimary c x ↔ ThinksPrimary s x := by
  unfold ThinksPrimary; rw [hlocalCfg, hinc]

/-- Whether a node is authoritative depends only on the configuration and its
incarnation. -/
theorem isAuthoritative_congr {s c : State Node} {x : Node} (hcfg : c.cfg = s.cfg)
    (hinc : c.incarnation x = s.incarnation x) : IsAuthoritative c x ↔ IsAuthoritative s x := by
  unfold IsAuthoritative; rw [hcfg, hinc]

/-! ## The invariant -/

/-- The inductive invariant of the lease layer. -/
structure LeaseInvariant (P : LeaseParams) (a : LeaseState Node) : Prop where
  /-- The replication invariant. -/
  core : Invariant a.core
  /-- Every recorded time is in the past. -/
  primaryTrafficLe : ∀ r, a.primaryTraffic r ≤ a.now
  ackReceivedLe  : ∀ p r b, a.ackReceived p r = some b → b ≤ a.now
  primarySinceLe      : ∀ p T, a.primarySince p = some T → T ≤ a.now
  /-- The data a replica would acknowledge was sent no later than its last traffic. -/
  dataSentLe    : ∀ r, a.dataSent r ≤ a.primaryTraffic r
  /-- A primary lease starts no later than the holder's last traffic to the grantor. -/
  primaryLeaseLe       : ∀ p r x, a.primaryLease p r = some x → x ≤ a.primaryTraffic r
  /-- The acknowledgement a primary would echo was sent no later than it was received. -/
  echoLe     : ∀ p r e, a.ackEcho p r = some e → ∃ b, a.ackReceived p r = some b ∧ e ≤ b
  /-- Every acknowledgement a primary holds arrived during its current primaryship, or
  the replica is still marked as one of the old configuration (so the demotion wait
  covers it). Lets a read lease bounded by the takeover time be renewed into one bounded
  by an acknowledgement (`leaseBound`). The second disjunct lets a restart keep its
  grantor rows (`RestartGrantorRows.lean`). -/
  primarySinceAck     : ∀ p r T b, a.primarySince p = some T → a.ackReceived p r = some b →
    T ≤ b ∨ a.oldEligible p r = true
  /-- A deposed primary's lease from the replica that deposed it is over for good. That
  replica is eligible in the deposed primary's configuration and follows someone else,
  so its acknowledgements never reach the deposed primary again and the lease is never
  renewed. -/
  deposed    : ∀ p, ThinksPrimary a.core p → (a.core.localCfg p).epoch < a.core.cfg.epoch →
    ∃ t, t ≠ p ∧ (a.core.localCfg p).eligible t = true ∧ (a.core.localCfg t).primary ≠ p ∧
      ∀ x, a.primaryLease p t = some x → x + P.primDur ≤ a.now + P.drift
  /-- A read lease started no later than the current primary's last acknowledgement from
  its holder, or no later than the current primary's takeover; in the latter case the
  holder was eligible in the configuration the takeover replaced, or the lease has
  already expired. -/
  leaseBound : ∀ r x, a.readLease r = some x →
    (∃ b, a.ackReceived a.core.cfg.primary r = some b ∧ x ≤ b) ∨
    (∃ T, a.primarySince a.core.cfg.primary = some T ∧ x ≤ T ∧
      (a.oldEligible a.core.cfg.primary r = true ∨ ¬ HolderValid P a.now (some x) P.readDur))
  /-- A replica with a valid read lease is authoritative. -/
  leaseAuth  : ∀ r, ¬ ThinksPrimary a.core r → ReadLeaseValid P a r → IsAuthoritative a.core r
  /-- A node whose configuration names it primary holds no read lease. Keeps a deposed
  primary out of the read-lease holders, which `leaseAuth` needs across Takeover and
  Learn. -/
  selfPrimNoLease : ∀ p, (a.core.localCfg p).primary = p → a.readLease p = none
  /-- A replica's committed view is within its log and is a committed prefix. -/
  committedViewLen   : ∀ r, a.committedView r ≤ (a.core.log r).length
  committedViewHist  : ∀ r, a.committedView r ≤ a.core.hist.length ∧ (a.core.log r).take (a.committedView r) <+: a.core.hist

/-- Every read lease started in the past. A lease is bounded by an acknowledgement time
or a primaryship start (`leaseBound`), and both are in the past (`ackReceivedLe`,
`primarySinceLe`). Formerly a conjunct of `LeaseInvariant`. -/
theorem LeaseInvariant.readLeaseLe {P : LeaseParams} {a : LeaseState Node} (h : LeaseInvariant P a) :
    ∀ r x, a.readLease r = some x → x ≤ a.now := by
  intro r x hx
  rcases h.leaseBound r x hx with ⟨b, hb, hxb⟩ | ⟨T, hT, hxT, _⟩
  · exact hxb.trans (h.ackReceivedLe _ r b hb)
  · exact hxT.trans (h.primarySinceLe _ T hT)

theorem leaseInvariant_init (P : LeaseParams) (i : Node) : LeaseInvariant P (leaseInit i) where
  core := invariant_init i
  primaryTrafficLe := fun _ => Nat.le_refl _
  ackReceivedLe := by intro _ _ _ h; simp [leaseInit] at h
  primarySinceLe := by intro _ _ h; simp [leaseInit] at h
  dataSentLe := fun _ => Nat.le_refl _
  primaryLeaseLe := by intro _ _ _ h; simp [leaseInit] at h
  echoLe := by intro _ _ _ h; simp [leaseInit] at h
  primarySinceAck := by intro _ _ _ _ h; simp [leaseInit] at h
  deposed := by intro p _ hv; simp [leaseInit, init, initCfg] at hv
  leaseBound := by intro _ _ h; simp [leaseInit] at h
  leaseAuth := by intro r _ hv; simp [ReadLeaseValid, HolderValid, leaseInit] at hv
  selfPrimNoLease := by intro _ _; rfl
  committedViewLen := by intro _; simp [leaseInit]
  committedViewHist := by intro _; simp [leaseInit, init]

/-! ## The current primary is the only one that can hold its lease -/

/-- A deposed primary holds no valid primary lease, since its lease from the replica that
deposed it is over, and that replica is eligible in its configuration. -/
theorem deposed_not_leaseValid {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {a : LeaseState Node}
    (h : LeaseInvariant P a) {p : Node} (hp : ThinksPrimary a.core p)
    (hv : (a.core.localCfg p).epoch < a.core.cfg.epoch) : ¬ PrimLeaseValid P a p := by
  intro hL
  obtain ⟨t, htp, hel, _, hpl⟩ := h.deposed p hp hv
  have := hL t hel htp
  unfold HolderValid at this
  split at this
  · exact this
  · rename_i x hx
    have := hpl x hx
    -- `now + margin < x + primDur + drift` against `x + primDur ≤ now + drift`: needs
    -- `margin ≥ 2 · drift` (`hM`).
    omega

/-- A primary that holds its lease is the current primary and knows the latest
configuration. -/
theorem leaseValid_current {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {a : LeaseState Node}
    (h : LeaseInvariant P a) {p : Node} (hp : ThinksPrimary a.core p) (hL : PrimLeaseValid P a p) :
    p = a.core.cfg.primary ∧ a.core.localCfg p = a.core.cfg := by
  by_cases hk : KnowsLatest a.core p
  · exact ⟨knowsLatest_iff_prim h.core hp hk, h.core.localCfgEq p hk⟩
  · exfalso
    have hle := h.core.localCfgLe p
    have hv : (a.core.localCfg p).epoch < a.core.cfg.epoch := by
      unfold KnowsLatest at hk; omega
    exact deposed_not_leaseValid hM h hp hv hL

/-- The main theorem's content, from the invariant. -/
theorem leaseInvariant_noStaleRead {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {a : LeaseState Node}
    (h : LeaseInvariant P a) : NoStaleRead P a := by
  constructor
  · intro p ⟨hp, hL, hc⟩
    obtain ⟨hpp, hkn⟩ := leaseValid_current hM h hp hL
    have hpa : PrimaryAuthoritative a.core := by
      unfold PrimaryAuthoritative; rw [← hpp]; have := hp.2; rw [hkn] at this; exact this
    have h1 : a.core.hist.length ≤ a.core.commit p := by
      rcases h.core.historyWithinCommitOrInherited hpa with hl | hl
      · rw [← hpp] at hl; exact hl
      · have := h.core.inheritedEndWithinLog; rw [← hpp] at this hl; omega
    have h2 := h.core.commitWithinHistory p
    have he : a.core.commit p = a.core.hist.length := Nat.le_antisymm h2 h1
    have := h.core.committedIsHistoryPrefix p
    rw [hc, List.take_length] at this
    rw [this, ← hc, he, List.take_length]
  · intro r ⟨hnp, hL, hv⟩
    have hauth := h.leaseAuth r hnp hL
    have hholds := h.core.eligibleHoldsCommitted r hauth
    obtain ⟨_, hpre⟩ := h.committedViewHist r
    rw [hv, List.take_length] at hpre
    exact hpre.eq_of_length (Nat.le_antisymm hpre.length_le hholds.length_le)

/-! ## Preservation -/

section preserve

variable {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {a : LeaseState Node} (h : LeaseInvariant P a)

/-- A lease valid later was valid earlier. -/
theorem holderValid_mono {now now' : Nat} {start : Option Nat} {dur : Nat} (hle : now ≤ now')
    (hv : HolderValid P now' start dur) : HolderValid P now start dur := by
  unfold HolderValid at *
  cases start with
  | none => exact hv
  | some t0 => simp only at hv ⊢; omega

include h

/-- Time advances. -/
theorem leaseInvariant_tick : LeaseInvariant P (tick a) where
  core := h.core
  primaryTrafficLe := fun r => Nat.le_succ_of_le (h.primaryTrafficLe r)
  ackReceivedLe := fun p r b hb => Nat.le_succ_of_le (h.ackReceivedLe p r b hb)
  primarySinceLe := fun p T hT => Nat.le_succ_of_le (h.primarySinceLe p T hT)
  dataSentLe := h.dataSentLe
  primaryLeaseLe := h.primaryLeaseLe
  echoLe := h.echoLe
  primarySinceAck := h.primarySinceAck
  deposed := by
    intro p hp hv
    obtain ⟨t, h1, h2, h3, h4⟩ := h.deposed p hp hv
    exact ⟨t, h1, h2, h3, fun x hx => by have := h4 x hx; show _ ≤ a.now + 1 + _; omega⟩
  leaseBound := by
    intro r x hx
    rcases h.leaseBound r x hx with hb | ⟨T, hT, hxT, hold⟩
    · exact Or.inl hb
    · right; refine ⟨T, hT, hxT, ?_⟩
      rcases hold with hold | hold
      · exact Or.inl hold
      · right; show ¬ HolderValid P (a.now + 1) (some x) P.readDur
        exact fun hv => hold (holderValid_mono (Nat.le_succ _) hv)
  leaseAuth := fun r hnp hv => h.leaseAuth r hnp (holderValid_mono (Nat.le_succ _) hv)
  selfPrimNoLease := h.selfPrimNoLease
  committedViewLen := h.committedViewLen
  committedViewHist := h.committedViewHist

/-! ### Frames -/

/-- A node whose configuration names it primary holds no valid read lease
(`selfPrimNoLease`); in particular, no node that thinks it is primary does. -/
theorem not_readLeaseValid_of_selfPrim {q : Node} (hq : (a.core.localCfg q).primary = q) :
    ¬ ReadLeaseValid P a q := by
  unfold ReadLeaseValid HolderValid; rw [h.selfPrimNoLease q hq]; intro hv; exact hv

/-- Setting node `n`'s last traffic to now moves no traffic time backwards and keeps
every one in the past. -/
theorem primaryTraffic_bump (n r : Node) :
    a.primaryTraffic r ≤ update a.primaryTraffic n a.now r ∧ update a.primaryTraffic n a.now r ≤ a.now := by
  unfold update; split_ifs
  · exact ⟨h.primaryTrafficLe r, Nat.le_refl _⟩
  · exact ⟨Nat.le_refl _, h.primaryTrafficLe r⟩

/-- Under a replication change that keeps the configuration and every node's copy of it,
a deposed primary keeps its witness. -/
theorem deposed_frame {c : State Node} (hcfg : c.cfg = a.core.cfg) (hlocalCfg : c.localCfg = a.core.localCfg)
    {p : Node} (hp : ThinksPrimary a.core p) (hv : (c.localCfg p).epoch < c.cfg.epoch) :
    ∃ t, t ≠ p ∧ (c.localCfg p).eligible t = true ∧ (c.localCfg t).primary ≠ p ∧
      ∀ x, a.primaryLease p t = some x → x + P.primDur ≤ a.now + P.drift := by
  rw [hlocalCfg]; rw [hlocalCfg, hcfg] at hv; exact h.deposed p hp hv

/-- A configuration change by the current primary (MakeEligible, MakeIneligible) deposes
nobody: the primary's own copy moves with the configuration, every other copy is
unchanged, and the only copy one epoch behind the new one is the primary's. A node
already deposed keeps its witness. -/
theorem deposed_cfgBump {c : State Node} {cfg' : Cfg Node} (hcfg : c.cfg = cfg')
    (hlocalCfg : ∀ x, c.localCfg x = if x = a.core.cfg.primary then cfg' else a.core.localCfg x)
    (hver : cfg'.epoch = a.core.cfg.epoch + 1) (hprim : cfg'.primary = a.core.cfg.primary)
    (htp : ∀ x, ThinksPrimary c x ↔ ThinksPrimary a.core x) {q : Node}
    (hq : ThinksPrimary c q) (hv : (c.localCfg q).epoch < c.cfg.epoch) :
    ∃ t, t ≠ q ∧ (c.localCfg q).eligible t = true ∧ (c.localCfg t).primary ≠ q ∧
      ∀ x, a.primaryLease q t = some x → x + P.primDur ≤ a.now + P.drift := by
  have hq' := (htp q).1 hq
  have hqp : q ≠ a.core.cfg.primary := by
    intro e; rw [hlocalCfg, if_pos e, hcfg] at hv; exact Nat.lt_irrefl _ hv
  rw [hlocalCfg, if_neg hqp, hcfg, hver] at hv
  have hv' : (a.core.localCfg q).epoch < a.core.cfg.epoch := by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hl | heq
    · exact hl
    · exact absurd (knowsLatest_iff_prim h.core hq' heq) hqp
  obtain ⟨t, h1, h2, h3, h4⟩ := h.deposed q hq' hv'
  refine ⟨t, h1, ?_, ?_, h4⟩
  · rw [hlocalCfg, if_neg hqp]; exact h2
  · rw [hlocalCfg]; split_ifs with e
    · rw [hprim]; exact fun e' => hqp e'.symm
    · exact h3

/-- A configuration change by the current primary leaves `selfPrimNoLease` to the old
state: the primary's new copy still names it, and no other copy changes. -/
theorem selfPrimNoLease_cfgBump {c : State Node} {cfg' : Cfg Node}
    (hkp : a.core.localCfg a.core.cfg.primary = a.core.cfg)
    (hlocalCfg : ∀ x, c.localCfg x = if x = a.core.cfg.primary then cfg' else a.core.localCfg x)
    {q : Node} (hq : (c.localCfg q).primary = q) : a.readLease q = none := by
  rw [hlocalCfg] at hq; split_ifs at hq with e
  · subst e; exact h.selfPrimNoLease _ (by rw [hkp])
  · exact h.selfPrimNoLease q hq

/-- Resetting node `n`'s committed view to 0 (Resync, Restart) keeps the committed-view
conjuncts whatever happened to `n`'s log, as long as the other logs and the history are
unchanged. -/
theorem committedView_reset {c : State Node} (n : Node)
    (hlog : ∀ x, x ≠ n → c.log x = a.core.log x) (hhist : c.hist = a.core.hist) :
    (∀ x, update a.committedView n 0 x ≤ (c.log x).length) ∧
    (∀ x, update a.committedView n 0 x ≤ c.hist.length ∧
      (c.log x).take (update a.committedView n 0 x) <+: c.hist) := by
  rw [hhist]
  refine ⟨fun x => ?_, fun x => ?_⟩ <;> unfold update <;> split_ifs with e
  · exact Nat.zero_le _
  · rw [hlog x e]; exact h.committedViewLen x
  · exact ⟨Nat.zero_le _, by simp⟩
  · rw [hlog x e]; exact h.committedViewHist x

/-- Clearing node `n`'s lease rows and starting its primaryship now (Takeover, Restart)
keeps the bookkeeping conjuncts about lease, acknowledgement and primaryship times. -/
theorem cleared_rows {a' : LeaseState Node} (n : Node) (hnow : a'.now = a.now)
    (hAR : a'.ackReceived = update a.ackReceived n (fun _ => none))
    (hAE : a'.ackEcho = update a.ackEcho n (fun _ => none))
    (hPS : a'.primarySince = update a.primarySince n (some a.now))
    (hOE : ∀ q, q ≠ n → a'.oldEligible q = a.oldEligible q) :
    (∀ p r b, a'.ackReceived p r = some b → b ≤ a'.now) ∧
    (∀ p T, a'.primarySince p = some T → T ≤ a'.now) ∧
    (∀ p r e, a'.ackEcho p r = some e → ∃ b, a'.ackReceived p r = some b ∧ e ≤ b) ∧
    (∀ p r T b, a'.primarySince p = some T → a'.ackReceived p r = some b →
      T ≤ b ∨ a'.oldEligible p r = true) := by
  rw [hnow, hAR, hAE, hPS]
  refine ⟨fun q x b hb => h.ackReceivedLe q x b (update_row_some _ _ _ _ hb).2, ?_, ?_, ?_⟩
  · intro q T hT
    by_cases e : q = n
    · subst e; rw [update_self] at hT; cases hT; exact Nat.le_refl _
    · rw [update_of_ne _ _ e] at hT; exact h.primarySinceLe q T hT
  · intro q x e he
    obtain ⟨hqn, he⟩ := update_row_some _ _ _ _ he
    obtain ⟨b, hb, heb⟩ := h.echoLe q x e he
    exact ⟨b, by rw [update_of_ne _ _ hqn]; exact hb, heb⟩
  · intro q x T b hT hb
    obtain ⟨hqn, hb⟩ := update_row_some _ _ _ _ hb
    rw [update_of_ne _ _ hqn] at hT; rw [hOE q hqn]; exact h.primarySinceAck q x T b hT hb

/-- The frame for steps that keep the configuration, every node's copy of it and every
incarnation, and move no lease start, acknowledgement time or primaryship time. Traffic
times may only move forward, to now; the caller supplies the facts about the data-sent
times and the committed views, the only other fields such a step may change. -/
theorem leaseInvariant_frame {a' : LeaseState Node} (hc : Invariant a'.core)
    (hcfg : a'.core.cfg = a.core.cfg) (hlocalCfg : a'.core.localCfg = a.core.localCfg)
    (hinc : a'.core.incarnation = a.core.incarnation) (hnow : a'.now = a.now)
    (hPL : a'.primaryLease = a.primaryLease) (hAR : a'.ackReceived = a.ackReceived)
    (hAE : a'.ackEcho = a.ackEcho) (hRL : a'.readLease = a.readLease)
    (hPS : a'.primarySince = a.primarySince) (hOE : a'.oldEligible = a.oldEligible)
    (hPT : ∀ r, a.primaryTraffic r ≤ a'.primaryTraffic r ∧ a'.primaryTraffic r ≤ a.now)
    (hDS : ∀ r, a'.dataSent r ≤ a'.primaryTraffic r)
    (hCV : ∀ r, a'.committedView r ≤ (a'.core.log r).length)
    (hCH : ∀ r, a'.committedView r ≤ a'.core.hist.length ∧
      (a'.core.log r).take (a'.committedView r) <+: a'.core.hist) :
    LeaseInvariant P a' where
  core := hc
  primaryTrafficLe := fun r => by rw [hnow]; exact (hPT r).2
  ackReceivedLe := by rw [hAR, hnow]; exact h.ackReceivedLe
  primarySinceLe := by rw [hPS, hnow]; exact h.primarySinceLe
  dataSentLe := hDS
  primaryLeaseLe := by
    intro p r x hx; rw [hPL] at hx; exact Nat.le_trans (h.primaryLeaseLe p r x hx) (hPT r).1
  echoLe := by rw [hAE, hAR]; exact h.echoLe
  primarySinceAck := by rw [hPS, hAR, hOE]; exact h.primarySinceAck
  deposed := by
    intro p hp hv
    obtain ⟨t, h1, h2, h3, h4⟩ :=
      deposed_frame h (hcfg := hcfg) (hlocalCfg := hlocalCfg) ((thinksPrimary_congr hlocalCfg (congrFun hinc p)).1 hp) hv
    exact ⟨t, h1, h2, h3, by rw [hPL, hnow]; exact h4⟩
  leaseBound := by
    intro r x hx; rw [hRL] at hx; rw [hAR, hPS, hOE, hcfg, hnow]; exact h.leaseBound r x hx
  leaseAuth := by
    intro r hnp hv
    unfold ReadLeaseValid at hv; rw [hRL, hnow] at hv
    exact (isAuthoritative_congr hcfg (congrFun hinc r)).2
      (h.leaseAuth r (fun hp => hnp ((thinksPrimary_congr hlocalCfg (congrFun hinc r)).2 hp)) hv)
  selfPrimNoLease := by
    intro p hp; rw [hlocalCfg] at hp; rw [hRL]; exact h.selfPrimNoLease p hp
  committedViewLen := hCV
  committedViewHist := hCH

/-! ### Replication actions that touch no lease state -/

/-- A replication step that changes neither the configuration, nor any node's copy of
it, nor any incarnation, and only extends logs and the history, keeps the lease
invariant with the lease state unchanged. -/
theorem leaseInvariant_withCore {c : State Node} (hc : Invariant c)
    (hcfg : c.cfg = a.core.cfg) (hlocalCfg : c.localCfg = a.core.localCfg)
    (hinc : c.incarnation = a.core.incarnation)
    (hlog : ∀ x, a.core.log x <+: c.log x) (hhist : a.core.hist <+: c.hist) :
    LeaseInvariant P (withCore a c) :=
  leaseInvariant_frame h hc (hcfg := hcfg) (hlocalCfg := hlocalCfg) (hinc := hinc)
    (hnow := rfl) (hPL := rfl) (hAR := rfl) (hAE := rfl) (hRL := rfl) (hPS := rfl) (hOE := rfl)
    (fun r => ⟨Nat.le_refl _, h.primaryTrafficLe r⟩) h.dataSentLe
    (fun r => Nat.le_trans (h.committedViewLen r) (hlog r).length_le)
    (fun r => by
      obtain ⟨h1, h2⟩ := h.committedViewHist r
      refine ⟨Nat.le_trans h1 hhist.length_le, ?_⟩
      show (c.log r).take (a.committedView r) <+: c.hist
      rw [← prefix_take_eq (hlog r) (h.committedViewLen r)]
      exact h2.trans hhist)

/-- MakeEligible by the current primary. The new eligible replica's recorded incarnation
is its current one, so authority only grows; no lease state moves. -/
theorem leaseInvariant_makeEligible {p r : Node} (hp : ThinksPrimary a.core p)
    (hkl : KnowsLatest a.core p) (hs : a.core.sync p r = true) (hel : a.core.cfg.eligible r = false) :
    LeaseInvariant P (withCore a (makeEligible a.core p r)) := by
  have hrp : r ≠ p := by
    intro e; subst e; rw [h.core.noSelfSync] at hs; exact absurd hs (by decide)
  have hpp : p = a.core.cfg.primary := knowsLatest_iff_prim h.core hp hkl
  subst hpp
  have hkp : a.core.localCfg a.core.cfg.primary = a.core.cfg := h.core.localCfgEq _ hkl
  have htp := makeEligible_thinksPrimary (s := a.core) (r := r) hkp hrp
  exact {
  core := invariant_makeEligible h.core hp hkl hs hel
  primaryTrafficLe := h.primaryTrafficLe, ackReceivedLe := h.ackReceivedLe, primarySinceLe := h.primarySinceLe
  dataSentLe := h.dataSentLe, primaryLeaseLe := h.primaryLeaseLe, echoLe := h.echoLe, primarySinceAck := h.primarySinceAck
  deposed := fun q hq hv => deposed_cfgBump h rfl makeEligible_localCfg rfl rfl htp hq hv
  leaseBound := h.leaseBound
  leaseAuth := by
    intro x hnp hv
    obtain ⟨h1, h2⟩ := h.leaseAuth x (fun hp' => hnp ((htp x).2 hp')) hv
    refine ⟨?_, ?_⟩
    · show (if x = r then true else a.core.cfg.eligible x) = true ∨ x = a.core.cfg.primary
      split_ifs with e
      · exact Or.inl rfl
      · exact h1
    · show (if x = r then a.core.incarnation r else a.core.cfg.incarnation x) = a.core.incarnation x
      split_ifs with e
      · subst e; rfl
      · exact h2
  selfPrimNoLease := fun q hq => selfPrimNoLease_cfgBump h hkp makeEligible_localCfg hq
  committedViewLen := h.committedViewLen
  committedViewHist := h.committedViewHist }

/-- The replication actions that touch no lease state. -/
theorem leaseInvariant_core {m : Nat} {μ : Action Node} {c : State Node} (hs : Step m a.core μ c)
    (hpl : μ.isPlain = true) : LeaseInvariant P (withCore a c) := by
  cases hs
  case append p _ _ =>
    refine leaseInvariant_withCore h (invariant_append h.core p) rfl rfl rfl ?_ (List.prefix_refl _)
    intro x; show a.core.log x <+: update a.core.log p (a.core.log p ++ _) x
    unfold update; split_ifs with e
    · subst e; exact List.prefix_append _ _
    · exact List.prefix_refl _
  case commit p hp _ hlen hcap =>
    refine leaseInvariant_withCore h (invariant_commit h.core p hp hlen hcap) rfl rfl rfl
      (fun _ => List.prefix_refl _) ?_
    show a.core.hist <+: (if a.core.commit p = a.core.hist.length then _ else _)
    split_ifs
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  case addToSyncSet p r hp hrp hf _ hle =>
    exact leaseInvariant_withCore h (invariant_addToSyncSet h.core p r hp hrp hf hle) rfl rfl rfl
      (fun _ => List.prefix_refl _) (List.prefix_refl _)
  case removeFromSyncSet p r hp hsy hel =>
    exact leaseInvariant_withCore h (invariant_removeFromSyncSet h.core p r hp hsy hel) rfl rfl rfl
      (fun _ => List.prefix_refl _) (List.prefix_refl _)
  case makeEligible p r hp hkl hsy hel => exact leaseInvariant_makeEligible h hp hkl hsy hel
  -- the remaining actions are not plain
  all_goals simp [Action.isPlain] at hpl

/-! ### Data messages -/

omit h in
/-- After copying one entry, the replica's log is still a prefix of its primary's. -/
theorem replicate_log_prefix {s : State Node} {r : Node} (hpre : s.log r <+: s.log (primaryOf s r))
    (hlt : (s.log r).length < (s.log (primaryOf s r)).length) :
    (replicate s r).log r <+: s.log (primaryOf s r) := by
  show update s.log r (s.log r ++ [(s.log (primaryOf s r)).getD (s.log r).length 0]) r <+: _
  rw [update_self]
  obtain ⟨t, ht⟩ := hpre
  have hne : t ≠ [] := by
    intro e; subst e; simp at ht; rw [← ht] at hlt; exact absurd hlt (Nat.lt_irrefl _)
  obtain ⟨x, t', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hx : (s.log (primaryOf s r)).getD (s.log r).length 0 = x := by
    rw [← ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
  rw [hx, ← ht]
  exact ⟨t', by simp⟩

/-- The committed-view facts after a data message: with `L` the replica's log after the
message (a prefix of its primary's, extending its old log), the new view
`max (committedView r) (min (commit p) |L|)` is within `L`, within the history, and a
committed prefix. -/
theorem rview_data_ok {r : Node} {L : List Nat} (hpre : L <+: a.core.log (primaryOf a.core r))
    (hgrow : a.core.log r <+: L) :
    max (a.committedView r) (min (a.core.commit (primaryOf a.core r)) L.length) ≤ L.length ∧
    max (a.committedView r) (min (a.core.commit (primaryOf a.core r)) L.length) ≤ a.core.hist.length ∧
    L.take (max (a.committedView r) (min (a.core.commit (primaryOf a.core r)) L.length)) <+: a.core.hist := by
  obtain ⟨h1, h2⟩ := h.committedViewHist r
  have hrl := h.committedViewLen r
  have hcH := h.core.commitWithinHistory (primaryOf a.core r)
  have hcE := h.core.committedIsHistoryPrefix (primaryOf a.core r)
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.max_le.2 ⟨Nat.le_trans hrl hgrow.length_le, Nat.min_le_right _ _⟩
  · exact Nat.max_le.2 ⟨h1, Nat.le_trans (Nat.min_le_left _ _) hcH⟩
  · rcases Nat.le_total (a.committedView r) (min (a.core.commit (primaryOf a.core r)) L.length) with hle | hle
    · rw [Nat.max_eq_right hle]
      rw [prefix_take_eq hpre (Nat.min_le_right _ _)]
      have : (a.core.log (primaryOf a.core r)).take (min (a.core.commit (primaryOf a.core r)) L.length) =
          ((a.core.log (primaryOf a.core r)).take (a.core.commit (primaryOf a.core r))).take
            (min (a.core.commit (primaryOf a.core r)) L.length) := by
        rw [List.take_take, Nat.min_eq_left (Nat.min_le_left _ _)]
      rw [this, hcE, List.take_take, Nat.min_eq_left (Nat.min_le_left _ _)]
      exact List.take_prefix _ _
    · rw [Nat.max_eq_left hle, ← prefix_take_eq hgrow hrl]; exact h2

/-- A data message without an echo, applied to a replication state `c` that only
extends `r`'s log and changes nothing else. -/
theorem leaseInvariant_recvData_noEcho {r : Node} {c : State Node} (hc : Invariant c)
    (hcfg : c.cfg = a.core.cfg) (hlocalCfg : c.localCfg = a.core.localCfg)
    (hinc : c.incarnation = a.core.incarnation) (hhist : c.hist = a.core.hist)
    (hlogo : ∀ x, x ≠ r → c.log x = a.core.log x)
    (hpre : c.log r <+: a.core.log (primaryOf a.core r)) (hgrow : a.core.log r <+: c.log r) :
    LeaseInvariant P (recvData a r c none) := by
  obtain ⟨hv1, hv2, hv3⟩ := rview_data_ok h hpre hgrow
  refine leaseInvariant_frame h hc (hcfg := hcfg) (hlocalCfg := hlocalCfg) (hinc := hinc)
    (hnow := rfl) (hPL := rfl) (hAR := rfl) (hAE := rfl) (hRL := rfl) (hPS := rfl) (hOE := rfl)
    (primaryTraffic_bump h r) ?_ ?_ ?_
  · intro x; show update a.dataSent r a.now x ≤ update a.primaryTraffic r a.now x
    unfold update; split_ifs
    · exact Nat.le_refl _
    · exact h.dataSentLe x
  · intro x; show update a.committedView r _ x ≤ (c.log x).length
    unfold update; split_ifs with e
    · subst e; exact hv1
    · rw [hlogo x e]; exact h.committedViewLen x
  · intro x
    show update a.committedView r _ x ≤ c.hist.length ∧ (c.log x).take (update a.committedView r _ x) <+: c.hist
    rw [hhist]
    unfold update; split_ifs with e
    · subst e; exact ⟨hv2, hv3⟩
    · rw [hlogo x e]; exact h.committedViewHist x

theorem leaseInvariant_replicate {r : Node}
    (hpre : a.core.log r <+: a.core.log (primaryOf a.core r))
    (hlt : (a.core.log r).length < (a.core.log (primaryOf a.core r)).length) :
    LeaseInvariant P (recvData a r (replicate a.core r) none) := by
  refine leaseInvariant_recvData_noEcho h (invariant_replicate h.core r) rfl rfl rfl rfl ?_
    (replicate_log_prefix hpre hlt) ?_
  · intro x hx; show update a.core.log r _ x = a.core.log x; exact update_of_ne _ _ hx
  · show a.core.log r <+: update a.core.log r (a.core.log r ++ _) r
    rw [update_self]; exact List.prefix_append _ _

theorem leaseInvariant_heartbeat {r : Node}
    (hpre : a.core.log r <+: a.core.log (primaryOf a.core r)) :
    LeaseInvariant P (recvData a r a.core none) :=
  leaseInvariant_recvData_noEcho h h.core rfl rfl rfl rfl (fun _ _ => rfl) hpre (List.prefix_refl _)

include hM in
/-- A heartbeat that echoes `r`'s acknowledgement. The grant comes from the current
primary and goes to an eligible replica with a matching incarnation. -/
theorem leaseInvariant_heartbeatGrant {r : Node} (hne : primaryOf a.core r ≠ r)
    (hp : ThinksPrimary a.core (primaryOf a.core r))
    (hpre : a.core.log r <+: a.core.log (primaryOf a.core r))
    (hg : MayGrant P a (primaryOf a.core r) r) :
    LeaseInvariant P (recvData a r a.core (a.ackEcho (primaryOf a.core r) r)) := by
  obtain ⟨hL, _, hel, hin⟩ := hg
  obtain ⟨hpp, hkn⟩ := leaseValid_current hM h hp hL
  have hbase := leaseInvariant_heartbeat h hpre
  cases hecho : a.ackEcho (primaryOf a.core r) r with
  | none => exact hbase
  | some e =>
    obtain ⟨b, hb, heb⟩ := h.echoLe _ r e hecho
    have hbn := h.ackReceivedLe _ r b hb
    -- The renewed lease starts no later than `b`, the current primary's last
    -- acknowledgement from `r`: the echo does, and so does any lease `r` already held.
    have hnew : (∃ b', a.ackReceived a.core.cfg.primary r = some b' ∧ maxOpt (a.readLease r) e ≤ b') ∨
        (∃ T, a.primarySince a.core.cfg.primary = some T ∧ maxOpt (a.readLease r) e ≤ T ∧
          (a.oldEligible a.core.cfg.primary r = true ∨
            ¬ HolderValid P a.now (some (maxOpt (a.readLease r) e)) P.readDur)) := by
      unfold maxOpt
      cases hv : a.readLease r with
      | none => exact Or.inl ⟨b, by rw [← hpp]; exact hb, heb⟩
      | some v =>
        rcases h.leaseBound r v hv with ⟨b', hb', hvb⟩ | ⟨T, hT, hvT, _⟩
        · rw [← hpp, hb] at hb'; cases hb'
          exact Or.inl ⟨b, by rw [← hpp]; exact hb, Nat.max_le.2 ⟨hvb, heb⟩⟩
        · have hT' := hT; rw [← hpp] at hT'
          rcases h.primarySinceAck _ r T b hT' hb with hTb | hold
          · exact Or.inl ⟨b, by rw [← hpp]; exact hb, Nat.max_le.2 ⟨Nat.le_trans hvT hTb, heb⟩⟩
          · by_cases hTb : T ≤ b
            · exact Or.inl ⟨b, by rw [← hpp]; exact hb, Nat.max_le.2 ⟨Nat.le_trans hvT hTb, heb⟩⟩
            · refine Or.inr ⟨T, hT, Nat.max_le.2 ⟨hvT, by omega⟩, Or.inl ?_⟩
              rw [← hpp]; exact hold
    exact {
    core := hbase.core
    primaryTrafficLe := hbase.primaryTrafficLe, ackReceivedLe := hbase.ackReceivedLe, primarySinceLe := hbase.primarySinceLe
    dataSentLe := hbase.dataSentLe, primaryLeaseLe := hbase.primaryLeaseLe, echoLe := hbase.echoLe, primarySinceAck := hbase.primarySinceAck
    deposed := hbase.deposed
    leaseBound := by
      intro x v hx
      change update a.readLease r (some (maxOpt (a.readLease r) e)) x = some v at hx
      show (∃ b, a.ackReceived a.core.cfg.primary x = some b ∧ v ≤ b) ∨
        (∃ T, a.primarySince a.core.cfg.primary = some T ∧ v ≤ T ∧
          (a.oldEligible a.core.cfg.primary x = true ∨ ¬ HolderValid P a.now (some v) P.readDur))
      unfold update at hx; split_ifs at hx with ex
      · subst ex; cases hx; exact hnew
      · exact h.leaseBound x v hx
    leaseAuth := by
      intro x hnp hv
      change HolderValid P a.now (update a.readLease r (some (maxOpt (a.readLease r) e)) x) P.readDur at hv
      show IsAuthoritative a.core x
      by_cases ex : x = r
      · subst ex; rw [hkn] at hel hin; exact ⟨Or.inl hel, hin⟩
      · unfold update at hv; rw [if_neg ex] at hv
        exact h.leaseAuth x hnp hv
    selfPrimNoLease := by
      intro q hq; show update a.readLease r (some (maxOpt (a.readLease r) e)) q = none
      unfold update; split_ifs with eq
      · subst eq; exact absurd hq hne
      · exact h.selfPrimNoLease q hq
    committedViewLen := hbase.committedViewLen
    committedViewHist := hbase.committedViewHist }

/-! ### Acknowledgements -/

/-- An acknowledgement from `r`, applied to a replication state `c` that changes only
`acked` and `ackHigh`. The primary's lease from `r` and its acknowledgement times for
`r` move; everything else is the frame. -/
theorem leaseInvariant_recvAck {r : Node} {c : State Node} (hc : Invariant c)
    (hcfg : c.cfg = a.core.cfg) (hlocalCfg : c.localCfg = a.core.localCfg)
    (hinc : c.incarnation = a.core.incarnation) (hlog : c.log = a.core.log)
    (hhist : c.hist = a.core.hist) :
    LeaseInvariant P (recvAck a r c) := by
  set p := primaryOf a.core r with hp
  have hAR : (recvAck a r c).ackReceived = update2 a.ackReceived p r (some a.now) := rfl
  have hAE : (recvAck a r c).ackEcho = update2 a.ackEcho p r (some a.now) := rfl
  have hPL : (recvAck a r c).primaryLease = update2 a.primaryLease p r (some (maxOpt (a.primaryLease p r) (a.dataSent r))) := rfl
  exact {
  core := hc
  primaryTrafficLe := h.primaryTrafficLe, primarySinceLe := h.primarySinceLe, dataSentLe := h.dataSentLe
  ackReceivedLe := by
    intro q x b hb; rw [hAR] at hb
    by_cases e : q = p ∧ x = r
    · obtain ⟨rfl, rfl⟩ := e; rw [update2_self] at hb; cases hb; exact Nat.le_refl _
    · rw [update2_of_ne _ _ e] at hb; exact h.ackReceivedLe q x b hb
  primaryLeaseLe := by
    intro q x v hv; rw [hPL] at hv; show v ≤ a.primaryTraffic x
    by_cases e : q = p ∧ x = r
    · obtain ⟨rfl, rfl⟩ := e; rw [update2_self] at hv; cases hv
      unfold maxOpt; split
      · exact h.dataSentLe _
      · rename_i w hw; exact Nat.max_le.2 ⟨h.primaryLeaseLe _ _ w hw, h.dataSentLe _⟩
    · rw [update2_of_ne _ _ e] at hv; exact h.primaryLeaseLe q x v hv
  echoLe := by
    intro q x e he; rw [hAE] at he; rw [hAR]
    by_cases hqx : q = p ∧ x = r
    · obtain ⟨rfl, rfl⟩ := hqx; rw [update2_self] at he; cases he
      exact ⟨a.now, update2_self _ _ _ _, Nat.le_refl _⟩
    · rw [update2_of_ne _ _ hqx] at he; rw [update2_of_ne _ _ hqx]; exact h.echoLe q x e he
  primarySinceAck := by
    intro q x T b hT hb; rw [hAR] at hb
    by_cases e : q = p ∧ x = r
    · obtain ⟨rfl, rfl⟩ := e; rw [update2_self] at hb; cases hb; exact Or.inl (h.primarySinceLe _ T hT)
    · rw [update2_of_ne _ _ e] at hb; exact h.primarySinceAck q x T b hT hb
  deposed := by
    intro q hq hv
    obtain ⟨t, h1, h2, h3, h4⟩ :=
      deposed_frame h (hcfg := hcfg) (hlocalCfg := hlocalCfg) ((thinksPrimary_congr hlocalCfg (congrFun hinc q)).1 hq) hv
    refine ⟨t, h1, h2, h3, fun x hx => ?_⟩
    rw [hPL] at hx
    by_cases e : q = p ∧ t = r
    · -- the witness `t` follows someone other than `q`, so this is not its acknowledgement.
      exfalso; obtain ⟨rfl, rfl⟩ := e; exact h3 (by rw [hlocalCfg]; rfl)
    · rw [update2_of_ne _ _ e] at hx; exact h4 x hx
  leaseBound := by
    intro x v hx
    show (∃ b, update2 a.ackReceived p r (some a.now) c.cfg.primary x = some b ∧ v ≤ b) ∨
      (∃ T, a.primarySince c.cfg.primary = some T ∧ v ≤ T ∧
        (a.oldEligible c.cfg.primary x = true ∨ ¬ HolderValid P a.now (some v) P.readDur))
    rw [hcfg]
    by_cases e : a.core.cfg.primary = p ∧ x = r
    · obtain ⟨e1, rfl⟩ := e; rw [e1, update2_self]; left; exact ⟨a.now, rfl, h.readLeaseLe x v hx⟩
    · rw [update2_of_ne _ _ e]; exact h.leaseBound x v hx
  leaseAuth := fun x hnp hv => (isAuthoritative_congr hcfg (congrFun hinc x)).2
    (h.leaseAuth x (fun hp => hnp ((thinksPrimary_congr hlocalCfg (congrFun hinc x)).2 hp)) hv)
  selfPrimNoLease := by
    intro q hq; change (c.localCfg q).primary = q at hq; rw [hlocalCfg] at hq; exact h.selfPrimNoLease q hq
  committedViewLen := by intro x; show a.committedView x ≤ (c.log x).length; rw [hlog]; exact h.committedViewLen x
  committedViewHist := by
    intro x; show a.committedView x ≤ c.hist.length ∧ (c.log x).take (a.committedView x) <+: c.hist
    rw [hlog, hhist]; exact h.committedViewHist x }

theorem leaseInvariant_ack {r : Node} (hne : primaryOf a.core r ≠ r)
    (hpre : a.core.log r <+: a.core.log (primaryOf a.core r))
    (hlt : a.core.acked (primaryOf a.core r) r < (a.core.log r).length) :
    LeaseInvariant P (recvAck a r (ack a.core r)) :=
  leaseInvariant_recvAck h (invariant_ack h.core r hne hpre hlt) rfl rfl rfl rfl rfl

theorem leaseInvariant_ackRenew {r : Node} : LeaseInvariant P (recvAck a r a.core) :=
  leaseInvariant_recvAck h h.core rfl rfl rfl rfl rfl

/-! ### Configuration changes -/

/-- Learn. The learner restarts its takeover timer; a deposed primary that learns stops
thinking it is primary, and held no read lease. -/
theorem leaseInvariant_learn {n : Node} (hnkl : ¬ KnowsLatest a.core n) :
    LeaseInvariant P (leaseLearn a n) := by
  have hnp : n ≠ a.core.cfg.primary := by
    intro e; apply hnkl; unfold KnowsLatest; rw [e, h.core.primKnows]
  have hK := learn_localCfg (s := a.core) (n := n)
  have hcfg : (learn a.core n).cfg = a.core.cfg := rfl
  have htp : ∀ x, ThinksPrimary (learn a.core n) x → x ≠ n ∧ ThinksPrimary a.core x :=
    fun _ => learn_thinksPrimary hnp
  have hPT := primaryTraffic_bump h n
  exact {
  core := invariant_learn h.core n hnkl
  primaryTrafficLe := fun x => (hPT x).2
  ackReceivedLe := h.ackReceivedLe, primarySinceLe := h.primarySinceLe
  dataSentLe := fun x => Nat.le_trans (h.dataSentLe x) (hPT x).1
  primaryLeaseLe := fun p x v hv => Nat.le_trans (h.primaryLeaseLe p x v hv) (hPT x).1
  echoLe := h.echoLe, primarySinceAck := h.primarySinceAck
  deposed := by
    intro p hp hv
    obtain ⟨hpn, hp'⟩ := htp p hp
    have hv' : (a.core.localCfg p).epoch < a.core.cfg.epoch := by
      have := hv; change ((learn a.core n).localCfg p).epoch < (learn a.core n).cfg.epoch at this
      rwa [hK, if_neg hpn, hcfg] at this
    obtain ⟨t, h1, h2, h3, h4⟩ := h.deposed p hp' hv'
    refine ⟨t, h1, ?_, ?_, h4⟩
    · show ((learn a.core n).localCfg p).eligible t = true; rw [hK, if_neg hpn]; exact h2
    · show ((learn a.core n).localCfg t).primary ≠ p
      rw [hK]; split_ifs with e
      · show a.core.cfg.primary ≠ p; exact (stale_ne_prim h.core hv').symm
      · exact h3
  leaseBound := h.leaseBound
  leaseAuth := by
    intro x hnp hv
    show IsAuthoritative a.core x
    by_cases hx : ThinksPrimary a.core x
    · exact absurd hv (not_readLeaseValid_of_selfPrim h hx.1)
    · exact h.leaseAuth x hx hv
  selfPrimNoLease := by
    intro q hq
    change ((learn a.core n).localCfg q).primary = q at hq
    rw [hK] at hq; split_ifs at hq with e
    · subst e; exact absurd hq.symm hnp
    · exact h.selfPrimNoLease q hq
  committedViewLen := h.committedViewLen
  committedViewHist := h.committedViewHist }

omit h in
include hM in
/-- A read lease whose start is bounded by the demotion guards is not valid. -/
theorem lease_over_of_guards {now v : Nat} {ackReceived primarySince : Option Nat} {old : Bool}
    (hb : (∃ b, ackReceived = some b ∧ v ≤ b) ∨
      (∃ T, primarySince = some T ∧ v ≤ T ∧ (old = true ∨ ¬ HolderValid P now (some v) P.readDur)))
    (hgo : GrantorOver P now ackReceived P.readDur)
    (hwo : ∀ T, primarySince = some T → old = true → T + P.readDur + P.margin ≤ now + P.drift) :
    ¬ HolderValid P now (some v) P.readDur := by
  intro hv
  rcases hb with ⟨b, hb, hvb⟩ | ⟨T, hT, hvT, hold | hold⟩
  · -- `now + margin < v + readDur + drift`, `v ≤ b`, `b + readDur ≤ now + drift`: needs
    -- `margin ≥ 2 · drift` (`hM`).
    unfold HolderValid at hv; rw [hb] at hgo; unfold GrantorOver at hgo; omega
  · -- `v ≤ T`, `T + readDur + margin ≤ now + drift`: needs only `margin ≥ drift`.
    unfold HolderValid at hv; have := hwo T hT hold; omega
  · exact hold hv

include hM in
/-- Demotion. The demoted replica's read lease is over, by the two waits. -/
theorem leaseInvariant_demote {p r : Node} (hp : ThinksPrimary a.core p) (hkl : KnowsLatest a.core p)
    (hel : a.core.cfg.eligible r = true) (hgo : GrantorOver P a.now (a.ackReceived p r) P.readDur)
    (hwo : ∀ T, a.primarySince p = some T → a.oldEligible p r = true →
      T + P.readDur + P.margin ≤ a.now + P.drift) :
    LeaseInvariant P (withCore a (makeIneligible a.core p r)) := by
  have hpp : p = a.core.cfg.primary := knowsLatest_iff_prim h.core hp hkl
  subst hpp
  have hkp : a.core.localCfg a.core.cfg.primary = a.core.cfg := h.core.localCfgEq _ hkl
  have htp := makeIneligible_thinksPrimary (s := a.core) (r := r) hkp
  exact {
  core := invariant_makeIneligible h.core hp hkl hel
  primaryTrafficLe := h.primaryTrafficLe, ackReceivedLe := h.ackReceivedLe, primarySinceLe := h.primarySinceLe
  dataSentLe := h.dataSentLe, primaryLeaseLe := h.primaryLeaseLe, echoLe := h.echoLe, primarySinceAck := h.primarySinceAck
  deposed := fun q hq hv => deposed_cfgBump h rfl makeIneligible_localCfg rfl rfl htp hq hv
  leaseBound := h.leaseBound
  leaseAuth := by
    intro x hnp hv
    have hx := h.leaseAuth x (fun hp' => hnp ((htp x).2 hp')) hv
    by_cases ex : x = r
    · exfalso; subst ex
      change HolderValid P a.now (a.readLease x) P.readDur at hv
      cases hrl : a.readLease x with
      | none => rw [hrl] at hv; exact hv
      | some v =>
        rw [hrl] at hv
        exact lease_over_of_guards hM (h.leaseBound x v hrl) hgo hwo hv
    · obtain ⟨h1, h2⟩ := hx
      refine ⟨?_, h2⟩
      show (if x = r then false else a.core.cfg.eligible x) = true ∨ x = a.core.cfg.primary
      rw [if_neg ex]; exact h1
  selfPrimNoLease := fun q hq => selfPrimNoLease_cfgBump h hkp makeIneligible_localCfg hq
  committedViewLen := h.committedViewLen
  committedViewHist := h.committedViewHist }

/-- Takeover. The deposed primary gets its witness: the taker, eligible in its
configuration, whose lease it can never again hold; every existing read lease started
before the takeover. The taker's own lease rows are cleared (`update_row_some`). -/
theorem leaseInvariant_takeover {n : Node} (hkl : KnowsLatest a.core n) (hel : a.core.cfg.eligible n = true)
    (hnp : n ≠ a.core.cfg.primary) (hin : a.core.cfg.incarnation n = a.core.incarnation n)
    (hwait : a.primaryTraffic n + P.primDur ≤ a.now + P.drift) :
    LeaseInvariant P (leaseTakeover a n) := by
  have hK := takeover_localCfg (s := a.core) (n := n)
  have htp := takeover_thinksPrimary (s := a.core) hin
  obtain ⟨hAR, hPS, hAE, hPA⟩ := cleared_rows h (a' := leaseTakeover a n) n rfl rfl rfl rfl (fun _ e => update_of_ne _ _ e)
  exact {
  core := invariant_takeover h.core n hkl hel hnp hin
  primaryTrafficLe := h.primaryTrafficLe, dataSentLe := h.dataSentLe
  ackReceivedLe := hAR, primarySinceLe := hPS, echoLe := hAE, primarySinceAck := hPA
  primaryLeaseLe := fun q x v hv => h.primaryLeaseLe q x v (update_row_some _ _ _ _ hv).2
  deposed := by
    intro q hq hv
    rcases (htp q).1 hq with rfl | ⟨hqn, hq'⟩
    · exfalso; have := hv; change ((takeover a.core q).localCfg q).epoch < (takeoverCfg a.core q).epoch at this
      rw [hK, if_pos rfl] at this; exact Nat.lt_irrefl _ this
    · have hv0 : (a.core.localCfg q).epoch < a.core.cfg.epoch + 1 := by
        have := hv; change ((takeover a.core n).localCfg q).epoch < (takeoverCfg a.core n).epoch at this
        rw [hK, if_neg hqn] at this; exact this
      rcases Nat.lt_succ_iff_lt_or_eq.1 hv0 with hl | heq
      · -- deposed before: the old witness still serves.
        obtain ⟨t, h1, h2, h3, h4⟩ := h.deposed q hq' hl
        refine ⟨t, h1, ?_, ?_, fun x hx => h4 x (update_row_some _ _ _ _ hx).2⟩
        · show ((takeover a.core n).localCfg q).eligible t = true; rw [hK, if_neg hqn]; exact h2
        · show ((takeover a.core n).localCfg t).primary ≠ q
          rw [hK]; split_ifs with e
          · show n ≠ q; exact fun e' => hqn e'.symm
          · exact h3
      · -- deposed now: `q` was the primary, and `n` is its witness.
        have hqp : q = a.core.cfg.primary := knowsLatest_iff_prim h.core hq' heq
        refine ⟨n, fun e => hnp (e ▸ hqp), ?_, ?_, ?_⟩
        · show ((takeover a.core n).localCfg q).eligible n = true
          rw [hK, if_neg hqn, h.core.localCfgEq q heq]; exact hel
        · show ((takeover a.core n).localCfg n).primary ≠ q
          rw [hK, if_pos rfl]; show n ≠ q; exact fun e => hnp (e ▸ hqp)
        · -- `q`'s lease from `n` started no later than `n`'s last traffic, which `n`
          -- waited out (`hwait`).
          intro x hx; show x + P.primDur ≤ a.now + P.drift
          have := h.primaryLeaseLe q n x (update_row_some _ _ _ _ hx).2; omega
  leaseBound := by
    intro x v hx
    obtain ⟨hxn, hx⟩ := update_none_some _ _ _ hx
    show (∃ b, update a.ackReceived n (fun _ => none) (takeoverCfg a.core n).primary x = some b ∧ v ≤ b) ∨
      (∃ T, update a.primarySince n (some a.now) (takeoverCfg a.core n).primary = some T ∧ v ≤ T ∧
        (update a.oldEligible n a.core.cfg.eligible (takeoverCfg a.core n).primary x = true ∨
          ¬ HolderValid P a.now (some v) P.readDur))
    right; refine ⟨a.now, update_self _ _ _, h.readLeaseLe x v hx, ?_⟩
    show (update a.oldEligible n a.core.cfg.eligible n x = true) ∨ _
    rw [update_self]
    by_cases hel : a.core.cfg.eligible x = true
    · exact Or.inl hel
    · -- `x` was not eligible in the configuration being replaced: a valid lease would
      -- make it authoritative, so its lease is not valid.
      right; intro hv
      have hvv : ReadLeaseValid P a x := by unfold ReadLeaseValid; rw [hx]; exact hv
      have hxp : ¬ ThinksPrimary a.core x := fun hp => not_readLeaseValid_of_selfPrim h hp.1 hvv
      rcases (h.leaseAuth x hxp hvv).1 with h1 | h1
      · exact hel h1
      · exact not_readLeaseValid_of_selfPrim h (by rw [h1, h.core.primKnows]) hvv
  leaseAuth := by
    intro x hnp' hv
    change HolderValid P a.now (update a.readLease n none x) P.readDur at hv
    by_cases ex : x = n
    · subst ex; rw [update_self] at hv; exact hv.elim
    · rw [update_of_ne _ _ ex] at hv
      have hx : ¬ ThinksPrimary a.core x := fun hp => hnp' ((htp x).2 (Or.inr ⟨ex, hp⟩))
      obtain ⟨h1, h2⟩ := h.leaseAuth x hx hv
      have hxq : x ≠ a.core.cfg.primary := fun e =>
        not_readLeaseValid_of_selfPrim h (by rw [e, h.core.primKnows]) hv
      refine ⟨Or.inl ?_, h2⟩
      show eligibleAfterTakeover a.core n x = true
      unfold eligibleAfterTakeover
      rcases h1 with h1 | h1
      · simp [h1, hxq, ex]
      · exact absurd h1 hxq
  selfPrimNoLease := by
    intro q hq
    show update a.readLease n none q = none
    unfold update; split_ifs with e
    · rfl
    · change ((takeover a.core n).localCfg q).primary = q at hq
      rw [hK, if_neg e] at hq; exact h.selfPrimNoLease q hq
  committedViewLen := h.committedViewLen
  committedViewHist := h.committedViewHist }

/-- A full resync: the replica's committed view starts over. -/
theorem leaseInvariant_resync {r : Node} (hne : primaryOf a.core r ≠ r)
    (hnpre : ¬ (a.core.log r <+: a.core.log (primaryOf a.core r)))
    (hsy : a.core.sync (primaryOf a.core r) r = false)
    (hke : (a.core.localCfg (primaryOf a.core r)).eligible r = false) :
    LeaseInvariant P (leaseResync a r) := by
  obtain ⟨hCV, hCH⟩ := committedView_reset h (c := resync a.core r) r (fun _ e => resync_log_other e) rfl
  exact leaseInvariant_frame h (invariant_resync h.core r hne hsy hke)
    (hcfg := rfl) (hlocalCfg := rfl) (hinc := rfl) (hnow := rfl) (hPL := rfl)
    (hAR := rfl) (hAE := rfl) (hRL := rfl) (hPS := rfl) (hOE := rfl)
    (fun x => ⟨Nat.le_refl _, h.primaryTrafficLe x⟩) h.dataSentLe hCV hCH

/-! ### Restarts -/

/-- A restart of `n`, with replication state `c` afterwards. `c` keeps the configuration
and every other node's incarnation and log, and the history. `n`'s lease rows are
cleared (`update_row_some`), its committed view starts over, and both its timers restart. -/
theorem leaseInvariant_restart {n : Node} {c : State Node} (hc : Invariant c)
    (hkl : KnowsLatest a.core n)
    (hcfg : c.cfg = a.core.cfg) (hlocalCfg : c.localCfg = a.core.localCfg)
    (hinc : ∀ x, x ≠ n → c.incarnation x = a.core.incarnation x)
    (hlog : ∀ x, x ≠ n → c.log x = a.core.log x) (hhist : c.hist = a.core.hist) :
    LeaseInvariant P (leaseRestart a n c) := by
  have hPT := primaryTraffic_bump h n
  obtain ⟨hAR, hPS, hAE, hPA⟩ := cleared_rows h (a' := leaseRestart a n c) n rfl rfl rfl rfl (fun _ e => update_of_ne _ _ e)
  obtain ⟨hCV, hCH⟩ := committedView_reset h n hlog hhist
  exact {
  core := hc
  primaryTrafficLe := fun x => (hPT x).2
  ackReceivedLe := hAR, primarySinceLe := hPS, echoLe := hAE, primarySinceAck := hPA
  primaryLeaseLe := fun q x v hv =>
    Nat.le_trans (h.primaryLeaseLe q x v (update_row_some _ _ _ _ hv).2) (hPT x).1
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
    exact ⟨t, h1, h2, h3, fun x hx => h4 x (update_row_some _ _ _ _ hx).2⟩
  leaseBound := by
    intro x v hx
    obtain ⟨hxn, hx⟩ := update_none_some _ _ _ hx
    show (∃ b, update a.ackReceived n (fun _ => none) c.cfg.primary x = some b ∧ v ≤ b) ∨
      (∃ T, update a.primarySince n (some a.now) c.cfg.primary = some T ∧ v ≤ T ∧
        (update a.oldEligible n (fun _ => true) c.cfg.primary x = true ∨
          ¬ HolderValid P a.now (some v) P.readDur))
    rw [hcfg]
    by_cases hpn : a.core.cfg.primary = n
    · -- the primary restarted: every remaining lease is bounded by its new primaryship.
      rw [hpn, update_self, update_self, update_self]
      right; exact ⟨a.now, rfl, h.readLeaseLe x v hx, Or.inl rfl⟩
    · rw [update_of_ne _ _ hpn, update_of_ne _ _ hpn, update_of_ne _ _ hpn]; exact h.leaseBound x v hx
  leaseAuth := by
    intro x hnp hv
    change HolderValid P a.now (update a.readLease n none x) P.readDur at hv
    by_cases ex : x = n
    · subst ex; rw [update_self] at hv; exact hv.elim
    · rw [update_of_ne _ _ ex] at hv
      exact (isAuthoritative_congr hcfg (hinc x ex)).2
        (h.leaseAuth x (fun hp => hnp ((thinksPrimary_congr hlocalCfg (hinc x ex)).2 hp)) hv)
  selfPrimNoLease := by
    intro q hq
    show update a.readLease n none q = none
    unfold update; split_ifs with e
    · rfl
    · change (c.localCfg q).primary = q at hq; rw [hlocalCfg] at hq; exact h.selfPrimNoLease q hq
  committedViewLen := hCV
  committedViewHist := hCH }

theorem leaseInvariant_restartEmpty {n : Node} (hkl : KnowsLatest a.core n)
    (hsurv : ∃ m, m ≠ n ∧ IsAuthoritative a.core m) :
    LeaseInvariant P (leaseRestart a n (restartEmpty a.core n)) :=
  leaseInvariant_restart h (invariant_restartEmpty h.core n hkl hsurv) hkl rfl rfl
    (fun _ e => restartEmpty_inc_other e) (fun _ e => restartEmpty_log_other e) rfl

theorem leaseInvariant_restartKeep {n : Node} (hkl : KnowsLatest a.core n) :
    LeaseInvariant P (leaseRestart a n (restartKeep a.core n)) :=
  leaseInvariant_restart h (invariant_restartKeep h.core n hkl) hkl rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) rfl

theorem leaseInvariant_restartPartialKeep {n : Node} {k : Nat} (hkl : KnowsLatest a.core n)
    (hk : k < (a.core.log n).length) (hkeep : a.core.ackHigh n ≤ k) :
    LeaseInvariant P (leaseRestart a n (restartPartialKeep a.core n k)) :=
  leaseInvariant_restart h (invariant_restartPartialKeep h.core n k hkl hk hkeep) hkl rfl rfl
    (fun _ _ => rfl) (fun _ e => restartPartialKeep_log_other e) rfl

theorem leaseInvariant_restartPartialFresh {n : Node} {k : Nat} (hkl : KnowsLatest a.core n)
    (hk : k < (a.core.log n).length) (hfresh : k < a.core.ackHigh n)
    (hsurv : ∃ m, m ≠ n ∧ IsAuthoritative a.core m) :
    LeaseInvariant P (leaseRestart a n (restartPartialFresh a.core n k)) :=
  leaseInvariant_restart h (invariant_restartPartialFresh h.core n k hkl hsurv hk hfresh) hkl rfl rfl
    (fun _ e => restartEmpty_inc_other e) (fun _ e => restartPartialFresh_log_other e) rfl

end preserve

/-! ## Every step preserves the invariant; the theorem -/

/-- Every lease-layer step preserves the invariant, given `margin ≥ 2 · drift`. -/
theorem leaseInvariant_step {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {m : Nat}
    {a a' : LeaseState Node} {μ : LeaseAction Node} (h : LeaseInvariant P a) (hs : LeaseStep m P a μ a') :
    LeaseInvariant P a' := by
  cases hs with
  | tick => exact leaseInvariant_tick h
  | core μ c hc hpl => exact leaseInvariant_core h hc hpl
  | replicate r _ hpre hlt => exact leaseInvariant_replicate h hpre hlt
  | heartbeat r _ hpre => exact leaseInvariant_heartbeat h hpre
  | heartbeatGrant r hne hp hpre hg => exact leaseInvariant_heartbeatGrant hM h hne hp hpre hg
  | ack r hne hpre hlt => exact leaseInvariant_ack h hne hpre hlt
  | ackRenew r _ _ => exact leaseInvariant_ackRenew h
  | learn n hnkl => exact leaseInvariant_learn h hnkl
  | demote p r hp hkl hel hgo hwo => exact leaseInvariant_demote hM h hp hkl hel hgo hwo
  | takeover n hkl hel hnp hin hwait => exact leaseInvariant_takeover h hkl hel hnp hin hwait
  | resync r hne hnpre hsy hke => exact leaseInvariant_resync h hne hnpre hsy hke
  | restartEmpty n hkl hsurv => exact leaseInvariant_restartEmpty h hkl hsurv
  | restartKeep n hkl => exact leaseInvariant_restartKeep h hkl
  | restartPartialKeep n k hkl hk hkeep => exact leaseInvariant_restartPartialKeep h hkl hk hkeep
  | restartPartialFresh n k hkl hk hfresh hsurv => exact leaseInvariant_restartPartialFresh h hkl hk hfresh hsurv

/-- The invariant holds in every reachable state. -/
theorem leaseInvariant_reachable {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {m : Nat}
    {i : Node} {a : LeaseState Node} (h : LeaseReachable m P i a) : LeaseInvariant P a :=
  let ⟨_, run⟩ := h
  LTS.mtrInv_of_trInv (p := LeaseInvariant P) (fun _ _ _ hs h => leaseInvariant_step hM h hs) _ _ _ run
    (leaseInvariant_init P i)

/-- **No stale linearizable read.** If the clock-drift margin is at least twice the drift
bound, then in every reachable state, for every `min-sync-replicas` value, any node
that may serve a linearizable read (a primary holding its lease from every eligible
replica it knows, or a sync replica holding a read lease, each with nothing
uncommitted) has exactly the committed history as its log. -/
theorem noStaleRead {P : LeaseParams} (hMargin : 2 * P.drift ≤ P.margin) {m : Nat} {i : Node}
    {a : LeaseState Node} (hReachable : LeaseReachable m P i a) : NoStaleRead P a :=
  leaseInvariant_noStaleRead hMargin (leaseInvariant_reachable hMargin hReachable)

/-- The replication safety theorem also holds of the lease layer's reachable states. -/
theorem lease_safety {P : LeaseParams} (hMargin : 2 * P.drift ≤ P.margin) {m : Nat} {i : Node}
    {a : LeaseState Node} (hReachable : LeaseReachable m P i a) : Safety a.core :=
  invariant_safety (leaseInvariant_reachable hMargin hReachable).core

end SyncReplication
