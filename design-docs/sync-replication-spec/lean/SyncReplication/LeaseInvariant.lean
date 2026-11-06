import SyncReplication.Leases
import SyncReplication.Preserve

/-!
# No stale linearizable read

The invariant of the lease layer and the theorem `noStaleRead`: whenever a node may
serve a linearizable read, its log is exactly the committed history.

## The argument

**Primary reads.** A primary that holds a valid lease from every eligible replica it
knows of is the *current* primary. Why: a deposed primary `p` was deposed by a takeover
of some `t` that was eligible in `p`'s own configuration (only `p` could have made `t`
eligible). `t` waited until `p`'s lease must have expired, measured from the last
traffic `t` received from `p`, and `p`'s lease from `t` started no later than that
traffic. So `p`'s lease from `t` is over for good (`deposed`), and `p` cannot hold a
valid lease from every eligible replica it knows. The current primary, by the
replication invariant, has the whole committed history below its committed offset or
its catch-up point; with nothing uncommitted, its log is the history.

**Replica reads.** A read lease is granted only by a primary that holds its own lease,
hence by the current primary, and only to an eligible replica with a matching
incarnation (`leaseAuth`: a valid read lease implies the holder is authoritative).
Demotion waits until the lease must have expired; a new primary waits one read lease
plus the margin after its takeover before demoting anyone, and every lease granted
before the takeover started before it (`leaseBound`). An authoritative node holds the
whole history (`ehc`), and a replica's committed view is a committed prefix of its log
(`rviewHist`); with nothing uncommitted, its log is the history.

Both arguments need `margin ≥ 2 · drift`: a holder's worst case (its clock slow) and
a grantor's worst case (its clock fast) are `drift` apart each.
-/

open Cslib

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

theorem update2_self {β : Type} (f : Node → Node → β) (p r : Node) (b : β) :
    update2 f p r b p r = b := by simp [update2, update]

theorem update2_of_ne {β : Type} (f : Node → Node → β) {p r q x : Node} (b : β)
    (h : ¬ (q = p ∧ x = r)) : update2 f p r b q x = f q x := by
  unfold update2 update
  by_cases hq : q = p
  · subst hq; have : x ≠ r := fun e => h ⟨rfl, e⟩; simp [this]
  · simp [hq]

/-- The inductive invariant of the lease layer. -/
structure LeaseInvariant (P : LeaseParams) (a : LState Node) : Prop where
  /-- The replication invariant. -/
  core : Invariant a.core
  /-- Every recorded time is in the past. -/
  primRecvLe : ∀ r, a.primRecv r ≤ a.now
  ackRecvLe  : ∀ p r b, a.ackRecv p r = some b → b ≤ a.now
  rlLe       : ∀ r x, a.rl r = some x → x ≤ a.now
  tkoLe      : ∀ p T, a.tko p = some T → T ≤ a.now
  /-- The data a replica would acknowledge was sent no later than its last traffic. -/
  dataTLe    : ∀ r, a.dataT r ≤ a.primRecv r
  /-- A primary lease starts no later than the holder's last traffic to the grantor. -/
  plLe       : ∀ p r x, a.pl p r = some x → x ≤ a.primRecv r
  /-- The acknowledgement a primary would echo was sent no later than it was received. -/
  echoLe     : ∀ p r e, a.ackEcho p r = some e → ∃ b, a.ackRecv p r = some b ∧ e ≤ b
  /-- Every acknowledgement a primary holds arrived during its current primaryship. -/
  tkoAck     : ∀ p r T b, a.tko p = some T → a.ackRecv p r = some b → T ≤ b
  /-- A deposed primary's lease from the replica that deposed it is over for good. That
  replica is eligible in the deposed primary's configuration and follows someone else. -/
  deposed    : ∀ p, ThinksPrimary a.core p → (a.core.known p).version < a.core.cfg.version →
    ∃ t, t ≠ p ∧ (a.core.known p).eligible t = true ∧ (a.core.known t).primary ≠ p ∧
      ∀ x, a.pl p t = some x → x + P.primDur ≤ a.now + P.drift
  /-- A read lease started no later than the current primary's last acknowledgement from
  its holder, or no later than the current primary's takeover. -/
  leaseBound : ∀ r x, a.rl r = some x →
    (∃ b, a.ackRecv a.core.cfg.primary r = some b ∧ x ≤ b) ∨
    (∃ T, a.tko a.core.cfg.primary = some T ∧ x ≤ T)
  /-- A replica with a valid read lease is authoritative. -/
  leaseAuth  : ∀ r, ¬ ThinksPrimary a.core r → ReadLeaseValid P a r → IsAuthoritative a.core r
  /-- A node whose configuration names it primary holds no read lease. -/
  selfPrimNoLease : ∀ p, (a.core.known p).primary = p → a.rl p = none
  /-- A replica's committed view is within its log and is a committed prefix. -/
  rviewLen   : ∀ r, a.rview r ≤ (a.core.log r).length
  rviewHist  : ∀ r, a.rview r ≤ a.core.hist.length ∧ (a.core.log r).take (a.rview r) <+: a.core.hist

theorem leaseInvariant_init (P : LeaseParams) (i : Node) : LeaseInvariant P (linit i) where
  core := invariant_init i
  primRecvLe := fun _ => Nat.le_refl _
  ackRecvLe := by intro _ _ _ h; simp [linit] at h
  rlLe := by intro _ _ h; simp [linit] at h
  tkoLe := by intro _ _ h; simp [linit] at h
  dataTLe := fun _ => Nat.le_refl _
  plLe := by intro _ _ _ h; simp [linit] at h
  echoLe := by intro _ _ _ h; simp [linit] at h
  tkoAck := by intro _ _ _ _ h; simp [linit] at h
  deposed := by intro p _ hv; simp [linit, init, initCfg] at hv
  leaseBound := by intro _ _ h; simp [linit] at h
  leaseAuth := by intro r _ hv; simp [ReadLeaseValid, HolderValid, linit] at hv
  selfPrimNoLease := by intro _ _; rfl
  rviewLen := by intro _; simp [linit]
  rviewHist := by intro _; simp [linit, init]

/-! ## The current primary is the only one that can hold its lease -/

/-- A deposed primary holds no valid primary lease, since its lease from the replica that
deposed it is over, and that replica is eligible in its configuration. -/
theorem deposed_not_leaseValid {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {a : LState Node}
    (h : LeaseInvariant P a) {p : Node} (hp : ThinksPrimary a.core p)
    (hv : (a.core.known p).version < a.core.cfg.version) : ¬ PrimLeaseValid P a p := by
  intro hL
  obtain ⟨t, htp, hel, _, hpl⟩ := h.deposed p hp hv
  have := hL t hel htp
  unfold HolderValid at this
  split at this
  · exact this
  · rename_i x hx
    have := hpl x hx
    omega

/-- A primary that holds its lease is the current primary and knows the latest
configuration. -/
theorem leaseValid_current {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {a : LState Node}
    (h : LeaseInvariant P a) {p : Node} (hp : ThinksPrimary a.core p) (hL : PrimLeaseValid P a p) :
    p = a.core.cfg.primary ∧ a.core.known p = a.core.cfg := by
  by_cases hk : KnowsLatest a.core p
  · have hkn := h.core.knownEq p hk
    refine ⟨?_, hkn⟩
    have := hp.1; rw [hkn] at this; exact this.symm
  · exfalso
    have hle := h.core.knownLe p
    have hv : (a.core.known p).version < a.core.cfg.version := by
      unfold KnowsLatest at hk; omega
    exact deposed_not_leaseValid hM h hp hv hL

/-- The main theorem's content, from the invariant. -/
theorem leaseInvariant_noStaleRead {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {a : LState Node}
    (h : LeaseInvariant P a) : NoStaleRead P a := by
  constructor
  · intro p ⟨hp, hL, hc⟩
    obtain ⟨hpp, hkn⟩ := leaseValid_current hM h hp hL
    have hpa : PrimaryAuthoritative a.core := by
      unfold PrimaryAuthoritative; rw [← hpp]; have := hp.2; rw [hkn] at this; exact this
    have h1 : a.core.hist.length ≤ a.core.commit p := by
      rcases h.core.histLe hpa with hl | hl
      · rw [← hpp] at hl; exact hl
      · have := h.core.reconLen; rw [← hpp] at this hl; omega
    have h2 := h.core.caHist p
    have he : a.core.commit p = a.core.hist.length := Nat.le_antisymm h2 h1
    have := h.core.caEq p
    rw [hc, List.take_length] at this
    rw [this, ← hc, he, List.take_length]
  · intro r ⟨hnp, hL, hv⟩
    have hauth := h.leaseAuth r hnp hL
    have hehc := h.core.ehc r hauth
    obtain ⟨_, hpre⟩ := h.rviewHist r
    rw [hv, List.take_length] at hpre
    exact hpre.eq_of_length (Nat.le_antisymm hpre.length_le hehc.length_le)

/-! ## Preservation -/

section preserve

variable {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {a : LState Node} (h : LeaseInvariant P a)

/-- Facts about `HolderValid` and time. -/
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
  primRecvLe := fun r => Nat.le_succ_of_le (h.primRecvLe r)
  ackRecvLe := fun p r b hb => Nat.le_succ_of_le (h.ackRecvLe p r b hb)
  rlLe := fun r x hx => Nat.le_succ_of_le (h.rlLe r x hx)
  tkoLe := fun p T hT => Nat.le_succ_of_le (h.tkoLe p T hT)
  dataTLe := h.dataTLe
  plLe := h.plLe
  echoLe := h.echoLe
  tkoAck := h.tkoAck
  deposed := by
    intro p hp hv
    obtain ⟨t, h1, h2, h3, h4⟩ := h.deposed p hp hv
    exact ⟨t, h1, h2, h3, fun x hx => by have := h4 x hx; show _ ≤ a.now + 1 + _; omega⟩
  leaseBound := h.leaseBound
  leaseAuth := fun r hnp hv => h.leaseAuth r hnp (holderValid_mono (Nat.le_succ _) hv)
  selfPrimNoLease := h.selfPrimNoLease
  rviewLen := h.rviewLen
  rviewHist := h.rviewHist

/-! ### Replication actions that touch no lease state -/

/-- A replication step that changes neither the configuration, nor any node's copy of
it, nor any incarnation, and only extends logs and the history, keeps the lease
invariant with the lease state unchanged. -/
theorem leaseInvariant_withCore {c : State Node} (hc : Invariant c)
    (hcfg : c.cfg = a.core.cfg) (hknown : c.known = a.core.known)
    (hinc : c.incarnation = a.core.incarnation)
    (hlog : ∀ x, a.core.log x <+: c.log x) (hhist : a.core.hist <+: c.hist) :
    LeaseInvariant P (withCore a c) := by
  have htp : ∀ x, ThinksPrimary c x ↔ ThinksPrimary a.core x := by
    intro x; unfold ThinksPrimary; rw [hknown, hinc]
  have hau : ∀ x, IsAuthoritative c x ↔ IsAuthoritative a.core x := by
    intro x; unfold IsAuthoritative; rw [hcfg, hinc]
  exact {
  core := hc
  primRecvLe := h.primRecvLe, ackRecvLe := h.ackRecvLe, rlLe := h.rlLe, tkoLe := h.tkoLe
  dataTLe := h.dataTLe, plLe := h.plLe, echoLe := h.echoLe, tkoAck := h.tkoAck
  deposed := by
    intro p hp hv
    show ∃ t, t ≠ p ∧ (c.known p).eligible t = true ∧ (c.known t).primary ≠ p ∧ _
    rw [hknown]
    have hv' : (a.core.known p).version < a.core.cfg.version := by
      have := hv; change (c.known p).version < c.cfg.version at this; rwa [hknown, hcfg] at this
    exact h.deposed p ((htp p).1 hp) hv'
  leaseBound := by
    intro r x hx; show (∃ b, a.ackRecv c.cfg.primary r = some b ∧ x ≤ b) ∨
      (∃ T, a.tko c.cfg.primary = some T ∧ x ≤ T)
    rw [hcfg]; exact h.leaseBound r x hx
  leaseAuth := fun r hnp hv => (hau r).2 (h.leaseAuth r (fun hp => hnp ((htp r).2 hp)) hv)
  selfPrimNoLease := by
    intro p hp; change (c.known p).primary = p at hp; rw [hknown] at hp; exact h.selfPrimNoLease p hp
  rviewLen := fun r => Nat.le_trans (h.rviewLen r) (hlog r).length_le
  rviewHist := by
    intro r
    obtain ⟨h1, h2⟩ := h.rviewHist r
    refine ⟨Nat.le_trans h1 hhist.length_le, ?_⟩
    show (c.log r).take (a.rview r) <+: c.hist
    rw [← prefix_take_eq (hlog r) (h.rviewLen r)]
    exact h2.trans hhist }

/-- MakeEligible by the current primary. The new eligible replica's recorded incarnation
is its current one, so authority only grows; no lease state moves. -/
theorem leaseInvariant_makeEligible {p r : Node} (hp : ThinksPrimary a.core p)
    (hk : KnowsLatest a.core p) (hs : a.core.sync p r = true) (he : a.core.cfg.eligible r = false) :
    LeaseInvariant P (withCore a (makeEligible a.core p r)) := by
  have hkn : a.core.known p = a.core.cfg := h.core.knownEq p hk
  have hpp : p = a.core.cfg.primary := by have := hp.1; rw [hkn] at this; exact this.symm
  have hrp : r ≠ p := by
    intro e; subst e; rw [h.core.noSelfSync] at hs; exact absurd hs (by decide)
  subst hpp
  have hkp : a.core.known a.core.cfg.primary = a.core.cfg := hkn
  have htp := makeEligible_thinksPrimary (s := a.core) (r := r) hkp hrp
  exact {
  core := invariant_makeEligible h.core hp hk hs he
  primRecvLe := h.primRecvLe, ackRecvLe := h.ackRecvLe, rlLe := h.rlLe, tkoLe := h.tkoLe
  dataTLe := h.dataTLe, plLe := h.plLe, echoLe := h.echoLe, tkoAck := h.tkoAck
  deposed := by
    intro q hq hv
    have hq' := (htp q).1 hq
    have hqp : q ≠ a.core.cfg.primary := by
      intro e; subst e
      have := hv
      change ((makeEligible a.core a.core.cfg.primary r).known a.core.cfg.primary).version <
        (makeEligibleCfg a.core r).version at this
      rw [makeEligible_known, if_pos rfl] at this; exact absurd this (Nat.lt_irrefl _)
    have hv' : (a.core.known q).version < a.core.cfg.version := by
      have := hv
      change ((makeEligible a.core a.core.cfg.primary r).known q).version <
        (makeEligibleCfg a.core r).version at this
      rw [makeEligible_known, if_neg hqp] at this
      change (a.core.known q).version < a.core.cfg.version + 1 at this
      rcases Nat.lt_succ_iff_lt_or_eq.1 this with hl | heq
      · exact hl
      · exfalso
        have hkq := h.core.knownEq q heq
        apply hqp; have := hq'.1; rw [hkq] at this; exact this.symm
    obtain ⟨t, h1, h2, h3, h4⟩ := h.deposed q hq' hv'
    refine ⟨t, h1, ?_, ?_, h4⟩
    · show ((makeEligible a.core a.core.cfg.primary r).known q).eligible t = true
      rw [makeEligible_known, if_neg hqp]; exact h2
    · show ((makeEligible a.core a.core.cfg.primary r).known t).primary ≠ q
      rw [makeEligible_known]; split_ifs with e
      · show a.core.cfg.primary ≠ q; exact fun e' => hqp e'.symm
      · exact h3
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
  selfPrimNoLease := by
    intro q hq
    change ((makeEligible a.core a.core.cfg.primary r).known q).primary = q at hq
    rw [makeEligible_known] at hq; split_ifs at hq with e
    · subst e; exact h.selfPrimNoLease _ (by rw [hkp])
    · exact h.selfPrimNoLease q hq
  rviewLen := h.rviewLen
  rviewHist := h.rviewHist }

/-- The replication actions that touch no lease state. -/
theorem leaseInvariant_core {m : Nat} {μ : Action Node} {c : State Node} (hs : Step m a.core μ c)
    (hpl : μ.isPlain = true) : LeaseInvariant P (withCore a c) := by
  cases hs with
  | append p _ _ _ =>
    refine leaseInvariant_withCore h (invariant_append h.core p) rfl rfl rfl ?_ (List.prefix_refl _)
    intro x; show a.core.log x <+: update a.core.log p (a.core.log p ++ _) x
    unfold update; split_ifs with e
    · subst e; exact List.prefix_append _ _
    · exact List.prefix_refl _
  | commit p hp _ hlen hcap =>
    refine leaseInvariant_withCore h (invariant_commit h.core p hp hlen hcap) rfl rfl rfl
      (fun _ => List.prefix_refl _) ?_
    show a.core.hist <+: (if a.core.commit p = a.core.hist.length then _ else _)
    split_ifs
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  | count p r hp hrp hf _ hle =>
    exact leaseInvariant_withCore h (invariant_count h.core p r hp hrp hf hle) rfl rfl rfl
      (fun _ => List.prefix_refl _) (List.prefix_refl _)
  | uncount p r hp hk hsy he =>
    exact leaseInvariant_withCore h (invariant_uncount h.core p r hp hk hsy he) rfl rfl rfl
      (fun _ => List.prefix_refl _) (List.prefix_refl _)
  | makeEligible p r hp hk hsy he => exact leaseInvariant_makeEligible h hp hk hsy he
  | replicate => simp [Action.isPlain] at hpl
  | ack => simp [Action.isPlain] at hpl
  | makeIneligible => simp [Action.isPlain] at hpl
  | learn => simp [Action.isPlain] at hpl
  | takeover => simp [Action.isPlain] at hpl
  | resync => simp [Action.isPlain] at hpl
  | restartEmpty => simp [Action.isPlain] at hpl
  | restartKeep => simp [Action.isPlain] at hpl
  | restartPartialKeep => simp [Action.isPlain] at hpl
  | restartPartialFresh => simp [Action.isPlain] at hpl

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
`max (rview r) (min (commit p) |L|)` is within `L`, within the history, and a
committed prefix. -/
theorem rview_data_ok {r : Node} {L : List Nat} (hpre : L <+: a.core.log (primaryOf a.core r))
    (hgrow : a.core.log r <+: L) :
    max (a.rview r) (min (a.core.commit (primaryOf a.core r)) L.length) ≤ L.length ∧
    max (a.rview r) (min (a.core.commit (primaryOf a.core r)) L.length) ≤ a.core.hist.length ∧
    L.take (max (a.rview r) (min (a.core.commit (primaryOf a.core r)) L.length)) <+: a.core.hist := by
  obtain ⟨h1, h2⟩ := h.rviewHist r
  have hrl := h.rviewLen r
  have hcH := h.core.caHist (primaryOf a.core r)
  have hcE := h.core.caEq (primaryOf a.core r)
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.max_le.2 ⟨Nat.le_trans hrl hgrow.length_le, Nat.min_le_right _ _⟩
  · exact Nat.max_le.2 ⟨h1, Nat.le_trans (Nat.min_le_left _ _) hcH⟩
  · rcases Nat.le_total (a.rview r) (min (a.core.commit (primaryOf a.core r)) L.length) with hle | hle
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
    (hcfg : c.cfg = a.core.cfg) (hknown : c.known = a.core.known)
    (hinc : c.incarnation = a.core.incarnation) (hhist : c.hist = a.core.hist)
    (hlogo : ∀ x, x ≠ r → c.log x = a.core.log x)
    (hpre : c.log r <+: a.core.log (primaryOf a.core r)) (hgrow : a.core.log r <+: c.log r) :
    LeaseInvariant P (recvData a r c none) := by
  have htp : ∀ x, ThinksPrimary c x ↔ ThinksPrimary a.core x := by
    intro x; unfold ThinksPrimary; rw [hknown, hinc]
  have hau : ∀ x, IsAuthoritative c x ↔ IsAuthoritative a.core x := by
    intro x; unfold IsAuthoritative; rw [hcfg, hinc]
  obtain ⟨hv1, hv2, hv3⟩ := rview_data_ok h hpre hgrow
  exact {
  core := hc
  primRecvLe := by
    intro x; show update a.primRecv r a.now x ≤ a.now
    unfold update; split_ifs
    · exact Nat.le_refl _
    · exact h.primRecvLe x
  ackRecvLe := h.ackRecvLe, rlLe := h.rlLe, tkoLe := h.tkoLe
  dataTLe := by
    intro x; show update a.dataT r a.now x ≤ update a.primRecv r a.now x
    unfold update; split_ifs
    · exact Nat.le_refl _
    · exact h.dataTLe x
  plLe := by
    intro p x v hv; show v ≤ update a.primRecv r a.now x
    unfold update; split_ifs with e
    · subst e; exact Nat.le_trans (h.plLe p x v hv) (h.primRecvLe x)
    · exact h.plLe p x v hv
  echoLe := h.echoLe, tkoAck := h.tkoAck
  deposed := by
    intro p hp hv
    show ∃ t, t ≠ p ∧ (c.known p).eligible t = true ∧ (c.known t).primary ≠ p ∧ _
    rw [hknown]
    have hv' : (a.core.known p).version < a.core.cfg.version := by
      have := hv; change (c.known p).version < c.cfg.version at this; rwa [hknown, hcfg] at this
    exact h.deposed p ((htp p).1 hp) hv'
  leaseBound := by
    intro x v hx; show (∃ b, a.ackRecv c.cfg.primary x = some b ∧ v ≤ b) ∨
      (∃ T, a.tko c.cfg.primary = some T ∧ v ≤ T)
    rw [hcfg]; exact h.leaseBound x v hx
  leaseAuth := fun x hnp hv => (hau x).2 (h.leaseAuth x (fun hp => hnp ((htp x).2 hp)) hv)
  selfPrimNoLease := by
    intro p hp; change (c.known p).primary = p at hp; rw [hknown] at hp; exact h.selfPrimNoLease p hp
  rviewLen := by
    intro x
    show update a.rview r (max (a.rview r) (min (a.core.commit (primaryOf a.core r)) (c.log r).length)) x
      ≤ (c.log x).length
    unfold update; split_ifs with e
    · subst e; exact hv1
    · rw [hlogo x e]; exact h.rviewLen x
  rviewHist := by
    intro x
    show update a.rview r (max (a.rview r) (min (a.core.commit (primaryOf a.core r)) (c.log r).length)) x
        ≤ c.hist.length ∧
      (c.log x).take (update a.rview r
        (max (a.rview r) (min (a.core.commit (primaryOf a.core r)) (c.log r).length)) x) <+: c.hist
    rw [hhist]
    unfold update; split_ifs with e
    · subst e; exact ⟨hv2, hv3⟩
    · rw [hlogo x e]; exact h.rviewHist x }

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
    have hbn := h.ackRecvLe _ r b hb
    have hmax' : maxOpt (a.rl r) e ≤ b := by
      unfold maxOpt
      cases hv : a.rl r with
      | none => exact heb
      | some v =>
        rcases h.leaseBound r v hv with ⟨b', hb', hvb⟩ | ⟨T, hT, hvT⟩
        · rw [← hpp, hb] at hb'; cases hb'; exact Nat.max_le.2 ⟨hvb, heb⟩
        · rw [← hpp] at hT
          exact Nat.max_le.2 ⟨Nat.le_trans hvT (h.tkoAck _ r T b hT hb), heb⟩
    exact {
    core := hbase.core
    primRecvLe := hbase.primRecvLe, ackRecvLe := hbase.ackRecvLe, tkoLe := hbase.tkoLe
    dataTLe := hbase.dataTLe, plLe := hbase.plLe, echoLe := hbase.echoLe, tkoAck := hbase.tkoAck
    deposed := hbase.deposed
    rlLe := by
      intro x v hx; show v ≤ a.now
      change update a.rl r (some (maxOpt (a.rl r) e)) x = some v at hx
      unfold update at hx; split_ifs at hx
      · cases hx; exact Nat.le_trans hmax' hbn
      · exact h.rlLe x v hx
    leaseBound := by
      intro x v hx
      change update a.rl r (some (maxOpt (a.rl r) e)) x = some v at hx
      show (∃ b, a.ackRecv a.core.cfg.primary x = some b ∧ v ≤ b) ∨
        (∃ T, a.tko a.core.cfg.primary = some T ∧ v ≤ T)
      unfold update at hx; split_ifs at hx with ex
      · subst ex; cases hx; left; exact ⟨b, by rw [← hpp]; exact hb, hmax'⟩
      · exact h.leaseBound x v hx
    leaseAuth := by
      intro x hnp hv
      change HolderValid P a.now (update a.rl r (some (maxOpt (a.rl r) e)) x) P.readDur at hv
      show IsAuthoritative a.core x
      by_cases ex : x = r
      · subst ex; rw [hkn] at hel hin; exact ⟨Or.inl hel, hin⟩
      · unfold update at hv; rw [if_neg ex] at hv
        exact h.leaseAuth x hnp hv
    selfPrimNoLease := by
      intro q hq; show update a.rl r (some (maxOpt (a.rl r) e)) q = none
      unfold update; split_ifs with eq
      · subst eq; exact absurd hq hne
      · exact h.selfPrimNoLease q hq
    rviewLen := hbase.rviewLen
    rviewHist := hbase.rviewHist }

/-! ### Acknowledgements -/

/-- An acknowledgement from `r`, applied to a replication state `c` that changes only
`acked` and `ackHigh`. -/
theorem leaseInvariant_recvAck {r : Node} {c : State Node} (hc : Invariant c)
    (hcfg : c.cfg = a.core.cfg) (hknown : c.known = a.core.known)
    (hinc : c.incarnation = a.core.incarnation) (hlog : c.log = a.core.log)
    (hhist : c.hist = a.core.hist) :
    LeaseInvariant P (recvAck a r c) := by
  have htp : ∀ x, ThinksPrimary c x ↔ ThinksPrimary a.core x := by
    intro x; unfold ThinksPrimary; rw [hknown, hinc]
  have hau : ∀ x, IsAuthoritative c x ↔ IsAuthoritative a.core x := by
    intro x; unfold IsAuthoritative; rw [hcfg, hinc]
  set p := primaryOf a.core r with hp
  have hAR : (recvAck a r c).ackRecv = update2 a.ackRecv p r (some a.now) := rfl
  have hAE : (recvAck a r c).ackEcho = update2 a.ackEcho p r (some a.now) := rfl
  have hPL : (recvAck a r c).pl = update2 a.pl p r (some (maxOpt (a.pl p r) (a.dataT r))) := rfl
  exact {
  core := hc
  primRecvLe := h.primRecvLe, rlLe := h.rlLe, tkoLe := h.tkoLe, dataTLe := h.dataTLe
  ackRecvLe := by
    intro q x b hb; rw [hAR] at hb
    by_cases e : q = p ∧ x = r
    · obtain ⟨rfl, rfl⟩ := e; rw [update2_self] at hb; cases hb; exact Nat.le_refl _
    · rw [update2_of_ne _ _ e] at hb; exact h.ackRecvLe q x b hb
  plLe := by
    intro q x v hv; rw [hPL] at hv; show v ≤ a.primRecv x
    by_cases e : q = p ∧ x = r
    · obtain ⟨rfl, rfl⟩ := e; rw [update2_self] at hv; cases hv
      unfold maxOpt; split
      · exact h.dataTLe _
      · rename_i w hw; exact Nat.max_le.2 ⟨h.plLe _ _ w hw, h.dataTLe _⟩
    · rw [update2_of_ne _ _ e] at hv; exact h.plLe q x v hv
  echoLe := by
    intro q x e he; rw [hAE] at he; rw [hAR]
    by_cases hqx : q = p ∧ x = r
    · obtain ⟨rfl, rfl⟩ := hqx; rw [update2_self] at he; cases he
      exact ⟨a.now, update2_self _ _ _ _, Nat.le_refl _⟩
    · rw [update2_of_ne _ _ hqx] at he; rw [update2_of_ne _ _ hqx]; exact h.echoLe q x e he
  tkoAck := by
    intro q x T b hT hb; rw [hAR] at hb
    by_cases e : q = p ∧ x = r
    · obtain ⟨rfl, rfl⟩ := e; rw [update2_self] at hb; cases hb; exact h.tkoLe _ T hT
    · rw [update2_of_ne _ _ e] at hb; exact h.tkoAck q x T b hT hb
  deposed := by
    intro q hq hv
    show ∃ t, t ≠ q ∧ (c.known q).eligible t = true ∧ (c.known t).primary ≠ q ∧
      ∀ x, update2 a.pl p r (some (maxOpt (a.pl p r) (a.dataT r))) q t = some x →
        x + P.primDur ≤ a.now + P.drift
    rw [hknown]
    have hv' : (a.core.known q).version < a.core.cfg.version := by
      have := hv; change (c.known q).version < c.cfg.version at this; rwa [hknown, hcfg] at this
    obtain ⟨t, h1, h2, h3, h4⟩ := h.deposed q ((htp q).1 hq) hv'
    refine ⟨t, h1, h2, h3, ?_⟩
    intro x hx
    by_cases e : q = p ∧ t = r
    · exfalso; obtain ⟨rfl, rfl⟩ := e; exact h3 rfl
    · rw [update2_of_ne _ _ e] at hx; exact h4 x hx
  leaseBound := by
    intro x v hx
    show (∃ b, update2 a.ackRecv p r (some a.now) c.cfg.primary x = some b ∧ v ≤ b) ∨
      (∃ T, a.tko c.cfg.primary = some T ∧ v ≤ T)
    rw [hcfg]
    by_cases e : a.core.cfg.primary = p ∧ x = r
    · obtain ⟨e1, rfl⟩ := e; rw [e1, update2_self]; left; exact ⟨a.now, rfl, h.rlLe x v hx⟩
    · rw [update2_of_ne _ _ e]; exact h.leaseBound x v hx
  leaseAuth := fun x hnp hv => (hau x).2 (h.leaseAuth x (fun hp => hnp ((htp x).2 hp)) hv)
  selfPrimNoLease := by
    intro q hq; change (c.known q).primary = q at hq; rw [hknown] at hq; exact h.selfPrimNoLease q hq
  rviewLen := by intro x; show a.rview x ≤ (c.log x).length; rw [hlog]; exact h.rviewLen x
  rviewHist := by
    intro x; show a.rview x ≤ c.hist.length ∧ (c.log x).take (a.rview x) <+: c.hist
    rw [hlog, hhist]; exact h.rviewHist x }

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
theorem leaseInvariant_learn {n : Node} (hk : ¬ KnowsLatest a.core n) :
    LeaseInvariant P (learnL a n) := by
  have hnp : n ≠ a.core.cfg.primary := by
    intro e; apply hk; unfold KnowsLatest; rw [e, h.core.primKnows]
  have hK := learn_known (s := a.core) (n := n)
  have hinc : (learn a.core n).incarnation = a.core.incarnation := rfl
  have hcfg : (learn a.core n).cfg = a.core.cfg := rfl
  have htp : ∀ x, ThinksPrimary (learn a.core n) x → x ≠ n ∧ ThinksPrimary a.core x :=
    fun _ => learn_thinksPrimary hnp
  exact {
  core := invariant_learn h.core n hk
  primRecvLe := by
    intro x; show update a.primRecv n a.now x ≤ a.now
    unfold update; split_ifs
    · exact Nat.le_refl _
    · exact h.primRecvLe x
  ackRecvLe := h.ackRecvLe, rlLe := h.rlLe, tkoLe := h.tkoLe
  dataTLe := by
    intro x; show a.dataT x ≤ update a.primRecv n a.now x
    unfold update; split_ifs with e
    · subst e; exact Nat.le_trans (h.dataTLe x) (h.primRecvLe x)
    · exact h.dataTLe x
  plLe := by
    intro p x v hv; show v ≤ update a.primRecv n a.now x
    unfold update; split_ifs with e
    · subst e; exact Nat.le_trans (h.plLe p x v hv) (h.primRecvLe x)
    · exact h.plLe p x v hv
  echoLe := h.echoLe, tkoAck := h.tkoAck
  deposed := by
    intro p hp hv
    obtain ⟨hpn, hp'⟩ := htp p hp
    have hv' : (a.core.known p).version < a.core.cfg.version := by
      have := hv; change ((learn a.core n).known p).version < (learn a.core n).cfg.version at this
      rwa [hK, if_neg hpn, hcfg] at this
    obtain ⟨t, h1, h2, h3, h4⟩ := h.deposed p hp' hv'
    refine ⟨t, h1, ?_, ?_, h4⟩
    · show ((learn a.core n).known p).eligible t = true; rw [hK, if_neg hpn]; exact h2
    · show ((learn a.core n).known t).primary ≠ p
      rw [hK]; split_ifs with e
      · show a.core.cfg.primary ≠ p; exact (stale_ne_prim h.core hv').symm
      · exact h3
  leaseBound := h.leaseBound
  leaseAuth := by
    intro x hnp hv
    show IsAuthoritative a.core x
    by_cases hx : ThinksPrimary a.core x
    · exfalso
      have := h.selfPrimNoLease x hx.1
      unfold ReadLeaseValid HolderValid at hv; change HolderValid P a.now (a.rl x) P.readDur at hv
      unfold HolderValid at hv; rw [this] at hv; exact hv
    · exact h.leaseAuth x hx hv
  selfPrimNoLease := by
    intro q hq
    change ((learn a.core n).known q).primary = q at hq
    rw [hK] at hq; split_ifs at hq with e
    · subst e; exact absurd hq.symm hnp
    · exact h.selfPrimNoLease q hq
  rviewLen := h.rviewLen
  rviewHist := h.rviewHist }

omit h in
include hM in
/-- A read lease whose start is bounded by the demotion guards is not valid. -/
theorem lease_over_of_guards {now v : Nat} {ackRecv tko : Option Nat}
    (hb : (∃ b, ackRecv = some b ∧ v ≤ b) ∨ (∃ T, tko = some T ∧ v ≤ T))
    (hgo : GrantorOver P now ackRecv P.readDur)
    (hwo : ∀ T, tko = some T → T + P.readDur + P.margin ≤ now + P.drift) :
    ¬ HolderValid P now (some v) P.readDur := by
  intro hv; unfold HolderValid at hv
  rcases hb with ⟨b, hb, hvb⟩ | ⟨T, hT, hvT⟩
  · rw [hb] at hgo; unfold GrantorOver at hgo; omega
  · have := hwo T hT; omega

include hM in
/-- Demotion. The demoted replica's read lease is over, by the two waits. -/
theorem leaseInvariant_demote {p r : Node} (hp : ThinksPrimary a.core p) (hk : KnowsLatest a.core p)
    (he : a.core.cfg.eligible r = true) (hgo : GrantorOver P a.now (a.ackRecv p r) P.readDur)
    (hwo : ∀ T, a.tko p = some T → T + P.readDur + P.margin ≤ a.now + P.drift) :
    LeaseInvariant P (withCore a (makeIneligible a.core p r)) := by
  have hkn : a.core.known p = a.core.cfg := h.core.knownEq p hk
  have hpp : p = a.core.cfg.primary := by have := hp.1; rw [hkn] at this; exact this.symm
  subst hpp
  have hkp : a.core.known a.core.cfg.primary = a.core.cfg := hkn
  have htp := makeIneligible_thinksPrimary (s := a.core) (r := r) hkp
  exact {
  core := invariant_makeIneligible h.core hp hk he
  primRecvLe := h.primRecvLe, ackRecvLe := h.ackRecvLe, rlLe := h.rlLe, tkoLe := h.tkoLe
  dataTLe := h.dataTLe, plLe := h.plLe, echoLe := h.echoLe, tkoAck := h.tkoAck
  deposed := by
    intro q hq hv
    have hq' := (htp q).1 hq
    have hqp : q ≠ a.core.cfg.primary := by
      intro e; subst e
      have := hv
      change ((makeIneligible a.core a.core.cfg.primary r).known a.core.cfg.primary).version <
        (makeIneligibleCfg a.core r).version at this
      rw [makeIneligible_known, if_pos rfl] at this; exact absurd this (Nat.lt_irrefl _)
    have hv' : (a.core.known q).version < a.core.cfg.version := by
      have := hv
      change ((makeIneligible a.core a.core.cfg.primary r).known q).version <
        (makeIneligibleCfg a.core r).version at this
      rw [makeIneligible_known, if_neg hqp] at this
      change (a.core.known q).version < a.core.cfg.version + 1 at this
      rcases Nat.lt_succ_iff_lt_or_eq.1 this with hl | heq
      · exact hl
      · exfalso
        have hkq := h.core.knownEq q heq
        apply hqp; have := hq'.1; rw [hkq] at this; exact this.symm
    obtain ⟨t, h1, h2, h3, h4⟩ := h.deposed q hq' hv'
    refine ⟨t, h1, ?_, ?_, h4⟩
    · show ((makeIneligible a.core a.core.cfg.primary r).known q).eligible t = true
      rw [makeIneligible_known, if_neg hqp]; exact h2
    · show ((makeIneligible a.core a.core.cfg.primary r).known t).primary ≠ q
      rw [makeIneligible_known]; split_ifs with e
      · show a.core.cfg.primary ≠ q; exact fun e' => hqp e'.symm
      · exact h3
  leaseBound := h.leaseBound
  leaseAuth := by
    intro x hnp hv
    have hx := h.leaseAuth x (fun hp' => hnp ((htp x).2 hp')) hv
    by_cases ex : x = r
    · exfalso; subst ex
      change HolderValid P a.now (a.rl x) P.readDur at hv
      cases hrl : a.rl x with
      | none => rw [hrl] at hv; exact hv
      | some v =>
        rw [hrl] at hv
        exact lease_over_of_guards hM (h.leaseBound x v hrl) hgo hwo hv
    · obtain ⟨h1, h2⟩ := hx
      refine ⟨?_, h2⟩
      show (if x = r then false else a.core.cfg.eligible x) = true ∨ x = a.core.cfg.primary
      rw [if_neg ex]; exact h1
  selfPrimNoLease := by
    intro q hq
    change ((makeIneligible a.core a.core.cfg.primary r).known q).primary = q at hq
    rw [makeIneligible_known] at hq; split_ifs at hq with e
    · subst e; exact h.selfPrimNoLease _ (by rw [hkp])
    · exact h.selfPrimNoLease q hq
  rviewLen := h.rviewLen
  rviewHist := h.rviewHist }

/-- Takeover. The deposed primary gets its witness: the taker, eligible in its
configuration, whose lease it can never again hold; every existing read lease started
before the takeover. -/
theorem leaseInvariant_takeover {n : Node} (hk : KnowsLatest a.core n) (he : a.core.cfg.eligible n = true)
    (hnp : n ≠ a.core.cfg.primary) (hin : a.core.cfg.incarnation n = a.core.incarnation n)
    (hwait : a.primRecv n + P.primDur ≤ a.now + P.drift) :
    LeaseInvariant P (takeoverL a n) := by
  have hK := takeover_known (s := a.core) (n := n)
  have htp := takeover_thinksPrimary (s := a.core) hin
  have hcfg : (takeover a.core n).cfg = takeoverCfg a.core n := rfl
  have hinc : (takeover a.core n).incarnation = a.core.incarnation := rfl
  have hlog : (takeover a.core n).log = a.core.log := rfl
  have hhist : (takeover a.core n).hist = a.core.hist := rfl
  exact {
  core := invariant_takeover h.core n hk he hnp hin
  primRecvLe := h.primRecvLe, dataTLe := h.dataTLe
  ackRecvLe := by
    intro q x b hb; change update a.ackRecv n (fun _ => none) q x = some b at hb
    by_cases e : q = n
    · subst e; rw [update_self] at hb; exact absurd hb (by simp)
    · rw [update_of_ne _ _ e] at hb; exact h.ackRecvLe q x b hb
  rlLe := by
    intro x v hx; change update a.rl n none x = some v at hx
    by_cases e : x = n
    · subst e; rw [update_self] at hx; exact absurd hx (by simp)
    · rw [update_of_ne _ _ e] at hx; exact h.rlLe x v hx
  tkoLe := by
    intro q T hT; change update a.tko n (some a.now) q = some T at hT
    by_cases e : q = n
    · subst e; rw [update_self] at hT; cases hT; exact Nat.le_refl _
    · rw [update_of_ne _ _ e] at hT; exact h.tkoLe q T hT
  plLe := by
    intro q x v hv; change update a.pl n (fun _ => none) q x = some v at hv
    by_cases e : q = n
    · subst e; rw [update_self] at hv; exact absurd hv (by simp)
    · rw [update_of_ne _ _ e] at hv; exact h.plLe q x v hv
  echoLe := by
    intro q x e he
    change update a.ackEcho n (fun _ => none) q x = some e at he
    show ∃ b, update a.ackRecv n (fun _ => none) q x = some b ∧ e ≤ b
    by_cases eq : q = n
    · subst eq; rw [update_self] at he; exact absurd he (by simp)
    · rw [update_of_ne _ _ eq] at he; rw [update_of_ne _ _ eq]; exact h.echoLe q x e he
  tkoAck := by
    intro q x T b hT hb
    change update a.tko n (some a.now) q = some T at hT
    change update a.ackRecv n (fun _ => none) q x = some b at hb
    by_cases eq : q = n
    · subst eq; rw [update_self] at hb; exact absurd hb (by simp)
    · rw [update_of_ne _ _ eq] at hT hb; exact h.tkoAck q x T b hT hb
  deposed := by
    intro q hq hv
    show ∃ t, t ≠ q ∧ ((takeover a.core n).known q).eligible t = true ∧
      ((takeover a.core n).known t).primary ≠ q ∧
      ∀ x, update a.pl n (fun _ => none) q t = some x → x + P.primDur ≤ a.now + P.drift
    rcases (htp q).1 hq with rfl | ⟨hqn, hq'⟩
    · exfalso; have := hv; change ((takeover a.core q).known q).version < (takeoverCfg a.core q).version at this
      rw [hK, if_pos rfl] at this; exact Nat.lt_irrefl _ this
    · have hv0 : (a.core.known q).version < a.core.cfg.version + 1 := by
        have := hv; change ((takeover a.core n).known q).version < (takeoverCfg a.core n).version at this
        rw [hK, if_neg hqn] at this; exact this
      rcases Nat.lt_succ_iff_lt_or_eq.1 hv0 with hl | heq
      · -- deposed before: the old witness still serves.
        obtain ⟨t, h1, h2, h3, h4⟩ := h.deposed q hq' hl
        refine ⟨t, h1, ?_, ?_, ?_⟩
        · rw [hK, if_neg hqn]; exact h2
        · rw [hK]; split_ifs with e
          · show n ≠ q; exact fun e' => hqn e'.symm
          · exact h3
        · intro x hx; unfold update at hx; rw [if_neg hqn] at hx; exact h4 x hx
      · -- deposed now: `q` was the primary, and `n` is its witness.
        have hkq := h.core.knownEq q heq
        have hqp : q = a.core.cfg.primary := by have := hq'.1; rw [hkq] at this; exact this.symm
        refine ⟨n, fun e => hnp (e ▸ hqp), ?_, ?_, ?_⟩
        · rw [hK, if_neg hqn, hkq]; exact he
        · rw [hK, if_pos rfl]; show n ≠ q; exact fun e => hnp (e ▸ hqp)
        · intro x hx; unfold update at hx; rw [if_neg hqn] at hx
          have := h.plLe q n x hx; omega
  leaseBound := by
    intro x v hx
    change update a.rl n none x = some v at hx
    show (∃ b, update a.ackRecv n (fun _ => none) (takeoverCfg a.core n).primary x = some b ∧ v ≤ b) ∨
      (∃ T, update a.tko n (some a.now) (takeoverCfg a.core n).primary = some T ∧ v ≤ T)
    by_cases ex : x = n
    · subst ex; rw [update_self] at hx; exact absurd hx (by simp)
    · rw [update_of_ne _ _ ex] at hx
      right; refine ⟨a.now, ?_, h.rlLe x v hx⟩
      show update a.tko n (some a.now) n = some a.now; exact update_self _ _ _
  leaseAuth := by
    intro x hnp' hv
    change HolderValid P a.now (update a.rl n none x) P.readDur at hv
    by_cases ex : x = n
    · subst ex; rw [update_self] at hv; exact hv.elim
    · rw [update_of_ne _ _ ex] at hv
      have hx : ¬ ThinksPrimary a.core x := fun hp => hnp' ((htp x).2 (Or.inr ⟨ex, hp⟩))
      obtain ⟨h1, h2⟩ := h.leaseAuth x hx hv
      have hxq : x ≠ a.core.cfg.primary := by
        intro e; apply hx; subst e
        -- the primary thinks it is primary iff authoritative; and a non-thinking primary holds no lease
        exfalso
        have := h.selfPrimNoLease _ (by rw [h.core.primKnows])
        unfold HolderValid at hv; rw [this] at hv; exact hv
      refine ⟨Or.inl ?_, h2⟩
      show takeoverEligible a.core n x = true
      unfold takeoverEligible
      rcases h1 with h1 | h1
      · simp [h1, hxq, ex]
      · exact absurd h1 hxq
  selfPrimNoLease := by
    intro q hq
    show update a.rl n none q = none
    unfold update; split_ifs with e
    · rfl
    · change ((takeover a.core n).known q).primary = q at hq
      rw [hK, if_neg e] at hq; exact h.selfPrimNoLease q hq
  rviewLen := h.rviewLen
  rviewHist := h.rviewHist }

/-- A full resync: the replica's committed view starts over. -/
theorem leaseInvariant_resync {r : Node} (hne : primaryOf a.core r ≠ r)
    (hnpre : ¬ (a.core.log r <+: a.core.log (primaryOf a.core r)))
    (hsy : a.core.sync (primaryOf a.core r) r = false)
    (hke : (a.core.known (primaryOf a.core r)).eligible r = false) :
    LeaseInvariant P (resyncL a r) := by
  have hcfg : (resync a.core r).cfg = a.core.cfg := rfl
  have hknown : (resync a.core r).known = a.core.known := rfl
  have hinc : (resync a.core r).incarnation = a.core.incarnation := rfl
  have hhist : (resync a.core r).hist = a.core.hist := rfl
  have htp : ∀ x, ThinksPrimary (resync a.core r) x ↔ ThinksPrimary a.core x := fun _ => Iff.rfl
  have hau : ∀ x, IsAuthoritative (resync a.core r) x ↔ IsAuthoritative a.core x := fun _ => Iff.rfl
  exact {
  core := invariant_resync h.core r hne hsy hke
  primRecvLe := h.primRecvLe, ackRecvLe := h.ackRecvLe, rlLe := h.rlLe, tkoLe := h.tkoLe
  dataTLe := h.dataTLe, plLe := h.plLe, echoLe := h.echoLe, tkoAck := h.tkoAck
  deposed := h.deposed
  leaseBound := h.leaseBound
  leaseAuth := fun x hnp hv => h.leaseAuth x hnp hv
  selfPrimNoLease := h.selfPrimNoLease
  rviewLen := by
    intro x; show update a.rview r 0 x ≤ ((resync a.core r).log x).length
    unfold update; split_ifs with e
    · exact Nat.zero_le _
    · rw [resync_log_other e]; exact h.rviewLen x
  rviewHist := by
    intro x
    show update a.rview r 0 x ≤ a.core.hist.length ∧
      ((resync a.core r).log x).take (update a.rview r 0 x) <+: a.core.hist
    unfold update; split_ifs with e
    · exact ⟨Nat.zero_le _, by simp⟩
    · rw [resync_log_other e]; exact h.rviewHist x }

/-! ### Restarts -/

/-- A restart of `n`, with replication state `c` afterwards. `c` keeps the configuration
and every other node's incarnation and log, and the history. -/
theorem leaseInvariant_restart {n : Node} {c : State Node} (hc : Invariant c)
    (hk : KnowsLatest a.core n)
    (hcfg : c.cfg = a.core.cfg) (hknown : c.known = a.core.known)
    (hinc : ∀ x, x ≠ n → c.incarnation x = a.core.incarnation x)
    (hlog : ∀ x, x ≠ n → c.log x = a.core.log x) (hhist : c.hist = a.core.hist) :
    LeaseInvariant P (restartL a n c) := by
  have htp : ∀ x, x ≠ n → (ThinksPrimary c x ↔ ThinksPrimary a.core x) := by
    intro x hx; unfold ThinksPrimary; rw [hknown, hinc x hx]
  have hau : ∀ x, x ≠ n → (IsAuthoritative c x ↔ IsAuthoritative a.core x) := by
    intro x hx; unfold IsAuthoritative; rw [hcfg, hinc x hx]
  exact {
  core := hc
  primRecvLe := by
    intro x; show update a.primRecv n a.now x ≤ a.now
    unfold update; split_ifs
    · exact Nat.le_refl _
    · exact h.primRecvLe x
  ackRecvLe := by
    intro q x b hb; change update a.ackRecv n (fun _ => none) q x = some b at hb
    by_cases e : q = n
    · subst e; rw [update_self] at hb; exact absurd hb (by simp)
    · rw [update_of_ne _ _ e] at hb; exact h.ackRecvLe q x b hb
  rlLe := by
    intro x v hx; change update a.rl n none x = some v at hx
    by_cases e : x = n
    · subst e; rw [update_self] at hx; exact absurd hx (by simp)
    · rw [update_of_ne _ _ e] at hx; exact h.rlLe x v hx
  tkoLe := by
    intro q T hT; change update a.tko n (some a.now) q = some T at hT
    by_cases e : q = n
    · subst e; rw [update_self] at hT; cases hT; exact Nat.le_refl _
    · rw [update_of_ne _ _ e] at hT; exact h.tkoLe q T hT
  dataTLe := by
    intro x; show update a.dataT n a.now x ≤ update a.primRecv n a.now x
    unfold update; split_ifs
    · exact Nat.le_refl _
    · exact h.dataTLe x
  plLe := by
    intro q x v hv; change update a.pl n (fun _ => none) q x = some v at hv
    show v ≤ update a.primRecv n a.now x
    by_cases eq : q = n
    · subst eq; rw [update_self] at hv; exact absurd hv (by simp)
    · rw [update_of_ne _ _ eq] at hv
      by_cases ex : x = n
      · subst ex; rw [update_self]; exact Nat.le_trans (h.plLe q x v hv) (h.primRecvLe x)
      · rw [update_of_ne _ _ ex]; exact h.plLe q x v hv
  echoLe := by
    intro q x e he
    change update a.ackEcho n (fun _ => none) q x = some e at he
    show ∃ b, update a.ackRecv n (fun _ => none) q x = some b ∧ e ≤ b
    by_cases eq : q = n
    · subst eq; rw [update_self] at he; exact absurd he (by simp)
    · rw [update_of_ne _ _ eq] at he; rw [update_of_ne _ _ eq]; exact h.echoLe q x e he
  tkoAck := by
    intro q x T b hT hb
    change update a.tko n (some a.now) q = some T at hT
    change update a.ackRecv n (fun _ => none) q x = some b at hb
    by_cases eq : q = n
    · subst eq; rw [update_self] at hb; exact absurd hb (by simp)
    · rw [update_of_ne _ _ eq] at hT hb; exact h.tkoAck q x T b hT hb
  deposed := by
    intro q hq hv
    have hv' : (a.core.known q).version < a.core.cfg.version := by
      have := hv; change (c.known q).version < c.cfg.version at this; rwa [hknown, hcfg] at this
    have hqn : q ≠ n := by
      intro e; subst e; apply Nat.lt_irrefl _; unfold KnowsLatest at hk; rw [hk] at hv'; exact hv'
    obtain ⟨t, h1, h2, h3, h4⟩ := h.deposed q ((htp q hqn).1 hq) hv'
    refine ⟨t, h1, ?_, ?_, ?_⟩
    · show (c.known q).eligible t = true; rw [hknown]; exact h2
    · show (c.known t).primary ≠ q; rw [hknown]; exact h3
    · intro x hx; change update a.pl n (fun _ => none) q t = some x at hx
      unfold update at hx; rw [if_neg hqn] at hx; exact h4 x hx
  leaseBound := by
    intro x v hx
    change update a.rl n none x = some v at hx
    show (∃ b, update a.ackRecv n (fun _ => none) c.cfg.primary x = some b ∧ v ≤ b) ∨
      (∃ T, update a.tko n (some a.now) c.cfg.primary = some T ∧ v ≤ T)
    rw [hcfg]
    by_cases ex : x = n
    · subst ex; rw [update_self] at hx; exact absurd hx (by simp)
    · rw [update_of_ne _ _ ex] at hx
      by_cases hpn : a.core.cfg.primary = n
      · rw [hpn, update_self]; right; exact ⟨a.now, update_self _ _ _, h.rlLe x v hx⟩
      · rw [update_of_ne _ _ hpn, update_of_ne _ _ hpn]; exact h.leaseBound x v hx
  leaseAuth := by
    intro x hnp hv
    change HolderValid P a.now (update a.rl n none x) P.readDur at hv
    by_cases ex : x = n
    · subst ex; rw [update_self] at hv; exact hv.elim
    · rw [update_of_ne _ _ ex] at hv
      exact (hau x ex).2 (h.leaseAuth x (fun hp => hnp ((htp x ex).2 hp)) hv)
  selfPrimNoLease := by
    intro q hq
    show update a.rl n none q = none
    unfold update; split_ifs with e
    · rfl
    · change (c.known q).primary = q at hq; rw [hknown] at hq; exact h.selfPrimNoLease q hq
  rviewLen := by
    intro x; show update a.rview n 0 x ≤ (c.log x).length
    unfold update; split_ifs with e
    · exact Nat.zero_le _
    · rw [hlog x e]; exact h.rviewLen x
  rviewHist := by
    intro x
    show update a.rview n 0 x ≤ c.hist.length ∧ (c.log x).take (update a.rview n 0 x) <+: c.hist
    rw [hhist]
    unfold update; split_ifs with e
    · exact ⟨Nat.zero_le _, by simp⟩
    · rw [hlog x e]; exact h.rviewHist x }

theorem leaseInvariant_restartEmpty {n : Node} (hk : KnowsLatest a.core n)
    (hsv : ∃ m, m ≠ n ∧ IsAuthoritative a.core m) :
    LeaseInvariant P (restartL a n (restartEmpty a.core n)) :=
  leaseInvariant_restart h (invariant_restartEmpty h.core n hk hsv) hk rfl rfl
    (fun _ e => restartEmpty_inc_other e) (fun _ e => restartEmpty_log_other e) rfl

theorem leaseInvariant_restartKeep {n : Node} (hk : KnowsLatest a.core n) :
    LeaseInvariant P (restartL a n (restartKeep a.core n)) :=
  leaseInvariant_restart h (invariant_restartKeep h.core n hk) hk rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) rfl

theorem leaseInvariant_restartPartialKeep {n : Node} {k : Nat} (hk : KnowsLatest a.core n)
    (hkl : k < (a.core.log n).length) (hkeep : a.core.ackHigh n ≤ k) :
    LeaseInvariant P (restartL a n (restartPartialKeep a.core n k)) :=
  leaseInvariant_restart h (invariant_restartPartialKeep h.core n k hk hkl hkeep) hk rfl rfl
    (fun _ _ => rfl) (fun _ e => restartPartialKeep_log_other e) rfl

theorem leaseInvariant_restartPartialFresh {n : Node} {k : Nat} (hk : KnowsLatest a.core n)
    (hkl : k < (a.core.log n).length) (hfresh : k < a.core.ackHigh n)
    (hsv : ∃ m, m ≠ n ∧ IsAuthoritative a.core m) :
    LeaseInvariant P (restartL a n (restartPartialFresh a.core n k)) :=
  leaseInvariant_restart h (invariant_restartPartialFresh h.core n k hk hsv hkl hfresh) hk rfl rfl
    (fun _ e => restartEmpty_inc_other e) (fun _ e => restartPartialFresh_log_other e) rfl

end preserve

/-! ## Every step preserves the invariant; the theorem -/

/-- Every lease-layer step preserves the invariant, given `margin ≥ 2 · drift`. -/
theorem leaseInvariant_step {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {m : Nat}
    {a a' : LState Node} {μ : LAction Node} (h : LeaseInvariant P a) (hs : LStep m P a μ a') :
    LeaseInvariant P a' := by
  cases hs with
  | tick => exact leaseInvariant_tick h
  | core μ c hc hpl => exact leaseInvariant_core h hc hpl
  | replicate r _ hpre hlt => exact leaseInvariant_replicate h hpre hlt
  | heartbeat r _ hpre => exact leaseInvariant_heartbeat h hpre
  | heartbeatGrant r hne hp hpre hg => exact leaseInvariant_heartbeatGrant hM h hne hp hpre hg
  | ack r hne hpre hlt => exact leaseInvariant_ack h hne hpre hlt
  | ackRenew r _ _ => exact leaseInvariant_ackRenew h
  | learn n hk => exact leaseInvariant_learn h hk
  | demote p r hp hk he hgo hwo => exact leaseInvariant_demote hM h hp hk he hgo hwo
  | takeover n hk he hnp hin hwait => exact leaseInvariant_takeover h hk he hnp hin hwait
  | resync r hne hnpre hsy hke => exact leaseInvariant_resync h hne hnpre hsy hke
  | restartEmpty n hk hsv => exact leaseInvariant_restartEmpty h hk hsv
  | restartKeep n hk => exact leaseInvariant_restartKeep h hk
  | restartPartialKeep n k hk hkl hkeep => exact leaseInvariant_restartPartialKeep h hk hkl hkeep
  | restartPartialFresh n k hk hkl hfresh hsv => exact leaseInvariant_restartPartialFresh h hk hkl hfresh hsv

/-- The invariant holds in every reachable state. -/
theorem leaseInvariant_reachable {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {m : Nat}
    {i : Node} {a : LState Node} (h : LReachable m P i a) : LeaseInvariant P a :=
  let ⟨_, run⟩ := h
  LTS.mtrInv_of_trInv (p := LeaseInvariant P) (fun _ _ _ hs h => leaseInvariant_step hM h hs) _ _ _ run
    (leaseInvariant_init P i)

/-- **No stale linearizable read.** If the clock-drift margin is at least twice the drift
bound, then in every reachable state, for every `min-sync-replicas` value, any node
that may serve a linearizable read (a primary holding its lease from every eligible
replica it knows, or a sync replica holding a read lease, each with nothing
uncommitted) has exactly the committed history as its log. -/
theorem noStaleRead {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {m : Nat} {i : Node}
    {a : LState Node} (h : LReachable m P i a) : NoStaleRead P a :=
  leaseInvariant_noStaleRead hM (leaseInvariant_reachable hM h)

/-- The replication safety theorem also holds of the lease layer's reachable states. -/
theorem lease_safety {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {m : Nat} {i : Node}
    {a : LState Node} (h : LReachable m P i a) : Safety a.core :=
  invariant_safety (leaseInvariant_reachable hM h).core

end SyncReplication
