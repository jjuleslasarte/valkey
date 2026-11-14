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
`p` cannot hold a valid lease from every eligible replica it knows. An acknowledgement
from `t` still in flight was sent on a connection the takeover closed. The current primary, by the
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
of change: `leaseInvariant_frame` for a step that moves no lease state (resync, a
dropped message, the plain actions), `msgs_frame` for the conjuncts about messages in
flight, `deposed_frame` and `deposed_cfgBump` for
the deposed primary's witness, `cleared_rows` for a node whose lease rows are cleared
(takeover, restart), `committedView_reset` for a node whose view starts over (resync,
restart), `primaryTraffic_bump` for a node whose traffic timer restarts. Each
preservation proof is then left with the conjuncts its action touches: the grant of a
read lease in `sendGrant` and its arrival in `deliverData`, the deposed primary's new witness and the bound on
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

/-! ## Lease starts, held and in flight -/

/-- `x` is the start of a read lease `r` holds, or of one that a current echo in flight
to `r` would give it. -/
def LeaseStart (a : LeaseState Node) (r : Node) (x : Nat) : Prop :=
  a.readLease r = some x ∨ ∃ msg ∈ a.net, msg.Current a ∧ msg.dst = r ∧ msg.echo = some x

/-- `x` is the start of the primary lease `p` holds from `r`, or of one that a current
acknowledgement in flight from `r` to `p` would give it. -/
def PrimStart (a : LeaseState Node) (p r : Node) (x : Nat) : Prop :=
  a.primaryLease p r = some x ∨
    ∃ msg ∈ a.net, msg.Current a ∧ msg.dst = p ∧ msg.src = r ∧ msg.ackStart = some x

/-- A step that keeps or shrinks the read leases and the current messages keeps or
shrinks the lease starts. -/
theorem leaseStart_mono (a a' : LeaseState Node)
    (hRL : ∀ r x, a'.readLease r = some x → a.readLease r = some x)
    (hnet : ∀ msg ∈ a'.net, msg ∈ a.net ∧ (msg.Current a' → msg.Current a))
    {r : Node} {x : Nat} (h : LeaseStart a' r x) : LeaseStart a r x := by
  rcases h with h | ⟨msg, hm, hc, hd, he⟩
  · exact Or.inl (hRL r x h)
  · obtain ⟨hm', hc'⟩ := hnet msg hm; exact Or.inr ⟨msg, hm', hc' hc, hd, he⟩

/-- The same for primary-lease starts. -/
theorem primStart_mono (a a' : LeaseState Node)
    (hPL : ∀ p r x, a'.primaryLease p r = some x → a.primaryLease p r = some x)
    (hnet : ∀ msg ∈ a'.net, msg ∈ a.net ∧ (msg.Current a' → msg.Current a))
    {p r : Node} {x : Nat} (h : PrimStart a' p r x) : PrimStart a p r x := by
  rcases h with h | ⟨msg, hm, hc, hd, hs, he⟩
  · exact Or.inl (hPL p r x h)
  · obtain ⟨hm', hc'⟩ := hnet msg hm; exact Or.inr ⟨msg, hm', hc' hc, hd, hs, he⟩

/-- A message's connection has its two ends. -/
theorem Msg.link_ends {Node : Type} (m : Msg Node) :
    (m.link.1 = m.src ∧ m.link.2 = m.dst) ∨ (m.link.1 = m.dst ∧ m.link.2 = m.src) := by
  cases m <;> simp [Msg.link, Msg.src, Msg.dst]

/-- After `n`'s connections close, a message still current was current before and has
neither end at `n`. -/
theorem current_of_bump {a a' : LeaseState Node} {n : Node} (hg : a'.gen = closeAll a.gen n)
    {msg : Msg Node} (hle : msg.g ≤ a.gen msg.link.1 msg.link.2) (hc : msg.Current a') :
    msg.Current a ∧ msg.src ≠ n ∧ msg.dst ≠ n := by
  unfold Msg.Current at *; rw [hg] at hc
  obtain ⟨h1, h2, h3⟩ := closeAll_open hle hc
  refine ⟨h3, ?_, ?_⟩ <;> rcases Msg.link_ends msg with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [← e1]; exact h1
  · rw [← e2]; exact h2
  · rw [← e2]; exact h2
  · rw [← e1]; exact h1

/-! ## Planned demotion -/

/-- `x` is the start of a read lease that a current echo in flight to `r` would give it. -/
def InFlightEcho (a : LeaseState Node) (r : Node) (x : Nat) : Prop :=
  ∃ msg ∈ a.net, msg.Current a ∧ msg.dst = r ∧ msg.echo = some x

/-- The facts that make a planned demotion safe. `p` asks `r` to drop its read lease and
waits for the confirmation; the request closes the connection, so no echo sent before it
is still current, and `p` echoes nothing while it has received no acknowledgement since
asking. -/
structure DropInvariant (a : LeaseState Node) : Prop where
  /-- A confirmed drop is reset by any later acknowledgement. -/
  confirmedNoEcho : ∀ p r, a.dropConfirmed p r = true → a.ackEcho p r = none
  /-- The current primary's confirmed drop: the replica holds no read lease and has none
  in flight. -/
  confirmedNoLease : ∀ p r, a.dropConfirmed p r = true → p = a.core.cfg.primary →
    ∀ x, ¬ LeaseStart a r x
  /-- While the current primary's drop request is in flight and it has received no
  acknowledgement since, no echo is on its way to the replica. -/
  requestNoEcho : ∀ p r g t, Msg.dropReq p r g t ∈ a.net → (Msg.dropReq p r g t).Current a →
    a.ackEcho p r = none → p = a.core.cfg.primary → ∀ x, ¬ InFlightEcho a r x
  /-- While a confirmation is in flight to the current primary, which has received no
  acknowledgement since, the replica holds no read lease and has none in flight. -/
  confirmNoLease : ∀ r p g t, Msg.dropAck r p g t ∈ a.net → (Msg.dropAck r p g t).Current a →
    a.ackEcho p r = none → p = a.core.cfg.primary → ∀ x, ¬ LeaseStart a r x

/-- The drop facts survive a step that keeps the current primary, keeps every confirmed
drop and its echo, only clears echoes of pairs whose drop messages it discards, shrinks
the lease starts and the echoes in flight, and adds no drop message. -/
theorem DropInvariant.frame {a a' : LeaseState Node} (h : DropInvariant a)
    (hprim : a'.core.cfg.primary = a.core.cfg.primary)
    (hDC : ∀ p r, a'.dropConfirmed p r = true → a.dropConfirmed p r = true ∧ a'.ackEcho p r = a.ackEcho p r)
    (hAE : ∀ p r, a'.ackEcho p r = none → a.ackEcho p r = none ∨
      ∀ m ∈ a'.net, m.Current a' → m.link ≠ (p, r))
    (hLS : ∀ r x, LeaseStart a' r x → LeaseStart a r x)
    (hIF : ∀ r x, InFlightEcho a' r x → InFlightEcho a r x)
    (hNet : ∀ m ∈ a'.net, m.Current a' → m ∈ a.net ∧ m.Current a) :
    DropInvariant a' where
  confirmedNoEcho := by
    intro p r hd; obtain ⟨hd', he⟩ := hDC p r hd; rw [he]; exact h.confirmedNoEcho p r hd'
  confirmedNoLease := by
    intro p r hd hp x hx; exact h.confirmedNoLease p r (hDC p r hd).1 (hp.trans hprim) x (hLS r x hx)
  requestNoEcho := by
    intro p r g t hm hc he hp x hx
    obtain ⟨hm', hc'⟩ := hNet _ hm hc
    rcases hAE p r he with he' | hdead
    · exact h.requestNoEcho p r g t hm' hc' he' (hp.trans hprim) x (hIF r x hx)
    · exact hdead _ hm hc rfl
  confirmNoLease := by
    intro r p g t hm hc he hp x hx
    obtain ⟨hm', hc'⟩ := hNet _ hm hc
    rcases hAE p r he with he' | hdead
    · exact h.confirmNoLease r p g t hm' hc' he' (hp.trans hprim) x (hLS r x hx)
    · exact hdead _ hm hc rfl

/-- An echo in flight after a send was in flight before, or is the new message's. -/
theorem inFlight_send {a : LeaseState Node} {msg : Msg Node} {r : Node} {x : Nat}
    (hx : InFlightEcho (send a msg) r x) : InFlightEcho a r x ∨ (msg.dst = r ∧ msg.echo = some x) := by
  obtain ⟨m', hm, hc, hd, he⟩ := hx
  rcases List.mem_cons.1 hm with rfl | hm
  · exact Or.inr ⟨hd, he⟩
  · exact Or.inl ⟨m', hm, hc, hd, he⟩

/-- A lease start after a send was one before, or is the new message's echo. -/
theorem leaseStart_send' {a : LeaseState Node} {msg : Msg Node} {r : Node} {x : Nat}
    (hx : LeaseStart (send a msg) r x) : LeaseStart a r x ∨ (msg.dst = r ∧ msg.echo = some x) := by
  rcases hx with hx | hx
  · exact Or.inl (Or.inl hx)
  · rcases inFlight_send hx with hx | hx
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx

/-- Sending a message without an echo keeps the drop facts, given what a new drop request
or confirmation needs. -/
theorem DropInvariant.sendMsg {a : LeaseState Node} (h : DropInvariant a) {msg : Msg Node}
    (hecho : msg.echo = none)
    (hReq : ∀ p r g t, msg = .dropReq p r g t → a.ackEcho p r = none → p = a.core.cfg.primary →
      ∀ x, ¬ InFlightEcho a r x)
    (hAck : ∀ r p g t, msg = .dropAck r p g t → a.ackEcho p r = none → p = a.core.cfg.primary →
      ∀ x, ¬ LeaseStart a r x) :
    DropInvariant (send a msg) := by
  have hIF : ∀ r x, InFlightEcho (send a msg) r x → InFlightEcho a r x := by
    intro r x hx; rcases inFlight_send hx with hx | ⟨_, he⟩
    · exact hx
    · rw [hecho] at he; cases he
  have hLS : ∀ r x, LeaseStart (send a msg) r x → LeaseStart a r x := by
    intro r x hx; rcases leaseStart_send' hx with hx | ⟨_, he⟩
    · exact hx
    · rw [hecho] at he; cases he
  exact {
  confirmedNoEcho := h.confirmedNoEcho
  confirmedNoLease := fun p r hd hp x hx => h.confirmedNoLease p r hd hp x (hLS r x hx)
  requestNoEcho := by
    intro p r g t hm hc he hp x hx
    rcases List.mem_cons.1 hm with e | hm
    · exact hReq p r g t e.symm he hp x (hIF r x hx)
    · exact h.requestNoEcho p r g t hm hc he hp x (hIF r x hx)
  confirmNoLease := by
    intro r p g t hm hc he hp x hx
    rcases List.mem_cons.1 hm with e | hm
    · exact hAck r p g t e.symm he hp x (hLS r x hx)
    · exact h.confirmNoLease r p g t hm hc he hp x (hLS r x hx) }

/-! ## The invariant -/

/-- The inductive invariant of the lease layer. -/
structure LeaseInvariant (P : LeaseParams) (a : LeaseState Node) : Prop where
  /-- The replication invariant. -/
  core : Invariant a.core
  /-- The replication-message invariant. -/
  rcore : RInvariant a.core
  /-- Every recorded time is in the past. -/
  primaryTrafficLe : ∀ r, a.primaryTraffic r ≤ a.now
  ackReceivedLe  : ∀ p r b, a.ackReceived p r = some b → b ≤ a.now
  primarySinceLe      : ∀ p T, a.primarySince p = some T → T ≤ a.now
  /-- The data a replica would acknowledge was sent no later than its last traffic. -/
  dataSentLe    : ∀ r, a.dataSent r ≤ a.primaryTraffic r
  /-- A primary lease, held or in flight, starts no later than the grantor's last
  traffic from its primary. -/
  primaryLeaseLe       : ∀ p r x, PrimStart a p r x → x ≤ a.primaryTraffic r
  /-- The acknowledgement a primary would echo was sent no later than it was received. -/
  echoLe     : ∀ p r e, a.ackEcho p r = some e → ∃ b, a.ackReceived p r = some b ∧ e ≤ b
  /-- Every acknowledgement a primary holds arrived during its current primaryship, or
  the replica is still marked as one of the old configuration (so the demotion wait
  covers it). Lets a read lease bounded by the takeover time be renewed into one bounded
  by an acknowledgement (`leaseBound`). The second disjunct lets a restart keep its
  grantor rows (`RestartGrantorRows.lean`). -/
  primarySinceAck     : ∀ p r T b, a.primarySince p = some T → a.ackReceived p r = some b →
    T ≤ b ∨ a.oldEligible p r = true
  /-- A deposed primary's lease from the replica that deposed it is over for good, and so
  is any such lease still in flight. That replica is eligible in the deposed primary's
  configuration and follows someone else, so its acknowledgements never reach the
  deposed primary again and the lease is never renewed. -/
  deposed    : ∀ p, ThinksPrimary a.core p → (a.core.localCfg p).epoch < a.core.cfg.epoch →
    ∃ t, t ≠ p ∧ (a.core.localCfg p).eligible t = true ∧ (a.core.localCfg t).primary ≠ p ∧
      ∀ x, PrimStart a p t x → x + P.primDur ≤ a.now + P.drift
  /-- A read lease, held or in flight, started no later than the current primary's last
  acknowledgement from its holder, or no later than the current primary's takeover; in
  the latter case the holder was eligible in the configuration the takeover replaced, or
  the lease has already expired. -/
  leaseBound : ∀ r x, LeaseStart a r x →
    (∃ b, a.ackReceived a.core.cfg.primary r = some b ∧ x ≤ b) ∨
    (∃ T, a.primarySince a.core.cfg.primary = some T ∧ x ≤ T ∧
      (a.oldEligible a.core.cfg.primary r = true ∨ ¬ HolderValid P a.now (some x) P.readDur))
  /-- A replica with a valid read lease, held or in flight, is authoritative. -/
  leaseAuth  : ∀ r x, LeaseStart a r x → ¬ ThinksPrimary a.core r →
    HolderValid P a.now (some x) P.readDur → IsAuthoritative a.core r
  /-- A node whose configuration names it primary holds no read lease and has none in
  flight. Keeps a deposed primary out of the read-lease holders, which `leaseAuth` needs
  across Takeover and Learn. -/
  selfPrimNoLease : ∀ p, (a.core.localCfg p).primary = p → ∀ x, ¬ LeaseStart a p x
  /-- A replica's committed view is within its log and is a committed prefix. -/
  committedViewLen   : ∀ r, a.committedView r ≤ (a.core.log r).length
  committedViewHist  : ∀ r, a.committedView r ≤ a.core.hist.length ∧ (a.core.log r).take (a.committedView r) <+: a.core.hist
  /-- Every message in flight was sent in the past, by connections no newer than now's. -/
  sentLe : ∀ msg ∈ a.net, msg.sent ≤ a.now
  genLe : ∀ msg ∈ a.net, msg.g ≤ a.gen msg.link.1 msg.link.2
  /-- A current `REPLCONF COMMIT` carries no more than its sender's committed offset: a
  committed offset only goes down at a takeover, resync or restart, which closes the
  connections. -/
  commitLe : ∀ msg ∈ a.net, msg.Current a → ∀ c, msg.commitOf = some c → c ≤ a.core.commit msg.src
  /-- A current `REPLCONF COMMIT` goes from a replica's primary to the replica. -/
  follows : ∀ msg ∈ a.net, msg.Current a → msg.commitOf.isSome →
    primaryOf a.core msg.dst = msg.src ∧ msg.src ≠ msg.dst
  /-- The planned-demotion facts. -/
  drop : DropInvariant a

/-- Every read lease, held or in flight, started in the past. A lease is bounded by an
acknowledgement time or a primaryship start (`leaseBound`), and both are in the past
(`ackReceivedLe`, `primarySinceLe`). -/
theorem LeaseInvariant.leaseStartLe {P : LeaseParams} {a : LeaseState Node} (h : LeaseInvariant P a) :
    ∀ r x, LeaseStart a r x → x ≤ a.now := by
  intro r x hx
  rcases h.leaseBound r x hx with ⟨b, hb, hxb⟩ | ⟨T, hT, hxT, _⟩
  · exact hxb.trans (h.ackReceivedLe _ r b hb)
  · exact hxT.trans (h.primarySinceLe _ T hT)

/-- The same, for a held read lease. -/
theorem LeaseInvariant.readLeaseLe {P : LeaseParams} {a : LeaseState Node} (h : LeaseInvariant P a) :
    ∀ r x, a.readLease r = some x → x ≤ a.now :=
  fun r x hx => h.leaseStartLe r x (Or.inl hx)

theorem leaseInvariant_init (P : LeaseParams) (i : Node) : LeaseInvariant P (leaseInit i) where
  core := invariant_init i
  rcore := rInvariant_init i
  primaryTrafficLe := fun _ => Nat.le_refl _
  ackReceivedLe := by intro _ _ _ h; simp [leaseInit] at h
  primarySinceLe := by intro _ _ h; simp [leaseInit] at h
  dataSentLe := fun _ => Nat.le_refl _
  primaryLeaseLe := by
    intro _ _ _ h; rcases h with h | ⟨_, hm, _⟩
    · simp [leaseInit] at h
    · simp [leaseInit] at hm
  echoLe := by intro _ _ _ h; simp [leaseInit] at h
  primarySinceAck := by intro _ _ _ _ h; simp [leaseInit] at h
  deposed := by intro p _ hv; simp [leaseInit, init, initCfg] at hv
  leaseBound := by
    intro _ _ h; rcases h with h | ⟨_, hm, _⟩
    · simp [leaseInit] at h
    · simp [leaseInit] at hm
  leaseAuth := by
    intro _ _ h; rcases h with h | ⟨_, hm, _⟩
    · simp [leaseInit] at h
    · simp [leaseInit] at hm
  selfPrimNoLease := by
    intro _ _ _ h; rcases h with h | ⟨_, hm, _⟩
    · simp [leaseInit] at h
    · simp [leaseInit] at hm
  committedViewLen := by intro _; simp [leaseInit]
  committedViewHist := by intro _; simp [leaseInit, init]
  sentLe := by intro _ hm; simp [leaseInit] at hm
  genLe := by intro _ hm; simp [leaseInit] at hm
  commitLe := by intro _ hm; simp [leaseInit] at hm
  follows := by intro _ hm; simp [leaseInit] at hm
  drop := {
    confirmedNoEcho := by intro _ _ h; simp [leaseInit] at h
    confirmedNoLease := by intro _ _ h; simp [leaseInit] at h
    requestNoEcho := by intro _ _ _ _ hm; simp [leaseInit] at hm
    confirmNoLease := by intro _ _ _ _ hm; simp [leaseInit] at hm }

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
    have := hpl x (Or.inl hx)
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
    have hauth : IsAuthoritative a.core r := by
      unfold ReadLeaseValid HolderValid at hL
      cases hx : a.readLease r with
      | none => rw [hx] at hL; exact hL.elim
      | some x => rw [hx] at hL; exact h.leaseAuth r x (Or.inl hx) hnp hL
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
  rcore := h.rcore
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
  leaseAuth := fun r x hx hnp hv => h.leaseAuth r x hx hnp (holderValid_mono (Nat.le_succ _) hv)
  selfPrimNoLease := h.selfPrimNoLease
  committedViewLen := h.committedViewLen
  committedViewHist := h.committedViewHist
  sentLe := fun msg hm => Nat.le_succ_of_le (h.sentLe msg hm)
  genLe := h.genLe
  commitLe := h.commitLe
  follows := h.follows
  drop := h.drop.frame rfl (fun _ _ hd => ⟨hd, rfl⟩) (fun _ _ he => Or.inl he) (fun _ _ hx => hx)
    (fun _ _ hx => hx) (fun _ hm hc => ⟨hm, hc⟩)

/-! ### Frames -/

/-- A node whose configuration names it primary holds no valid read lease
(`selfPrimNoLease`); in particular, no node that thinks it is primary does. -/
theorem not_readLeaseValid_of_selfPrim {q : Node} (hq : (a.core.localCfg q).primary = q) :
    ¬ ReadLeaseValid P a q := by
  unfold ReadLeaseValid HolderValid
  cases hx : a.readLease q with
  | none => exact id
  | some x => exact fun _ => h.selfPrimNoLease q hq x (Or.inl hx)

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
      ∀ x, PrimStart a p t x → x + P.primDur ≤ a.now + P.drift := by
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
      ∀ x, PrimStart a q t x → x + P.primDur ≤ a.now + P.drift := by
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
    {q : Node} (hq : (c.localCfg q).primary = q) : ∀ x, ¬ LeaseStart a q x := by
  rw [hlocalCfg] at hq; split_ifs at hq with e
  · subst e; exact h.selfPrimNoLease _ (by rw [hkp])
  · exact h.selfPrimNoLease q hq

/-- The same configuration change keeps every node's primary in the configuration it knows. -/
theorem primaryOf_cfgBump {c : State Node} {cfg' : Cfg Node}
    (hkp : a.core.localCfg a.core.cfg.primary = a.core.cfg)
    (hlocalCfg : ∀ x, c.localCfg x = if x = a.core.cfg.primary then cfg' else a.core.localCfg x)
    (hprim : cfg'.primary = a.core.cfg.primary)
    (x : Node) : primaryOf c x = primaryOf a.core x := by
  unfold primaryOf; rw [hlocalCfg]; split_ifs with e
  · subst e; rw [hprim, hkp]
  · rfl

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

/-- The four conjuncts about messages in flight, after a step that keeps or shrinks the
messages, closes no connection it then uses, and lowers no committed offset of a
sender whose connections are still open. -/
theorem msgs_frame {a' : LeaseState Node} (hnow : a.now ≤ a'.now)
    (hNet : ∀ msg ∈ a'.net, msg ∈ a.net)
    (hCur : ∀ msg ∈ a.net, msg.Current a' → msg.Current a)
    (hGenLe : ∀ msg ∈ a.net, msg.g ≤ a'.gen msg.link.1 msg.link.2)
    (hCommit : ∀ msg ∈ a.net, msg.Current a' → a.core.commit msg.src ≤ a'.core.commit msg.src)
    (hPrim : ∀ msg ∈ a.net, msg.Current a' → msg.commitOf.isSome →
      primaryOf a'.core msg.dst = primaryOf a.core msg.dst) :
    (∀ msg ∈ a'.net, msg.sent ≤ a'.now) ∧
    (∀ msg ∈ a'.net, msg.g ≤ a'.gen msg.link.1 msg.link.2) ∧
    (∀ msg ∈ a'.net, msg.Current a' → ∀ c, msg.commitOf = some c → c ≤ a'.core.commit msg.src) ∧
    (∀ msg ∈ a'.net, msg.Current a' → msg.commitOf.isSome →
      primaryOf a'.core msg.dst = msg.src ∧ msg.src ≠ msg.dst) := by
  refine ⟨fun msg hm => Nat.le_trans (h.sentLe msg (hNet msg hm)) hnow,
    fun msg hm => hGenLe msg (hNet msg hm), ?_, ?_⟩
  · intro msg hm hc c hcm
    have hm' := hNet msg hm
    exact Nat.le_trans (h.commitLe msg hm' (hCur msg hm' hc) c hcm) (hCommit msg hm' hc)
  · intro msg hm hc hd
    have hm' := hNet msg hm
    rw [hPrim msg hm' hc hd]; exact h.follows msg hm' (hCur msg hm' hc) hd

/-- The frame for steps that keep the configuration, every node's copy of it and every
incarnation, move no lease start, acknowledgement time or primaryship time, and only
shrink the messages in flight or close connections. Traffic times may only move
forward, to now; the caller supplies the facts about the data-sent times and the
committed views, and about committed offsets of senders whose connections stay open. -/
theorem leaseInvariant_frame {a' : LeaseState Node} (hc : Invariant a'.core) (hrc : RInvariant a'.core)
    (hcfg : a'.core.cfg = a.core.cfg) (hlocalCfg : a'.core.localCfg = a.core.localCfg)
    (hinc : a'.core.incarnation = a.core.incarnation) (hnow : a'.now = a.now)
    (hPL : a'.primaryLease = a.primaryLease) (hAR : a'.ackReceived = a.ackReceived)
    (hAE : ∀ p r e, a'.ackEcho p r = some e → a.ackEcho p r = some e)
    (hRL : ∀ r x, a'.readLease r = some x → a.readLease r = some x)
    (hPS : a'.primarySince = a.primarySince) (hOE : a'.oldEligible = a.oldEligible)
    (hNet : ∀ msg ∈ a'.net, msg ∈ a.net)
    (hCur : ∀ msg ∈ a.net, msg.Current a' → msg.Current a)
    (hGenLe : ∀ msg ∈ a.net, msg.g ≤ a'.gen msg.link.1 msg.link.2)
    (hCommit : ∀ msg ∈ a.net, msg.Current a' → a.core.commit msg.src ≤ a'.core.commit msg.src)
    (hPT : ∀ r, a.primaryTraffic r ≤ a'.primaryTraffic r ∧ a'.primaryTraffic r ≤ a.now)
    (hDS : ∀ r, a'.dataSent r ≤ a'.primaryTraffic r)
    (hCV : ∀ r, a'.committedView r ≤ (a'.core.log r).length)
    (hCH : ∀ r, a'.committedView r ≤ a'.core.hist.length ∧
      (a'.core.log r).take (a'.committedView r) <+: a'.core.hist)
    (hDrop : DropInvariant a') :
    LeaseInvariant P a' := by
  have hmono : ∀ msg ∈ a'.net, msg ∈ a.net ∧ (msg.Current a' → msg.Current a) :=
    fun msg hm => ⟨hNet msg hm, hCur msg (hNet msg hm)⟩
  have hLS : ∀ r x, LeaseStart a' r x → LeaseStart a r x :=
    fun r x hx => leaseStart_mono a _ hRL hmono hx
  have hPLS : ∀ p r x, PrimStart a' p r x → PrimStart a p r x :=
    fun p r x hx => primStart_mono a _ (fun p r x e => by rw [hPL] at e; exact e) hmono hx
  obtain ⟨hS1, hS2, hS3, hS4⟩ := msgs_frame h (le_of_eq hnow.symm) hNet hCur hGenLe hCommit
    (fun _ _ _ _ => by unfold primaryOf; rw [hlocalCfg])
  exact {
  core := hc
  rcore := hrc
  primaryTrafficLe := fun r => by rw [hnow]; exact (hPT r).2
  ackReceivedLe := by rw [hAR, hnow]; exact h.ackReceivedLe
  primarySinceLe := by rw [hPS, hnow]; exact h.primarySinceLe
  dataSentLe := hDS
  primaryLeaseLe := fun p r x hx => Nat.le_trans (h.primaryLeaseLe p r x (hPLS p r x hx)) (hPT r).1
  echoLe := by
    intro p r e he; rw [hAR]; exact h.echoLe p r e (hAE p r e he)
  primarySinceAck := by rw [hPS, hAR, hOE]; exact h.primarySinceAck
  deposed := by
    intro p hp hv
    obtain ⟨t, h1, h2, h3, h4⟩ :=
      deposed_frame h (hcfg := hcfg) (hlocalCfg := hlocalCfg) ((thinksPrimary_congr hlocalCfg (congrFun hinc p)).1 hp) hv
    exact ⟨t, h1, h2, h3, fun x hx => by rw [hnow]; exact h4 x (hPLS p t x hx)⟩
  leaseBound := by
    intro r x hx; rw [hAR, hPS, hOE, hcfg, hnow]; exact h.leaseBound r x (hLS r x hx)
  leaseAuth := by
    intro r x hx hnp hv
    rw [hnow] at hv
    exact (isAuthoritative_congr hcfg (congrFun hinc r)).2
      (h.leaseAuth r x (hLS r x hx) (fun hp => hnp ((thinksPrimary_congr hlocalCfg (congrFun hinc r)).2 hp)) hv)
  selfPrimNoLease := by
    intro p hp x hx; rw [hlocalCfg] at hp; exact h.selfPrimNoLease p hp x (hLS p x hx)
  committedViewLen := hCV
  committedViewHist := hCH
  sentLe := hS1, genLe := hS2, commitLe := hS3, follows := hS4
  drop := hDrop }

/-- The frame's drop facts, for a step that keeps the current primary, every confirmed
drop and every echo, and only shrinks the lease starts, the echoes in flight and the
current messages. -/
theorem drop_mono {a' : LeaseState Node} (hprim : a'.core.cfg.primary = a.core.cfg.primary)
    (hDC : a'.dropConfirmed = a.dropConfirmed) (hAE : a'.ackEcho = a.ackEcho)
    (hRL : ∀ r x, a'.readLease r = some x → a.readLease r = some x)
    (hnet : ∀ msg ∈ a'.net, msg ∈ a.net ∧ (msg.Current a' → msg.Current a)) : DropInvariant a' :=
  h.drop.frame hprim (fun p r hd => ⟨by rw [← hDC]; exact hd, by rw [hAE]⟩)
    (fun p r he => Or.inl (by rw [← hAE]; exact he))
    (fun r x hx => leaseStart_mono a a' hRL hnet hx)
    (fun r x ⟨m, hm, hc, hd, he⟩ => ⟨m, (hnet m hm).1, (hnet m hm).2 hc, hd, he⟩)
    (fun m hm hc => ⟨(hnet m hm).1, (hnet m hm).2 hc⟩)

/-! ### Replication actions that touch no lease state -/

/-- A replication step that changes neither the configuration, nor any node's copy of
it, nor any incarnation, lowers no committed offset, and only extends logs and the
history, keeps the lease invariant with the lease state unchanged. -/
theorem leaseInvariant_withCore {c : State Node} (hc : Invariant c) (hrc : RInvariant c)
    (hcfg : c.cfg = a.core.cfg) (hlocalCfg : c.localCfg = a.core.localCfg)
    (hinc : c.incarnation = a.core.incarnation) (hcommit : ∀ x, a.core.commit x ≤ c.commit x)
    (hlog : ∀ x, a.core.log x <+: c.log x) (hhist : a.core.hist <+: c.hist) :
    LeaseInvariant P (withCore a c) :=
  leaseInvariant_frame h hc hrc (hcfg := hcfg) (hlocalCfg := hlocalCfg) (hinc := hinc)
    (hnow := rfl) (hPL := rfl) (hAR := rfl) (hAE := fun _ _ _ e => e) (hRL := fun _ _ e => e)
    (hPS := rfl) (hOE := rfl)
    (fun _ hm => hm) (fun _ _ hc => hc) h.genLe (fun msg _ _ => hcommit msg.src)
    (fun r => ⟨Nat.le_refl _, h.primaryTrafficLe r⟩) h.dataSentLe
    (fun r => Nat.le_trans (h.committedViewLen r) (hlog r).length_le)
    (fun r => by
      obtain ⟨h1, h2⟩ := h.committedViewHist r
      refine ⟨Nat.le_trans h1 hhist.length_le, ?_⟩
      show (c.log r).take (a.committedView r) <+: c.hist
      rw [← prefix_take_eq (hlog r) (h.committedViewLen r)]
      exact h2.trans hhist)
    (drop_mono h (congrArg Cfg.primary hcfg) rfl rfl (fun _ _ e => e) (fun _ hm => ⟨hm, id⟩))

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
  have hpo := primaryOf_cfgBump h hkp (makeEligible_localCfg (s := a.core) (r := r)) rfl
  exact {
  core := invariant_makeEligible h.core hp hkl hs hel
  rcore := h.rcore.makeEligible h.core hp hkl hs
  primaryTrafficLe := h.primaryTrafficLe, ackReceivedLe := h.ackReceivedLe, primarySinceLe := h.primarySinceLe
  dataSentLe := h.dataSentLe, primaryLeaseLe := h.primaryLeaseLe, echoLe := h.echoLe, primarySinceAck := h.primarySinceAck
  deposed := fun q hq hv => deposed_cfgBump h rfl makeEligible_localCfg rfl rfl htp hq hv
  leaseBound := h.leaseBound
  leaseAuth := by
    intro x v hx hnp hv
    obtain ⟨h1, h2⟩ := h.leaseAuth x v hx (fun hp' => hnp ((htp x).2 hp')) hv
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
  committedViewHist := h.committedViewHist
  sentLe := h.sentLe, genLe := h.genLe, commitLe := h.commitLe
  follows := fun msg hm hc hd =>
    ⟨(hpo msg.dst).trans (h.follows msg hm hc hd).1, (h.follows msg hm hc hd).2⟩
  drop := drop_mono h rfl rfl rfl (fun _ _ e => e) (fun _ hm => ⟨hm, id⟩) }

/-- The replication actions whose lease effects, if any, travel as lease messages. -/
theorem leaseInvariant_core {m : Nat} {μ : Action Node} {c : State Node} (hs : Step m a.core μ c)
    (hpl : μ.isCore = true) : LeaseInvariant P (withCore a c) := by
  obtain ⟨hcore, hrcore⟩ := invariants_step h.core h.rcore hs
  have hkeep : ∀ x, a.core.log x <+: a.core.log x := fun _ => List.prefix_refl _
  cases hs
  case append p _ _ =>
    exact leaseInvariant_withCore h hcore hrcore rfl rfl rfl (fun _ => Nat.le_refl _)
      (grow_upd a.core.log p _) (List.prefix_refl _)
  case commit p hp _ hlen hcap =>
    refine leaseInvariant_withCore h hcore hrcore rfl rfl rfl ?_ hkeep ?_
    · intro x; show a.core.commit x ≤ update a.core.commit p (a.core.commit p + 1) x
      unfold update; split_ifs with e
      · subst e; exact Nat.le_succ _
      · exact Nat.le_refl _
    · show a.core.hist <+: (if a.core.commit p = a.core.hist.length then _ else _)
      split_ifs
      · exact List.prefix_append _ _
      · exact List.prefix_refl _
  case addToSyncSet p r hp hrp hf _ hle =>
    exact leaseInvariant_withCore h hcore hrcore rfl rfl rfl (fun _ => Nat.le_refl _) hkeep (List.prefix_refl _)
  case removeFromSyncSet p r hp hsy hel =>
    exact leaseInvariant_withCore h hcore hrcore rfl rfl rfl (fun _ => Nat.le_refl _) hkeep (List.prefix_refl _)
  case makeEligible p r hp hkl hsy hel => exact leaseInvariant_makeEligible h hp hkl hsy hel
  case psync r _ _ _ =>
    exact leaseInvariant_withCore h hcore hrcore rfl rfl rfl (fun _ => Nat.le_refl _) hkeep (List.prefix_refl _)
  case sendData p r k _ _ =>
    exact leaseInvariant_withCore h hcore hrcore rfl rfl rfl (fun _ => Nat.le_refl _) hkeep (List.prefix_refl _)
  case deliverData p r g v rid _ _ _ _ =>
    exact leaseInvariant_withCore h hcore hrcore rfl rfl rfl (fun _ => Nat.le_refl _)
      (grow_upd a.core.log r _) (List.prefix_refl _)
  case sendAck r _ =>
    exact leaseInvariant_withCore h hcore hrcore rfl rfl rfl (fun _ => Nat.le_refl _) hkeep (List.prefix_refl _)
  case deliverAck r p g off k _ _ _ _ =>
    exact leaseInvariant_withCore h hcore hrcore rfl rfl rfl (fun _ => Nat.le_refl _) hkeep (List.prefix_refl _)
  case dropMsg msg _ =>
    exact leaseInvariant_withCore h hcore hrcore rfl rfl rfl (fun _ => Nat.le_refl _) hkeep (List.prefix_refl _)
  -- the remaining actions are not core actions of the lease layer
  all_goals simp [Action.isCore] at hpl

/-! ### Messages: send, deliver, drop -/

/-- A message is lost. -/
theorem leaseInvariant_drop {msg : Msg Node} : LeaseInvariant P (dropMsg a msg) :=
  leaseInvariant_frame h h.core h.rcore rfl rfl rfl rfl rfl rfl (fun _ _ _ e => e) (fun _ _ e => e) rfl rfl
    (fun _ hm => List.mem_of_mem_erase hm) (fun _ _ hc => hc) h.genLe (fun _ _ _ => Nat.le_refl _)
    (fun r => ⟨Nat.le_refl _, h.primaryTrafficLe r⟩) h.dataSentLe h.committedViewLen h.committedViewHist
    (drop_mono h rfl rfl rfl (fun _ _ e => e) (fun _ hm => ⟨List.mem_of_mem_erase hm, id⟩))

/-- A new message, before the step's own effect on leases: every old lease start, held
or in flight, is still one, and a new start can only come from the new message. -/
theorem leaseStart_send {msg : Msg Node} {r : Node} {x : Nat} (hx : LeaseStart (send a msg) r x) :
    LeaseStart a r x ∨ (msg.dst = r ∧ msg.echo = some x) := by
  rcases hx with hx | ⟨m', hm, hc, hd, he⟩
  · exact Or.inl (Or.inl hx)
  · rcases List.mem_cons.1 hm with rfl | hm
    · exact Or.inr ⟨hd, he⟩
    · exact Or.inl (Or.inr ⟨m', hm, hc, hd, he⟩)

theorem primStart_send {msg : Msg Node} {p r : Node} {x : Nat} (hx : PrimStart (send a msg) p r x) :
    PrimStart a p r x ∨ (msg.dst = p ∧ msg.src = r ∧ msg.ackStart = some x) := by
  rcases hx with hx | ⟨m', hm, hc, hd, hs, he⟩
  · exact Or.inl (Or.inl hx)
  · rcases List.mem_cons.1 hm with rfl | hm
    · exact Or.inr ⟨hd, hs, he⟩
    · exact Or.inl (Or.inr ⟨m', hm, hc, hd, hs, he⟩)

/-- Sending: the new message is current, was sent now, and the caller supplies what it
carries. -/
theorem leaseInvariant_send {msg : Msg Node} (hg : msg.g = a.gen msg.link.1 msg.link.2)
    (hsent : msg.sent = a.now)
    (hcommit : ∀ c, msg.commitOf = some c → c ≤ a.core.commit msg.src)
    (hfollows : msg.commitOf.isSome → primaryOf a.core msg.dst = msg.src ∧ msg.src ≠ msg.dst)
    (hPS : ∀ x, msg.ackStart = some x → x ≤ a.primaryTraffic msg.src ∧
      ∀ p, ThinksPrimary a.core p → (a.core.localCfg p).epoch < a.core.cfg.epoch →
        msg.dst = p → primaryOf a.core msg.src = p)
    (hLS : ∀ x, msg.echo = some x → LeaseStart a msg.dst x ∨
      ((∃ b, a.ackReceived a.core.cfg.primary msg.dst = some b ∧ x ≤ b) ∧
        IsAuthoritative a.core msg.dst ∧ (a.core.localCfg msg.dst).primary ≠ msg.dst))
    (hDrop : DropInvariant (send a msg)) :
    LeaseInvariant P (send a msg) := by
  have hcur : ∀ m' ∈ (send a msg).net, m'.Current (send a msg) ↔ m'.Current a := fun _ _ => Iff.rfl
  exact {
  core := h.core
  rcore := h.rcore
  primaryTrafficLe := h.primaryTrafficLe, ackReceivedLe := h.ackReceivedLe, primarySinceLe := h.primarySinceLe
  dataSentLe := h.dataSentLe, echoLe := h.echoLe, primarySinceAck := h.primarySinceAck
  primaryLeaseLe := by
    intro p r x hx
    rcases primStart_send h hx with hx | ⟨_, rfl, he⟩
    · exact h.primaryLeaseLe p r x hx
    · exact (hPS x he).1
  deposed := by
    intro p hp hv
    obtain ⟨t, h1, h2, h3, h4⟩ := h.deposed p hp hv
    refine ⟨t, h1, h2, h3, fun x hx => ?_⟩
    rcases primStart_send h hx with hx | ⟨hd, rfl, he⟩
    · exact h4 x hx
    · -- the witness follows someone other than `p`, so it sends `p` no acknowledgement.
      exact absurd ((hPS x he).2 p hp hv hd) h3
  leaseBound := by
    intro r x hx
    rcases leaseStart_send h hx with hx | ⟨rfl, he⟩
    · exact h.leaseBound r x hx
    · rcases hLS x he with hx | ⟨hb, _, _⟩
      · exact h.leaseBound _ x hx
      · exact Or.inl hb
  leaseAuth := by
    intro r x hx hnp hv
    rcases leaseStart_send h hx with hx | ⟨rfl, he⟩
    · exact h.leaseAuth r x hx hnp hv
    · rcases hLS x he with hx | ⟨_, ha, _⟩
      · exact h.leaseAuth _ x hx hnp hv
      · exact ha
  selfPrimNoLease := by
    intro q hq x hx
    rcases leaseStart_send h hx with hx | ⟨rfl, he⟩
    · exact h.selfPrimNoLease q hq x hx
    · rcases hLS x he with hx | ⟨_, _, hne⟩
      · exact h.selfPrimNoLease _ hq x hx
      · exact hne hq
  committedViewLen := h.committedViewLen
  committedViewHist := h.committedViewHist
  sentLe := by
    intro m' hm; rcases List.mem_cons.1 hm with rfl | hm
    · rw [hsent]; rfl
    · exact h.sentLe m' hm
  genLe := by
    intro m' hm; rcases List.mem_cons.1 hm with rfl | hm
    · exact le_of_eq hg
    · exact h.genLe m' hm
  commitLe := by
    intro m' hm hc c hcm; rcases List.mem_cons.1 hm with rfl | hm
    · exact hcommit c hcm
    · exact h.commitLe m' hm hc c hcm
  follows := by
    intro m' hm hc hd; rcases List.mem_cons.1 hm with rfl | hm
    · exact hfollows hd
    · exact h.follows m' hm hc hd
  drop := hDrop }

/-- `p` sends `REPLCONF COMMIT` without an echo. -/
theorem leaseInvariant_sendData {p r : Node} (hne : p ≠ r) (hf : primaryOf a.core r = p) :
    LeaseInvariant P (send a (.data p r (a.gen p r) a.now (a.core.commit p) none)) :=
  leaseInvariant_send h rfl rfl (fun c hc => by cases hc; exact Nat.le_refl _)
    (fun _ => ⟨hf, hne⟩) (fun _ hx => by cases hx) (fun _ hx => by cases hx)
    (h.drop.sendMsg rfl (fun _ _ _ _ e => by cases e) (fun _ _ _ _ e => by cases e))

include hM in
/-- `p` sends `REPLCONF COMMIT` echoing `r`'s acknowledgement. The grant comes from the
current primary and goes to an eligible replica with a matching incarnation. -/
theorem leaseInvariant_sendGrant {p r : Node} (hne : p ≠ r) (hf : primaryOf a.core r = p)
    (hp : ThinksPrimary a.core p) (hg : MayGrant P a p r) :
    LeaseInvariant P (send a (.data p r (a.gen p r) a.now (a.core.commit p) (a.ackEcho p r))) := by
  obtain ⟨hL, _, hel, hin⟩ := hg
  obtain ⟨hpp, hkn⟩ := leaseValid_current hM h hp hL
  refine leaseInvariant_send h rfl rfl (fun c hc => by cases hc; exact Nat.le_refl _)
    (fun _ => ⟨hf, hne⟩) (fun _ hx => by cases hx) ?_ ?_
  rotate_left
  · -- the current primary echoes nothing to a replica whose drop it has confirmed or
    -- requested, since it has received no acknowledgement from it since.
    have hnew : ∀ q x y, q = a.core.cfg.primary → p = q → r = x → a.ackEcho p r = some y →
        a.ackEcho q x = none → False := by
      intro q x y _ e1 e2 he hn; subst e1; subst e2; rw [hn] at he; cases he
    exact {
    confirmedNoEcho := h.drop.confirmedNoEcho
    confirmedNoLease := by
      intro q x hd hq y hy
      rcases leaseStart_send' hy with hy | ⟨hd', he⟩
      · exact h.drop.confirmedNoLease q x hd hq y hy
      · exact hnew q x y hq (hpp.trans hq.symm) hd' he (h.drop.confirmedNoEcho q x hd)
    requestNoEcho := by
      intro q x g t hm hc hn hq y hy
      rcases List.mem_cons.1 hm with e | hm
      · cases e
      rcases inFlight_send hy with hy | ⟨hd', he⟩
      · exact h.drop.requestNoEcho q x g t hm hc hn hq y hy
      · exact hnew q x y hq (hpp.trans hq.symm) hd' he hn
    confirmNoLease := by
      intro x q g t hm hc hn hq y hy
      rcases List.mem_cons.1 hm with e | hm
      · cases e
      rcases leaseStart_send' hy with hy | ⟨hd', he⟩
      · exact h.drop.confirmNoLease x q g t hm hc hn hq y hy
      · exact hnew q x y hq (hpp.trans hq.symm) hd' he hn }
  intro e he
  obtain ⟨b, hb, heb⟩ := h.echoLe p r e he
  right
  refine ⟨⟨b, by rw [← hpp]; exact hb, heb⟩, ?_, ?_⟩
  · rw [hkn] at hel hin; exact ⟨Or.inl hel, hin⟩
  · show (a.core.localCfg r).primary ≠ r
    intro e'; apply hne; rw [← hf]; exact e'

/-- A replica acknowledges to its primary. -/
theorem leaseInvariant_sendAck {r : Node} (hne : primaryOf a.core r ≠ r) :
    LeaseInvariant P (send a (.ack r (primaryOf a.core r) (a.gen (primaryOf a.core r) r)
      a.now (a.dataSent r))) :=
  leaseInvariant_send h rfl rfl (fun _ hx => by cases hx) (fun hx => by cases hx)
    (fun x hx => by
      cases hx
      exact ⟨h.dataSentLe r, fun p _ _ hd => hd⟩)
    (fun _ hx => by cases hx)
    (h.drop.sendMsg rfl (fun _ _ _ _ e => by cases e) (fun _ _ _ _ e => by cases e))

/-- The committed-view facts after a data message: with `L` the replica's log after the
message (a prefix of its primary's, extending its old log) and `c` a committed offset of
the primary, the new view `max (committedView r) (min c |L|)` is within `L`, within the
history, and a committed prefix. -/
theorem rview_data_ok {r q : Node} {L : List Nat} {c : Nat} (hpre : L <+: a.core.log q)
    (hgrow : a.core.log r <+: L) (hc : c ≤ a.core.commit q) :
    max (a.committedView r) (min c L.length) ≤ L.length ∧
    max (a.committedView r) (min c L.length) ≤ a.core.hist.length ∧
    L.take (max (a.committedView r) (min c L.length)) <+: a.core.hist := by
  obtain ⟨h1, h2⟩ := h.committedViewHist r
  have hrl := h.committedViewLen r
  have hcH := h.core.commitWithinHistory q
  have hcE := h.core.committedIsHistoryPrefix q
  have hk : min c L.length ≤ a.core.commit q := Nat.le_trans (Nat.min_le_left _ _) hc
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.max_le.2 ⟨Nat.le_trans hrl hgrow.length_le, Nat.min_le_right _ _⟩
  · exact Nat.max_le.2 ⟨h1, Nat.le_trans hk hcH⟩
  · rcases Nat.le_total (a.committedView r) (min c L.length) with hle | hle
    · rw [Nat.max_eq_right hle]
      rw [prefix_take_eq hpre (Nat.min_le_right _ _)]
      have : (a.core.log q).take (min c L.length) =
          ((a.core.log q).take (a.core.commit q)).take (min c L.length) := by
        rw [List.take_take, Nat.min_eq_left hk]
      rw [this, hcE, List.take_take, Nat.min_eq_left hk]
      exact List.take_prefix _ _
    · rw [Nat.max_eq_left hle, ← prefix_take_eq hgrow hrl]; exact h2

/-- Two lease starts that each satisfy `leaseBound` have a later one that does too. -/
theorem bound_max {r : Node} {v e : Nat}
    (hv : (∃ b, a.ackReceived a.core.cfg.primary r = some b ∧ v ≤ b) ∨
      (∃ T, a.primarySince a.core.cfg.primary = some T ∧ v ≤ T ∧
        (a.oldEligible a.core.cfg.primary r = true ∨ ¬ HolderValid P a.now (some v) P.readDur)))
    (he : (∃ b, a.ackReceived a.core.cfg.primary r = some b ∧ e ≤ b) ∨
      (∃ T, a.primarySince a.core.cfg.primary = some T ∧ e ≤ T ∧
        (a.oldEligible a.core.cfg.primary r = true ∨ ¬ HolderValid P a.now (some e) P.readDur))) :
    (∃ b, a.ackReceived a.core.cfg.primary r = some b ∧ max v e ≤ b) ∨
      (∃ T, a.primarySince a.core.cfg.primary = some T ∧ max v e ≤ T ∧
        (a.oldEligible a.core.cfg.primary r = true ∨ ¬ HolderValid P a.now (some (max v e)) P.readDur)) := by
  -- an acknowledgement bound and a primaryship bound: `primarySinceAck` orders them.
  have mixed : ∀ {x y : Nat} (b T : Nat), a.ackReceived a.core.cfg.primary r = some b → x ≤ b →
      a.primarySince a.core.cfg.primary = some T → y ≤ T →
      (∃ b, a.ackReceived a.core.cfg.primary r = some b ∧ max x y ≤ b) ∨
        (∃ T, a.primarySince a.core.cfg.primary = some T ∧ max x y ≤ T ∧
          (a.oldEligible a.core.cfg.primary r = true ∨ ¬ HolderValid P a.now (some (max x y)) P.readDur)) ∨
        (a.oldEligible a.core.cfg.primary r = false ∧ T ≤ b) := by
    intro x y b T hb hxb hT hyT
    rcases h.primarySinceAck _ r T b hT hb with hTb | hold
    · exact Or.inl ⟨b, hb, Nat.max_le.2 ⟨hxb, Nat.le_trans hyT hTb⟩⟩
    · by_cases hTb : T ≤ b
      · exact Or.inl ⟨b, hb, Nat.max_le.2 ⟨hxb, Nat.le_trans hyT hTb⟩⟩
      · exact Or.inr (Or.inl ⟨T, hT, Nat.max_le.2 ⟨by omega, hyT⟩, Or.inl hold⟩)
  rcases hv with ⟨b, hb, hvb⟩ | ⟨T, hT, hvT, hvo⟩ <;> rcases he with ⟨b', hb', heb⟩ | ⟨T', hT', heT, heo⟩
  · rw [hb] at hb'; cases hb'; exact Or.inl ⟨b, hb, Nat.max_le.2 ⟨hvb, heb⟩⟩
  · rcases mixed b T' hb hvb hT' heT with h1 | h1 | ⟨_, hTb⟩
    · exact Or.inl h1
    · exact Or.inr h1
    · exact Or.inl ⟨b, hb, Nat.max_le.2 ⟨hvb, Nat.le_trans heT hTb⟩⟩
  · rcases mixed b' T hb' heb hT hvT with h1 | h1 | ⟨_, hTb⟩
    · obtain ⟨b, hb, hm⟩ := h1; exact Or.inl ⟨b, hb, by rw [Nat.max_comm]; exact hm⟩
    · obtain ⟨T, hT, hm, ho⟩ := h1
      exact Or.inr ⟨T, hT, by rw [Nat.max_comm]; exact hm, by rw [Nat.max_comm]; exact ho⟩
    · exact Or.inl ⟨b', hb', Nat.max_le.2 ⟨Nat.le_trans hvT hTb, heb⟩⟩
  · rw [hT] at hT'; cases hT'
    refine Or.inr ⟨T, hT, Nat.max_le.2 ⟨hvT, heT⟩, ?_⟩
    rcases hvo with hvo | hvo
    · exact Or.inl hvo
    · rcases heo with heo | heo
      · exact Or.inl heo
      · right; intro hmv; unfold HolderValid at hmv hvo heo
        rcases Nat.le_total v e with hle | hle
        · rw [Nat.max_eq_right hle] at hmv; exact heo hmv
        · rw [Nat.max_eq_left hle] at hmv; exact hvo hmv

/-- A current `REPLCONF COMMIT` from `p` reaches `r`, which follows `p` and whose log is
a prefix of `p`'s (on an open stream, by `RInvariant.prefix_of_open`). -/
theorem leaseInvariant_deliverData {p r : Node} {g t c : Nat} {e : Option Nat}
    (hm : Msg.data p r g t c e ∈ a.net) (hc : (Msg.data p r g t c e).Current a)
    (hf : primaryOf a.core r = p) (hpre : a.core.log r <+: a.core.log p) :
    LeaseInvariant P (deliverData a (.data p r g t c e) r t c e) := by
  set msg := Msg.data p r g t c e with hmsg
  have hcp : c ≤ a.core.commit p := h.commitLe msg hm hc c rfl
  have hpr : p ≠ r := (h.follows msg hm hc rfl).2
  have htn : t ≤ a.now := h.sentLe msg hm
  obtain ⟨hv1, hv2, hv3⟩ := rview_data_ok h (r := r) hpre (List.prefix_refl _) hcp
  have hnet : ∀ m' ∈ (deliverData a msg r t c e).net, m' ∈ a.net ∧
      (m'.Current (deliverData a msg r t c e) → m'.Current a) :=
    fun m' hm' => ⟨List.mem_of_mem_erase hm', id⟩
  have hPLS : ∀ q x v, PrimStart (deliverData a msg r t c e) q x v → PrimStart a q x v :=
    fun q x v hx => primStart_mono a (deliverData a msg r t c e) (fun _ _ _ e => e) hnet hx
  -- every lease start after the delivery was one before, or is the later of `r`'s held
  -- lease and the echo, both of which were.
  have hLS : ∀ x v, LeaseStart (deliverData a msg r t c e) x v →
      LeaseStart a x v ∨ (x = r ∧ ∃ e0, e = some e0 ∧ LeaseStart a r e0 ∧
        v = maxOpt (a.readLease r) e0) := by
    intro x v hx
    rcases hx with hx | hx
    · cases e with
      | none => exact Or.inl (Or.inl hx)
      | some e0 =>
        change update a.readLease r (some (maxOpt (a.readLease r) e0)) x = some v at hx
        by_cases ex : x = r
        · subst ex; rw [update_self] at hx; cases hx
          exact Or.inr ⟨rfl, e0, rfl, Or.inr ⟨msg, hm, hc, rfl, rfl⟩, rfl⟩
        · rw [update_of_ne _ _ ex] at hx; exact Or.inl (Or.inl hx)
    · obtain ⟨m', hm', hc', hd, he⟩ := hx
      exact Or.inl (Or.inr ⟨m', List.mem_of_mem_erase hm', hc', hd, he⟩)
  -- the later of two starts is one of them.
  have hmax : ∀ (e0 : Nat), LeaseStart a r e0 → ∀ (Q : Nat → Prop), (∀ v, LeaseStart a r v → Q v) →
      Q (maxOpt (a.readLease r) e0) := by
    intro e0 he0 Q hQ
    cases hv : a.readLease r with
    | none => exact hQ e0 he0
    | some w =>
      show Q (max w e0)
      rcases Nat.le_total w e0 with hle | hle
      · rw [Nat.max_eq_right hle]; exact hQ e0 he0
      · rw [Nat.max_eq_left hle]; exact hQ w (Or.inl hv)
  have hPT := primaryTraffic_bump h r
  exact {
  core := h.core
  rcore := h.rcore
  primaryTrafficLe := fun x => (hPT x).2
  ackReceivedLe := h.ackReceivedLe, primarySinceLe := h.primarySinceLe
  dataSentLe := by
    intro x; show update a.dataSent r t x ≤ update a.primaryTraffic r a.now x
    unfold update; split_ifs
    · exact htn
    · exact h.dataSentLe x
  primaryLeaseLe := fun q x v hx => Nat.le_trans (h.primaryLeaseLe q x v (hPLS q x v hx)) (hPT x).1
  echoLe := h.echoLe, primarySinceAck := h.primarySinceAck
  deposed := by
    intro q hq hv
    obtain ⟨w, h1, h2, h3, h4⟩ := h.deposed q hq hv
    exact ⟨w, h1, h2, h3, fun x hx => h4 x (hPLS q w x hx)⟩
  leaseBound := by
    intro x v hx
    rcases hLS x v hx with hx | ⟨rfl, e0, rfl, he0, rfl⟩
    · exact h.leaseBound x v hx
    · cases hv : a.readLease x with
      | none => exact h.leaseBound x e0 he0
      | some w => exact bound_max h (h.leaseBound x w (Or.inl hv)) (h.leaseBound x e0 he0)
  leaseAuth := by
    intro x v hx hnp hv
    rcases hLS x v hx with hx | ⟨rfl, e0, rfl, he0, rfl⟩
    · exact h.leaseAuth x v hx hnp hv
    · revert hv
      exact hmax e0 he0 (fun v => HolderValid P a.now (some v) P.readDur → IsAuthoritative a.core x)
        (fun v hv' => h.leaseAuth x v hv' hnp)
  selfPrimNoLease := by
    intro q hq v hx
    rcases hLS q v hx with hx | ⟨rfl, _, _, _, _⟩
    · exact h.selfPrimNoLease q hq v hx
    · exact hpr (by rw [← hf]; exact hq)
  committedViewLen := by
    intro x; show update a.committedView r _ x ≤ (a.core.log x).length
    unfold update; split_ifs with ex
    · subst ex; exact hv1
    · exact h.committedViewLen x
  committedViewHist := by
    intro x
    show update a.committedView r _ x ≤ a.core.hist.length ∧
      (a.core.log x).take (update a.committedView r _ x) <+: a.core.hist
    unfold update; split_ifs with ex
    · subst ex; exact ⟨hv2, hv3⟩
    · exact h.committedViewHist x
  sentLe := fun m' hm' => h.sentLe m' (List.mem_of_mem_erase hm')
  genLe := fun m' hm' => h.genLe m' (List.mem_of_mem_erase hm')
  commitLe := fun m' hm' => h.commitLe m' (List.mem_of_mem_erase hm')
  follows := fun m' hm' => h.follows m' (List.mem_of_mem_erase hm')
  drop := h.drop.frame rfl (fun _ _ hd => ⟨hd, rfl⟩) (fun _ _ he => Or.inl he)
    (fun x v hx => by
      rcases hLS x v hx with hx | ⟨rfl, e0, rfl, he0, rfl⟩
      · exact hx
      · exact hmax e0 he0 (LeaseStart a x) (fun _ h => h))
    (fun _ _ ⟨m, hm, hc, hd, he⟩ => ⟨m, List.mem_of_mem_erase hm, hc, hd, he⟩)
    (fun _ hm hc => ⟨List.mem_of_mem_erase hm, hc⟩) }

/-- A current acknowledgement from `r` reaches `p`. The primary's lease from `r` and its
acknowledgement times for `r` move; everything else is the frame. -/
theorem leaseInvariant_deliverAck {r p : Node} {g t d : Nat}
    (hm : Msg.ack r p g t d ∈ a.net) (hc : (Msg.ack r p g t d).Current a) :
    LeaseInvariant P (deliverAck a (.ack r p g t d) r p t d) := by
  set msg := Msg.ack r p g t d with hmsg
  set a' := deliverAck a msg r p t d with ha'
  have htn : t ≤ a.now := h.sentLe msg hm
  have hd : PrimStart a p r d := Or.inr ⟨msg, hm, hc, rfl, rfl, rfl⟩
  have hAR : a'.ackReceived = update2 a.ackReceived p r (some a.now) := rfl
  have hAE : a'.ackEcho = update2 a.ackEcho p r (some t) := rfl
  have hnet : ∀ m' ∈ a'.net, m' ∈ a.net ∧ (m'.Current a' → m'.Current a) :=
    fun m' hm' => ⟨List.mem_of_mem_erase hm', id⟩
  have hLS : ∀ x v, LeaseStart a' x v → LeaseStart a x v :=
    fun x v hx => leaseStart_mono a a' (fun _ _ e => e) hnet hx
  -- a primary-lease start after the delivery was one before, or is the later of `p`'s
  -- lease from `r` and the acknowledged data's send time, both of which were.
  have hPLS : ∀ q x v, PrimStart a' q x v → ∀ (Q : Nat → Prop), (∀ w, PrimStart a q x w → Q w) → Q v := by
    intro q x v hx Q hQ
    rcases hx with hx | ⟨m', hm', hc', hd', hs', he'⟩
    · change update2 a.primaryLease p r (some (maxOpt (a.primaryLease p r) d)) q x = some v at hx
      by_cases e : q = p ∧ x = r
      · obtain ⟨rfl, rfl⟩ := e; rw [update2_self] at hx; cases hx
        cases hw : a.primaryLease q x with
        | none => exact hQ d hd
        | some w =>
          show Q (max w d)
          rcases Nat.le_total w d with hle | hle
          · rw [Nat.max_eq_right hle]; exact hQ d hd
          · rw [Nat.max_eq_left hle]; exact hQ w (Or.inl hw)
      · rw [update2_of_ne _ _ e] at hx; exact hQ v (Or.inl hx)
    · exact hQ v (Or.inr ⟨m', List.mem_of_mem_erase hm', hc', hd', hs', he'⟩)
  exact {
  core := h.core
  rcore := h.rcore
  primaryTrafficLe := h.primaryTrafficLe, primarySinceLe := h.primarySinceLe, dataSentLe := h.dataSentLe
  ackReceivedLe := by
    intro q x b hb; rw [hAR] at hb
    by_cases e : q = p ∧ x = r
    · obtain ⟨rfl, rfl⟩ := e; rw [update2_self] at hb; cases hb; exact Nat.le_refl _
    · rw [update2_of_ne _ _ e] at hb; exact h.ackReceivedLe q x b hb
  primaryLeaseLe := fun q x v hx => hPLS q x v hx _ (fun w hw => h.primaryLeaseLe q x w hw)
  echoLe := by
    intro q x e he; rw [hAE] at he; rw [hAR]
    by_cases hqx : q = p ∧ x = r
    · obtain ⟨rfl, rfl⟩ := hqx; rw [update2_self] at he; cases he
      exact ⟨a.now, update2_self _ _ _ _, htn⟩
    · rw [update2_of_ne _ _ hqx] at he; rw [update2_of_ne _ _ hqx]; exact h.echoLe q x e he
  primarySinceAck := by
    intro q x T b hT hb; rw [hAR] at hb
    by_cases e : q = p ∧ x = r
    · obtain ⟨rfl, rfl⟩ := e; rw [update2_self] at hb; cases hb; exact Or.inl (h.primarySinceLe _ T hT)
    · rw [update2_of_ne _ _ e] at hb; exact h.primarySinceAck q x T b hT hb
  deposed := by
    intro q hq hv
    obtain ⟨w, h1, h2, h3, h4⟩ := h.deposed q hq hv
    exact ⟨w, h1, h2, h3, fun x hx => hPLS q w x hx _ (fun v hv => h4 v hv)⟩
  leaseBound := by
    intro x v hx
    have hx' := hLS x v hx
    show (∃ b, update2 a.ackReceived p r (some a.now) a.core.cfg.primary x = some b ∧ v ≤ b) ∨
      (∃ T, a.primarySince a.core.cfg.primary = some T ∧ v ≤ T ∧
        (a.oldEligible a.core.cfg.primary x = true ∨ ¬ HolderValid P a.now (some v) P.readDur))
    by_cases e : a.core.cfg.primary = p ∧ x = r
    · obtain ⟨e1, rfl⟩ := e; rw [e1, update2_self]; left; exact ⟨a.now, rfl, h.leaseStartLe x v hx'⟩
    · rw [update2_of_ne _ _ e]; exact h.leaseBound x v hx'
  leaseAuth := fun x v hx hnp hv => h.leaseAuth x v (hLS x v hx) hnp hv
  selfPrimNoLease := fun q hq v hx => h.selfPrimNoLease q hq v (hLS q v hx)
  committedViewLen := h.committedViewLen
  committedViewHist := h.committedViewHist
  sentLe := fun m' hm' => h.sentLe m' (List.mem_of_mem_erase hm')
  genLe := fun m' hm' => h.genLe m' (List.mem_of_mem_erase hm')
  commitLe := fun m' hm' => h.commitLe m' (List.mem_of_mem_erase hm')
  follows := fun m' hm' => h.follows m' (List.mem_of_mem_erase hm')
  drop := by
    refine h.drop.frame rfl ?_ ?_ hLS
      (fun _ _ ⟨m, hm, hc, hd, he⟩ => ⟨m, List.mem_of_mem_erase hm, hc, hd, he⟩)
      (fun _ hm hc => ⟨List.mem_of_mem_erase hm, hc⟩)
    · -- the acknowledgement resets `p`'s confirmed drop of `r`.
      intro q x hd
      change update2 a.dropConfirmed p r false q x = true at hd
      by_cases e : q = p ∧ x = r
      · obtain ⟨rfl, rfl⟩ := e; rw [update2_self] at hd; cases hd
      · rw [update2_of_ne _ _ e] at hd
        exact ⟨hd, update2_of_ne _ _ e⟩
    · intro q x he
      change update2 a.ackEcho p r (some t) q x = none at he
      by_cases e : q = p ∧ x = r
      · obtain ⟨rfl, rfl⟩ := e; rw [update2_self] at he; cases he
      · rw [update2_of_ne _ _ e] at he; exact Or.inl he }

/-! ### Configuration changes -/

/-- Learn. The learner restarts its takeover timer, and closes its connections if its
primary changes; a deposed primary that learns stops thinking it is primary, and held no
read lease. -/
theorem leaseInvariant_learn {n : Node} (hnkl : ¬ KnowsLatest a.core n) :
    LeaseInvariant P (leaseLearn a n) := by
  have hnp : n ≠ a.core.cfg.primary := by
    intro e; apply hnkl; unfold KnowsLatest; rw [e, h.core.primKnows]
  have hK := learn_localCfg (s := a.core) (n := n)
  have hcfg : (learn a.core n).cfg = a.core.cfg := rfl
  have htp : ∀ x, ThinksPrimary (learn a.core n) x → x ≠ n ∧ ThinksPrimary a.core x :=
    fun _ => learn_thinksPrimary hnp
  have hPT := primaryTraffic_bump h n
  -- the connections still open after the step were open before, and every current
  -- `REPLCONF COMMIT`'s receiver still follows the same primary.
  have hcur : ∀ msg ∈ a.net, msg.Current (leaseLearn a n) →
      msg.Current a ∧ (msg.commitOf.isSome → primaryOf (learn a.core n) msg.dst = primaryOf a.core msg.dst) := by
    intro msg hm hc
    by_cases hsame : a.core.cfg.primary = (a.core.localCfg n).primary
    · have hg : (leaseLearn a n).gen = a.gen := by simp [leaseLearn, hsame]
      refine ⟨by unfold Msg.Current at hc ⊢; rw [hg] at hc; exact hc, fun _ => ?_⟩
      unfold primaryOf; rw [hK]; split_ifs with e
      · rw [e]; exact hsame
      · rfl
    · have hg : (leaseLearn a n).gen = closeInto a.gen n := by simp [leaseLearn, hsame]
      have hc0 : closeInto a.gen n msg.link.1 msg.link.2 = msg.g := by
        unfold Msg.Current at hc; rw [hg] at hc; exact hc
      obtain ⟨hd, hc'⟩ := closeInto_open (h.genLe msg hm) hc0
      refine ⟨hc', fun hdat => ?_⟩
      have hdl : msg.dst = msg.link.2 := by cases msg <;> simp_all [Msg.commitOf, Msg.dst, Msg.link]
      rw [← hdl] at hd
      unfold primaryOf; rw [hK, if_neg hd]
  have hgen : ∀ x y, a.gen x y ≤ (leaseLearn a n).gen x y := by
    intro x y
    by_cases hsame : a.core.cfg.primary = (a.core.localCfg n).primary
    · have hg : (leaseLearn a n).gen = a.gen := by simp [leaseLearn, hsame]
      rw [hg]
    · have hg : (leaseLearn a n).gen = closeInto a.gen n := by simp [leaseLearn, hsame]
      rw [hg]; exact le_closeInto _ _ _ _
  have hmono : ∀ msg ∈ (leaseLearn a n).net, msg ∈ a.net ∧ (msg.Current (leaseLearn a n) → msg.Current a) :=
    fun msg hm => ⟨hm, fun hc => (hcur msg hm hc).1⟩
  have hLS : ∀ r x, LeaseStart (leaseLearn a n) r x → LeaseStart a r x :=
    fun r x hx => leaseStart_mono a (leaseLearn a n) (fun _ _ e => e) hmono hx
  have hPLS : ∀ p r x, PrimStart (leaseLearn a n) p r x → PrimStart a p r x :=
    fun p r x hx => primStart_mono a (leaseLearn a n) (fun _ _ _ e => e) hmono hx
  obtain ⟨hS1, hS2, hS3, hS4⟩ := msgs_frame h (a' := leaseLearn a n) (Nat.le_refl _) (fun _ hm => hm)
    (fun msg hm hc => (hcur msg hm hc).1)
    (fun msg hm => Nat.le_trans (h.genLe msg hm) (hgen _ _))
    (fun _ _ _ => Nat.le_refl _) (fun msg hm hc => (hcur msg hm hc).2)
  exact {
  core := invariant_learn h.core n hnkl
  rcore := h.rcore.learn h.core hnkl
  primaryTrafficLe := fun x => (hPT x).2
  ackReceivedLe := h.ackReceivedLe, primarySinceLe := h.primarySinceLe
  dataSentLe := fun x => Nat.le_trans (h.dataSentLe x) (hPT x).1
  primaryLeaseLe := fun p x v hv => Nat.le_trans (h.primaryLeaseLe p x v (hPLS p x v hv)) (hPT x).1
  echoLe := h.echoLe, primarySinceAck := h.primarySinceAck
  deposed := by
    intro p hp hv
    obtain ⟨hpn, hp'⟩ := htp p hp
    have hv' : (a.core.localCfg p).epoch < a.core.cfg.epoch := by
      have := hv; change ((learn a.core n).localCfg p).epoch < (learn a.core n).cfg.epoch at this
      rwa [hK, if_neg hpn, hcfg] at this
    obtain ⟨t, h1, h2, h3, h4⟩ := h.deposed p hp' hv'
    refine ⟨t, h1, ?_, ?_, fun x hx => h4 x (hPLS p t x hx)⟩
    · show ((learn a.core n).localCfg p).eligible t = true; rw [hK, if_neg hpn]; exact h2
    · show ((learn a.core n).localCfg t).primary ≠ p
      rw [hK]; split_ifs with e
      · show a.core.cfg.primary ≠ p; exact (stale_ne_prim h.core hv').symm
      · exact h3
  leaseBound := fun r x hx => h.leaseBound r x (hLS r x hx)
  leaseAuth := by
    intro x v hx hnp hv
    show IsAuthoritative a.core x
    have hx' := hLS x v hx
    by_cases hxp : ThinksPrimary a.core x
    · exact absurd hx' (h.selfPrimNoLease x hxp.1 v)
    · exact h.leaseAuth x v hx' hxp hv
  selfPrimNoLease := by
    intro q hq v hx
    change ((learn a.core n).localCfg q).primary = q at hq
    rw [hK] at hq; split_ifs at hq with e
    · subst e; exact hnp hq.symm
    · exact h.selfPrimNoLease q hq v (hLS q v hx)
  committedViewLen := h.committedViewLen
  committedViewHist := h.committedViewHist
  sentLe := hS1, genLe := hS2, commitLe := hS3, follows := hS4
  drop := drop_mono h rfl rfl rfl (fun _ _ e => e) hmono }

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
/-- Demotion. The demoted replica's read lease, held or in flight, is over, by the two
waits, or it has none, by its confirmation. -/
theorem leaseInvariant_demote {p r : Node} (hp : ThinksPrimary a.core p) (hkl : KnowsLatest a.core p)
    (hel : a.core.cfg.eligible r = true)
    (hWaited : (GrantorOver P a.now (a.ackReceived p r) P.readDur ∧
      ∀ T, a.primarySince p = some T → a.oldEligible p r = true →
        T + P.readDur + P.margin ≤ a.now + P.drift) ∨ a.dropConfirmed p r = true) :
    LeaseInvariant P (withCore a (makeIneligible a.core p r)) := by
  have hpp : p = a.core.cfg.primary := knowsLatest_iff_prim h.core hp hkl
  subst hpp
  have hkp : a.core.localCfg a.core.cfg.primary = a.core.cfg := h.core.localCfgEq _ hkl
  have htp := makeIneligible_thinksPrimary (s := a.core) (r := r) hkp
  have hpo := primaryOf_cfgBump h hkp (makeIneligible_localCfg (s := a.core) (r := r)) rfl
  exact {
  core := invariant_makeIneligible h.core hp hkl hel
  rcore := h.rcore.makeIneligible h.core hp hkl
  primaryTrafficLe := h.primaryTrafficLe, ackReceivedLe := h.ackReceivedLe, primarySinceLe := h.primarySinceLe
  dataSentLe := h.dataSentLe, primaryLeaseLe := h.primaryLeaseLe, echoLe := h.echoLe, primarySinceAck := h.primarySinceAck
  deposed := fun q hq hv => deposed_cfgBump h rfl makeIneligible_localCfg rfl rfl htp hq hv
  leaseBound := h.leaseBound
  leaseAuth := by
    intro x v hx hnp hv
    have hx' := h.leaseAuth x v hx (fun hp' => hnp ((htp x).2 hp')) hv
    by_cases ex : x = r
    · exfalso; subst ex
      rcases hWaited with ⟨hgo, hwo⟩ | hdc
      · exact lease_over_of_guards hM (h.leaseBound x v hx) hgo hwo hv
      · -- a planned demotion: the replica has confirmed it holds no lease.
        exact h.drop.confirmedNoLease _ x hdc rfl v hx
    · obtain ⟨h1, h2⟩ := hx'
      refine ⟨?_, h2⟩
      show (if x = r then false else a.core.cfg.eligible x) = true ∨ x = a.core.cfg.primary
      rw [if_neg ex]; exact h1
  selfPrimNoLease := fun q hq => selfPrimNoLease_cfgBump h hkp makeIneligible_localCfg hq
  committedViewLen := h.committedViewLen
  committedViewHist := h.committedViewHist
  sentLe := h.sentLe, genLe := h.genLe, commitLe := h.commitLe
  follows := fun msg hm hc hd =>
    ⟨(hpo msg.dst).trans (h.follows msg hm hc hd).1, (h.follows msg hm hc hd).2⟩
  drop := drop_mono h rfl rfl rfl (fun _ _ e => e) (fun _ hm => ⟨hm, id⟩) }

/-- Closing `n`'s connections: every message still current was current before and has
neither end at `n`; generations only grow. -/
theorem bump_facts {a' : LeaseState Node} {n : Node} (hg : a'.gen = closeAll a.gen n) (hnet : a'.net = a.net) :
    (∀ msg ∈ a'.net, msg ∈ a.net ∧ (msg.Current a' → msg.Current a)) ∧
    (∀ msg ∈ a.net, msg.Current a' → msg.Current a ∧ msg.src ≠ n ∧ msg.dst ≠ n) ∧
    (∀ msg ∈ a.net, msg.g ≤ a'.gen msg.link.1 msg.link.2) := by
  have hcb : ∀ msg ∈ a.net, msg.Current a' → msg.Current a ∧ msg.src ≠ n ∧ msg.dst ≠ n :=
    fun msg hm hc => current_of_bump hg (h.genLe msg hm) hc
  have hle : ∀ x y, a.gen x y ≤ a'.gen x y := by
    intro x y; rw [hg]; exact le_closeAll _ _ _ _
  refine ⟨fun msg hm => ?_, hcb, fun msg hm => ?_⟩
  · rw [hnet] at hm; exact ⟨hm, fun hc => (hcb msg hm hc).1⟩
  · exact Nat.le_trans (h.genLe msg hm) (hle _ _)

/-- Takeover. The deposed primary gets its witness: the taker, eligible in its
configuration, whose lease it can never again hold; every existing read lease, held or in
flight, started before the takeover. The taker's own lease rows are cleared and its
connections closed. -/
theorem leaseInvariant_takeover {n : Node} (hkl : KnowsLatest a.core n) (hel : a.core.cfg.eligible n = true)
    (hnp : n ≠ a.core.cfg.primary) (hin : a.core.cfg.incarnation n = a.core.incarnation n)
    (hwait : a.primaryTraffic n + P.primDur ≤ a.now + P.drift) :
    LeaseInvariant P (leaseTakeover a n) := by
  have hK := takeover_localCfg (s := a.core) (n := n)
  have htp := takeover_thinksPrimary (s := a.core) hin
  obtain ⟨hAR, hPS, hAE, hPA⟩ := cleared_rows h (a' := leaseTakeover a n) n rfl rfl rfl rfl (fun _ e => update_of_ne _ _ e)
  obtain ⟨hmono, hcb, hgle⟩ := bump_facts h (a' := leaseTakeover a n) (n := n) rfl rfl
  have hLS : ∀ r x, LeaseStart (leaseTakeover a n) r x → r ≠ n ∧ LeaseStart a r x := by
    intro r x hx
    rcases hx with hx | ⟨msg, hm, hc, hd, he⟩
    · obtain ⟨hrn, hx⟩ := update_none_some _ _ _ hx; exact ⟨hrn, Or.inl hx⟩
    · obtain ⟨hc', _, hdn⟩ := hcb msg hm hc
      exact ⟨hd ▸ hdn, Or.inr ⟨msg, hm, hc', hd, he⟩⟩
  have hPLS : ∀ p r x, PrimStart (leaseTakeover a n) p r x → PrimStart a p r x ∧ (p = n → False) := by
    intro p r x hx
    rcases hx with hx | ⟨msg, hm, hc, hd, hs, he⟩
    · obtain ⟨hpn, hx⟩ := update_row_some _ _ _ _ hx; exact ⟨Or.inl hx, hpn⟩
    · obtain ⟨hc', _, hdn⟩ := hcb msg hm hc
      exact ⟨Or.inr ⟨msg, hm, hc', hd, hs, he⟩, fun e => hdn (hd.trans e)⟩
  have hPLSsrc : ∀ p x, PrimStart (leaseTakeover a n) p n x → a.primaryLease p n = some x := by
    intro p x hx
    rcases hx with hx | ⟨msg, hm, hc, hd, hs, he⟩
    · exact (update_row_some _ _ _ _ hx).2
    · exact absurd hs (hcb msg hm hc).2.1
  obtain ⟨hS1, hS2, hS3, hS4⟩ := msgs_frame h (a' := leaseTakeover a n) (Nat.le_refl _) (fun _ hm => hm)
    (fun msg hm hc => (hcb msg hm hc).1) hgle
    (fun msg hm hc => (takeover_commit_other (s := a.core) (hcb msg hm hc).2.1).ge)
    (fun msg hm hc _ => congrArg Cfg.primary (takeover_localCfg_other (s := a.core) (hcb msg hm hc).2.2))
  exact {
  core := invariant_takeover h.core n hkl hel hnp hin
  rcore := h.rcore.takeover n
  primaryTrafficLe := h.primaryTrafficLe, dataSentLe := h.dataSentLe
  ackReceivedLe := hAR, primarySinceLe := hPS, echoLe := hAE, primarySinceAck := hPA
  primaryLeaseLe := fun q x v hv => h.primaryLeaseLe q x v (hPLS q x v hv).1
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
        refine ⟨t, h1, ?_, ?_, fun x hx => h4 x (hPLS q t x hx).1⟩
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
          -- waited out (`hwait`); `n`'s acknowledgements in flight were discarded.
          intro x hx; show x + P.primDur ≤ a.now + P.drift
          have := h.primaryLeaseLe q n x (Or.inl (hPLSsrc q x hx)); omega
  leaseBound := by
    intro x v hx
    obtain ⟨hxn, hx⟩ := hLS x v hx
    show (∃ b, update a.ackReceived n (fun _ => none) (takeoverCfg a.core n).primary x = some b ∧ v ≤ b) ∨
      (∃ T, update a.primarySince n (some a.now) (takeoverCfg a.core n).primary = some T ∧ v ≤ T ∧
        (update a.oldEligible n a.core.cfg.eligible (takeoverCfg a.core n).primary x = true ∨
          ¬ HolderValid P a.now (some v) P.readDur))
    right; refine ⟨a.now, update_self _ _ _, h.leaseStartLe x v hx, ?_⟩
    show (update a.oldEligible n a.core.cfg.eligible n x = true) ∨ _
    rw [update_self]
    by_cases hel : a.core.cfg.eligible x = true
    · exact Or.inl hel
    · -- `x` was not eligible in the configuration being replaced: a valid lease would
      -- make it authoritative, so its lease is not valid.
      right; intro hv
      have hxp : ¬ ThinksPrimary a.core x := fun hp => h.selfPrimNoLease x hp.1 v hx
      rcases (h.leaseAuth x v hx hxp hv).1 with h1 | h1
      · exact hel h1
      · exact h.selfPrimNoLease x (by rw [h1, h.core.primKnows]) v hx
  leaseAuth := by
    intro x v hx' hnp' hv
    obtain ⟨ex, hx⟩ := hLS x v hx'
    have hxt : ¬ ThinksPrimary a.core x := fun hp => hnp' ((htp x).2 (Or.inr ⟨ex, hp⟩))
    obtain ⟨h1, h2⟩ := h.leaseAuth x v hx hxt hv
    have hxq : x ≠ a.core.cfg.primary := fun e =>
      h.selfPrimNoLease x (by rw [e, h.core.primKnows]) v hx
    refine ⟨Or.inl ?_, h2⟩
    show eligibleAfterTakeover a.core n x = true
    unfold eligibleAfterTakeover
    rcases h1 with h1 | h1
    · simp [h1, hxq, ex]
    · exact absurd h1 hxq
  selfPrimNoLease := by
    intro q hq v hx
    obtain ⟨e, hx⟩ := hLS q v hx
    change ((takeover a.core n).localCfg q).primary = q at hq
    rw [hK, if_neg e] at hq; exact h.selfPrimNoLease q hq v hx
  committedViewLen := h.committedViewLen
  committedViewHist := h.committedViewHist
  sentLe := hS1, genLe := hS2, commitLe := hS3, follows := hS4
  drop := {
    -- the new primary `n` has confirmed no drop and its drop messages were discarded.
    confirmedNoEcho := by
      intro q x hd
      change update a.dropConfirmed n (fun _ => false) q x = true at hd
      show update a.ackEcho n (fun _ => none) q x = none
      by_cases e : q = n
      · rw [e, update_self] at hd; cases hd
      · rw [update_of_ne _ _ e] at hd; rw [update_of_ne _ _ e]; exact h.drop.confirmedNoEcho q x hd
    confirmedNoLease := by
      intro q x hd hq
      change q = n at hq
      change update a.dropConfirmed n (fun _ => false) q x = true at hd
      rw [hq, update_self] at hd; cases hd
    requestNoEcho := by
      intro q x g t hm hc _ hq
      exact absurd hq (hcb _ hm hc).2.1
    confirmNoLease := by
      intro x q g t hm hc _ hq
      exact absurd hq (hcb _ hm hc).2.2 } }

/-- A full resync: the replica's committed view starts over and its connections close. -/
theorem leaseInvariant_resync {r : Node} (hne : primaryOf a.core r ≠ r)
    (hsy : a.core.sync (primaryOf a.core r) r = false)
    (hke : (a.core.localCfg (primaryOf a.core r)).eligible r = false) :
    LeaseInvariant P (leaseResync a r) := by
  obtain ⟨hCV, hCH⟩ := committedView_reset h (c := resync a.core r) r (fun _ e => resync_log_other e) rfl
  obtain ⟨_, hcb, hgle⟩ := bump_facts h (a' := leaseResync a r) (n := r) rfl rfl
  exact leaseInvariant_frame h (invariant_resync h.core r hne hsy hke) (h.rcore.resync hne)
    (hcfg := rfl) (hlocalCfg := rfl) (hinc := rfl) (hnow := rfl) (hPL := rfl)
    (hAR := rfl) (hAE := fun _ _ _ e => e) (hRL := fun _ _ e => e) (hPS := rfl) (hOE := rfl)
    (fun _ hm => hm) (fun msg hm hc => (hcb msg hm hc).1) hgle
    (fun msg hm hc => (resync_commit_other (s := a.core) (hcb msg hm hc).2.1).ge)
    (fun x => ⟨Nat.le_refl _, h.primaryTrafficLe x⟩) h.dataSentLe hCV hCH
    (drop_mono h rfl rfl rfl (fun _ _ e => e) (fun msg hm => ⟨hm, fun hc => (hcb msg hm hc).1⟩))

/-! ### Restarts -/

/-- A restart of `n`, with replication state `c` afterwards. `c` keeps the configuration
and every other node's incarnation, log and committed offset, and the history. `n`'s
lease rows are cleared, its committed view starts over, its timers restart, and its
connections close. -/
theorem leaseInvariant_restart {n : Node} {c : State Node} (hc : Invariant c) (hrc : RInvariant c)
    (hkl : KnowsLatest a.core n)
    (hcfg : c.cfg = a.core.cfg) (hlocalCfg : c.localCfg = a.core.localCfg)
    (hinc : ∀ x, x ≠ n → c.incarnation x = a.core.incarnation x)
    (hlog : ∀ x, x ≠ n → c.log x = a.core.log x) (hhist : c.hist = a.core.hist)
    (hcommit : ∀ x, x ≠ n → c.commit x = a.core.commit x) :
    LeaseInvariant P (leaseRestart a n c) := by
  have hPT := primaryTraffic_bump h n
  obtain ⟨hAR, hPS, hAE, hPA⟩ := cleared_rows h (a' := leaseRestart a n c) n rfl rfl rfl rfl (fun _ e => update_of_ne _ _ e)
  obtain ⟨hCV, hCH⟩ := committedView_reset h n hlog hhist
  obtain ⟨_, hcb, hgle⟩ := bump_facts h (a' := leaseRestart a n c) (n := n) rfl rfl
  have hLS : ∀ r x, LeaseStart (leaseRestart a n c) r x → r ≠ n ∧ LeaseStart a r x := by
    intro r x hx
    rcases hx with hx | ⟨msg, hm, hc, hd, he⟩
    · obtain ⟨hrn, hx⟩ := update_none_some _ _ _ hx; exact ⟨hrn, Or.inl hx⟩
    · obtain ⟨hc', _, hdn⟩ := hcb msg hm hc
      exact ⟨hd ▸ hdn, Or.inr ⟨msg, hm, hc', hd, he⟩⟩
  have hPLS : ∀ p r x, PrimStart (leaseRestart a n c) p r x → PrimStart a p r x := by
    intro p r x hx
    rcases hx with hx | ⟨msg, hm, hc, hd, hs, he⟩
    · exact Or.inl (update_row_some _ _ _ _ hx).2
    · exact Or.inr ⟨msg, hm, (hcb msg hm hc).1, hd, hs, he⟩
  obtain ⟨hS1, hS2, hS3, hS4⟩ := msgs_frame h (a' := leaseRestart a n c) (Nat.le_refl _) (fun _ hm => hm)
    (fun msg hm hc => (hcb msg hm hc).1) hgle
    (fun msg hm hc => (hcommit _ (hcb msg hm hc).2.1).ge)
    (fun msg _ _ _ => congrArg (fun f => (f msg.dst).primary) hlocalCfg)
  exact {
  core := hc
  rcore := hrc
  primaryTrafficLe := fun x => (hPT x).2
  ackReceivedLe := hAR, primarySinceLe := hPS, echoLe := hAE, primarySinceAck := hPA
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
    show (∃ b, update a.ackReceived n (fun _ => none) c.cfg.primary x = some b ∧ v ≤ b) ∨
      (∃ T, update a.primarySince n (some a.now) c.cfg.primary = some T ∧ v ≤ T ∧
        (update a.oldEligible n (fun _ => true) c.cfg.primary x = true ∨
          ¬ HolderValid P a.now (some v) P.readDur))
    rw [hcfg]
    by_cases hpn : a.core.cfg.primary = n
    · -- the primary restarted: every remaining lease is bounded by its new primaryship.
      rw [hpn, update_self, update_self, update_self]
      right; exact ⟨a.now, rfl, h.leaseStartLe x v hx, Or.inl rfl⟩
    · rw [update_of_ne _ _ hpn, update_of_ne _ _ hpn, update_of_ne _ _ hpn]; exact h.leaseBound x v hx
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
  sentLe := hS1, genLe := hS2, commitLe := hS3, follows := hS4
  drop := by
    refine h.drop.frame (congrArg Cfg.primary hcfg) ?_ ?_ (fun r x hx => (hLS r x hx).2)
      (fun _ _ ⟨m, hm, hc, hd, he⟩ => ⟨m, hm, (hcb m hm hc).1, hd, he⟩)
      (fun m hm hc => ⟨hm, (hcb m hm hc).1⟩)
    · -- `n`'s echoes are cleared, but a confirmed drop already had none.
      intro q x hd
      refine ⟨hd, ?_⟩
      show update a.ackEcho n (fun _ => none) q x = a.ackEcho q x
      by_cases e : q = n
      · rw [e, update_self]; rw [e] at hd; exact (h.drop.confirmedNoEcho n x hd).symm
      · rw [update_of_ne _ _ e]
    · -- `n`'s drop messages were discarded with its connections.
      intro q x he
      by_cases e : q = n
      · right; intro m hm hc hl
        have hm' := hcb m hm hc
        have h1 : m.link.1 = n := by rw [hl]; exact e
        rcases Msg.link_ends m with ⟨e1, _⟩ | ⟨e1, _⟩
        · exact hm'.2.1 (e1 ▸ h1)
        · exact hm'.2.2 (e1 ▸ h1)
      · left; change update a.ackEcho n (fun _ => none) q x = none at he
        rw [update_of_ne _ _ e] at he; exact he }

theorem leaseInvariant_restartEmpty {n : Node} (hkl : KnowsLatest a.core n)
    (hsurv : ∃ m, m ≠ n ∧ IsAuthoritative a.core m) :
    LeaseInvariant P (leaseRestart a n (restartEmpty a.core n)) :=
  leaseInvariant_restart h (invariant_restartEmpty h.core n hkl hsurv) (h.rcore.restartEmpty n) hkl rfl rfl
    (fun _ e => restartEmpty_inc_other e) (fun _ e => restartEmpty_log_other e) rfl
    (fun _ e => restartEmpty_commit_other e)

theorem leaseInvariant_restartKeep {n : Node} (hkl : KnowsLatest a.core n) :
    LeaseInvariant P (leaseRestart a n (restartKeep a.core n)) :=
  leaseInvariant_restart h (invariant_restartKeep h.core n hkl) (h.rcore.restartKeep n) hkl rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) rfl (fun _ e => restartKeep_commit_other e)

theorem leaseInvariant_restartPartialKeep {n : Node} {k : Nat} (hkl : KnowsLatest a.core n)
    (hk : k < (a.core.log n).length) (hkeep : a.core.ackHigh n ≤ k) :
    LeaseInvariant P (leaseRestart a n (restartPartialKeep a.core n k)) :=
  leaseInvariant_restart h (invariant_restartPartialKeep h.core n k hkl hk hkeep) (h.rcore.restartPartialKeep n hk) hkl rfl rfl
    (fun _ _ => rfl) (fun _ e => restartPartialKeep_log_other e) rfl
    (fun _ e => restartKeep_commit_other e)

theorem leaseInvariant_restartPartialFresh {n : Node} {k : Nat} (hkl : KnowsLatest a.core n)
    (hk : k < (a.core.log n).length) (hfresh : k < a.core.ackHigh n)
    (hsurv : ∃ m, m ≠ n ∧ IsAuthoritative a.core m) :
    LeaseInvariant P (leaseRestart a n (restartPartialFresh a.core n k)) :=
  leaseInvariant_restart h (invariant_restartPartialFresh h.core n k hkl hsurv hk hfresh) (h.rcore.restartPartialFresh n hk) hkl rfl rfl
    (fun _ e => restartEmpty_inc_other e) (fun _ e => restartPartialFresh_log_other e) rfl
    (fun _ e => restartEmpty_commit_other e)

/-! ### Planned demotion -/

/-- `p` asks `r` to drop its read lease: `p` clears its echo of `r`, closes the
connection to `r` (discarding every message on it in flight), and sends the request on
the new connection. Every echo to `r` in flight came from `r`'s primary `p`, so it was
on that connection. -/
theorem leaseInvariant_sendDropRequest {p r : Node} (hf : primaryOf a.core r = p) :
    LeaseInvariant P (sendDropRequest a p r) := by
  set b : LeaseState Node := { a with ackEcho := update2 a.ackEcho p r none, gen := closeLink a.gen p r } with hbdef
  -- the connection from `p` to `r` closes; every other one is as before.
  have hcb : ∀ msg ∈ a.net, msg.Current b → msg.Current a ∧ msg.link ≠ (p, r) := by
    intro msg hm hc
    obtain ⟨hn, he⟩ := closeLink_open (h.genLe msg hm) hc
    exact ⟨he, fun hl => hn ⟨congrArg Prod.fst hl, congrArg Prod.snd hl⟩⟩
  have hmono : ∀ msg ∈ b.net, msg ∈ a.net ∧ (msg.Current b → msg.Current a) :=
    fun msg hm => ⟨hm, fun hc => (hcb msg hm hc).1⟩
  have hgle : ∀ msg ∈ a.net, msg.g ≤ b.gen msg.link.1 msg.link.2 :=
    fun msg hm => Nat.le_trans (h.genLe msg hm) (le_closeLink _ _ _ _ _)
  have hAE : ∀ q x e, b.ackEcho q x = some e → a.ackEcho q x = some e := by
    intro q x e he
    change update2 a.ackEcho p r none q x = some e at he
    by_cases ex : q = p ∧ x = r
    · obtain ⟨rfl, rfl⟩ := ex; rw [update2_self] at he; cases he
    · rw [update2_of_ne _ _ ex] at he; exact he
  have hdrop : DropInvariant b := by
    refine h.drop.frame rfl ?_ ?_ (fun r x hx => leaseStart_mono a b (fun _ _ e => e) hmono hx)
      (fun _ _ ⟨m, hm, hc, hd, he⟩ => ⟨m, hm, (hcb m hm hc).1, hd, he⟩)
      (fun m hm hc => ⟨hm, (hcb m hm hc).1⟩)
    · intro q x hd
      refine ⟨hd, ?_⟩
      change update2 a.ackEcho p r none q x = a.ackEcho q x
      by_cases ex : q = p ∧ x = r
      · obtain ⟨rfl, rfl⟩ := ex; rw [update2_self]; exact (h.drop.confirmedNoEcho q x hd).symm
      · rw [update2_of_ne _ _ ex]
    · intro q x he
      by_cases ex : q = p ∧ x = r
      · obtain ⟨rfl, rfl⟩ := ex
        right; intro m hm hc; exact (hcb m hm hc).2
      · left; change update2 a.ackEcho p r none q x = none at he
        rw [update2_of_ne _ _ ex] at he; exact he
  have hb : LeaseInvariant P b :=
    leaseInvariant_frame h h.core h.rcore rfl rfl rfl rfl rfl rfl hAE (fun _ _ e => e) rfl rfl
      (fun _ hm => hm) (fun msg hm hc => (hcb msg hm hc).1) hgle (fun _ _ _ => Nat.le_refl _)
      (fun x => ⟨Nat.le_refl _, h.primaryTrafficLe x⟩) h.dataSentLe h.committedViewLen h.committedViewHist
      hdrop
  refine leaseInvariant_send hb (closeLink_self _ _ _).symm rfl (fun _ hx => by cases hx) (fun hx => by cases hx)
    (fun _ hx => by cases hx) (fun _ hx => by cases hx) ?_
  refine hb.drop.sendMsg rfl ?_ (fun _ _ _ _ e => by cases e)
  -- no echo to `r` is current: a current echo comes from `r`'s primary `p`, on the
  -- connection that just closed.
  intro q x g t e _ _ y ⟨m, hm, hc, hd, he⟩
  obtain ⟨-, rfl, -⟩ := Msg.dropReq.inj e
  obtain ⟨hca, hl⟩ := hcb m hm hc
  have hdata : m.commitOf.isSome := by cases m <;> simp_all [Msg.echo, Msg.commitOf]
  obtain ⟨hpf, -⟩ := h.follows m hm hca hdata
  apply hl
  cases m <;> simp_all [Msg.link, Msg.src, Msg.dst, Msg.commitOf]

/-- A current drop request reaches `r`: `r` drops its read lease and confirms. -/
theorem leaseInvariant_deliverDropRequest {p r : Node} {g t : Nat}
    (hm : Msg.dropReq p r g t ∈ a.net) (hc : (Msg.dropReq p r g t).Current a) :
    LeaseInvariant P (deliverDropRequest a (.dropReq p r g t) r p) := by
  set c : LeaseState Node :=
    { a with net := a.net.erase (.dropReq p r g t), readLease := update a.readLease r none } with hcdef
  have hRL : ∀ q x, c.readLease q = some x → a.readLease q = some x :=
    fun q x e => (update_none_some _ _ _ e).2
  have hnet : ∀ m ∈ c.net, m ∈ a.net ∧ (m.Current c → m.Current a) :=
    fun m hm => ⟨List.mem_of_mem_erase hm, id⟩
  have hcI : LeaseInvariant P c :=
    leaseInvariant_frame h h.core h.rcore rfl rfl rfl rfl rfl rfl (fun _ _ _ e => e) hRL rfl rfl
      (fun _ hm => List.mem_of_mem_erase hm) (fun _ _ hc => hc) h.genLe (fun _ _ _ => Nat.le_refl _)
      (fun x => ⟨Nat.le_refl _, h.primaryTrafficLe x⟩) h.dataSentLe h.committedViewLen h.committedViewHist
      (drop_mono h rfl rfl rfl hRL hnet)
  refine leaseInvariant_send hcI rfl rfl (fun _ hx => by cases hx) (fun hx => by cases hx)
    (fun _ hx => by cases hx) (fun _ hx => by cases hx) ?_
  refine hcI.drop.sendMsg rfl (fun _ _ _ _ e => by cases e) ?_
  -- `r` has just dropped its lease, and no echo to it was current while the request was.
  intro x q g' t' e he hq y hy
  obtain ⟨rfl, rfl, -⟩ := Msg.dropAck.inj e
  rcases hy with hy | ⟨m, hm', hc', hd, he'⟩
  · change update a.readLease r none r = some y at hy; rw [update_self] at hy; cases hy
  · exact h.drop.requestNoEcho p r g t hm hc he hq y ⟨m, List.mem_of_mem_erase hm', hc', hd, he'⟩

/-- A current confirmation reaches `p`, which has received no acknowledgement from `r`
since it asked: `p` records the confirmed drop. -/
theorem leaseInvariant_deliverDropConfirm {r p : Node} {g t : Nat}
    (hm : Msg.dropAck r p g t ∈ a.net) (hc : (Msg.dropAck r p g t).Current a)
    (hno : a.ackEcho p r = none) :
    LeaseInvariant P (deliverDropConfirm a (.dropAck r p g t) p r) := by
  set a' := deliverDropConfirm a (.dropAck r p g t) p r with ha'
  have hnet : ∀ m ∈ a'.net, m ∈ a.net ∧ (m.Current a' → m.Current a) :=
    fun m hm => ⟨List.mem_of_mem_erase hm, id⟩
  have hLS : ∀ x y, LeaseStart a' x y → LeaseStart a x y :=
    fun x y hy => leaseStart_mono a a' (fun _ _ e => e) hnet hy
  have hdrop : DropInvariant a' := {
    confirmedNoEcho := by
      intro q x hd
      change update2 a.dropConfirmed p r true q x = true at hd
      by_cases ex : q = p ∧ x = r
      · obtain ⟨rfl, rfl⟩ := ex; exact hno
      · rw [update2_of_ne _ _ ex] at hd; exact h.drop.confirmedNoEcho q x hd
    confirmedNoLease := by
      intro q x hd hq y hy
      change update2 a.dropConfirmed p r true q x = true at hd
      by_cases ex : q = p ∧ x = r
      · obtain ⟨rfl, rfl⟩ := ex; exact h.drop.confirmNoLease x q g t hm hc hno hq y (hLS x y hy)
      · rw [update2_of_ne _ _ ex] at hd; exact h.drop.confirmedNoLease q x hd hq y (hLS x y hy)
    requestNoEcho := by
      intro q x g' t' hm' hc' he hq y ⟨m, hmm, hmc, hd, hme⟩
      exact h.drop.requestNoEcho q x g' t' (List.mem_of_mem_erase hm') hc' he hq y
        ⟨m, List.mem_of_mem_erase hmm, hmc, hd, hme⟩
    confirmNoLease := by
      intro x q g' t' hm' hc' he hq y hy
      exact h.drop.confirmNoLease x q g' t' (List.mem_of_mem_erase hm') hc' he hq y (hLS x y hy) }
  exact leaseInvariant_frame h h.core h.rcore rfl rfl rfl rfl rfl rfl (fun _ _ _ e => e) (fun _ _ e => e) rfl rfl
    (fun _ hm => List.mem_of_mem_erase hm) (fun _ _ hc => hc) h.genLe (fun _ _ _ => Nat.le_refl _)
    (fun x => ⟨Nat.le_refl _, h.primaryTrafficLe x⟩) h.dataSentLe h.committedViewLen h.committedViewHist hdrop

end preserve

/-! ## Every step preserves the invariant; the theorem -/

/-- Every lease-layer step preserves the invariant, given `margin ≥ 2 · drift`. -/
theorem leaseInvariant_step {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {m : Nat}
    {a a' : LeaseState Node} {μ : LeaseAction Node} (h : LeaseInvariant P a) (hs : LeaseStep m P a μ a') :
    LeaseInvariant P a' := by
  cases hs with
  | tick => exact leaseInvariant_tick h
  | core μ c hc hpl => exact leaseInvariant_core h hc hpl
  | sendData p r hne hf => exact leaseInvariant_sendData h hne hf
  | sendGrant p r hne hf hp hg => exact leaseInvariant_sendGrant hM h hne hf hp hg
  | sendAck r hne => exact leaseInvariant_sendAck h hne
  | deliverData p r g t c e hm hc hf ho => exact leaseInvariant_deliverData h hm hc hf (h.rcore.prefix_of_open ho)
  | deliverAck r p g t d hm hc => exact leaseInvariant_deliverAck h hm hc
  | drop msg _ => exact leaseInvariant_drop h
  | learn n hnkl => exact leaseInvariant_learn h hnkl
  | demote p r hp hkl hel hw => exact leaseInvariant_demote hM h hp hkl hel hw
  | takeover n hkl hel hnp hin hwait => exact leaseInvariant_takeover h hkl hel hnp hin hwait
  | resync r hne hsy hke => exact leaseInvariant_resync h hne hsy hke
  | restartEmpty n hkl hsurv => exact leaseInvariant_restartEmpty h hkl hsurv
  | restartKeep n hkl => exact leaseInvariant_restartKeep h hkl
  | restartPartialKeep n k hkl hk hkeep => exact leaseInvariant_restartPartialKeep h hkl hk hkeep
  | restartPartialFresh n k hkl hk hfresh hsurv => exact leaseInvariant_restartPartialFresh h hkl hk hfresh hsurv
  | sendDropRequest p r _ hf _ => exact leaseInvariant_sendDropRequest h hf
  | deliverDropRequest p r g t hm hc => exact leaseInvariant_deliverDropRequest h hm hc
  | deliverDropConfirm r p g t hm hc hno => exact leaseInvariant_deliverDropConfirm h hm hc hno

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
