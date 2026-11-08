import SyncReplication.Lists
import Mathlib.Data.Nat.Lattice
import SyncReplication.Model

/-! # The inductive invariant

`Invariant` is the predicate on states that `Safety` is strengthened to so that every
step preserves it. It has five layers, each about one part of the design and stated
in terms of the earlier ones: `ConfigInvariant` (the Cluster V2 configuration and
incarnations), `ReplInvariant` (acknowledgements are real; the commit rule),
`MembershipInvariant` (the ordering rules of promotion and demotion),
`CommitInvariant` (committed prefixes and the reconciliation point) and
`FailoverInvariant` (deposed primaries are fenced; some node is authoritative). The
goal, EligibleHoldsCommitted, is `Invariant`'s own field `eligibleHoldsCommitted`. Each conjunct's
docstring cites the design.

Facts about the current primary (`historyWithinCommitOrInherited`, the primary clauses of `DeposedFenced`) hold
only while it is authoritative: a primary that came back empty holds nothing, and
nothing new is committed until an authoritative eligible replica takes over. -/

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-!
## The fence of a deposed primary

A takeover does not stop the old primary: it may still think it is primary and keep
committing. What stops it is the commit rule. Some members of its sync replica set
have moved to the new primary, so they never acknowledge the old primary again, and
it can never commit past the smallest of their frozen acknowledgements. That offset
is the old primary's *fence*. The design's "Writes can't split-brain" (§5) is then: a
deposed primary only commits below its fence, and the new configuration already
holds its log up to the fence.
-/

/-- The members of `p`'s sync replica set that follow a different primary and are
eligible in `p`'s configuration. -/
def leftSync (s : State Node) (p : Node) : Set Node :=
  {r | s.sync p r = true ∧ (s.known r).primary ≠ p ∧ (s.known p).eligible r = true}

/-- The fence of `p`: the smallest acknowledgement `p` has recorded from a sync
replica that has left it and that `p`'s configuration lists as eligible. Only those can
fence `p`: Uncount never drops them, since it may drop only members `p` does not list as
eligible. It is `0` when no replica has left (`sInf ∅ = 0`); it is only
used through `DeposedFenced`, which rules that case out. -/
noncomputable def fence (s : State Node) (p : Node) : Nat :=
  sInf (s.acked p '' leftSync s p)

/-- `p` is fenced: some sync replica has left it, and the new configuration holds
`p`'s log up to its fence. -/
structure DeposedFenced (s : State Node) (p : Node) : Prop where
  /-- Some member of `p`'s sync replica set that `p` lists as eligible has moved to a
  different primary. -/
  left      : (leftSync s p).Nonempty
  /-- While the current primary is authoritative, it must reconcile at least up to the
  fence. -/
  fenceLeInheritedEnd   : PrimaryAuthoritative s → fence s p ≤ s.inheritedEnd s.cfg.primary
  /-- While the current primary is authoritative, it holds `p`'s log up to the fence. -/
  primHolds : PrimaryAuthoritative s → (s.log p).take (fence s p) <+: s.log s.cfg.primary
  /-- ... and has acknowledged up to the fence, so a stale restore that keeps its
  incarnation (`ackHigh ≤ k`) keeps `p`'s log up to the fence (RestartPartial). -/
  primAck   : PrimaryAuthoritative s → fence s p ≤ s.ackHigh s.cfg.primary
  /-- Every eligible replica holds, and has acknowledged, `p`'s log up to the fence, or
  still follows `p` and is counted by it (so `p` cannot commit past what that replica
  holds). -/
  eligHolds : ∀ m, s.cfg.eligible m = true → s.cfg.incarnation m = s.incarnation m →
    ((s.log p).take (fence s p) <+: s.log m ∧ fence s p ≤ s.ackHigh m) ∨
      (s.sync p m = true ∧ (s.known m).primary = p)

theorem fence_le {s : State Node} {p r : Node} (hr : r ∈ leftSync s p) : fence s p ≤ s.acked p r :=
  Nat.sInf_le ⟨r, hr, rfl⟩

/-- To show `p` is fenced, name one sync replica `w` that has left it and show the
fence properties at `w`'s acknowledgement. The fence is at most that, and each
property still holds at a smaller offset. -/
theorem DeposedFenced.of_left {s : State Node} {p w : Node} (hw : w ∈ leftSync s p)
    (hrec : PrimaryAuthoritative s → s.acked p w ≤ s.inheritedEnd s.cfg.primary)
    (hprim : PrimaryAuthoritative s → (s.log p).take (s.acked p w) <+: s.log s.cfg.primary)
    (hprimAck : PrimaryAuthoritative s → s.acked p w ≤ s.ackHigh s.cfg.primary)
    (helig : ∀ m, s.cfg.eligible m = true → s.cfg.incarnation m = s.incarnation m →
      ((s.log p).take (s.acked p w) <+: s.log m ∧ s.acked p w ≤ s.ackHigh m) ∨
        (s.sync p m = true ∧ (s.known m).primary = p)) :
    DeposedFenced s p := by
  have hle := fence_le hw
  refine ⟨⟨w, hw⟩, fun hp => hle.trans (hrec hp), fun hp => take_mono_prefix hle (hprim hp),
    fun hp => hle.trans (hprimAck hp), ?_⟩
  intro m hm hi
  rcases helig m hm hi with ⟨d, da⟩ | d
  · exact Or.inl ⟨take_mono_prefix hle d, hle.trans da⟩
  · exact Or.inr d

/-- The fence is the acknowledgement of some replica that has left. -/
theorem DeposedFenced.attained {s : State Node} {p : Node} (hF : DeposedFenced s p) :
    ∃ w ∈ leftSync s p, s.acked p w = fence s p := Nat.sInf_mem (hF.left.image _)

/-- A step that only extends logs, may add sync replicas, and leaves the configuration,
the nodes' views of it and `p`'s acknowledgements from departed replicas alone keeps
`p` fenced (AppendWrite, Replicate, Ack, Commit, Count). -/
theorem DeposedFenced.mono {s s' : State Node} {p : Node} (hF : DeposedFenced s p)
    (hcfg : s'.cfg = s.cfg) (hknown : s'.known = s.known) (hinherited : s'.inheritedEnd = s.inheritedEnd)
    (hinc : s'.incarnation = s.incarnation) (hgrow : ∀ x, s.log x <+: s'.log x)
    (hah : ∀ x, s.ackHigh x ≤ s'.ackHigh x)
    (hlp : ∀ r, s.acked p r ≤ (s.log p).length)
    (hsync : ∀ r, s.sync p r = true → s'.sync p r = true)
    (hacked : ∀ r, (s.known r).primary ≠ p → s'.acked p r = s.acked p r) : DeposedFenced s' p := by
  obtain ⟨w, ⟨hw1, hw2⟩, hwF⟩ := hF.attained
  have hpa : PrimaryAuthoritative s' → PrimaryAuthoritative s := by
    unfold PrimaryAuthoritative; rw [hcfg, hinc]; exact id
  have ha : s'.acked p w = fence s p := (hacked w hw2.1).trans hwF
  have e : (s'.log p).take (s'.acked p w) = (s.log p).take (fence s p) := by
    rw [ha]; exact (prefix_take_eq (hgrow p) (by rw [← hwF]; exact hlp w)).symm
  refine DeposedFenced.of_left (w := w) ⟨hsync w hw1, by rw [hknown]; exact hw2⟩ ?_ ?_ ?_ ?_
  · intro hp; rw [ha, hinherited, hcfg]; exact hF.fenceLeInheritedEnd (hpa hp)
  · intro hp; rw [e, hcfg]; exact (hF.primHolds (hpa hp)).trans (hgrow _)
  · intro hp; rw [ha, hcfg]; exact (hF.primAck (hpa hp)).trans (hah _)
  · intro m hm hi
    rw [hcfg] at hm; rw [hcfg, hinc] at hi
    rcases hF.eligHolds m hm hi with ⟨d, da⟩ | ⟨d1, d2⟩
    · left; rw [e, ha]; exact ⟨d.trans (hgrow m), da.trans (hah m)⟩
    · right; exact ⟨hsync m d1, by rw [hknown]; exact d2⟩

/-- A step that leaves `x`'s log, sync replica set and counted acknowledgements alone
and does not move who follows whom or change which replicas `x` lists as eligible keeps
`x` fenced, provided the current primary still
satisfies the fence bounds and every authoritative eligible replica either is unchanged
or holds (and has acknowledged) `x`'s log up to the fence (MakeEligible, MakeIneligible,
Resync, the restarts). -/
theorem DeposedFenced.transfer {s s' : State Node} {x : Node} (hF : DeposedFenced s x)
    (hsync : s'.sync x = s.sync x) (hkn : ∀ y, (s'.known y).primary = (s.known y).primary)
    (hke : (s'.known x).eligible = (s.known x).eligible)
    (hack : ∀ r, s.sync x r = true → s'.acked x r = s.acked x r)
    (hlog : s'.log x = s.log x) (hprim : s'.cfg.primary = s.cfg.primary)
    (hpa : PrimaryAuthoritative s' → PrimaryAuthoritative s)
    (hrec : PrimaryAuthoritative s' → fence s x ≤ s'.inheritedEnd s.cfg.primary)
    (hlp : PrimaryAuthoritative s' → (s.log x).take (fence s x) <+: s'.log s.cfg.primary)
    (hahp : PrimaryAuthoritative s' → fence s x ≤ s'.ackHigh s.cfg.primary)
    (hcov : ∀ m, s'.cfg.eligible m = true → s'.cfg.incarnation m = s'.incarnation m →
      (s.cfg.eligible m = true ∧ s.cfg.incarnation m = s.incarnation m ∧ s'.log m = s.log m ∧
          s.ackHigh m ≤ s'.ackHigh m) ∨
        ((s.log x).take (fence s x) <+: s'.log m ∧ fence s x ≤ s'.ackHigh m)) : DeposedFenced s' x := by
  obtain ⟨w, ⟨hw1, hw2⟩, hwF⟩ := hF.attained
  have ha : s'.acked x w = fence s x := (hack w hw1).trans hwF
  refine DeposedFenced.of_left (w := w) ⟨by rw [hsync]; exact hw1, by rw [hkn, hke]; exact hw2⟩ ?_ ?_ ?_ ?_
  · intro hp; rw [ha, hprim]; exact hrec hp
  · intro hp; rw [ha, hlog, hprim]; exact hlp hp
  · intro hp; rw [ha, hprim]; exact hahp hp
  · intro m hm hi
    rcases hcov m hm hi with ⟨he, hi0, hl, hah⟩ | d
    · rcases hF.eligHolds m he hi0 with ⟨d, da⟩ | ⟨d1, d2⟩
      · left; rw [ha, hlog, hl]; exact ⟨d, da.trans hah⟩
      · right; rw [hsync, hkn]; exact ⟨d1, d2⟩
    · left; rw [ha, hlog]; exact d

/-- The fence is within `p`'s log when `p`'s recorded acknowledgements are. -/
theorem DeposedFenced.le_len {s : State Node} {p : Node} (hF : DeposedFenced s p)
    (hlp : ∀ r, s.acked p r ≤ (s.log p).length) : fence s p ≤ (s.log p).length := by
  obtain ⟨w, _, hwF⟩ := hF.attained; rw [← hwF]; exact hlp w

/-!
## The inductive invariant, in layers

`Invariant` is the conjunction of five layers. Each layer is about one part of the design,
and each is stated in terms of the layers listed before it, with one exception:
`MembershipInvariant.syncNew` already uses the reconciliation point that `CommitInvariant`
constrains. Read them in order; the last
field of the last layer, `eligibleHoldsCommitted`, is the property we want.
-/

/-- **Configuration.** Cluster V2 holds one totally ordered configuration; each node's
copy may be behind it but never ahead, and incarnation records never run ahead of the
nodes they describe (design §6). -/
structure ConfigInvariant (s : State Node) : Prop where
  /-- No node has seen a configuration newer than the latest one. -/
  knownLe    : ∀ n, (s.known n).version ≤ s.cfg.version
  /-- A node that has seen the latest version has the latest configuration. -/
  knownEq    : ∀ n, (s.known n).version = s.cfg.version → s.known n = s.cfg
  /-- The current primary knows the configuration that made it primary. -/
  primKnows  : s.known s.cfg.primary = s.cfg
  /-- No node's copy of the configuration records an incarnation newer than the node's
  own, so a node that came back empty never matches its old record ("Restarted nodes
  rejoin as ineligible"). -/
  knownIncLe : ∀ x n, (s.known x).incarnation n ≤ s.incarnation n

/-- A recorded incarnation in the latest configuration is never newer than the node's
own: the current primary's copy is the latest configuration (`primKnows`), and
`knownIncLe` bounds every copy. Formerly a conjunct of `ConfigInvariant`. -/
theorem ConfigInvariant.incLe {s : State Node} (h : ConfigInvariant s) :
    ∀ n, s.cfg.incarnation n ≤ s.incarnation n := by
  intro n; have := h.knownIncLe s.cfg.primary n; rwa [h.primKnows] at this

/-- **Replication.** An acknowledgement is real: a primary's record of a replica's
acknowledged offset never exceeds what the replica holds of the primary's log, and a
primary's committed offset never passes a sync replica's acknowledgement (design §2,
commit rule). -/
structure ReplInvariant (s : State Node) : Prop where
  /-- A node is never in its own sync replica set. -/
  noSelfSync : ∀ p, s.sync p p = false
  /-- The current primary has no acknowledgement recorded from a node that follows a
  different primary. -/
  ackedPrim  : ∀ r, (s.known r).primary ≠ s.cfg.primary → s.acked s.cfg.primary r = 0
  /-- A recorded acknowledgement is within the primary's own log. -/
  ackedLe    : ∀ p r, ThinksPrimary s p → s.acked p r ≤ (s.log p).length
  /-- A follower holds its primary's log up to the acknowledged offset. -/
  ackHolds   : ∀ p n, ThinksPrimary s p → n ≠ p → (s.known n).primary = p →
                 (s.log p).take (s.acked p n) <+: s.log n
  /-- A follower's acknowledgement at its primary is within its own high-water mark:
  what a primary believes a replica acknowledged, the replica remembers having
  acknowledged. -/
  ackedHigh  : ∀ p n, ThinksPrimary s p → n ≠ p → (s.known n).primary = p →
                 s.acked p n ≤ s.ackHigh n
  /-- Commit rule: a primary never commits past a sync replica's acknowledgement. -/
  syncCommit : ∀ q r, ThinksPrimary s q → s.sync q r = true → s.commit q ≤ s.acked q r

/-- **Membership.** The two ordering rules of promotion and demotion (design §4): a
replica counts toward commits before it becomes eligible, and stops being eligible
before a write commits without it. -/
structure MembershipInvariant (s : State Node) : Prop where
  /-- Every eligible replica with a matching incarnation is counted ("must count toward
  commits **before** it becomes eligible"). A restarted primary rebuilds its sync
  replica set so that this survives the restart. -/
  eligibleCounted   : ∀ p r, ThinksPrimary s p → (s.known p).eligible r = true → (s.known p).incarnation r = s.incarnation r →
                 s.sync p r = true
  /-- A replica the current primary counts but has not made eligible follows it and has
  acknowledged at least the reconciliation point (promotion steps 1-2). -/
  syncNew    : ∀ r, s.sync s.cfg.primary r = true → s.cfg.eligible r = false →
                 (s.known r).primary = s.cfg.primary ∧ s.inheritedEnd s.cfg.primary ≤ s.acked s.cfg.primary r
  /-- An eligible replica that follows an old primary is still eligible in that
  primary's configuration. -/
  eligibleInOldConfig    : ∀ m, s.cfg.eligible m = true → (s.known m).primary ≠ s.cfg.primary →
                 (s.known (s.known m).primary).eligible m = true

/-- **Commit.** Committed prefixes agree with the committed history, and the current
primary's catch-up point covers it (design §2, "committed offset"; §5, reconciliation). -/
structure CommitInvariant (s : State Node) : Prop where
  /-- A committed offset is within the node's log. -/
  commitWithinLog      : ∀ p, s.commit p ≤ (s.log p).length
  /-- What a node has committed is exactly the start of the committed history. -/
  committedIsHistoryPrefix       : ∀ p, (s.log p).take (s.commit p) = s.hist.take (s.commit p)
  /-- The current primary's catch-up point is within its log. -/
  inheritedEndWithinLog   : s.inheritedEnd s.cfg.primary ≤ (s.log s.cfg.primary).length
  /-- While the current primary is authoritative, the whole committed history is below
  its commit point or its catch-up point: a new primary reconciles against all of it. -/
  historyWithinCommitOrInherited     : PrimaryAuthoritative s → s.hist.length ≤ s.commit s.cfg.primary ∨ s.hist.length ≤ s.inheritedEnd s.cfg.primary
  /-- Every authoritative node has acknowledged the whole committed history: a replica
  is counted, and so made eligible, only after acknowledging past the reconciliation
  point, and a commit by the current primary waits for every counted replica. This is
  what makes a stale restore at or above `ackHigh` safe (RestartPartial). -/
  histAck    : ∀ n, IsAuthoritative s n → s.hist.length ≤ s.ackHigh n

/-- A committed offset is within the committed history: it is within the node's log
(`commitWithinLog`), and that prefix of the log is the same prefix of the history
(`committedIsHistoryPrefix`). Formerly a conjunct of `CommitInvariant`. -/
theorem CommitInvariant.commitWithinHistory {s : State Node} (h : CommitInvariant s) :
    ∀ p, s.commit p ≤ s.hist.length := by
  intro p
  have e := congrArg List.length (h.committedIsHistoryPrefix p)
  rw [List.length_take, List.length_take, Nat.min_eq_left (h.commitWithinLog p)] at e
  omega

/-- **Failover.** A deposed primary cannot commit anything the new configuration does
not hold ("Writes can't split-brain", design §5), and some node keeps the data (the
survival condition). -/
structure FailoverInvariant (s : State Node) : Prop where
  /-- A node that still thinks it is primary under an old configuration is fenced:
  it can only commit below its `fence`, and the new configuration holds its log up
  to there. -/
  stale      : ∀ p, ThinksPrimary s p → (s.known p).version < s.cfg.version → DeposedFenced s p
  /-- Survival: some node is authoritative (kept by the RestartEmpty guard). -/
  authEx     : ∃ n, IsAuthoritative s n

/-! ### Frame lemmas: a layer is kept by any step that leaves its variables alone. -/

/-- A step that changes neither the configuration, nor any node's copy of it, nor any
incarnation keeps `ConfigInvariant`. -/
theorem ConfigInvariant.frame {s s' : State Node} (h : ConfigInvariant s)
    (hcfg : s'.cfg = s.cfg) (hknown : s'.known = s.known) (hinc : s'.incarnation = s.incarnation) :
    ConfigInvariant s' := by
  obtain ⟨h1, h2, h3, h5⟩ := h
  exact ⟨by rw [hcfg, hknown]; exact h1, by rw [hcfg, hknown]; exact h2,
    by rw [hcfg, hknown]; exact h3, by rw [hknown, hinc]; exact h5⟩

/-- A step that changes no commit point, catch-up point, log, history, configuration or
incarnation keeps `CommitInvariant`. -/
theorem CommitInvariant.frame {s s' : State Node} (h : CommitInvariant s)
    (hcommit : s'.commit = s.commit) (hinherited : s'.inheritedEnd = s.inheritedEnd) (hlog : s'.log = s.log)
    (hhist : s'.hist = s.hist) (hcfg : s'.cfg = s.cfg) (hinc : s'.incarnation = s.incarnation)
    (hah : s'.ackHigh = s.ackHigh) : CommitInvariant s' := by
  obtain ⟨h1, h3, h4, h5, h6⟩ := h
  refine ⟨by rw [hcommit, hlog]; exact h1,
    by rw [hcommit, hlog, hhist]; exact h3, by rw [hinherited, hlog, hcfg]; exact h4, ?_, ?_⟩
  · intro hpa; rw [hhist, hcommit, hinherited, hcfg]
    exact h5 (by unfold PrimaryAuthoritative at hpa ⊢; rw [hcfg, hinc] at hpa; exact hpa)
  · intro n hn; rw [hhist, hah]
    exact h6 n (by unfold IsAuthoritative at hn ⊢; rw [hcfg, hinc] at hn; exact hn)

/-- A step that changes no sync replica set, acknowledgement, configuration, copy of it,
incarnation or catch-up point keeps `MembershipInvariant`. -/
theorem MembershipInvariant.frame {s s' : State Node} (h : MembershipInvariant s)
    (hsync : s'.sync = s.sync) (hacked : s'.acked = s.acked) (hcfg : s'.cfg = s.cfg)
    (hknown : s'.known = s.known) (hinc : s'.incarnation = s.incarnation) (hinherited : s'.inheritedEnd = s.inheritedEnd) :
    MembershipInvariant s' := by
  obtain ⟨h1, h2, h3⟩ := h
  have htp : ∀ p, ThinksPrimary s' p ↔ ThinksPrimary s p := by
    intro p; unfold ThinksPrimary; rw [hknown, hinc]
  refine ⟨?_, ?_, ?_⟩
  · intro p r hp; rw [hknown, hinc, hsync]; exact h1 p r ((htp p).1 hp)
  · intro r; rw [hcfg, hsync, hknown, hinherited, hacked]; exact h2 r
  · intro m; rw [hcfg, hknown]; exact h3 m

/-- The inductive invariant: the five layers plus the goal. -/
structure Invariant (s : State Node) : Prop
    extends ConfigInvariant s, ReplInvariant s, MembershipInvariant s, CommitInvariant s, FailoverInvariant s where
  /-- **Goal**, EligibleHoldsCommitted: every authoritative node holds the whole
  committed history. -/
  eligibleHoldsCommitted        : ∀ n, IsAuthoritative s n → s.hist <+: s.log n

theorem invariant_safety {s : State Node} (h : Invariant s) : Safety s :=
  ⟨h.eligibleHoldsCommitted, fun p => ⟨h.commitWithinLog p, h.committedIsHistoryPrefix p⟩⟩

/-- The invariant does not mention replication IDs: changing `replId` and `usedIds` alone
keeps it. -/
theorem Invariant.replId_frame {s : State Node} (h : Invariant s) (t : Node → Nat) (u : Finset Nat) :
    Invariant { s with replId := t, usedIds := u } where
  toConfigInvariant := ⟨h.knownLe, h.knownEq, h.primKnows, h.knownIncLe⟩
  toReplInvariant := ⟨h.noSelfSync, h.ackedPrim, h.ackedLe, h.ackHolds, h.ackedHigh, h.syncCommit⟩
  toMembershipInvariant := ⟨h.eligibleCounted, h.syncNew, h.eligibleInOldConfig⟩
  toCommitInvariant := ⟨h.commitWithinLog, h.committedIsHistoryPrefix, h.inheritedEndWithinLog,
    h.historyWithinCommitOrInherited, h.histAck⟩
  toFailoverInvariant := ⟨fun p hp hv => let hF := h.stale p hp hv
      ⟨hF.left, hF.fenceLeInheritedEnd, hF.primHolds, hF.primAck, hF.eligHolds⟩, h.authEx⟩
  eligibleHoldsCommitted := h.eligibleHoldsCommitted

theorem invariant_init (i : Node) : Invariant (init i) where
  eligibleHoldsCommitted := by intro n _; simp [init]
  commitWithinLog := by intro p; simp [init]
  committedIsHistoryPrefix := by intro p; simp [init]
  knownLe := by intro n; simp [init]
  knownEq := by intro n _; rfl
  primKnows := rfl
  authEx := ⟨i, Or.inr rfl, rfl⟩
  knownIncLe := by intro x n; simp [init, initCfg]
  eligibleCounted := by intro p r _ h; simp [init, initCfg] at h
  noSelfSync := by intro p; rfl
  ackedPrim := by intro r _; rfl
  ackedLe := by intro p r _; simp [init]
  ackHolds := by intro p n _ _ _; simp [init]
  syncNew := by intro r h; simp [init] at h
  inheritedEndWithinLog := by simp [init]
  syncCommit := by intro q r _ _; simp [init]
  eligibleInOldConfig := by intro m h; simp [init, initCfg] at h
  historyWithinCommitOrInherited := by intro _; simp [init]
  stale := by intro p _ h; simp [init, initCfg] at h
  ackedHigh := by intro p n _ _ _; simp [init]
  histAck := by intro n _; simp [init]

/-! ### Derived facts -/

section
variable {s : State Node} (h : Invariant s)
include h

theorem thinksPrimary_prim (hpa : PrimaryAuthoritative s) : ThinksPrimary s s.cfg.primary := by
  unfold ThinksPrimary; rw [h.primKnows]; exact ⟨rfl, hpa⟩

theorem thinksPrimary_knowsLatest {p : Node} (hp : ThinksPrimary s p) (hk : KnowsLatest s p) : s.known p = s.cfg ∧ s.cfg.primary = p := by
  have e := h.knownEq p hk
  refine ⟨e, ?_⟩
  have := hp.1; rw [e] at this; exact this

theorem thinksPrimary_cases {p : Node} (hp : ThinksPrimary s p) :
    (p = s.cfg.primary ∧ s.known p = s.cfg) ∨ (s.known p).version < s.cfg.version := by
  rcases Nat.lt_or_ge (s.known p).version s.cfg.version with hl | hg
  · exact Or.inr hl
  · have hk : KnowsLatest s p := Nat.le_antisymm (h.knownLe p) hg
    have := thinksPrimary_knowsLatest h hp hk
    exact Or.inl ⟨this.2.symm, this.1⟩

omit h in
/-- A node that thinks it is primary and knows the latest config is the current,
authoritative primary. -/
theorem thinksPrimary_primaryAuthoritative {p : Node} (hp : ThinksPrimary s p) (hk : s.known p = s.cfg) : p = s.cfg.primary ∧ PrimaryAuthoritative s := by
  have e1 := hp.1; have e2 := hp.2
  rw [hk] at e1 e2
  subst e1; exact ⟨rfl, e2⟩

theorem stale_ne_prim {p : Node} (hv : (s.known p).version < s.cfg.version) : p ≠ s.cfg.primary := by
  intro e; subst e; rw [h.primKnows] at hv; omega

theorem knowsLatest_iff_prim {p : Node} (hp : ThinksPrimary s p) (hk : KnowsLatest s p) : p = s.cfg.primary :=
  (thinksPrimary_knowsLatest h hp hk).2.symm

theorem prim_holds_sync (hpa : PrimaryAuthoritative s) {m : Node} (hs : s.sync s.cfg.primary m = true) :
    (s.log s.cfg.primary).take (s.acked s.cfg.primary m) <+: s.log m := by
  by_cases hf : (s.known m).primary = s.cfg.primary
  · have hne : m ≠ s.cfg.primary := by
      intro e; rw [e, h.noSelfSync] at hs; exact Bool.false_ne_true hs
    exact h.ackHolds _ _ (thinksPrimary_prim h hpa) hne hf
  · rw [h.ackedPrim m hf]; simp

/-- The commit fact: if `p` may commit offset `c` by the commit rule, every
authoritative node holds the first `c+1` entries of `p`. -/
theorem commit_holds {p : Node} (hp : ThinksPrimary s p) (hlen : s.commit p < (s.log p).length)
    (hcap : ∀ r, s.sync p r = true → s.commit p < s.acked p r) :
    ∀ m, IsAuthoritative s m → (s.log p).take (s.commit p + 1) <+: s.log m := by
  intro m ⟨hm, hi⟩
  rcases thinksPrimary_cases h hp with ⟨rfl, hk⟩ | hv
  · have hpa : PrimaryAuthoritative s := (thinksPrimary_primaryAuthoritative hp hk).2
    rcases hm with he | rfl
    · have hs : s.sync s.cfg.primary m = true :=
        h.eligibleCounted _ _ hp (by rw [hk]; exact he) (by rw [hk]; exact hi)
      exact take_mono_prefix (hcap m hs) (prim_holds_sync h hpa hs)
    · exact List.take_prefix _ _
  · -- `p` is deposed. By the commit rule it commits below its fence, and the new
    -- configuration holds its log up to the fence.
    have hF := h.stale p hp hv
    obtain ⟨w, ⟨hw1, _⟩, hwF⟩ := hF.attained
    have hcw : s.commit p + 1 ≤ fence s p := hwF ▸ hcap w hw1
    rcases hm with he | rfl
    · rcases hF.eligHolds m he hi with ⟨hd, _⟩ | ⟨hs, hf⟩
      · exact take_mono_prefix hcw hd
      · by_cases hmp : m = p
        · subst hmp; exact List.take_prefix _ _
        · exact take_mono_prefix (hcap m hs) (h.ackHolds _ _ hp hmp hf)
    · exact take_mono_prefix hcw (hF.primHolds hi)

/-- The acknowledgement side of `commit_holds`: if `p` may commit offset `c` by the
commit rule, every other authoritative node has acknowledged the first `c+1` entries. -/
theorem commit_ackHigh {p : Node} (hp : ThinksPrimary s p)
    (hcap : ∀ r, s.sync p r = true → s.commit p < s.acked p r) :
    ∀ m, IsAuthoritative s m → m ≠ p → s.commit p + 1 ≤ s.ackHigh m := by
  intro m ⟨hm, hi⟩ hmp
  rcases thinksPrimary_cases h hp with ⟨rfl, hk⟩ | hv
  · -- `p` is the current primary: it counts `m`, and `m`'s acknowledgement is within
    -- `m`'s high-water mark (or is 0, which the commit rule rules out).
    rcases hm with he | rfl
    · have hs := h.eligibleCounted _ _ hp (by rw [hk]; exact he) (by rw [hk]; exact hi)
      by_cases hf : (s.known m).primary = s.cfg.primary
      · exact Nat.le_trans (hcap m hs) (h.ackedHigh _ m hp hmp hf)
      · have := hcap m hs; rw [h.ackedPrim m hf] at this; omega
    · exact absurd rfl hmp
  · have hF := h.stale p hp hv
    obtain ⟨w, ⟨hw1, _⟩, hwF⟩ := hF.attained
    have hcw : s.commit p + 1 ≤ fence s p := hwF ▸ hcap w hw1
    rcases hm with he | rfl
    · rcases hF.eligHolds m he hi with ⟨_, hd⟩ | ⟨hs, hf⟩
      · exact hcw.trans hd
      · exact Nat.le_trans (hcap m hs) (h.ackedHigh p m hp hmp hf)
    · exact hcw.trans (hF.primAck hi)

end


/-! ### CatchUpPoint facts -/

/-- CatchUpPoint is at least the committed offset. -/
theorem commit_le_catchUpPoint {s : State Node} (h : Invariant s) (p : Node) : s.commit p ≤ catchUpPoint s p := by
  have := h.commitWithinLog p
  unfold catchUpPoint; split_ifs with c
  · omega
  · exact Nat.le_refl _

/-- For the current primary, CatchUpPoint covers the reconciliation point. -/
theorem inheritedEnd_le_catchUpPoint {s : State Node} (h : Invariant s) : s.inheritedEnd s.cfg.primary ≤ catchUpPoint s s.cfg.primary := by
  have := h.inheritedEndWithinLog
  unfold catchUpPoint; split_ifs with c
  · omega
  · simp at c; exact c

theorem catchUpPoint_le_len {s : State Node} (h : Invariant s) (p : Node) : catchUpPoint s p ≤ (s.log p).length := by
  unfold catchUpPoint; split
  · exact Nat.min_le_right _ _
  · exact h.commitWithinLog p

end SyncReplication
