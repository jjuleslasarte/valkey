import SyncReplication.Model

/-!
# Action contracts

What each action of `Model.lean` changes and what it leaves alone (AppendWrite and
Replicate only extend one log, and are covered by `invariant_grow` instead), stated in the
design's terms: who thinks it is primary, who is authoritative, whose log, sync
replica set, acknowledgements and commit point move. The invariant proofs
(`Preserve/*.lean`) use these lemmas instead of unfolding the
actions, so each action's effect is written down, and can be checked against the
design doc, in one place.

None of these lemmas needs the invariant; they follow from the action's definition
alone. Hypotheses that come from the action's guard are named after it.
-/

namespace SyncReplication

variable {Node : Type} [DecidableEq Node] {s : State Node}

/-! ## Takeover(n)

An eligible replica `n` becomes primary in a new configuration. Logs do not move. `n`
starts a new primaryship: its sync replica set is the eligible replicas,
its acknowledgements and commit point are reset, and its catch-up point is the end of
its log, so it commits what it inherited before anything it appends afterwards, and
serves no linearizable read before that. Every other node keeps its state,
including the old primary, which is
not told. -/

section takeover
variable {n : Node}

theorem takeover_log : (takeover s n).log = s.log := rfl

theorem takeover_known (x : Node) :
    (takeover s n).known x = if x = n then takeoverCfg s n else s.known x := rfl

theorem takeover_known_other {x : Node} (hx : x ≠ n) : (takeover s n).known x = s.known x := by
  rw [takeover_known, if_neg hx]

theorem takeover_sync_self : (takeover s n).sync n = takeoverSync s n := by simp [takeover]

theorem takeover_sync_other {x : Node} (hx : x ≠ n) : (takeover s n).sync x = s.sync x := by
  simp [takeover, update, hx]

theorem takeover_acked_self : (takeover s n).acked n = fun _ => 0 := by simp [takeover]

theorem takeover_acked_other {x : Node} (hx : x ≠ n) : (takeover s n).acked x = s.acked x := by
  simp [takeover, update, hx]

theorem takeover_commit_self : (takeover s n).commit n = 0 := by simp [takeover]

theorem takeover_commit_other {x : Node} (hx : x ≠ n) : (takeover s n).commit x = s.commit x := by
  simp [takeover, update, hx]

/-- The new primary must commit its whole inherited log before it serves. -/
theorem takeover_inheritedEnd_self : (takeover s n).inheritedEnd n = (s.log n).length := by simp [takeover]

/-- The new primary counts exactly the eligible replicas of the new configuration. -/
theorem takeoverSync_iff (x : Node) :
    takeoverSync s n x = true ↔ takeoverEligible s n x = true := by
  simp [takeoverSync]

/-- The new primary does not count itself. -/
theorem takeoverSync_self : takeoverSync s n n = false := by
  simp [takeoverSync, takeoverEligible]

/-- The new eligible set: the old one without the old primary and without `n`. -/
theorem takeoverEligible_iff (x : Node) :
    takeoverEligible s n x = true ↔ s.cfg.eligible x = true ∧ x ≠ s.cfg.primary ∧ x ≠ n := by
  simp [takeoverEligible, and_assoc]

/-- After a takeover the new primary thinks it is primary, and every other node
thinks so exactly when it did before. In particular a deposed primary still does. -/
theorem takeover_thinksPrimary (hin : s.cfg.incarnation n = s.incarnation n) (x : Node) :
    ThinksPrimary (takeover s n) x ↔ x = n ∨ (x ≠ n ∧ ThinksPrimary s x) := by
  unfold ThinksPrimary; rw [takeover_known]
  by_cases e : x = n
  · subst e; simp only [takeoverCfg, true_or, iff_true]
    exact ⟨rfl, hin⟩
  · simp only [if_neg e]
    constructor
    · intro c; exact Or.inr ⟨e, c⟩
    · rintro (c | ⟨_, c⟩)
      · exact absurd c e
      · exact c

end takeover

/-! ## Learn(n)

`n` adopts the latest configuration. If it is not the primary there, it drops its
sync replica set. Nothing else changes. -/

section learn
variable {n : Node}

theorem learn_known (x : Node) : (learn s n).known x = if x = n then s.cfg else s.known x := rfl

theorem learn_sync_self (hnp : n ≠ s.cfg.primary) : (learn s n).sync n = fun _ => false := by
  simp [learn, update, Ne.symm hnp]

theorem learn_sync_other {x : Node} (hx : x ≠ n) : (learn s n).sync x = s.sync x := by
  simp [learn, update, hx]

/-- Learning a configuration never makes a node primary: a node that is not the
primary of the latest configuration learns that it is not. -/
theorem learn_thinksPrimary (hnp : n ≠ s.cfg.primary) {x : Node} (hx : ThinksPrimary (learn s n) x) :
    x ≠ n ∧ ThinksPrimary s x := by
  obtain ⟨hx1, hx2⟩ := hx
  rw [learn_known] at hx1 hx2
  by_cases e : x = n
  · rw [if_pos e] at hx1; exact absurd (hx1.trans e).symm hnp
  · rw [if_neg e] at hx1 hx2; exact ⟨e, hx1, hx2⟩

end learn

/-! ## MakeEligible(prim, r) and MakeIneligible(prim, r)

The current primary publishes a configuration with `r` added to or removed from the
eligible set (step 4 of promotion, step 2 of demotion). Only its own copy of the
configuration changes; MakeIneligible also stops counting `r`. Stated for the
current primary, which is the only node these steps can run on (`hkp`: it knows the
latest configuration). -/

section cas
variable {r : Node}

theorem makeEligible_known (x : Node) : (makeEligible s s.cfg.primary r).known x =
    if x = s.cfg.primary then makeEligibleCfg s r else s.known x := rfl

theorem makeEligible_known_prim (hkp : s.known s.cfg.primary = s.cfg) (x : Node) :
    ((makeEligible s s.cfg.primary r).known x).primary = (s.known x).primary := by
  rw [makeEligible_known]; split_ifs with e
  · subst e; rw [hkp]; rfl
  · rfl

theorem makeEligible_elig (x : Node) :
    (makeEligible s s.cfg.primary r).cfg.eligible x = if x = r then true else s.cfg.eligible x := rfl

/-- MakeEligible records `r`'s current incarnation. -/
theorem makeEligible_inc (x : Node) :
    (makeEligible s s.cfg.primary r).cfg.incarnation x = if x = r then s.incarnation r else s.cfg.incarnation x := rfl

theorem makeEligible_known_inc (hkp : s.known s.cfg.primary = s.cfg) (hrp : r ≠ s.cfg.primary) (x : Node) :
    ((makeEligible s s.cfg.primary r).known x).incarnation x = (s.known x).incarnation x := by
  rw [makeEligible_known]; split_ifs with e
  · subst e; rw [hkp]
    show update s.cfg.incarnation r (s.incarnation r) s.cfg.primary = s.cfg.incarnation s.cfg.primary
    exact update_of_ne _ _ (Ne.symm hrp)
  · rfl

/-- Promotion does not change who thinks it is primary. -/
theorem makeEligible_thinksPrimary (hkp : s.known s.cfg.primary = s.cfg) (hrp : r ≠ s.cfg.primary) (x : Node) :
    ThinksPrimary (makeEligible s s.cfg.primary r) x ↔ ThinksPrimary s x := by
  unfold ThinksPrimary; rw [makeEligible_known_prim hkp, makeEligible_known_inc hkp hrp]; rfl

/-- The only node promotion can make authoritative is `r`. -/
theorem makeEligible_isAuthoritative {x : Node} (hx : IsAuthoritative (makeEligible s s.cfg.primary r) x) :
    x = r ∨ IsAuthoritative s x := by
  obtain ⟨hn, hi⟩ := hx
  by_cases e : x = r
  · exact Or.inl e
  · right
    change (if x = r then true else s.cfg.eligible x) = true ∨ x = s.cfg.primary at hn
    change (if x = r then s.incarnation r else s.cfg.incarnation x) = s.incarnation x at hi
    rw [if_neg e] at hn hi; exact ⟨hn, hi⟩

theorem makeIneligible_known (x : Node) : (makeIneligible s s.cfg.primary r).known x =
    if x = s.cfg.primary then makeIneligibleCfg s r else s.known x := rfl

theorem makeIneligible_known_prim (hkp : s.known s.cfg.primary = s.cfg) (x : Node) :
    ((makeIneligible s s.cfg.primary r).known x).primary = (s.known x).primary := by
  rw [makeIneligible_known]; split_ifs with e
  · subst e; rw [hkp]; rfl
  · rfl

theorem makeIneligible_known_inc (hkp : s.known s.cfg.primary = s.cfg) (x : Node) :
    ((makeIneligible s s.cfg.primary r).known x).incarnation = (s.known x).incarnation := by
  rw [makeIneligible_known]; split_ifs with e
  · subst e; rw [hkp]; rfl
  · rfl

theorem makeIneligible_elig (x : Node) :
    (makeIneligible s s.cfg.primary r).cfg.eligible x = if x = r then false else s.cfg.eligible x := rfl

/-- Demotion stops the primary counting `r`, and changes no other sync replica set. -/
theorem makeIneligible_sync (x y : Node) : (makeIneligible s s.cfg.primary r).sync x y =
    if x = s.cfg.primary ∧ y = r then false else s.sync x y := by
  by_cases ex : x = s.cfg.primary
  · subst ex; by_cases ey : y = r
    · subst ey; simp [makeIneligible, update]
    · simp [makeIneligible, update, ey]
  · simp [makeIneligible, update, ex]

theorem makeIneligible_sync_le {x y : Node} (hxy : (makeIneligible s s.cfg.primary r).sync x y = true) :
    s.sync x y = true := by
  rw [makeIneligible_sync] at hxy; split at hxy
  · exact absurd hxy Bool.false_ne_true
  · exact hxy

/-- Demotion does not change who thinks it is primary. -/
theorem makeIneligible_thinksPrimary (hkp : s.known s.cfg.primary = s.cfg) (x : Node) :
    ThinksPrimary (makeIneligible s s.cfg.primary r) x ↔ ThinksPrimary s x := by
  unfold ThinksPrimary; rw [makeIneligible_known_prim hkp, makeIneligible_known_inc hkp]; rfl

theorem makeIneligible_elig_true {m : Node} (hm : (makeIneligible s s.cfg.primary r).cfg.eligible m = true) :
    m ≠ r ∧ s.cfg.eligible m = true := by
  rw [makeIneligible_elig] at hm; split_ifs at hm with e
  exact ⟨e, hm⟩

/-- Demotion makes no node authoritative. -/
theorem makeIneligible_isAuthoritative {x : Node} (hx : IsAuthoritative (makeIneligible s s.cfg.primary r) x) :
    IsAuthoritative s x := by
  obtain ⟨hn, hi⟩ := hx
  rcases hn with hn | hn
  · exact ⟨Or.inl (makeIneligible_elig_true hn).2, hi⟩
  · exact ⟨Or.inr hn, hi⟩

end cas

/-! ## Replication: Ack(r), Count(p, r), Commit(p)

Each changes one entry: `p`'s view of `r`'s acknowledged offset, `p`'s sync replica
set, or `p`'s commit point (and the committed history, the first time an offset
commits). -/

section repl

/-- Ack(r): only `r`'s primary's record of `r`'s acknowledgement moves, to the end of
`r`'s log. -/
theorem ack_acked (r q x : Node) : (ack s r).acked q x =
    if q = primaryOf s r ∧ x = r then (s.log r).length else s.acked q x := by
  by_cases hq : q = primaryOf s r
  · subst hq; by_cases hx : x = r
    · subst hx; simp [ack, update]
    · simp [ack, update, hx]
  · simp [ack, update, hq]

/-- Count(p, r): `p` adds `r` to its sync replica set (promotion step 2). -/
theorem count_sync (p r q x : Node) : (count s p r).sync q x = (s.sync q x || (q = p ∧ x = r)) := by
  by_cases hq : q = p
  · subst hq; by_cases hx : x = r
    · subst hx; simp [count, update]
    · simp [count, update, hx]
  · simp [count, update, hq]

/-- Uncount changes only `p`'s sync replica set, where `r` is no longer counted. -/
theorem uncount_sync (p r q x : Node) :
    (uncount s p r).sync q x = (s.sync q x && !(q = p ∧ x = r)) := by
  by_cases hq : q = p
  · subst hq; by_cases hx : x = r
    · subst hx; simp [uncount, update]
    · simp [uncount, update, hx]
  · simp [uncount, update, hq]

/-- The high-water mark only grows: Ack raises the replica's to its log length. -/
theorem ack_ackHigh_le (r x : Node) : s.ackHigh x ≤ (ack s r).ackHigh x := by
  show s.ackHigh x ≤ update s.ackHigh r (max (s.ackHigh r) (s.log r).length) x
  unfold update; split_ifs with e
  · subst e; exact Nat.le_max_left _ _
  · exact Nat.le_refl _

theorem ack_ackHigh_self (r : Node) : (s.log r).length ≤ (ack s r).ackHigh r := by
  show (s.log r).length ≤ update s.ackHigh r (max (s.ackHigh r) (s.log r).length) r
  rw [update_self]; exact Nat.le_max_right _ _

/-- Commit raises the primary's high-water mark to the new commit point. -/
theorem commitNext_ackHigh_le (p x : Node) : s.ackHigh x ≤ (commitNext s p).ackHigh x := by
  show s.ackHigh x ≤ update s.ackHigh p (max (s.ackHigh p) (s.commit p + 1)) x
  unfold update; split_ifs with e
  · subst e; exact Nat.le_max_left _ _
  · exact Nat.le_refl _

theorem commitNext_ackHigh_self (p : Node) : s.commit p + 1 ≤ (commitNext s p).ackHigh p := by
  show s.commit p + 1 ≤ update s.ackHigh p (max (s.ackHigh p) (s.commit p + 1)) p
  rw [update_self]; exact Nat.le_max_right _ _

/-- Commit(p): `p`'s committed offset advances by one. -/
theorem commitNext_commit (p x : Node) :
    (commitNext s p).commit x = if x = p then s.commit p + 1 else s.commit x := by
  by_cases hx : x = p
  · subst hx; simp [commitNext, update]
  · simp [commitNext, update, hx]

/-- Commit(p) at an offset no node has committed yet: the entry joins the committed
history. -/
theorem commitNext_hist_new {p : Node} (he : s.commit p = s.hist.length) :
    (commitNext s p).hist = s.hist ++ [(s.log p).getD (s.commit p) 0] := by
  simp [commitNext, he]

/-- Commit(p) at an offset already committed elsewhere: the history does not change. -/
theorem commitNext_hist_old {p : Node} (he : ¬ s.commit p = s.hist.length) :
    (commitNext s p).hist = s.hist := by
  simp [commitNext, he]

end repl

/-! ## Resync(r)

A diverged, uncounted, ineligible replica `r` replaces its log by a prefix of its
primary's log, up to the primary's catch-up point, its acknowledgement is reset, and its commit
point is capped at its primary's. Nothing else changes. -/

section resync
variable {r : Node}

theorem resync_log_self :
    (resync s r).log r = (s.log (primaryOf s r)).take (catchUpPoint s (primaryOf s r)) := by
  simp [resync]

theorem resync_log_other {x : Node} (hx : x ≠ r) : (resync s r).log x = s.log x := by
  simp [resync, update, hx]

theorem resync_commit_self :
    (resync s r).commit r = min (s.commit r) (s.commit (primaryOf s r)) := by simp [resync]

theorem resync_commit_other {x : Node} (hx : x ≠ r) : (resync s r).commit x = s.commit x := by
  simp [resync, update, hx]

theorem resync_acked (q x : Node) :
    (resync s r).acked q x = if q = primaryOf s r ∧ x = r then 0 else s.acked q x := by
  by_cases hq : q = primaryOf s r
  · subst hq; by_cases hx : x = r
    · subst hx; simp [resync, update]
    · simp [resync, update, hx]
  · simp [resync, update, hq]

theorem resync_acked_le (q x : Node) : (resync s r).acked q x ≤ s.acked q x := by
  rw [resync_acked]; split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

/-- Acknowledgements the primary counts are untouched, because `r` is not counted. -/
theorem resync_acked_sync (hsy : s.sync (primaryOf s r) r = false) {q x : Node}
    (hs : s.sync q x = true) : (resync s r).acked q x = s.acked q x := by
  rw [resync_acked]; split_ifs with c
  · obtain ⟨rfl, rfl⟩ := c; rw [hsy] at hs; exact absurd hs (by decide)
  · rfl

end resync

/-! ## RestartEmpty(n)

`n` loses its log and its volatile state, and gets a new incarnation, so the
configuration's record of it no longer matches: it stops being authoritative and
stops thinking it is primary. The current primary stops counting `n` and forgets its
acknowledgement. Every other node is unchanged. -/

section restartEmpty
variable {n : Node}

theorem restartEmpty_inc (x : Node) :
    (restartEmpty s n).incarnation x = if x = n then s.incarnation n + 1 else s.incarnation x := by
  by_cases e : x = n
  · subst e; simp [restartEmpty]
  · simp [restartEmpty, update, e]

theorem restartEmpty_inc_other {x : Node} (e : x ≠ n) : (restartEmpty s n).incarnation x = s.incarnation x := by
  rw [restartEmpty_inc, if_neg e]

theorem restartEmpty_inc_self : (restartEmpty s n).incarnation n = s.incarnation n + 1 := by
  rw [restartEmpty_inc, if_pos rfl]

theorem restartEmpty_log_other {x : Node} (e : x ≠ n) : (restartEmpty s n).log x = s.log x := by
  simp [restartEmpty, update, e]

/-- `n`'s high-water mark is lost with its data. -/
theorem restartEmpty_ackHigh (x : Node) :
    (restartEmpty s n).ackHigh x = if x = n then 0 else s.ackHigh x := by
  show update s.ackHigh n 0 x = _; rfl

theorem restartEmpty_ackHigh_other {x : Node} (e : x ≠ n) :
    (restartEmpty s n).ackHigh x = s.ackHigh x := by rw [restartEmpty_ackHigh, if_neg e]

theorem restartEmpty_commit_other {x : Node} (e : x ≠ n) :
    (restartEmpty s n).commit x = s.commit x := by simp [restartEmpty, update, e]

theorem restartEmpty_commit_self : (restartEmpty s n).commit n = 0 := by simp [restartEmpty]

theorem restartEmpty_inheritedEnd_other {x : Node} (e : x ≠ n) :
    (restartEmpty s n).inheritedEnd x = s.inheritedEnd x := by simp [restartEmpty, update, e]

theorem restartEmpty_inheritedEnd_self : (restartEmpty s n).inheritedEnd n = 0 := by simp [restartEmpty]

theorem restartEmpty_sync (p r : Node) : (restartEmpty s n).sync p r =
    if p = n then false else if p = s.cfg.primary ∧ r = n then false else s.sync p r := by
  by_cases e : p = n
  · simp [restartEmpty, e]
  · by_cases ep : p = s.cfg.primary
    · subst ep
      by_cases er : r = n
      · simp [restartEmpty, e, er]
      · simp [restartEmpty, e, er, update]
    · simp [restartEmpty, e, ep]

theorem restartEmpty_acked (p r : Node) : (restartEmpty s n).acked p r =
    if p = n then 0 else if p = s.cfg.primary ∧ r = n then 0 else s.acked p r := by
  by_cases e : p = n
  · simp [restartEmpty, e]
  · by_cases ep : p = s.cfg.primary
    · subst ep
      by_cases er : r = n
      · simp [restartEmpty, e, er]
      · simp [restartEmpty, e, er, update]
    · simp [restartEmpty, e, ep]

theorem restartEmpty_acked_le (p r : Node) : (restartEmpty s n).acked p r ≤ s.acked p r := by
  rw [restartEmpty_acked]; split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · exact Nat.le_refl _

theorem restartEmpty_sync_le {p r : Node} (hs : (restartEmpty s n).sync p r = true) :
    s.sync p r = true := by
  rw [restartEmpty_sync] at hs; split at hs
  · exact absurd hs (by decide)
  · split at hs
    · exact absurd hs (by decide)
    · exact hs

/-- A node that restarted empty does not think it is primary any more: its own
configuration records its old incarnation. (`hinc`: recorded incarnations never run
ahead of the real ones; `hkn`: `n` knew the latest configuration.) -/
theorem restartEmpty_thinksPrimary (hkn : s.known n = s.cfg) (hinc : s.cfg.incarnation n ≤ s.incarnation n)
    {x : Node} (hx : ThinksPrimary (restartEmpty s n) x) : x ≠ n ∧ ThinksPrimary s x := by
  obtain ⟨h1, h2⟩ := hx
  have hxn : x ≠ n := by
    intro e; subst e
    change (s.known x).incarnation x = (restartEmpty s x).incarnation x at h2
    rw [hkn, restartEmpty_inc_self] at h2; omega
  refine ⟨hxn, h1, ?_⟩
  change (s.known x).incarnation x = (restartEmpty s n).incarnation x at h2
  rw [restartEmpty_inc_other hxn] at h2; exact h2

/-- A node that restarted empty is not authoritative, and no node becomes so. -/
theorem restartEmpty_isAuthoritative (hinc : s.cfg.incarnation n ≤ s.incarnation n) {x : Node}
    (hx : IsAuthoritative (restartEmpty s n) x) : x ≠ n ∧ IsAuthoritative s x := by
  obtain ⟨h1, h2⟩ := hx
  have hxn : x ≠ n := by
    intro e; subst e
    change s.cfg.incarnation x = (restartEmpty s x).incarnation x at h2
    rw [restartEmpty_inc_self] at h2; omega
  refine ⟨hxn, h1, ?_⟩
  change s.cfg.incarnation x = (restartEmpty s n).incarnation x at h2
  rw [restartEmpty_inc_other hxn] at h2; exact h2

theorem restartEmpty_primaryAuthoritative (hinc : s.cfg.incarnation n ≤ s.incarnation n)
    (hp : PrimaryAuthoritative (restartEmpty s n)) : s.cfg.primary ≠ n ∧ PrimaryAuthoritative s := by
  have := restartEmpty_isAuthoritative hinc (x := s.cfg.primary) ⟨Or.inr rfl, hp⟩
  exact ⟨this.1, this.2.2⟩

end restartEmpty

/-! ## RestartKeep(n)

`n` keeps its log and incarnation and loses its volatile state: commit point and
acknowledgements reset, and it must re-commit its whole log before serving. If it is
primary, its sync replica set is rebuilt from the configuration. Who thinks it
is primary does not change. -/

section restartKeep
variable {n : Node}

theorem restartKeep_commit_other {x : Node} (e : x ≠ n) :
    (restartKeep s n).commit x = s.commit x := by simp [restartKeep, update, e]

theorem restartKeep_commit_self : (restartKeep s n).commit n = 0 := by simp [restartKeep]

theorem restartKeep_inheritedEnd_other {x : Node} (e : x ≠ n) :
    (restartKeep s n).inheritedEnd x = s.inheritedEnd x := by simp [restartKeep, update, e]

theorem restartKeep_inheritedEnd_self : (restartKeep s n).inheritedEnd n = (s.log n).length := by
  simp [restartKeep]

theorem restartKeep_acked_other {x : Node} (e : x ≠ n) :
    (restartKeep s n).acked x = s.acked x := by simp [restartKeep, update, e]

theorem restartKeep_acked_self : (restartKeep s n).acked n = fun _ => 0 := by
  simp [restartKeep]

theorem restartKeep_sync_other {x : Node} (e : x ≠ n) :
    (restartKeep s n).sync x = s.sync x := by simp [restartKeep, update, e]

/-- A restarted primary's sync replica set is rebuilt from the configuration. -/
theorem restartKeep_sync_self : (restartKeep s n).sync n =
    if (s.known n).primary = n ∧ (s.known n).incarnation n = s.incarnation n then rebuiltSync s n
    else fun _ => false := by
  simp [restartKeep]

theorem restartKeep_thinksPrimary (x : Node) :
    ThinksPrimary (restartKeep s n) x ↔ ThinksPrimary s x := Iff.rfl

end restartKeep

/-! ## RestartPartial(n, k)

`n` restarts from a persistence file holding only the first `k` entries of its log.
Keeping its incarnation (`restartPartialKeep`), it is RestartKeep on the truncated log;
taking a new one (`restartPartialFresh`), it is RestartEmpty with those `k` entries as
its log. Every field but `log` (and, when keeping, `inheritedEnd`) is the corresponding
restart's, so these facts are the restart's facts restated. -/

section restartPartialKeep
variable {n : Node} {k : Nat}

theorem restartPartialKeep_log (x : Node) :
    (restartPartialKeep s n k).log x = if x = n then (s.log n).take k else s.log x := by
  show update s.log n ((s.log n).take k) x = _; rfl

theorem restartPartialKeep_log_other {x : Node} (e : x ≠ n) :
    (restartPartialKeep s n k).log x = s.log x := by rw [restartPartialKeep_log, if_neg e]

theorem restartPartialKeep_log_self : (restartPartialKeep s n k).log n = (s.log n).take k := by
  rw [restartPartialKeep_log, if_pos rfl]

theorem restartPartialKeep_commit_other {x : Node} (e : x ≠ n) :
    (restartPartialKeep s n k).commit x = s.commit x := restartKeep_commit_other e

theorem restartPartialKeep_commit_self : (restartPartialKeep s n k).commit n = 0 :=
  restartKeep_commit_self

theorem restartPartialKeep_inheritedEnd_other {x : Node} (e : x ≠ n) :
    (restartPartialKeep s n k).inheritedEnd x = s.inheritedEnd x := by
  show update s.inheritedEnd n k x = _; rw [update_of_ne _ _ e]

theorem restartPartialKeep_inheritedEnd_self : (restartPartialKeep s n k).inheritedEnd n = k := by
  show update s.inheritedEnd n k n = _; rw [update_self]

theorem restartPartialKeep_acked_other {x : Node} (e : x ≠ n) :
    (restartPartialKeep s n k).acked x = s.acked x := restartKeep_acked_other e

theorem restartPartialKeep_acked_self : (restartPartialKeep s n k).acked n = fun _ => 0 :=
  restartKeep_acked_self

theorem restartPartialKeep_sync_other {x : Node} (e : x ≠ n) :
    (restartPartialKeep s n k).sync x = s.sync x := restartKeep_sync_other e

theorem restartPartialKeep_sync_self : (restartPartialKeep s n k).sync n =
    if (s.known n).primary = n ∧ (s.known n).incarnation n = s.incarnation n then rebuiltSync s n
    else fun _ => false := restartKeep_sync_self

theorem restartPartialKeep_thinksPrimary (x : Node) :
    ThinksPrimary (restartPartialKeep s n k) x ↔ ThinksPrimary s x := Iff.rfl

end restartPartialKeep

section restartPartialFresh
variable {n : Node} {k : Nat}

theorem restartPartialFresh_log (x : Node) :
    (restartPartialFresh s n k).log x = if x = n then (s.log n).take k else s.log x := by
  show update s.log n ((s.log n).take k) x = _; rfl

theorem restartPartialFresh_log_other {x : Node} (e : x ≠ n) :
    (restartPartialFresh s n k).log x = s.log x := by rw [restartPartialFresh_log, if_neg e]

theorem restartPartialFresh_inc (x : Node) :
    (restartPartialFresh s n k).incarnation x = if x = n then s.incarnation n + 1 else s.incarnation x := restartEmpty_inc x

theorem restartPartialFresh_inc_other {x : Node} (e : x ≠ n) :
    (restartPartialFresh s n k).incarnation x = s.incarnation x := restartEmpty_inc_other e

theorem restartPartialFresh_inc_self : (restartPartialFresh s n k).incarnation n = s.incarnation n + 1 :=
  restartEmpty_inc_self

theorem restartPartialFresh_commit_other {x : Node} (e : x ≠ n) :
    (restartPartialFresh s n k).commit x = s.commit x := restartEmpty_commit_other e

theorem restartPartialFresh_commit_self : (restartPartialFresh s n k).commit n = 0 :=
  restartEmpty_commit_self

theorem restartPartialFresh_inheritedEnd_other {x : Node} (e : x ≠ n) :
    (restartPartialFresh s n k).inheritedEnd x = s.inheritedEnd x := restartEmpty_inheritedEnd_other e

theorem restartPartialFresh_inheritedEnd_self : (restartPartialFresh s n k).inheritedEnd n = 0 :=
  restartEmpty_inheritedEnd_self

theorem restartPartialFresh_sync (p r : Node) : (restartPartialFresh s n k).sync p r =
    if p = n then false else if p = s.cfg.primary ∧ r = n then false else s.sync p r :=
  restartEmpty_sync p r

theorem restartPartialFresh_acked (p r : Node) : (restartPartialFresh s n k).acked p r =
    if p = n then 0 else if p = s.cfg.primary ∧ r = n then 0 else s.acked p r :=
  restartEmpty_acked p r

theorem restartPartialFresh_acked_le (p r : Node) :
    (restartPartialFresh s n k).acked p r ≤ s.acked p r := restartEmpty_acked_le p r

theorem restartPartialFresh_sync_le {p r : Node} (hs : (restartPartialFresh s n k).sync p r = true) :
    s.sync p r = true := restartEmpty_sync_le hs

theorem restartPartialFresh_ackHigh (x : Node) :
    (restartPartialFresh s n k).ackHigh x = if x = n then 0 else s.ackHigh x := restartEmpty_ackHigh x

theorem restartPartialFresh_ackHigh_other {x : Node} (e : x ≠ n) :
    (restartPartialFresh s n k).ackHigh x = s.ackHigh x := restartEmpty_ackHigh_other e

theorem restartPartialFresh_thinksPrimary (hkn : s.known n = s.cfg) (hinc : s.cfg.incarnation n ≤ s.incarnation n)
    {x : Node} (hx : ThinksPrimary (restartPartialFresh s n k) x) : x ≠ n ∧ ThinksPrimary s x :=
  restartEmpty_thinksPrimary hkn hinc hx

theorem restartPartialFresh_isAuthoritative (hinc : s.cfg.incarnation n ≤ s.incarnation n) {x : Node}
    (hx : IsAuthoritative (restartPartialFresh s n k) x) : x ≠ n ∧ IsAuthoritative s x :=
  restartEmpty_isAuthoritative hinc hx

theorem restartPartialFresh_primaryAuthoritative (hinc : s.cfg.incarnation n ≤ s.incarnation n)
    (hp : PrimaryAuthoritative (restartPartialFresh s n k)) : s.cfg.primary ≠ n ∧ PrimaryAuthoritative s :=
  restartEmpty_primaryAuthoritative hinc hp

end restartPartialFresh

end SyncReplication
