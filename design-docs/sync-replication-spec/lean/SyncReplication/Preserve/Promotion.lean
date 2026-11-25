import SyncReplication.Preserve.Delayed

/-!
# Two-step promotion refines atomic promotion

In the model, MakeEligible is a proposal (`proposeEligible`): the latest configuration
makes the candidate eligible, and the primary's own configuration changes only when it
learns the outcome (Learn). Until then `proposing p = some c`, and `p` keeps counting
`c`: it does not drop `c` from its sync replica set, and its primary lease needs `c`.

The invariants are proved for `StepA`, where the primary learns the outcome at once
(`makeEligible`). This file relates the two. `PromSim s L` says that `simState s L`, the
state `s` with each node's configuration replaced by `L` and no proposal in flight, is
what `s` looks like to the atomic model: a node with a proposal in flight is seen as
having learned it (`promoteL`), every other node as it is. Every step of `Step` from
`s` is a step of `StepA` from `simState s L`, or leaves it unchanged (Learn of an
outcome the atomic model already knows), so the atomic invariants carry over.
-/

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-- The configuration `c` after the promotion of `r`, recording incarnation `i`. -/
def promoteL (c : Cfg Node) (r : Node) (i : Nat) : Cfg Node :=
  { c with epoch := c.epoch + 1, eligible := update c.eligible r true,
           incarnation := update c.incarnation r i }

/-- `s` as the atomic model sees it: configurations `L`, no proposal in flight. -/
def simState (s : State Node) (L : Node → Cfg Node) : State Node :=
  { s with localCfg := L, proposing := fun _ => none }

/-- `L` is the atomic model's view of `s`'s configurations. A node with no proposal in
flight keeps its own; a node with a proposal in flight for `c` sees it committed. The
other fields are what a proposal in flight implies, and what keeps the atomic model
able to take the same steps: the proposer still thinks it is primary and still counts
`c`, unless `c` has since restarted with a new incarnation; and then `c` is not
authoritative while it follows the proposer. -/
structure PromSim (s : State Node) (L : Node → Cfg Node) : Prop where
  same    : ∀ n, s.proposing n = none → L n = s.localCfg n
  pend    : ∀ n c, s.proposing n = some c → ∃ i, L n = promoteL (s.localCfg n) c i
  thinks  : ∀ n c, s.proposing n = some c → ThinksPrimary s n
  ne      : ∀ n c, s.proposing n = some c → c ≠ n
  notElig : ∀ n c, s.proposing n = some c → (s.localCfg n).eligible c = false
  counted : ∀ n c, s.proposing n = some c → s.sync n c = true ∨ (L n).incarnation c < s.incarnation c
  stale   : ∀ n c, s.proposing n = some c →
    s.sync n c = true ∨ ¬ IsAuthoritative s c ∨ (s.localCfg c).primary ≠ n

theorem promSim_init (i : Node) : PromSim (init i) (init i).localCfg where
  same := fun _ _ => rfl
  pend := fun _ _ h => by simp [init] at h
  thinks := fun _ _ h => by simp [init] at h
  ne := fun _ _ h => by simp [init] at h
  notElig := fun _ _ h => by simp [init] at h
  counted := fun _ _ h => by simp [init] at h
  stale := fun _ _ h => by simp [init] at h

theorem simState_init (i : Node) : simState (init i) (init i).localCfg = init i := rfl

section basic
variable {s : State Node} {L : Node → Cfg Node} (hP : PromSim s L)
include hP

theorem PromSim.primary (n : Node) : (L n).primary = (s.localCfg n).primary := by
  cases hn : s.proposing n with
  | none => rw [hP.same n hn]
  | some c => obtain ⟨i, e⟩ := hP.pend n c hn; rw [e]; rfl

theorem PromSim.primaryOf_eq (n : Node) : primaryOf (simState s L) n = primaryOf s n :=
  hP.primary n

theorem PromSim.incSelf (n : Node) : (L n).incarnation n = (s.localCfg n).incarnation n := by
  cases hn : s.proposing n with
  | none => rw [hP.same n hn]
  | some c =>
    obtain ⟨i, e⟩ := hP.pend n c hn; rw [e]
    exact update_of_ne _ _ (Ne.symm (hP.ne n c hn))

theorem PromSim.thinksPrimary (n : Node) : ThinksPrimary (simState s L) n ↔ ThinksPrimary s n := by
  unfold ThinksPrimary; rw [show (simState s L).localCfg n = L n from rfl, hP.primary, hP.incSelf]; rfl

/-- A node with a proposal in flight does not know the latest configuration. -/
theorem PromSim.notKnows (hi : Invariant (simState s L)) {n c : Node} (hn : s.proposing n = some c) :
    ¬ KnowsLatest s n := by
  intro hk
  obtain ⟨i, e⟩ := hP.pend n c hn
  have := hi.localCfgLe n
  change (L n).epoch ≤ s.cfg.epoch at this
  rw [e] at this; unfold KnowsLatest at hk; change (s.localCfg n).epoch + 1 ≤ _ at this; omega

theorem PromSim.none_of_knows (hi : Invariant (simState s L)) {n : Node} (hk : KnowsLatest s n) :
    s.proposing n = none := by
  cases hn : s.proposing n with
  | none => rfl
  | some c => exact absurd hk (hP.notKnows hi hn)

theorem PromSim.localCfg_of_knows (hi : Invariant (simState s L)) {n : Node} (hk : KnowsLatest s n) :
    L n = s.localCfg n := hP.same n (hP.none_of_knows hi hk)

theorem PromSim.knows (hi : Invariant (simState s L)) {n : Node} (hk : KnowsLatest s n) :
    KnowsLatest (simState s L) n := by
  unfold KnowsLatest; rw [show (simState s L).localCfg n = L n from rfl, hP.localCfg_of_knows hi hk]; exact hk

/-- What `n` lists as eligible, the atomic model lists too. -/
theorem PromSim.elig {n x : Node} (hx : (s.localCfg n).eligible x = true) : (L n).eligible x = true := by
  cases hn : s.proposing n with
  | none => rw [hP.same n hn]; exact hx
  | some c =>
    obtain ⟨i, e⟩ := hP.pend n c hn; rw [e]
    show update (s.localCfg n).eligible c true x = true
    unfold update; split_ifs <;> simp_all

/-- What the atomic model lists as eligible for `n`, `n` lists, or it is `n`'s candidate. -/
theorem PromSim.eligL {n x : Node} (hx : (L n).eligible x = true) :
    (s.localCfg n).eligible x = true ∨ s.proposing n = some x := by
  cases hn : s.proposing n with
  | none => rw [hP.same n hn] at hx; exact Or.inl hx
  | some c =>
    obtain ⟨i, e⟩ := hP.pend n c hn; rw [e] at hx
    change update (s.localCfg n).eligible c true x = true at hx
    by_cases hxc : x = c
    · subst hxc; exact Or.inr rfl
    · rw [update_of_ne _ _ hxc] at hx; exact Or.inl hx

/-- ... with the same recorded incarnation. -/
theorem PromSim.inc {n x : Node} (hx : (s.localCfg n).eligible x = true) :
    (L n).incarnation x = (s.localCfg n).incarnation x := by
  cases hn : s.proposing n with
  | none => rw [hP.same n hn]
  | some c =>
    obtain ⟨i, e⟩ := hP.pend n c hn; rw [e]
    have hxc : x ≠ c := fun h => by subst h; rw [hP.notElig n x hn] at hx; exact absurd hx (by decide)
    exact update_of_ne _ _ hxc

/-- A replica `n` does not list as eligible stays unlisted in the atomic model, unless it
is `n`'s candidate. -/
theorem PromSim.notElig' {n x : Node} (hx : (s.localCfg n).eligible x = false) (hc : s.proposing n ≠ some x) :
    (L n).eligible x = false := by
  cases hn : s.proposing n with
  | none => rw [hP.same n hn]; exact hx
  | some c =>
    obtain ⟨i, e⟩ := hP.pend n c hn; rw [e]
    have hxc : x ≠ c := fun h => by subst h; exact hc hn
    show update (s.localCfg n).eligible c true x = false
    rw [update_of_ne _ _ hxc]; exact hx

theorem PromSim.writable {m : Nat} {p : Node} (hw : Writable m s p) : Writable m (simState s L) p := by
  unfold Writable at hw ⊢
  refine le_trans hw (Set.encard_le_encard ?_)
  intro x ⟨h1, h2, h3⟩
  exact ⟨h1, hP.elig h2, by rw [show (simState s L).localCfg p = L p from rfl, hP.inc h2]; exact h3⟩

end basic

/-! ## Frame and commutation lemmas -/

theorem PromSim.frame {s s' : State Node} {L : Node → Cfg Node} (hP : PromSim s L)
    (hprop : s'.proposing = s.proposing) (hlc : s'.localCfg = s.localCfg) (hinc : s'.incarnation = s.incarnation)
    (hcfg : s'.cfg = s.cfg) (hsync : ∀ n c, s.proposing n = some c → s.sync n c = true → s'.sync n c = true) :
    PromSim s' L where
  same n h := by rw [hlc]; exact hP.same n (hprop ▸ h)
  pend n c h := by rw [hlc]; exact hP.pend n c (hprop ▸ h)
  thinks n c h := by
    have := hP.thinks n c (hprop ▸ h); unfold ThinksPrimary at this ⊢; rw [hlc, hinc]; exact this
  ne n c h := hP.ne n c (hprop ▸ h)
  notElig n c h := by rw [hlc]; exact hP.notElig n c (hprop ▸ h)
  counted n c h := by
    rcases hP.counted n c (hprop ▸ h) with e | e
    · exact Or.inl (hsync n c (hprop ▸ h) e)
    · right; rw [hinc]; exact e
  stale n c h := by
    rcases hP.stale n c (hprop ▸ h) with e | e | e
    · exact Or.inl (hsync n c (hprop ▸ h) e)
    · right; left; unfold IsAuthoritative at e ⊢; rw [hcfg, hinc]; exact e
    · right; right; rw [hlc]; exact e

theorem update_none_const (n : Node) : update (fun _ : Node => (none : Option Node)) n none = fun _ => none := by
  funext x; unfold update; split <;> rfl

/-- A restart with a new incarnation of a node with no proposal in flight (RestartEmpty,
RestartPartial with a new incarnation). -/
theorem PromSim.restartFresh {s s' : State Node} {L : Node → Cfg Node} (hP : PromSim s L)
    (hi : Invariant (simState s L)) {n : Node} (hn : s.proposing n = none)
    (hprop : s'.proposing = s.proposing) (hlc : s'.localCfg = s.localCfg) (hcfg : s'.cfg = s.cfg)
    (hinc : s'.incarnation = update s.incarnation n (s.incarnation n + 1))
    (hsync : s'.sync = (restartEmpty s n).sync) : PromSim s' L := by
  have hne : ∀ x c, s.proposing x = some c → x ≠ n := fun x c hx e => by subst e; rw [hn] at hx; exact absurd hx (by simp)
  have hincle : ∀ x c, (L x).incarnation c ≤ s.incarnation c := fun x c => hi.localCfgIncLe x c
  have hcfgle : s.cfg.incarnation n ≤ s.incarnation n := hi.toConfigInvariant.incLe n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; rw [hlc]; exact hP.same x (hprop ▸ hx)
  · intro x c hx; rw [hlc]; exact hP.pend x c (hprop ▸ hx)
  · intro x c hx
    have hx' : s.proposing x = some c := hprop ▸ hx
    have := hP.thinks x c hx'; unfold ThinksPrimary at this ⊢
    rw [hlc, hinc, update_of_ne _ _ (hne x c hx')]; exact this
  · intro x c hx; exact hP.ne x c (hprop ▸ hx)
  · intro x c hx; rw [hlc]; exact hP.notElig x c (hprop ▸ hx)
  · intro x c hx
    have hx' : s.proposing x = some c := hprop ▸ hx
    rw [hsync, hinc]
    by_cases hcn : c = n
    · subst hcn; right; rw [update_self]; exact Nat.lt_succ_of_le (hincle x c)
    · rw [update_of_ne _ _ hcn]
      rcases hP.counted x c hx' with h1 | h1
      · left; show (if x = n then _ else if x = s.cfg.primary then update (s.sync x) n false else s.sync x) c = true
        rw [if_neg (hne x c hx')]; split_ifs
        · rw [update_of_ne _ _ hcn]; exact h1
        · exact h1
      · exact Or.inr h1
  · intro x c hx
    have hx' : s.proposing x = some c := hprop ▸ hx
    unfold IsAuthoritative; rw [hsync, hinc, hcfg, hlc]
    by_cases hcn : c = n
    · subst hcn; right; left; intro ⟨_, hb⟩; rw [update_self] at hb; omega
    · rw [update_of_ne _ _ hcn]
      rcases hP.stale x c hx' with h1 | h1 | h1
      · left
        show (if x = n then _ else if x = s.cfg.primary then update (s.sync x) n false else s.sync x) c = true
        rw [if_neg (hne x c hx')]; split_ifs
        · rw [update_of_ne _ _ hcn]; exact h1
        · exact h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)

/-! ## Every step of `Step` is a step of `StepA`, or none -/

theorem PromSim.step {m : Nat} {s s' : State Node} {μ : Action Node} {L : Node → Cfg Node}
    (hP : PromSim s L) (hi : Invariant (simState s L)) (hs : Step m s μ s') :
    ∃ L', PromSim s' L' ∧ (StepA m (simState s L) μ (simState s' L') ∨
      (simState s' L' = simState s L ∧ ∃ n, μ = .learn n)) := by
  have htp := hP.thinksPrimary
  have hsame : ∀ {s' : State Node}, PromSim s' L → simState s' L = simState s' L := fun _ => rfl
  cases hs with
  | append p hp hw =>
    refine ⟨L, hP.frame rfl rfl rfl rfl (fun _ _ _ h => h), Or.inl ?_⟩
    exact StepA.append _ p ((htp p).2 hp) (hP.writable hw)
  | commit p hp hw hlen hcap =>
    refine ⟨L, hP.frame rfl rfl rfl rfl (fun _ _ _ h => h), Or.inl ?_⟩
    exact StepA.commit _ p ((htp p).2 hp) (hP.writable hw) hlen hcap
  | addToSyncSet p r hp hrp hf hns hle =>
    refine ⟨L, hP.frame rfl rfl rfl rfl (fun n c _ h => ?_), Or.inl ?_⟩
    · show update s.sync p (update (s.sync p) r true) n c = true
      unfold update; split_ifs <;> simp_all
    · exact StepA.addToSyncSet _ p r ((htp p).2 hp) hrp (by rw [hP.primaryOf_eq]; exact hf) hns hle
  | removeFromSyncSet p r hp hsy hel hnp =>
    refine ⟨L, hP.frame rfl rfl rfl rfl (fun n c hn h => ?_), Or.inl ?_⟩
    · show update s.sync p (update (s.sync p) r false) n c = true
      by_cases hnp' : n = p
      · subst hnp'
        have hrc : c ≠ r := fun e => by subst e; exact hnp hn
        rw [update_self, update_of_ne _ _ hrc]; exact h
      · rw [update_of_ne _ _ hnp']; exact h
    · exact StepA.removeFromSyncSet _ p r ((htp p).2 hp) hsy (hP.notElig' hel hnp)
  | makeEligible p r hp hkl hsy hel =>
    have hpn := hP.none_of_knows hi hkl
    have hLp := hP.localCfg_of_knows hi hkl
    have hkp : s.localCfg p = s.cfg := by
      have := hi.localCfgEq p (hP.knows hi hkl); rw [show (simState s L).localCfg p = L p from rfl, hLp] at this
      exact this
    have hpprim : s.cfg.primary = p := by have := hp.1; rw [hkp] at this; exact this
    have hrp : r ≠ p := fun e => by subst e; have := hi.noSelfSync r; rw [show (simState s L).sync = s.sync from rfl, hsy] at this; exact absurd this (by decide)
    refine ⟨update L p (makeEligibleCfg s r), ?_, Or.inl ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro n hn
        by_cases e : n = p
        · subst e; simp [proposeEligible] at hn
        · rw [update_of_ne _ _ e]; exact hP.same n (by simpa [proposeEligible, update, e] using hn)
      · intro n c hn
        by_cases e : n = p
        · subst e
          have hc : c = r := by simpa [proposeEligible] using hn.symm
          subst hc
          exact ⟨s.incarnation c, by rw [update_self]; show makeEligibleCfg s c = promoteL (s.localCfg n) c _; rw [hkp]; rfl⟩
        · rw [update_of_ne _ _ e]; exact hP.pend n c (by simpa [proposeEligible, update, e] using hn)
      · intro n c hn
        by_cases e : n = p
        · subst e; exact hp
        · exact hP.thinks n c (by simpa [proposeEligible, update, e] using hn)
      · intro n c hn
        by_cases e : n = p
        · subst e; have hc : c = r := by simpa [proposeEligible] using hn.symm
          subst hc; exact hrp
        · exact hP.ne n c (by simpa [proposeEligible, update, e] using hn)
      · intro n c hn
        by_cases e : n = p
        · subst e; have hc : c = r := by simpa [proposeEligible] using hn.symm
          subst hc; show (s.localCfg n).eligible c = false; rw [hkp]; exact hel
        · exact hP.notElig n c (by simpa [proposeEligible, update, e] using hn)
      · intro n c hn
        by_cases e : n = p
        · subst e; have hc : c = r := by simpa [proposeEligible] using hn.symm
          subst hc; exact Or.inl hsy
        · rw [update_of_ne _ _ e]; exact hP.counted n c (by simpa [proposeEligible, update, e] using hn)
      · intro n c hn
        by_cases e : n = p
        · subst e; have hc : c = r := by simpa [proposeEligible] using hn.symm
          subst hc; exact Or.inl hsy
        · have hn' : s.proposing n = some c := by simpa [proposeEligible, update, e] using hn
          rcases hP.stale n c hn' with h1 | h1 | h1
          · exact Or.inl h1
          · by_cases hcr : c = r
            · subst hcr
              right; right
              have := (hi.syncNew c (by rw [show (simState s L).cfg = s.cfg from rfl, hpprim]; exact hsy) hel).1
              change (L c).primary = s.cfg.primary at this
              rw [hP.primary, hpprim] at this
              show (s.localCfg c).primary ≠ n; rw [this]; exact Ne.symm e
            · right; left
              intro ⟨ha, hb⟩; apply h1
              change (update s.cfg.eligible r true c = true ∨ c = s.cfg.primary) at ha
              change update s.cfg.incarnation r (s.incarnation r) c = s.incarnation c at hb
              rw [update_of_ne _ _ hcr] at ha hb; exact ⟨ha, hb⟩
          · exact Or.inr (Or.inr h1)
    · exact StepA.makeEligible _ p r ((htp p).2 hp) (hP.knows hi hkl) hsy hel
  | makeIneligible p r hp hkl hel =>
    have hpn := hP.none_of_knows hi hkl
    have hne : ∀ n c, s.proposing n = some c → n ≠ p := fun n c hn e => by subst e; rw [hpn] at hn; exact absurd hn (by simp)
    refine ⟨update L p (makeIneligibleCfg s r), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inl ?_⟩
    · intro n hn; change s.proposing n = none at hn
      show update L p _ n = update s.localCfg p _ n
      by_cases e : n = p
      · subst e; rw [update_self, update_self]
      · rw [update_of_ne _ _ e, update_of_ne _ _ e]; exact hP.same n hn
    · intro n c hn; change s.proposing n = some c at hn
      show ∃ i, update L p _ n = promoteL (update s.localCfg p _ n) c i
      rw [update_of_ne _ _ (hne n c hn), update_of_ne _ _ (hne n c hn)]; exact hP.pend n c hn
    · intro n c hn; change s.proposing n = some c at hn
      have := hP.thinks n c hn; unfold ThinksPrimary at this ⊢
      show (update s.localCfg p _ n).primary = n ∧ (update s.localCfg p _ n).incarnation n = _
      rw [update_of_ne _ _ (hne n c hn)]; exact this
    · exact hP.ne
    · intro n c hn; change s.proposing n = some c at hn
      show (update s.localCfg p _ n).eligible c = false; rw [update_of_ne _ _ (hne n c hn)]; exact hP.notElig n c hn
    · intro n c hn; change s.proposing n = some c at hn
      show update s.sync p _ n c = true ∨ (update L p _ n).incarnation c < _
      rw [update_of_ne _ _ (hne n c hn), update_of_ne _ _ (hne n c hn)]; exact hP.counted n c hn
    · intro n c hn; change s.proposing n = some c at hn
      rcases hP.stale n c hn with h1 | h1 | h1
      · left; show update s.sync p _ n c = true; rw [update_of_ne _ _ (hne n c hn)]; exact h1
      · right; left; intro ⟨ha, hb⟩; apply h1
        change (update s.cfg.eligible r false c = true ∨ c = s.cfg.primary) at ha
        refine ⟨?_, hb⟩
        by_cases hcr : c = r
        · subst hcr; rw [update_self] at ha; rcases ha with ha | ha
          · exact absurd ha (by decide)
          · exact Or.inr ha
        · rw [update_of_ne _ _ hcr] at ha; exact ha
      · right; right
        by_cases ecp : c = p
        · subst ecp
          show (update s.localCfg c _ c).primary ≠ n; rw [update_self]
          show s.cfg.primary ≠ n
          have := (thinksPrimary_knowsLatest hi ((htp c).2 hp) (hP.knows hi hkl)).2
          rw [show (simState s L).cfg = s.cfg from rfl] at this; rw [this]; exact Ne.symm (hne n c hn)
        · show (update s.localCfg p _ c).primary ≠ n; rw [update_of_ne _ _ ecp]; exact h1
    · exact StepA.makeIneligible _ p r ((htp p).2 hp) (hP.knows hi hkl) hel
  | learn n hnkl =>
    -- `L'`: `n` sees the latest configuration and has no proposal in flight.
    have hPL : PromSim (learn s n) (update L n s.cfg) := by
      have hne : ∀ x c, (learn s n).proposing x = some c → x ≠ n := fun x c hx e => by
        subst e; change update s.proposing x none x = some c at hx; rw [update_self] at hx; exact absurd hx (by simp)
      have hpx : ∀ x c, (learn s n).proposing x = some c → s.proposing x = some c := fun x c hx => by
        have := hne x c hx; change update s.proposing n none x = some c at hx; rwa [update_of_ne _ _ this] at hx
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        show update L n s.cfg x = update s.localCfg n s.cfg x
        by_cases e : x = n
        · subst e; rw [update_self, update_self]
        · rw [update_of_ne _ _ e, update_of_ne _ _ e]
          exact hP.same x (by change update s.proposing n none x = none at hx; rwa [update_of_ne _ _ e] at hx)
      · intro x c hx
        show ∃ i, update L n s.cfg x = promoteL (update s.localCfg n s.cfg x) c i
        rw [update_of_ne _ _ (hne x c hx), update_of_ne _ _ (hne x c hx)]; exact hP.pend x c (hpx x c hx)
      · intro x c hx
        have := hP.thinks x c (hpx x c hx); unfold ThinksPrimary at this ⊢
        show (update s.localCfg n s.cfg x).primary = x ∧ (update s.localCfg n s.cfg x).incarnation x = _
        rw [update_of_ne _ _ (hne x c hx)]; exact this
      · exact fun x c hx => hP.ne x c (hpx x c hx)
      · intro x c hx
        show (update s.localCfg n s.cfg x).eligible c = false
        rw [update_of_ne _ _ (hne x c hx)]; exact hP.notElig x c (hpx x c hx)
      · intro x c hx
        show update s.sync n _ x c = true ∨ (update L n s.cfg x).incarnation c < _
        rw [update_of_ne _ _ (hne x c hx), update_of_ne _ _ (hne x c hx)]; exact hP.counted x c (hpx x c hx)
      · intro x c hx
        have hx' := hpx x c hx
        have hsy : (learn s n).sync x c = s.sync x c := by
          show update s.sync n _ x c = _; rw [update_of_ne _ _ (hne x c hx)]
        rw [hsy]
        rcases hP.stale x c hx' with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · by_cases ecn : c = n
          · subst ecn
            -- `c` learns the latest configuration and so follows the current primary.
            show s.sync x c = true ∨ ¬ IsAuthoritative s c ∨ (update s.localCfg c s.cfg c).primary ≠ x
            rw [update_self]
            by_cases hxp : s.cfg.primary = x
            · rcases hP.counted x c hx' with h2 | h2
              · exact Or.inl h2
              · right; left; intro ⟨_, hb⟩
                have hk : L x = s.cfg := by
                  have := hi.primKnows; rw [show (simState s L).cfg = s.cfg from rfl, hxp] at this; exact this
                rw [hk] at h2; omega
            · exact Or.inr (Or.inr hxp)
          · right; right; show (update s.localCfg n s.cfg c).primary ≠ x; rw [update_of_ne _ _ ecn]; exact h1
    refine ⟨update L n s.cfg, hPL, ?_⟩
    have hprim : (L n).primary = (s.localCfg n).primary := hP.primary n
    have heq : learn (simState s L) n = simState (learn s n) (update L n s.cfg) := by
      simp only [learn, simState, hprim, update_none_const]; rfl
    by_cases hk : KnowsLatest (simState s L) n
    · -- the atomic model already knows the outcome: no step
      right; refine ⟨?_, n, rfl⟩
      have hLn : L n = s.cfg := hi.localCfgEq n hk
      cases hn : s.proposing n with
      | none => exact absurd (by unfold KnowsLatest at hk ⊢; rw [← hP.same n hn]; exact hk) hnkl
      | some c =>
        have htn := hP.thinks n c hn
        have hpn : s.cfg.primary = n := by rw [← hLn, hprim]; exact htn.1
        have h1 : update L n s.cfg = L := by
          funext x; unfold update; split_ifs with e
          · subst e; exact hLn.symm
          · rfl
        have h2 : update s.sync n (if s.cfg.primary = n then s.sync n else fun _ => false) = s.sync := by
          rw [if_pos hpn]; funext x; unfold update; split_ifs with e
          · subst e; rfl
          · rfl
        have h3 : (if s.cfg.primary = (s.localCfg n).primary then s.rgen else closeInto s.rgen n) = s.rgen := by
          rw [if_pos (by rw [hpn, htn.1])]
        simp only [simState, learn, h1, h2, h3]
    · left; rw [← heq]; exact StepA.learn _ n hk
  | psync r hne hserv hok =>
    have hpo := hP.primaryOf_eq r
    have heq : reconnect (simState s L) r = simState (reconnect s r) L := by
      unfold reconnect; rw [hpo]; rfl
    refine ⟨L, hP.frame rfl rfl rfl rfl (fun _ _ _ h => h), Or.inl ?_⟩
    rw [← heq]
    refine StepA.psync _ r (by rw [hpo]; exact hne) ?_ (by rw [hpo]; exact hok)
    rw [hpo]
    unfold ServesPsync at hserv ⊢
    rcases hserv with h | h
    · left; show (L _).primary = _; rw [hP.primary]; exact h
    · right; rw [hP.primaryOf_eq]; exact h
  | sendData p r k hst hk =>
    refine ⟨L, hP.frame rfl rfl rfl rfl (fun _ _ _ h => h), Or.inl ?_⟩
    exact StepA.sendData _ p r k hst hk
  | deliverData p r g v rid hin hcur hf hfol =>
    refine ⟨L, hP.frame rfl rfl rfl rfl (fun _ _ _ h => h), Or.inl ?_⟩
    exact StepA.deliverData _ p r g v rid hin hcur hf (by rw [hP.primaryOf_eq]; exact hfol)
  | sendAck r hne =>
    have heq : sendAckMsg (simState s L) r = simState (sendAckMsg s r) L := by
      unfold sendAckMsg; rw [hP.primaryOf_eq r]; rfl
    refine ⟨L, hP.frame rfl rfl rfl rfl (fun _ _ _ h => h), Or.inl ?_⟩
    rw [← heq]; exact StepA.sendAck _ r (by rw [hP.primaryOf_eq]; exact hne)
  | deliverAck r p g off k hin hcur hf hst =>
    refine ⟨L, hP.frame rfl rfl rfl rfl (fun _ _ _ h => h), Or.inl ?_⟩
    exact StepA.deliverAck _ r p g off k hin hcur hf hst
  | dropMsg msg hin =>
    refine ⟨L, hP.frame rfl rfl rfl rfl (fun _ _ _ h => h), Or.inl ?_⟩
    exact StepA.dropMsg _ msg hin
  | takeover n hkl hel hnp hin =>
    have hnn := hP.none_of_knows hi hkl
    have hne : ∀ x c, s.proposing x = some c → x ≠ n := fun x c hx e => by subst e; rw [hnn] at hx; exact absurd hx (by simp)
    refine ⟨update L n (takeoverCfg s n), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inl ?_⟩
    · intro x hx; change s.proposing x = none at hx
      show update L n _ x = update s.localCfg n _ x
      by_cases e : x = n
      · subst e; rw [update_self, update_self]
      · rw [update_of_ne _ _ e, update_of_ne _ _ e]; exact hP.same x hx
    · intro x c hx; change s.proposing x = some c at hx
      show ∃ i, update L n _ x = promoteL (update s.localCfg n _ x) c i
      rw [update_of_ne _ _ (hne x c hx), update_of_ne _ _ (hne x c hx)]; exact hP.pend x c hx
    · intro x c hx; change s.proposing x = some c at hx
      have := hP.thinks x c hx; unfold ThinksPrimary at this ⊢
      show (update s.localCfg n _ x).primary = x ∧ (update s.localCfg n _ x).incarnation x = _
      rw [update_of_ne _ _ (hne x c hx)]; exact this
    · exact hP.ne
    · intro x c hx; change s.proposing x = some c at hx
      show (update s.localCfg n _ x).eligible c = false; rw [update_of_ne _ _ (hne x c hx)]; exact hP.notElig x c hx
    · intro x c hx; change s.proposing x = some c at hx
      show update s.sync n _ x c = true ∨ (update L n _ x).incarnation c < _
      rw [update_of_ne _ _ (hne x c hx), update_of_ne _ _ (hne x c hx)]; exact hP.counted x c hx
    · intro x c hx; change s.proposing x = some c at hx
      by_cases hcn : c = n
      · subst hcn; right; right
        show (update s.localCfg c _ c).primary ≠ x; rw [update_self]; exact Ne.symm (hne x c hx)
      · rcases hP.stale x c hx with h1 | h1 | h1
        · left; show update s.sync n _ x c = true; rw [update_of_ne _ _ (hne x c hx)]; exact h1
        · right; left; intro ⟨ha, hb⟩; apply h1; refine ⟨?_, hb⟩
          change (eligibleAfterTakeover s n c = true ∨ c = n) at ha
          rcases ha with ha | ha
          · left; unfold eligibleAfterTakeover at ha; simp at ha; exact ha.1.1
          · exact absurd ha hcn
        · right; right; show (update s.localCfg n _ c).primary ≠ x; rw [update_of_ne _ _ hcn]; exact h1
    · exact StepA.takeover _ n (hP.knows hi hkl) hel hnp hin
  | resync r hne hsy hke =>
    have hpo := hP.primaryOf_eq r
    have heq : resync (simState s L) r = simState (resync s r) L := by
      unfold resync catchUpPoint; rw [hpo]; rfl
    refine ⟨L, hP.frame rfl rfl rfl rfl (fun _ _ _ h => h), Or.inl ?_⟩
    rw [← heq]
    by_cases hc : s.proposing (primaryOf s r) = some r
    · rcases hP.stale _ r hc with h1 | h1 | h1
      · rw [hsy] at h1; exact absurd h1 (by decide)
      · exact StepA.resyncStale _ r (by rw [hpo]; exact hne) (by rw [hpo]; exact hsy) h1
      · exact absurd rfl h1
    · exact StepA.resync _ r (by rw [hpo]; exact hne) (by rw [hpo]; exact hsy)
        (by rw [hpo]; exact hP.notElig' hke hc)
  | restartEmpty n hkl hsurv =>
    have hnn := hP.none_of_knows hi hkl
    exact ⟨L, hP.restartFresh hi hnn rfl rfl rfl rfl rfl, Or.inl (StepA.restartEmpty _ n (hP.knows hi hkl) hsurv)⟩
  | restartPartialFresh n k hkl hk hfresh hsurv =>
    have hnn := hP.none_of_knows hi hkl
    have hLn : (simState s L).localCfg n = s.localCfg n := hP.localCfg_of_knows hi hkl
    have heq : restartPartialFresh (simState s L) n k = simState (restartPartialFresh s n k) L := by
      unfold restartPartialFresh restartIds; rw [hLn]; rfl
    refine ⟨L, hP.restartFresh hi hnn rfl rfl rfl rfl rfl, Or.inl ?_⟩
    rw [← heq]; exact StepA.restartPartialFresh _ n k (hP.knows hi hkl) hk hfresh hsurv
  | restartKeep n hkl =>
    have hnn := hP.none_of_knows hi hkl
    have hLn : (simState s L).localCfg n = s.localCfg n := hP.localCfg_of_knows hi hkl
    have heq : restartKeep (simState s L) n = simState (restartKeep s n) L := by
      unfold restartKeep rebuiltSync restartIds; rw [hLn]; rfl
    have hne : ∀ x c, s.proposing x = some c → x ≠ n := fun x c hx e => by subst e; rw [hnn] at hx; exact absurd hx (by simp)
    refine ⟨L, hP.frame rfl rfl rfl rfl (fun x c hx h => ?_), Or.inl ?_⟩
    · show update s.sync n _ x c = true; rw [update_of_ne _ _ (hne x c hx)]; exact h
    · rw [← heq]; exact StepA.restartKeep _ n (hP.knows hi hkl)
  | restartPartialKeep n k hkl hk hkeep =>
    have hnn := hP.none_of_knows hi hkl
    have hLn : (simState s L).localCfg n = s.localCfg n := hP.localCfg_of_knows hi hkl
    have heq : restartPartialKeep (simState s L) n k = simState (restartPartialKeep s n k) L := by
      unfold restartPartialKeep restartKeep rebuiltSync restartIds; rw [hLn]; rfl
    have hne : ∀ x c, s.proposing x = some c → x ≠ n := fun x c hx e => by subst e; rw [hnn] at hx; exact absurd hx (by simp)
    refine ⟨L, hP.frame rfl rfl rfl rfl (fun x c hx h => ?_), Or.inl ?_⟩
    · show update s.sync n _ x c = true; rw [update_of_ne _ _ (hne x c hx)]; exact h
    · rw [← heq]; exact StepA.restartPartialKeep _ n k (hP.knows hi hkl) hk hkeep

/-! ## Inversion: the post-state of an atomic step with a given label -/

section inv
variable {m : Nat} {t t' : State Node}

theorem StepA.learn_inv {n : Node} (h : StepA m t (.learn n) t') : t' = SyncReplication.learn t n ∧ ¬ KnowsLatest t n := by
  cases h; exact ⟨rfl, by assumption⟩
theorem StepA.takeover_inv {n : Node} (h : StepA m t (.takeover n) t') : t' = SyncReplication.takeover t n := by
  cases h; rfl
theorem StepA.resync_inv {r : Node} (h : StepA m t (.resync r) t') : t' = SyncReplication.resync t r := by
  cases h <;> rfl
theorem StepA.restartEmpty_inv {n : Node} (h : StepA m t (.restartEmpty n) t') : t' = SyncReplication.restartEmpty t n := by
  cases h; rfl
theorem StepA.restartKeep_inv {n : Node} (h : StepA m t (.restartKeep n) t') : t' = SyncReplication.restartKeep t n := by
  cases h; rfl
theorem StepA.restartPartial_inv {n : Node} {k : Nat} (h : StepA m t (.restartPartial n k) t') :
    t' = SyncReplication.restartPartialKeep t n k ∨ t' = SyncReplication.restartPartialFresh t n k := by
  cases h
  · exact Or.inl rfl
  · exact Or.inr rfl
theorem StepA.makeIneligible_inv {p r : Node} (h : StepA m t (.makeIneligible p r) t') : t' = SyncReplication.makeIneligible t p r := by
  cases h; rfl

end inv

end SyncReplication
