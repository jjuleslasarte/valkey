import SyncReplication.Counterexamples.Leases

/-!
# Two-step promotion: the two keep-counting rules

The model's MakeEligible is a proposal (`proposeEligible`): the primary's compare-and-set
on the cluster bus (design §4, promotion step 4) commits, and the latest configuration
lists the candidate as eligible, but the primary's own configuration changes only when
it learns the outcome with Learn. Until then `proposing p = some c`. Proposal then Learn
is the atomic MakeEligible (`learn_proposeEligible`). Shortcut: a compare-and-set that
fails is not modelled separately, and the proposal commits at once.

While the proposal is in flight the primary's configuration still lists `c` as not
eligible. Two rules keep counting `c` until the primary learns the outcome:

- **RemoveFromSyncSet does not drop the candidate** (`s.proposing p ≠ some r`). Without
  it (`StepDropCandidate`), at `min-sync-replicas = 1`: n0 promotes n2, counts n1 and
  proposes n1's promotion, which commits; n0 writes, n2 acknowledges, n0 drops n1 and
  commits with n2's acknowledgement only. n1 is eligible and authoritative and lacks
  the committed write (`proposeEligible_unsafe`).
- **The primary lease needs the candidate** (`PrimLeaseValid` counts `proposing p`).
  Without it (`PrimCanReadOwnCfg`, the read rule over the primary's own configuration
  alone), at `min-sync-replicas = 0` in the model itself: n0 proposes n1's promotion, n1
  learns it, waits out its takeover wait, takes over and commits a write; n0 still
  passes the read rule and its log misses the write (`proposeEligible_stale`).
-/

open Cslib

namespace SyncReplication

/-- Proposal then the primary's Learn is the atomic MakeEligible, when the primary knows
the configuration that made it primary and has no proposal in flight. -/
theorem learn_proposeEligible (s : State N) (p r : N) (hp : s.cfg.primary = p)
    (hl : (s.localCfg p).primary = p) (hn : s.proposing p = none) :
    learn (proposeEligible s p r) p = makeEligible s p r := by
  have hp' : (makeEligibleCfg s r).primary = p := hp
  unfold learn proposeEligible makeEligible
  simp only [hp', hl, ite_true, update_self]
  have h1 : update (update s.proposing p (some r)) p none = s.proposing := by
    funext x; by_cases e : x = p
    · subst e; rw [update_self, hn]
    · rw [update_of_ne _ _ e, update_of_ne _ _ e]
  have h2 : update s.sync p (s.sync p) = s.sync := by
    funext x; by_cases e : x = p
    · subst e; rw [update_self]
    · rw [update_of_ne _ _ e]
  rw [h1, h2]

/-! ## Without the removal guard -/

/-- `Step`, plus RemoveFromSyncSet of the candidate whose promotion is in flight. -/
inductive StepDropCandidate (m : Nat) : State N → Action N → State N → Prop
  | step {s μ s'} : Step m s μ s' → StepDropCandidate m s μ s'
  | removeFromSyncSet (s : State N) (p r : N) : ThinksPrimary s p → s.sync p r = true →
      (s.localCfg p).eligible r = false → StepDropCandidate m s (.removeFromSyncSet p r) (removeFromSyncSet s p r)

/-- The weakened protocol as a transition system. -/
def transitionSystemDropCandidate (m : Nat) : LTS (State N) (Action N) where
  Tr := StepDropCandidate m

def q0 : State N := init 0
def q1 := addToSyncSet q0 0 2             -- n0 counts n2
def q2p := proposeEligible q1 0 2         -- n0 proposes n2's promotion
def q2 := learn q2p 0                     -- n0 learns it: n2 eligible
def q3 := addToSyncSet q2 0 1             -- n0 counts n1
def q4 := proposeEligible q3 0 1          -- n0 proposes n1's promotion; it commits on the cluster bus
def q5 := appendWrite q4 0                -- n0 writes at offset 1
def q6 := applyData (streamNext (reconnect q5 2) 0 2 0) (.data 0 2 1 1 1) 2 1 1   -- n2 copies it
def q7 := recordAck (sendAckMsg q6 2) (.ack 2 0 1 1) 0 2 1                        -- n2 acknowledges
def q8 := removeFromSyncSet q7 0 1        -- n0, not knowing the outcome, drops n1
def q9 := commitNext q8 0                 -- n0 commits with n2's acknowledgement only

/-- The run; the label list is its trace. Only `removeFromSyncSet 0 1` is the weakened
action: it drops n1, whose promotion is in flight. -/
theorem proposeEligible_run : (transitionSystemDropCandidate 1).MTr q0
    [.addToSyncSet 0 2, .makeEligible 0 2, .learn 0, .addToSyncSet 0 1, .makeEligible 0 1, .append 0, .psync 2,
     .sendData 0 2, .deliver (.data 0 2 1 1 1), .sendAck 2, .deliver (.ack 2 0 1 1),
     .removeFromSyncSet 0 1, .commit 0] q9 :=
  .stepL (.step (Step.addToSyncSet q0 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.makeEligible q1 0 2 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.learn q2p 0 (by decide))) <|
  .stepL (.step (Step.addToSyncSet q2 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.makeEligible q3 0 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.append q4 0 (by decide) (writable_one (r := 2) (by decide) (by decide)
    (by decide)))) <|
  .stepL (.step (Step.psync q5 2 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.sendData _ 0 2 0 (by decide) (by decide))) <|
  .stepL (.step (Step.deliverData _ 0 2 1 1 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.sendAck _ 2 (by decide))) <|
  .stepL (.step (Step.deliverAck _ 2 0 1 1 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (StepDropCandidate.removeFromSyncSet q7 0 1 (by decide) (by decide) (by decide)) <|
  .stepL (.step (Step.commit q8 0 (by decide) (writable_one (r := 2) (by decide) (by decide)
    (by decide)) (by decide) (by decide))) <|
  .refl

/-- The removal guard is needed: dropping the candidate while its promotion is in flight
reaches a state where an authoritative eligible replica (n1) lacks the committed history. -/
theorem proposeEligible_unsafe : ∃ s, (transitionSystemDropCandidate 1).CanReach (init 0) s ∧ ¬ Safety s := by
  refine ⟨q9, ⟨_, proposeEligible_run⟩, ?_⟩
  intro ⟨hholds, _⟩
  exact absurd (hholds 1 (by decide)) (by decide)

/-! ## Without the lease check on the candidate -/

/-- The read rule with the primary lease checked over the replicas the primary's own
configuration lists as eligible, not the candidate of a promotion in flight. -/
def PrimCanReadOwnCfg (P : LeaseParams) (a : LeaseState N) (p : N) : Prop :=
  ThinksPrimary a.core p ∧
    (∀ r, (a.core.localCfg p).eligible r = true → r ≠ p → HolderValid P a.now (a.primaryLease p r) P.primDur) ∧
    a.core.commit p = (a.core.log p).length

instance (P : LeaseParams) (a : LeaseState N) (p : N) : Decidable (PrimCanReadOwnCfg P a p) := by
  unfold PrimCanReadOwnCfg; infer_instance

def pl0 : LeaseState N := leaseInit 0
def pl1 := withCore pl0 (addToSyncSet pl0.core 0 1)       -- n0 counts n1
def pl2 := withCore pl1 (proposeEligible pl1.core 0 1)    -- n0 proposes n1's promotion; it commits
def pl3 := leaseLearn pl2 1                               -- n1 learns it
def pl8 := tick (tick (tick (tick (tick pl3))))           -- five ticks: n1 has heard nothing from n0
def pl9 := leaseTakeover pl8 1                            -- n1 takes over
def pl10 := withCore pl9 (appendWrite pl9.core 1)         -- n1 writes
def pl11 := withCore pl10 (commitNext pl10.core 1)        -- and commits alone

theorem proposeEligible_lease_run : (leaseTransitionSystem 0 P3).MTr pl0
    [.core (.addToSyncSet 0 1), .core (.makeEligible 0 1), .learn 1, .tick, .tick, .tick, .tick, .tick,
     .takeover 1, .core (.append 1), .core (.commit 1)] pl11 :=
  .stepL (LeaseStep.core _ _ _ (Step.addToSyncSet _ 0 1 (by decide) (by decide) (by decide) (by decide)
    (by decide)) rfl) <|
  .stepL (LeaseStep.core _ _ _ (Step.makeEligible pl1.core 0 1 (by decide) (by decide) (by decide) (by decide)) rfl) <|
  .stepL (LeaseStep.learn pl2 1 (by decide)) <|
  .stepL (LeaseStep.tick _) <| .stepL (LeaseStep.tick _) <| .stepL (LeaseStep.tick _) <|
  .stepL (LeaseStep.tick _) <| .stepL (LeaseStep.tick _) <|
  .stepL (LeaseStep.takeover pl8 1 (by decide) (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (LeaseStep.core _ _ _ (Step.append _ 1 (by decide) (writable_zero _ _)) rfl) <|
  .stepL (LeaseStep.core _ _ _ (Step.commit _ 1 (by decide) (writable_zero _ _) (by decide)
    (by decide)) rfl) <|
  .refl

/-- The lease check on the candidate is needed: in the model, with `margin ≥ 2 · drift`,
a primary whose promotion of n1 is in flight passes the read rule checked over its own
configuration alone, while n1 has taken over and committed a write its log lacks. -/
theorem proposeEligible_stale : ∃ a, LeaseReachable 0 P3 0 a ∧ 2 * P3.drift ≤ P3.margin ∧
    PrimCanReadOwnCfg P3 a 0 ∧ a.core.log 0 ≠ a.core.hist :=
  ⟨pl11, ⟨_, proposeEligible_lease_run⟩, by decide, by decide, by decide⟩

end SyncReplication
