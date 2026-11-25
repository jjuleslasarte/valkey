import SyncReplication.InstantLeases
import SyncReplication.Counterexamples.Leases

/-!
# Write-ahead replicas: which rules are needed

Each run is a weakening of the model with write-ahead replicas (`Step`, `LeaseStep`),
with one rule removed, at three nodes.

- **Truncate at the switch offset** (`truncAtEnd_unsafe`, `min-sync-replicas = 1`): n0
  writes twice and n2 copies both; n1 takes over with an empty log and writes once; n2,
  still eligible, offers n0's ID and is truncated at the end of n1's log instead of where
  n0's ID ended. It keeps n0's first entry, receives n1's second, and acknowledges; n1
  commits with n2's acknowledgement. The eligible n2 lacks the committed history.
- **Only a node acting as primary answers with a truncation offset**
  (`truncNotPrimary_unsafe`, `min-sync-replicas = 1`): a write commits on n0 and n1; n0
  restarts from an empty file, takes a new incarnation (so it no longer acts as primary,
  though it is still named primary) and keeps its old ID as secondary up to 0; n1 offers
  the old ID and is truncated at 0. The eligible n1 lacks the committed write.
- **A restart applies only up to the applied offset** (`restartApplies_unsafe`): the
  write-ahead n1 logs an uncommitted write and restarts, applying its whole log; its
  keyspace then holds a write that never committed (`AppliedCommitted` fails).
- **A full sync does not count as applied** (`resyncSnapshotApplied_unsafe`): during n1's
  reconciliation the write-ahead n2 is fully resynced to n1's inherited log, which is not
  committed, and takes the snapshot's offset as its applied and committed offset.
-/

open Cslib

namespace SyncReplication

/-! ## Truncate at the switch offset -/

/-- `Step` with the truncation at the end of the primary's log instead of where its
secondary ID ended. -/
inductive StepTruncAtEnd (m : Nat) : State N → Action N → State N → Prop
  | step {s μ s'} : Step m s μ s' → StepTruncAtEnd m s μ s'
  | truncate (s : State N) (r : N) (k : Nat) : primaryOf s r ≠ r → ThinksPrimary s (primaryOf s r) →
      s.replId2 (primaryOf s r) = some (s.replId r, k) → k < (s.log r).length →
      (s.log (primaryOf s r)).length < (s.log r).length →
      StepTruncAtEnd m s (.truncate r (s.log (primaryOf s r)).length)
        (truncateAt s r (s.log (primaryOf s r)).length)

def transitionSystemTruncAtEnd (m : Nat) : LTS (State N) (Action N) where
  Tr := StepTruncAtEnd m

def ta0 : State N := init 0
def ta1 := addToSyncSet ta0 0 1
def ta1p := proposeEligible ta1 0 1
def ta2 := learn ta1p 0                         -- n1 eligible
def ta3 := addToSyncSet ta2 0 2
def ta3p := proposeEligible ta3 0 2
def ta4 := learn ta3p 0                         -- n2 eligible
def ta5 := appendWrite ta4 0
def ta6 := appendWrite ta5 0                    -- n0: [1, 1]
def ta7 := reconnect ta6 2
def ta8 := applyData (streamNext ta7 0 2 0) (.data 0 2 1 1 1) 2 1 1
def ta9 := applyData (streamNext ta8 0 2 1) (.data 0 2 1 1 1) 2 1 1   -- n2: [1, 1]
def ta10 := learn ta9 1
def ta11 := takeover ta10 1                     -- n1: [], ID 2, secondary (1, 0)
def ta12 := appendWrite ta11 1                  -- n1: [2]
def ta13 := learn ta12 2                        -- n2 follows n1
def ta14 := truncateAt ta13 2 1                 -- n2 truncated at n1's log end: [1]
def ta15 := appendWrite ta14 1                  -- n1: [2, 2]
def ta16 := applyData (streamNext ta15 1 2 1) (.data 1 2 4 2 2) 2 2 2  -- n2: [1, 2]
def ta17 := recordAck (sendAckMsg ta16 2) (.ack 2 1 4 2) 1 2 2
def ta18 := commitNext ta17 1                   -- history [2]

theorem truncAtEnd_run : (transitionSystemTruncAtEnd 1).MTr ta0
    [.addToSyncSet 0 1, .makeEligible 0 1, .learn 0, .addToSyncSet 0 2, .makeEligible 0 2, .learn 0,
     .append 0, .append 0, .psync 2, .sendData 0 2, .deliver (.data 0 2 1 1 1), .sendData 0 2,
     .deliver (.data 0 2 1 1 1), .learn 1, .takeover 1, .append 1, .learn 2, .truncate 2 1, .append 1,
     .sendData 1 2, .deliver (.data 1 2 4 2 2), .sendAck 2, .deliver (.ack 2 1 4 2), .commit 1] ta18 :=
  .stepL (.step (Step.addToSyncSet ta0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.makeEligible ta1 0 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.learn ta1p 0 (by decide))) <|
  .stepL (.step (Step.addToSyncSet ta2 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.makeEligible ta3 0 2 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.learn ta3p 0 (by decide))) <|
  .stepL (.step (Step.append ta4 0 (by decide) (writable_one (r := 1) (by decide) (by decide) (by decide)))) <|
  .stepL (.step (Step.append ta5 0 (by decide) (writable_one (r := 1) (by decide) (by decide) (by decide)))) <|
  .stepL (.step (Step.psync ta6 2 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.sendData _ 0 2 0 (by decide) (by decide))) <|
  .stepL (.step (Step.deliverData _ 0 2 1 1 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.sendData _ 0 2 1 (by decide) (by decide))) <|
  .stepL (.step (Step.deliverData _ 0 2 1 1 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.learn ta9 1 (by decide))) <|
  .stepL (.step (Step.takeover ta10 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.append ta11 1 (by decide) (writable_one (r := 2) (by decide) (by decide) (by decide)))) <|
  .stepL (.step (Step.learn ta12 2 (by decide))) <|
  .stepL (StepTruncAtEnd.truncate ta13 2 0 (by decide) (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (.step (Step.append ta14 1 (by decide) (writable_one (r := 2) (by decide) (by decide) (by decide)))) <|
  .stepL (.step (Step.sendData _ 1 2 1 (by decide) (by decide))) <|
  .stepL (.step (Step.deliverData _ 1 2 4 2 2 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.sendAck _ 2 (by decide))) <|
  .stepL (.step (Step.deliverAck _ 2 1 4 2 2 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.commit ta17 1 (by decide) (writable_one (r := 2) (by decide) (by decide) (by decide))
    (by decide) (by decide))) <|
  .refl

/-- Truncating at the new primary's log end instead of where its secondary ID ended
reaches a state where an authoritative eligible replica (n2) lacks the committed history. -/
theorem truncAtEnd_unsafe : ∃ s, (transitionSystemTruncAtEnd 1).CanReach (init 0) s ∧ ¬ Safety s := by
  refine ⟨ta18, ⟨_, truncAtEnd_run⟩, ?_⟩
  intro ⟨hholds, _⟩
  exact absurd (hholds 2 (by decide)) (by decide)

/-! ## Only a node acting as primary answers with a truncation offset -/

/-- `Step` with the truncation answered by a node that its own configuration names primary,
whether or not it records its current incarnation. -/
inductive StepTruncNotPrimary (m : Nat) : State N → Action N → State N → Prop
  | step {s μ s'} : Step m s μ s' → StepTruncNotPrimary m s μ s'
  | truncate (s : State N) (r : N) (k : Nat) : primaryOf s r ≠ r →
      (s.localCfg (primaryOf s r)).primary = primaryOf s r →
      s.replId2 (primaryOf s r) = some (s.replId r, k) → k < (s.log r).length →
      StepTruncNotPrimary m s (.truncate r k) (truncateAt s r k)

def transitionSystemTruncNotPrimary (m : Nat) : LTS (State N) (Action N) where
  Tr := StepTruncNotPrimary m

def tn7 := restartPartialFresh c6 0 0           -- n0 restarts from an empty file: new incarnation
def tn8 := truncateAt tn7 1 0                   -- n1 truncated at 0 by n0

theorem truncNotPrimary_run : (transitionSystemTruncNotPrimary 1).MTr c0
    [.addToSyncSet 0 1, .makeEligible 0 1, .learn 0, .append 0, .psync 1, .sendData 0 1,
     .deliver (.data 0 1 1 1 1), .sendAck 1, .deliver (.ack 1 0 1 1), .commit 0,
     .restartPartial 0 0, .truncate 1 0] tn8 :=
  LTS.MTr.comp (transitionSystemTruncNotPrimary 1) (mtr_of_step StepTruncNotPrimary.step committed_run) <|
  .stepL (.step (Step.restartPartialFresh c6 0 0 (by decide) (by decide) (by decide) ⟨1, by decide, by decide⟩)) <|
  .stepL (StepTruncNotPrimary.truncate tn7 1 0 (by decide) (by decide) (by decide) (by decide)) <|
  .refl

/-- Truncation answered by a node that no longer acts as primary reaches a state where an
authoritative eligible replica (n1) lacks the committed history. -/
theorem truncNotPrimary_unsafe : ∃ s, (transitionSystemTruncNotPrimary 1).CanReach (init 0) s ∧ ¬ Safety s := by
  refine ⟨tn8, ⟨_, truncNotPrimary_run⟩, ?_⟩
  intro ⟨hholds, _⟩
  exact absurd (hholds 1 (by decide)) (by decide)

/-! ## A restart applies only up to the applied offset -/

instance (a : LeaseState N) : Decidable (AppliedCommitted a) := by
  unfold AppliedCommitted ThinksPrimary; infer_instance

/-- `leaseRestart`, except that the restarted node applies its whole restored log. -/
def leaseRestartApplies (a : LeaseState N) (n : N) (c : State N) : LeaseState N :=
  { leaseRestart a n c with applied := update a.applied n (c.log n).length }

/-- `LeaseStep` plus a RestartKeep that applies the whole restored log. -/
inductive LeaseStepRestartApplies (m : Nat) (P : LeaseParams) : LeaseState N → LeaseAction N → LeaseState N → Prop
  | step {a μ a'} : LeaseStep m P a μ a' → LeaseStepRestartApplies m P a μ a'
  | restartKeep (a : LeaseState N) (n : N) : KnowsLatest a.core n →
      LeaseStepRestartApplies m P a (.restartKeep n) (leaseRestartApplies a n (restartKeep a.core n))

def leaseTransitionSystemRestartApplies (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepRestartApplies m P

def waR0 : LeaseState N := leaseInit 0
def waR1 := leaseSetMode waR0 1 true                        -- n1 is write-ahead
def waR2 := withCore waR1 (appendWrite waR1.core 0)          -- n0 writes
def waR3 := withCore waR2 (reconnect waR2.core 1)
def waR4 := withCore waR3 (streamNext waR3.core 0 1 0)
def waR5 := withCore waR4 (applyData waR4.core (.data 0 1 1 1 1) 1 1 1)   -- n1 logs it
def waR6 := leaseRestartApplies waR5 1 (restartKeep waR5.core 1)          -- n1 restarts, applies it

theorem restartApplies_run : (leaseTransitionSystemRestartApplies 0 P0).MTr waR0
    [.setMode 1 true, .core (.append 0), .core (.psync 1), .core (.sendData 0 1),
     .core (.deliver (.data 0 1 1 1 1)), .restartKeep 1] waR6 :=
  .stepL (.step (LeaseStep.setMode waR0 1 true (by unfold ModeSettable; decide))) <|
  .stepL (.step (LeaseStep.core _ _ _ (Step.append waR1.core 0 (by decide) (writable_zero _ _)) rfl)) <|
  .stepL (.step (LeaseStep.core _ _ _ (Step.psync waR2.core 1 (by decide) (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core _ _ _ (Step.sendData _ 0 1 0 (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core _ _ _ (Step.deliverData _ 0 1 1 1 1 (by decide) (by decide) (by decide)
    (by decide)) rfl)) <|
  .stepL (LeaseStepRestartApplies.restartKeep waR5 1 (by decide)) <|
  .refl

/-- A restart that applies past the applied offset puts a write that never committed in a
write-ahead replica's keyspace. -/
theorem restartApplies_unsafe :
    ∃ a, (leaseTransitionSystemRestartApplies 0 P0).CanReach (leaseInit 0) a ∧ ¬ AppliedCommitted a :=
  ⟨waR6, ⟨_, restartApplies_run⟩, by decide⟩

/-! ## A full sync does not count as applied -/

/-- `leaseResync`, except that the replica takes the snapshot's offset as its committed and
applied offset. -/
def leaseResyncSnapshot (a : LeaseState N) (r : N) : LeaseState N :=
  { leaseResync a r with committedView := update a.committedView r ((resync a.core r).log r).length,
                         applied := update a.applied r ((resync a.core r).log r).length }

/-- `LeaseStep` plus a full resync that counts the snapshot as committed and applied. -/
inductive LeaseStepResyncSnapshot (m : Nat) (P : LeaseParams) : LeaseState N → LeaseAction N → LeaseState N → Prop
  | step {a μ a'} : LeaseStep m P a μ a' → LeaseStepResyncSnapshot m P a μ a'
  | resync (a : LeaseState N) (r : N) : primaryOf a.core r ≠ r →
      a.core.sync (primaryOf a.core r) r = false → (a.core.localCfg (primaryOf a.core r)).eligible r = false →
      LeaseStepResyncSnapshot m P a (.resync r) (leaseResyncSnapshot a r)

def leaseTransitionSystemResyncSnapshot (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepResyncSnapshot m P

def waS0 : LeaseState N := leaseInit 0
def waS1 := leaseSetMode waS0 2 true                        -- n2 is write-ahead
def waS2 := withCore waS1 (addToSyncSet waS1.core 0 1)
def waS3 := withCore waS2 (proposeEligible waS2.core 0 1)
def waS4 := leaseLearn waS3 0                               -- n1 eligible
def waS5 := leaseLearn waS4 1
def waS6 := withCore waS5 (appendWrite waS5.core 0)          -- n0 writes
def waS7 := withCore waS6 (reconnect waS6.core 1)
def waS8 := withCore waS7 (streamNext waS7.core 0 1 0)
def waS9 := withCore waS8 (applyData waS8.core (.data 0 1 1 1 1) 1 1 1)   -- n1 holds it, uncommitted
def waS13 := tick (tick (tick (tick waS9)))
def waS14 := leaseTakeover waS13 1                          -- n1 takes over; its inherited log is [1]
def waS15 := leaseLearn waS14 2                             -- n2 follows n1
def waS16 := leaseResyncSnapshot waS15 2                    -- n2 gets [1] and counts it applied

theorem resyncSnapshot_run : (leaseTransitionSystemResyncSnapshot 0 P0).MTr waS0
    [.setMode 2 true, .core (.addToSyncSet 0 1), .core (.makeEligible 0 1), .learn 0, .learn 1,
     .core (.append 0), .core (.psync 1), .core (.sendData 0 1), .core (.deliver (.data 0 1 1 1 1)),
     .tick, .tick, .tick, .tick, .takeover 1, .learn 2, .resync 2] waS16 :=
  .stepL (.step (LeaseStep.setMode waS0 2 true (by unfold ModeSettable; decide))) <|
  .stepL (.step (LeaseStep.core _ _ _ (Step.addToSyncSet waS1.core 0 1 (by decide) (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core _ _ _ (Step.makeEligible waS2.core 0 1 (by decide) (by decide) (by decide)
    (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.learn waS3 0 (by decide))) <|
  .stepL (.step (LeaseStep.learn waS4 1 (by decide))) <|
  .stepL (.step (LeaseStep.core _ _ _ (Step.append waS5.core 0 (by decide) (writable_zero _ _)) rfl)) <|
  .stepL (.step (LeaseStep.core _ _ _ (Step.psync waS6.core 1 (by decide) (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core _ _ _ (Step.sendData _ 0 1 0 (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core _ _ _ (Step.deliverData _ 0 1 1 1 1 (by decide) (by decide) (by decide)
    (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.tick _)) <| .stepL (.step (LeaseStep.tick _)) <|
  .stepL (.step (LeaseStep.tick _)) <| .stepL (.step (LeaseStep.tick _)) <|
  .stepL (.step (LeaseStep.takeover waS13 1 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (LeaseStep.learn waS14 2 (by decide))) <|
  .stepL (LeaseStepResyncSnapshot.resync waS15 2 (by decide) (by decide) (by decide)) <|
  .refl

/-- A full sync that counts the snapshot's offset as committed and applied puts a write
that has not committed in a write-ahead replica's keyspace. -/
theorem resyncSnapshotApplied_unsafe :
    ∃ a, (leaseTransitionSystemResyncSnapshot 0 P0).CanReach (leaseInit 0) a ∧ ¬ AppliedCommitted a :=
  ⟨waS16, ⟨_, resyncSnapshot_run⟩, by decide⟩

end SyncReplication
