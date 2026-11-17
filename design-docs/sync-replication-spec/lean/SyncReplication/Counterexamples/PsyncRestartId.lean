import SyncReplication.Safety

/-!
# A restart must take a fresh replication ID

With delayed replication, a replica reconnects with PSYNC, offering its replication ID
and offset, and the primary continues the stream if the ID is its own (or its secondary
ID, within range) and the offset is within its log (`PsyncOk`). Nothing else is
compared. This is sound only if an ID and an offset name one history, so a node whose
log may have been cut back must take a new ID: a restart gives the node a fresh ID,
with its old one valid only up to what it loaded, as a Valkey node does at startup.

`StepRestartKeepsId` is `Step` plus the restarts that keep every replication ID as it
was. The run, two nodes, `min-sync-replicas = 0`: n0 writes; n1 PSYNCs and receives the
entry; n0 counts n1 and makes it eligible; n1 takes over (ID 2, secondary ID 1 up to
offset 1) and writes, so n1's log is `[1, 2]`. n0 learns, PSYNCs with (1, 1), which n1
accepts through its secondary ID, and receives n1's write: n0's log is `[1, 2]`, ID 2. n1
restarts from a file holding none of its log; it has acknowledged nothing, so it keeps
its incarnation, and here its ID 2. It writes twice: `[2, 2]`. n0 reconnects offering
(2, 2), which passes the check. n0 acknowledges 2; n1 counts n0, makes it eligible and
commits offset 1. The committed history is `[2]`; n0 is authoritative and holds
`[1, 2]`. With the fresh ID, n1's ID after the restart is new and its secondary ID 2 is
valid up to offset 0, so n0's offer is refused and n0 must resync in full.
-/

open Cslib

namespace SyncReplication

/-- The state `c` with the replication IDs (primary, secondary, used) of `s`. -/
def keepIdsOf {Node : Type} [DecidableEq Node] (s c : State Node) : State Node :=
  { c with replId := s.replId, usedIds := s.usedIds, replId2 := s.replId2 }

/-- `Step`, plus restarts that keep the node's replication ID and add no secondary ID. -/
inductive StepRestartKeepsId (m : Nat) : State (Fin 2) → Action (Fin 2) → State (Fin 2) → Prop
  | step {s μ s'} : Step m s μ s' → StepRestartKeepsId m s μ s'
  | restartEmpty (s n) : KnowsLatest s n → (∃ m, m ≠ n ∧ IsAuthoritative s m) →
      StepRestartKeepsId m s (.restartEmpty n) (keepIdsOf s (restartEmpty s n))
  | restartKeep (s n) : KnowsLatest s n → StepRestartKeepsId m s (.restartKeep n) (keepIdsOf s (restartKeep s n))
  | restartPartialKeep (s n k) : KnowsLatest s n → k < (s.log n).length → s.ackHigh n ≤ k →
      StepRestartKeepsId m s (.restartPartial n k) (keepIdsOf s (restartPartialKeep s n k))
  | restartPartialFresh (s n k) : KnowsLatest s n → k < (s.log n).length → k < s.ackHigh n →
      (∃ m, m ≠ n ∧ IsAuthoritative s m) →
      StepRestartKeepsId m s (.restartPartial n k) (keepIdsOf s (restartPartialFresh s n k))

def transitionSystemRestartKeepsId (m : Nat) : LTS (State (Fin 2)) (Action (Fin 2)) where
  Tr := StepRestartKeepsId m

section run

theorem tp2 (s : State (Fin 2)) (p : Fin 2) (h1 : (s.localCfg p).primary = p)
    (h2 : (s.localCfg p).incarnation p = s.incarnation p) : ThinksPrimary s p := ⟨h1, h2⟩

theorem wr2 (s : State (Fin 2)) (p : Fin 2) : Writable 0 s p := by unfold Writable; simp

def pk0 : State (Fin 2) := init 0
def pk1 := appendWrite pk0 0                                    -- n0 writes: [1]
def pk2 := reconnect pk1 1                                      -- n1: PSYNC (1, 0), accepted
def pk4 := streamNext pk2 0 1 0
def pk5 := applyData pk4 (.data 0 1 1 1 1) 1 1 1              -- n1: [1]
def pk6 := addToSyncSet pk5 0 1
def pk7 := makeEligible pk6 0 1
def pk8 := learn pk7 1
def pk9 := takeover pk8 1                                       -- n1: ID 2, secondary (1, 1)
def pk10 := appendWrite pk9 1                                   -- n1: [1, 2]
def pk11 := learn pk10 0                                        -- n0 follows n1
def pk13 := reconnect pk11 0                                    -- n0: PSYNC (1, 1), accepted by the secondary ID
def pk14 := streamNext pk13 1 0 1
def pk15 := applyData pk14 (.data 1 0 3 2 2) 0 2 2            -- n0: [1, 2], ID 2
def pk16 := keepIdsOf pk15 (restartPartialKeep pk15 1 0)        -- n1: [], keeps ID 2
def pk17 := appendWrite pk16 1
def pk18 := appendWrite pk17 1                                  -- n1: [2, 2]
def pk20 := reconnect pk18 0                                    -- n0: PSYNC (2, 2), accepted
def pk21 := sendAckMsg pk20 0
def pk22 := recordAck pk21 (.ack 0 1 5 2) 1 0 2
def pk23 := addToSyncSet pk22 1 0
def pk24 := makeEligible pk23 1 0
def pk25 := commitNext pk24 1                                   -- history [2]

theorem pk_run : (transitionSystemRestartKeepsId 0).MTr pk0
    [.append 0, .psync 1, .sendData 0 1, .deliver (.data 0 1 1 1 1),
     .addToSyncSet 0 1, .makeEligible 0 1, .learn 1, .takeover 1, .append 1, .learn 0, .psync 0,
     .sendData 1 0, .deliver (.data 1 0 3 2 2), .restartPartial 1 0,
     .append 1, .append 1, .psync 0, .sendAck 0, .deliver (.ack 0 1 5 2),
     .addToSyncSet 1 0, .makeEligible 1 0, .commit 1] pk25 :=
  .stepL (.step (Step.append _ 0 (tp2 _ _ rfl rfl) (wr2 _ _))) <|
  .stepL (.step (Step.psync _ 1 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.sendData _ 0 1 0 (by decide) (by decide))) <|
  .stepL (.step (Step.deliverData _ 0 1 1 1 1 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.addToSyncSet _ 0 1 (tp2 _ _ rfl rfl) (by decide) rfl rfl (by decide))) <|
  .stepL (.step (Step.makeEligible _ 0 1 (tp2 _ _ rfl rfl) rfl rfl rfl)) <|
  .stepL (.step (Step.learn _ 1 (by unfold KnowsLatest; decide))) <|
  .stepL (.step (Step.takeover _ 1 rfl rfl (by decide) rfl)) <|
  .stepL (.step (Step.append _ 1 (tp2 _ _ rfl rfl) (wr2 _ _))) <|
  .stepL (.step (Step.learn _ 0 (by unfold KnowsLatest; decide))) <|
  .stepL (.step (Step.psync _ 0 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.sendData _ 1 0 1 (by decide) (by decide))) <|
  .stepL (.step (Step.deliverData _ 1 0 3 2 2 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (StepRestartKeepsId.restartPartialKeep _ 1 0 rfl (by decide) (by decide)) <|
  .stepL (.step (Step.append _ 1 (tp2 _ _ rfl rfl) (wr2 _ _))) <|
  .stepL (.step (Step.append _ 1 (tp2 _ _ rfl rfl) (wr2 _ _))) <|
  .stepL (.step (Step.psync _ 0 (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.sendAck _ 0 (by decide))) <|
  .stepL (.step (Step.deliverAck _ 0 1 5 2 2 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (Step.addToSyncSet _ 1 0 (tp2 _ _ rfl rfl) (by decide) rfl rfl (by decide))) <|
  .stepL (.step (Step.makeEligible _ 1 0 (tp2 _ _ rfl rfl) rfl rfl rfl)) <|
  .stepL (.step (Step.commit _ 1 (tp2 _ _ rfl rfl) (wr2 _ _) (by decide) (fun r h => by revert r; decide))) <|
  .refl

/-- **A restart must take a fresh replication ID.** With delayed replication and
Valkey's PSYNC check, a restart that keeps the node's ID breaks property 1: an
authoritative node does not hold the committed history. -/
theorem psyncKeepsId_unsafe : ∃ s, (transitionSystemRestartKeepsId 0).CanReach (init (0 : Fin 2)) s ∧
    IsAuthoritative s 0 ∧ ¬ (s.hist <+: s.log 0) :=
  ⟨pk25, ⟨_, pk_run⟩, ⟨Or.inl (by decide), by decide⟩, by decide⟩

/-- In the same run with the fresh ID, n0's last PSYNC fails the check. -/
theorem psyncFreshId_refused : ¬ PsyncOk (appendWrite (appendWrite (restartPartialKeep pk15 1 0) 1) 1) 1 2 2 := by
  decide

end run

end SyncReplication
