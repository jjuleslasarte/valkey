import SyncReplication.Counterexamples.PsyncRestartId

/-!
# A fresh ID needs no secondary ID for safety

A takeover, and a restart with data of a node that is primary, give the node a fresh
replication ID and keep its old one as the secondary ID up to its offset (Valkey's
`shiftReplicationId`, `server.c:7760-7761`). The secondary ID is
read only by PSYNC's check (`PsyncOk`), where it lets a replica of the old ID continue
without a full resync. `StepNoSecondaryId` is `Step` with every takeover and restart
also clearing the node's secondary ID. `noSecondaryId_safety`: property 1 still holds;
the secondary ID buys availability, not safety. `noSecondaryId_refuses`: without it, a
replica that held the old primary's whole log is refused PSYNC by the new primary, so it
must resync in full; with it, the same PSYNC is accepted.
-/

open Cslib

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-- The node a takeover or a restart gives a fresh ID to. -/
def Action.renewed : Action Node → Option Node
  | .takeover n | .restartEmpty n | .restartKeep n | .restartPartial n _ => some n
  | _ => none

/-- `n` has no secondary ID. -/
def clearSec (s : State Node) (n : Node) : State Node := { s with replId2 := update s.replId2 n none }

/-- `Step`, with takeovers and restarts leaving the node without a secondary ID. -/
inductive StepNoSecondaryId (m : Nat) : State Node → Action Node → State Node → Prop
  | step {s μ s'} : Step m s μ s' → μ.renewed = none → StepNoSecondaryId m s μ s'
  | renew {s μ s' n} : Step m s μ s' → μ.renewed = some n → StepNoSecondaryId m s μ (clearSec s' n)

def transitionSystemNoSecondaryId (m : Nat) : LTS (State Node) (Action Node) where
  Tr := StepNoSecondaryId m

theorem RInvariant.clearSec {s : State Node} (h : RInvariant s) (n : Node) : RInvariant (clearSec s n) where
  ids := h.ids
  ackedLeMax := h.ackedLeMax
  secIds := fun x t o hx => by
    change update s.replId2 n none x = _ at hx
    by_cases e : x = n
    · rw [e, update_self] at hx; cases hx
    · rw [update_of_ne _ _ e] at hx; exact h.secIds x t o hx
  msgIds := h.msgIds
  uniqPrim := h.uniqPrim
  genLe := h.genLe
  streamGen := h.streamGen
  stream := h.stream
  dataStream := h.dataStream
  ackOk := h.ackOk
  hist := by
    obtain ⟨H, hH⟩ := h.hist
    exact ⟨H, { logH := hH.logH, ownH := hH.ownH, streamH := hH.streamH
                secH := fun x t o hx => by
                  change update s.replId2 n none x = _ at hx
                  by_cases e : x = n
                  · rw [e, update_self] at hx; cases hx
                  · rw [update_of_ne _ _ e] at hx; exact hH.secH x t o hx }⟩

theorem invariants_stepNoSecondaryId {m : Nat} {s s' : State Node} {μ : Action Node}
    (h : Invariant s ∧ RInvariant s) (hs : StepNoSecondaryId m s μ s') : Invariant s' ∧ RInvariant s' := by
  cases hs with
  | step hs _ => exact invariants_step h.1 h.2 hs
  | renew hs hn =>
    rename_i n
    obtain ⟨hi, hr⟩ := invariants_step h.1 h.2 hs
    exact ⟨hi.net_frame _ _ _ _ _ _ _, hr.clearSec n⟩

/-- **Without secondary IDs, property 1 still holds.** -/
theorem noSecondaryId_safety {m : Nat} {i : Node} {s : State Node}
    (h : (transitionSystemNoSecondaryId m).CanReach (init i) s) : Safety s :=
  let ⟨_, run⟩ := h
  invariant_safety (LTS.mtrInv_of_trInv (p := fun s => Invariant s ∧ RInvariant s)
    (fun _ _ _ hs h => invariants_stepNoSecondaryId h hs) _ _ _ run ⟨invariant_init i, rInvariant_init i⟩).1

/-! ## Without the secondary ID, PSYNC after a takeover is refused

Two nodes, `min-sync-replicas = 0`: n0 writes; n1 PSYNCs and receives the entry; n0
counts n1 and makes it eligible; n1 takes over, here without a secondary ID, and n0
learns it. n0 holds n1's whole log `[1]`, under n1's old ID. -/

section run

def ns9 := clearSec pk9 1
def ns10 := appendWrite ns9 1
def ns11 := learn ns10 0

theorem ns_run : (transitionSystemNoSecondaryId 0).MTr pk0
    [.append 0, .psync 1, .sendData 0 1, .deliver (.data 0 1 1 1 1),
     .addToSyncSet 0 1, .makeEligible 0 1, .learn 1, .takeover 1, .append 1, .learn 0] ns11 :=
  .stepL (.step (Step.append _ 0 (tp2 _ _ rfl rfl) (wr2 _ _)) rfl) <|
  .stepL (.step (Step.psync _ 1 (by decide) (by decide) (by decide)) rfl) <|
  .stepL (.step (Step.sendData _ 0 1 0 (by decide) (by decide)) rfl) <|
  .stepL (.step (Step.deliverData _ 0 1 1 1 1 (by decide) (by decide) (by decide) (by decide)) rfl) <|
  .stepL (.step (Step.addToSyncSet _ 0 1 (tp2 _ _ rfl rfl) (by decide) rfl rfl (by decide)) rfl) <|
  .stepL (.step (Step.makeEligible _ 0 1 (tp2 _ _ rfl rfl) rfl rfl rfl) rfl) <|
  .stepL (.step (Step.learn _ 1 (by unfold KnowsLatest; decide)) rfl) <|
  .stepL (.renew (Step.takeover _ 1 rfl rfl (by decide) rfl) rfl) <|
  .stepL (.step (Step.append _ 1 (tp2 _ _ rfl rfl) (wr2 _ _)) rfl) <|
  .stepL (.step (Step.learn _ 0 (by unfold KnowsLatest; decide)) rfl) <|
  .refl

/-- **Without the secondary ID, PSYNC after a takeover is refused**, though n0's log is
a prefix of n1's; with it (`pk11`, the same run in `Step`), the PSYNC is accepted. -/
theorem noSecondaryId_refuses : ∃ s, (transitionSystemNoSecondaryId 0).CanReach (init (0 : Fin 2)) s ∧
    s.log 0 <+: s.log 1 ∧ ¬ PsyncOk s 1 (s.replId 0) (s.log 0).length ∧
    PsyncOk pk11 1 (pk11.replId 0) (pk11.log 0).length :=
  ⟨ns11, ⟨_, ns_run⟩, by decide, by decide, by decide⟩

end run

end SyncReplication
