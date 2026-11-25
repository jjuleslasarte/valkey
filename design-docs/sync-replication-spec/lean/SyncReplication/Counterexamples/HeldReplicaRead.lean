import SyncReplication.ClientNaming

/-!
# A held read on a replica needs the replication-ID check

The client layer holds a read on a replica that holds a read lease and has entries it has
not been told are committed (`ClientStep.holdRead`, the whole-keyspace form of
dirty key tracking), and releases it once the replica's committed view reaches the
read's offset, and only while the replica still has the replication ID it had when the
read ran (`ClientStep.releaseRead`; design doc, "Execute immediately, hold the reply").
`ClientStepNoReadFence` is the client layer plus a release without that replication-ID
check; every other step is unchanged.

The run, two nodes, `min-sync-replicas = 0`, at `wP` (primary lease 5, read lease 3,
drift 1, margin 2, so `margin = 2 · drift`):

1. n0 counts n1 and makes it eligible; n1 learns the configuration.
2. Client 0 writes (operation 0). n0 appends it at offset 1, and n1 copies it (PSYNC,
   n0 streams the entry, n1 applies it). Nothing is committed.
3. n1 acknowledges; n0 echoes the acknowledgement, and n1 holds a read lease.
4. Client 1 reads from n1 (operation 1). n1 holds a read lease and has an uncommitted
   entry, so it runs the read against its log `[op 0]` and holds the reply at offset 1.
5. n0 restarts from a file holding none of its log. It keeps its incarnation (it has
   acknowledged nothing as a replica, so `ackHigh 0 = 0`) and takes a fresh replication
   ID.
6. Four ticks pass, and n0, as a restarted primary, demotes n1 (its read lease has
   expired).
7. Client 0 writes again (operation 2). n0 appends it at offset 1 and commits it alone.
8. n1 is fully resynced from n0 (its log is now `[op 2]`, with n0's new ID), reconnects
   with PSYNC, and receives n0's `REPLCONF COMMIT` for offset 1: its committed view is 1.
9. n1 releases the held read: offset 1 is now committed on n1. The reply is `[0]`, the
   write that was lost.
10. Client 1 reads from n0 (operation 3) and gets `[2]`.

The released read returns a write the committed history lacks
(`heldReadNoFence_returnsLost`), and the recorded history is not linearizable
(`heldReadNoFence_unsafe`): read 1 responded with `[0]` before read 3 was invoked, and
read 3 returned `[2]`. With the ID check, n1's replication ID changed at the resync
(step 8), so the read would be answered `UNCOMMITTED` instead.

The same failure occurs at `min-sync-replicas = 1` (`heldReadNoFence_unsafe_minSync1`, 38
steps). After the demotion n0 cannot write until it counts an eligible replica again, so
n1 is resynced first, to n0's empty log, reconnects, and is counted and made eligible
again. n0 then appends operation 2 at offset 1, n1 copies and acknowledges it, and n0
commits it. n1 learns that offset 1 is committed and releases the held read with `[0]`;
after n1 acknowledges again, n0 holds its lease from n1 and answers read 3 with `[2]`.
-/

open Cslib

namespace SyncReplication

open Lin

variable {Node : Type} [DecidableEq Node]

/-- `ClientStep`, plus a release of a held replica read once the replica's committed view
reaches its offset, with no check of the replication ID. -/
inductive ClientStepNoReadFence (m : Nat) (P : LeaseParams) : ClientState Node → ClientAction Node → ClientState Node → Prop
  | step {a μ a'} : ClientStep m P a μ a' → ClientStepNoReadFence m P a μ a'
  /-- A held read is released once the replica's committed view reaches its offset. No
  check of the replication ID. -/
  | releaseRead (a g) : (hm : g ∈ a.heldReads) →
      (hc : g.offset ≤ a.lease.committedView g.node) →
      ClientStepNoReadFence m P a (.releaseRead g)
        { a with history := a.history ++ [(g.toOp a.written).res], heldReads := a.heldReads.erase g }

/-- The weakened layer as a transition system. -/
def clientTransitionSystemNoReadFence (m : Nat) (P : LeaseParams) : LTS (ClientState Node) (ClientAction Node) where
  Tr := ClientStepNoReadFence m P

/-- The states of the weakened layer reachable from `clientInit i`. -/
def NoReadFenceReachable (m : Nat) (P : LeaseParams) (i : Node) (a : ClientState Node) : Prop :=
  (clientTransitionSystemNoReadFence m P).CanReach (clientInit i) a

theorem NoReadFenceReachable.stepR {m : Nat} {P : LeaseParams} {i : Node} {a a' : ClientState Node}
    {μ : ClientAction Node} (h : NoReadFenceReachable m P i a) (hs : ClientStepNoReadFence m P a μ a') :
    NoReadFenceReachable m P i a' :=
  let ⟨_, run⟩ := h; ⟨_, LTS.MTr.stepR (clientTransitionSystemNoReadFence m P) run hs⟩

/-! ## The run -/

section run

/-- The run's client history. -/
def hrBadHistory : ClientHistory :=
  [.inv 0 0 (.write 0), .inv 1 1 .read, .inv 2 0 (.write 2), .res 1 1 (.log [0]),
   .inv 3 1 .read, .res 3 1 (.log [2])]

/-- Read 1 returned `[0]` and responded before read 3 was invoked; read 3 returned `[2]`.
No sequential order of the log specification has both. -/
theorem hrBadHistory_not_linearizable : ¬ Linearizable LogLegal hrBadHistory := by
  rintro ⟨_, ⟨rs, rfl, -, -⟩, S, hp, hl, hrt⟩
  have h1 : (⟨1, 1, .read, .log [0]⟩ : ClientOp) ∈ S := hp.mem_iff.2 (mem_complete_append (by decide))
  have h3 : (⟨3, 1, .read, .log [2]⟩ : ClientOp) ∈ S := hp.mem_iff.2 (mem_complete_append (by decide))
  obtain ⟨u1, u2, hS, hr1⟩ := split_of_pair (hrt _ h1 _ h3 (by decide))
  obtain ⟨t1, t2, ht⟩ := List.append_of_mem hr1
  have e3 := hl.split (s₁ := u1.map Operation.call) (s₂ := u2.map Operation.call)
    (c := (⟨3, 1, .read, .log [2]⟩ : ClientOp).call) (by simp [hS])
  have e1 := hl.split (s₁ := t1.map Operation.call) (s₂ := (t2 ++ (⟨3, 1, .read, .log [2]⟩ : ClientOp) :: u2).map Operation.call)
    (c := (⟨1, 1, .read, .log [0]⟩ : ClientOp).call) (by simp [hS, ht])
  rw [ht] at e3
  simp only [Operation.call, answer, LogRes.log.injEq, List.map_append, List.map_cons, writes_append] at e1 e3
  rw [← e1] at e3
  simp [writes] at e3

/-- The held read of the run. -/
def hrRead : HeldRead N2 := ⟨1, 1, 1, 1, 1, [1]⟩

theorem hrDemoteWait (a : LeaseState N2) (h : a.primarySince 0 = some 0) (hn : a.now = 4) :
    ∀ T, a.primarySince 0 = some T → a.oldEligible 0 1 = true →
      T + wP.readDur + wP.margin ≤ a.now + wP.drift := by
  intro T hT _; rw [h] at hT; cases hT; rw [hn]; decide

/-- The run reaches a state whose history is `hrBadHistory`, in which the committed
history holds the write of operation 2 and not that of operation 0. -/
theorem hr_run : ∃ a : ClientState N2, NoReadFenceReachable 0 wP 0 a ∧
    a.history = hrBadHistory ∧ logOps a.written a.lease.core.hist = [2] := by
  have r0 : NoReadFenceReachable 0 wP (0 : N2) (clientInit 0) := LTS.CanReach.refl _ _
  -- 1. n0 counts n1 and makes it eligible; n1 learns the configuration.
  have r1 := r0.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.addToSyncSet 0 1)) _
    (LeaseStep.core _ _ _ (Step.addToSyncSet _ 0 1 (thinks2 _ _ rfl rfl) (by decide) rfl rfl (by decide)) rfl) rfl))
  have r2 := r1.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.makeEligible 0 1)) _
    (LeaseStep.core _ _ _ (Step.makeEligible _ 0 1 (thinks2 _ _ rfl rfl) rfl rfl rfl) rfl) rfl))
  have r2b := r2.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.learn 0) _
    (LeaseStep.learn _ 0 (by unfold KnowsLatest; decide)) rfl))
  have r3 := r2b.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.learn 1) _
    (LeaseStep.learn _ 1 (by unfold KnowsLatest; decide)) rfl))
  -- 2. Client 0 writes; n0 appends it and n1 copies it.
  have r4 := r3.stepR (ClientStepNoReadFence.step (ClientStep.invokeWrite _ 0))
  have r5 := r4.stepR (ClientStepNoReadFence.step
    (ClientStep.append _ 0 0 0 (by decide) (thinks2 _ _ rfl rfl) (writable0 _ _)))
  have r6 := r5.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.psync 1)) _
    (LeaseStep.core _ _ _ (Step.psync _ 1 (by decide) (by decide) (by decide)) rfl) rfl))
  have r7 := r6.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.sendData 0 1)) _
    (LeaseStep.core _ _ _ (Step.sendData _ 0 1 0 (by decide) (by decide)) rfl) rfl))
  have r8 := r7.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.deliver (.data 0 1 1 1 1))) _
    (LeaseStep.core _ _ _ (Step.deliverData _ 0 1 1 1 1 (by decide) (by decide) (by decide) rfl) rfl) rfl))
  -- 3. n1 acknowledges, n0 echoes it: n1 holds a read lease.
  have r9 := r8.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.sendAck 1) _
    (LeaseStep.sendAck _ 1 (by decide)) rfl))
  have r10 := r9.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.deliver (.ack 1 0 0 0 0)) _
    (LeaseStep.deliverAck _ 1 0 0 0 0 (by decide) (by decide)) rfl))
  have r11 := r10.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.sendData 0 1) _
    (LeaseStep.sendGrant _ 0 1 (by decide) (by decide) (thinks2 _ _ rfl rfl)
      (by unfold MayGrant PrimLeaseValid; decide)) rfl))
  have r12 := r11.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.deliver (.data 0 1 0 0 0 (some 0))) _
    (LeaseStep.deliverData _ 0 1 0 0 0 (some 0) (by decide) (by decide) (by decide) (by decide)) rfl))
  -- 4. Client 1 reads from n1; n1 holds the read.
  have r13 := r12.stepR (ClientStepNoReadFence.step (ClientStep.invokeRead _ 1 1))
  have r14 := r13.stepR (ClientStepNoReadFence.step (ClientStep.holdRead _ 1 1 1 (by decide)
    (by unfold ThinksPrimary; decide) (by unfold ReadLeaseValid; decide) (by decide)))
  -- 5. n0 restarts from a file holding none of its log, with a fresh ID.
  have r15 := r14.stepR (ClientStepNoReadFence.step (ClientStep.restart _ (.restartPartial 0 0) _ 0
    (LeaseStep.restartPartialKeep _ 0 0 rfl (by decide) (by decide)) rfl))
  -- 6. Four ticks; n0 demotes n1.
  have r16 := r15.stepR (ClientStepNoReadFence.step (ClientStep.lease _ .tick _ (LeaseStep.tick _) rfl))
  have r17 := r16.stepR (ClientStepNoReadFence.step (ClientStep.lease _ .tick _ (LeaseStep.tick _) rfl))
  have r18 := r17.stepR (ClientStepNoReadFence.step (ClientStep.lease _ .tick _ (LeaseStep.tick _) rfl))
  have r19 := r18.stepR (ClientStepNoReadFence.step (ClientStep.lease _ .tick _ (LeaseStep.tick _) rfl))
  have r20 := r19.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.demote 0 1) _
    (LeaseStep.demote _ 0 1 (thinks2 _ _ rfl rfl) (by unfold KnowsLatest; decide) (by decide)
      (Or.inl ⟨by decide, hrDemoteWait _ (by decide) (by decide)⟩)) rfl))
  -- 7. Client 0 writes again; n0 appends it at offset 1 and commits it alone.
  have r21 := r20.stepR (ClientStepNoReadFence.step (ClientStep.invokeWrite _ 0))
  have r22 := r21.stepR (ClientStepNoReadFence.step
    (ClientStep.append _ 0 2 0 (by decide) (thinks2 _ _ rfl rfl) (writable0 _ _)))
  have r23 := r22.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.commit 0)) _
    (LeaseStep.core _ _ _ (Step.commit _ 0 (thinks2 _ _ rfl rfl) (writable0 _ _) (by decide)
      (fun r h => by revert r; decide)) rfl) rfl))
  -- 8. n1 is fully resynced, reconnects, and learns that offset 1 is committed.
  have r24 := r23.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.resync 1) _
    (LeaseStep.resync _ 1 (by decide) (by decide) (by decide)) rfl))
  have r25 := r24.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.psync 1)) _
    (LeaseStep.core _ _ _ (Step.psync _ 1 (by decide) (by decide) (by decide)) rfl) rfl))
  have r26 := r25.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.sendData 0 1) _
    (LeaseStep.sendData _ 0 1 (by decide) (by decide)) rfl))
  have r27 := r26.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.deliver (.data 0 1 2 4 1 none)) _
    (LeaseStep.deliverData _ 0 1 2 4 1 none (by decide) (by decide) (by decide) (by decide)) rfl))
  -- 9. n1 releases the held read: `[0]`.
  have r28 := r27.stepR (ClientStepNoReadFence.releaseRead _ hrRead (by decide) (by decide))
  -- 10. Client 1 reads from n0 and gets `[2]`.
  have r29 := r28.stepR (ClientStepNoReadFence.step (ClientStep.invokeRead _ 1 0))
  have r30 := r29.stepR (ClientStepNoReadFence.step (ClientStep.respondRead _ 3 1 0 (by decide)
    (Or.inl ⟨thinks2 _ _ rfl rfl, by unfold PrimLeaseValid; decide, by decide⟩)))
  exact ⟨_, r30, by decide, by decide⟩

/-- In the client layer with held replica reads released on the committed offset alone,
a released read returns a write that is not in the committed history: the reply is
`[0]`, while the committed history is the write of operation 2 alone. -/
theorem heldReadNoFence_returnsLost : ∃ a : ClientState N2, NoReadFenceReachable 0 wP 0 a ∧
    Event.res 1 1 (.log [0]) ∈ a.history ∧ 0 ∉ logOps a.written a.lease.core.hist := by
  obtain ⟨a, ha, hh, hc⟩ := hr_run
  exact ⟨a, ha, by rw [hh]; decide, by rw [hc]; decide⟩

/-- Without the replication-ID check on release, a held replica read makes the client
history non-linearizable, with `margin ≥ 2 · drift`. -/
theorem heldReadNoFence_unsafe : ∃ a : ClientState N2, NoReadFenceReachable 0 wP 0 a ∧
    2 * wP.drift ≤ wP.margin ∧ ¬ Linearizable LogLegal a.history := by
  obtain ⟨a, ha, hh, -⟩ := hr_run
  exact ⟨a, ha, by decide, by rw [hh]; exact hrBadHistory_not_linearizable⟩

/-- `Writable 1` from one counted replica. -/
theorem writable1 {s : State N2} {p r : N2} (hs : s.sync p r = true)
    (he : (s.localCfg p).eligible r = true) (hi : (s.localCfg p).incarnation r = s.incarnation r) : Writable 1 s p :=
  (writable_iff_list 1 s p).2 ⟨[r], List.nodup_singleton r, by simp, by simp [hs, he, hi]⟩

/-- The same failure at `min-sync-replicas = 1`: after the demotion, n1 is resynced to
n0's empty log and counted again before n0 writes, so the second write commits with n1's
acknowledgement. The run reaches a state whose history is `hrBadHistory`. -/
theorem hr_run1 : ∃ a : ClientState N2, NoReadFenceReachable 1 wP 0 a ∧
    a.history = hrBadHistory ∧ logOps a.written a.lease.core.hist = [2] := by
  have r0 : NoReadFenceReachable 1 wP (0 : N2) (clientInit 0) := LTS.CanReach.refl _ _
  -- 1-4 as in `hr_run`: n0 counts n1 and makes it eligible, writes operation 0, n1 copies
  -- it and gets a read lease, and n1 holds a read of `[op 0]` at offset 1.
  have r1 := r0.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.addToSyncSet 0 1)) _
    (LeaseStep.core _ _ _ (Step.addToSyncSet _ 0 1 (thinks2 _ _ rfl rfl) (by decide) rfl rfl (by decide)) rfl) rfl))
  have r2 := r1.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.makeEligible 0 1)) _
    (LeaseStep.core _ _ _ (Step.makeEligible _ 0 1 (thinks2 _ _ rfl rfl) rfl rfl rfl) rfl) rfl))
  have r2b := r2.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.learn 0) _
    (LeaseStep.learn _ 0 (by unfold KnowsLatest; decide)) rfl))
  have r3 := r2b.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.learn 1) _
    (LeaseStep.learn _ 1 (by unfold KnowsLatest; decide)) rfl))
  have r4 := r3.stepR (ClientStepNoReadFence.step (ClientStep.invokeWrite _ 0))
  have r5 := r4.stepR (ClientStepNoReadFence.step
    (ClientStep.append _ 0 0 0 (by decide) (thinks2 _ _ rfl rfl) (writable1 (r := 1) (by decide) (by decide) (by decide))))
  have r6 := r5.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.psync 1)) _
    (LeaseStep.core _ _ _ (Step.psync _ 1 (by decide) (by decide) (by decide)) rfl) rfl))
  have r7 := r6.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.sendData 0 1)) _
    (LeaseStep.core _ _ _ (Step.sendData _ 0 1 0 (by decide) (by decide)) rfl) rfl))
  have r8 := r7.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.deliver (.data 0 1 1 1 1))) _
    (LeaseStep.core _ _ _ (Step.deliverData _ 0 1 1 1 1 (by decide) (by decide) (by decide) rfl) rfl) rfl))
  have r9 := r8.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.sendAck 1) _
    (LeaseStep.sendAck _ 1 (by decide)) rfl))
  have r10 := r9.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.deliver (.ack 1 0 0 0 0)) _
    (LeaseStep.deliverAck _ 1 0 0 0 0 (by decide) (by decide)) rfl))
  have r11 := r10.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.sendData 0 1) _
    (LeaseStep.sendGrant _ 0 1 (by decide) (by decide) (thinks2 _ _ rfl rfl)
      (by unfold MayGrant PrimLeaseValid; decide)) rfl))
  have r12 := r11.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.deliver (.data 0 1 0 0 0 (some 0))) _
    (LeaseStep.deliverData _ 0 1 0 0 0 (some 0) (by decide) (by decide) (by decide) (by decide)) rfl))
  have r13 := r12.stepR (ClientStepNoReadFence.step (ClientStep.invokeRead _ 1 1))
  have r14 := r13.stepR (ClientStepNoReadFence.step (ClientStep.holdRead _ 1 1 1 (by decide)
    (by unfold ThinksPrimary; decide) (by unfold ReadLeaseValid; decide) (by decide)))
  -- 5-6 as in `hr_run`: n0 restarts from a file holding none of its log, and demotes n1.
  have r15 := r14.stepR (ClientStepNoReadFence.step (ClientStep.restart _ (.restartPartial 0 0) _ 0
    (LeaseStep.restartPartialKeep _ 0 0 rfl (by decide) (by decide)) rfl))
  have r16 := r15.stepR (ClientStepNoReadFence.step (ClientStep.lease _ .tick _ (LeaseStep.tick _) rfl))
  have r17 := r16.stepR (ClientStepNoReadFence.step (ClientStep.lease _ .tick _ (LeaseStep.tick _) rfl))
  have r18 := r17.stepR (ClientStepNoReadFence.step (ClientStep.lease _ .tick _ (LeaseStep.tick _) rfl))
  have r19 := r18.stepR (ClientStepNoReadFence.step (ClientStep.lease _ .tick _ (LeaseStep.tick _) rfl))
  have r20 := r19.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.demote 0 1) _
    (LeaseStep.demote _ 0 1 (thinks2 _ _ rfl rfl) (by unfold KnowsLatest; decide) (by decide)
      (Or.inl ⟨by decide, hrDemoteWait _ (by decide) (by decide)⟩)) rfl))
  -- 7. n1 is fully resynced to n0's empty log, reconnects, and is counted and made
  -- eligible again, so n0 is writable at `min-sync-replicas = 1`.
  have r21 := r20.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.resync 1) _
    (LeaseStep.resync _ 1 (by decide) (by decide) (by decide)) rfl))
  have r22 := r21.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.psync 1)) _
    (LeaseStep.core _ _ _ (Step.psync _ 1 (by decide) (by decide) (by decide)) rfl) rfl))
  have r23 := r22.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.addToSyncSet 0 1)) _
    (LeaseStep.core _ _ _ (Step.addToSyncSet _ 0 1 (thinks2 _ _ rfl rfl) (by decide) (by decide) (by decide) (by decide)) rfl) rfl))
  have r24 := r23.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.makeEligible 0 1)) _
    (LeaseStep.core _ _ _ (Step.makeEligible _ 0 1 (thinks2 _ _ rfl rfl) (by unfold KnowsLatest; decide) (by decide) (by decide)) rfl) rfl))
  have r24b := r24.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.learn 0) _
    (LeaseStep.learn _ 0 (by unfold KnowsLatest; decide)) rfl))
  -- 8. Client 0 writes again; n0 appends it at offset 1, n1 copies and acknowledges it, and
  -- n0 commits it.
  have r25 := r24b.stepR (ClientStepNoReadFence.step (ClientStep.invokeWrite _ 0))
  have r26 := r25.stepR (ClientStepNoReadFence.step
    (ClientStep.append _ 0 2 0 (by decide) (thinks2 _ _ rfl rfl) (writable1 (r := 1) (by decide) (by decide) (by decide))))
  have r27 := r26.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.sendData 0 1)) _
    (LeaseStep.core _ _ _ (Step.sendData _ 0 1 0 (by decide) (by decide)) rfl) rfl))
  have r28 := r27.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.deliver (.data 0 1 4 3 3))) _
    (LeaseStep.core _ _ _ (Step.deliverData _ 0 1 4 3 3 (by decide) (by decide) (by decide) rfl) rfl) rfl))
  have r29 := r28.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.sendAck 1)) _
    (LeaseStep.core _ _ _ (Step.sendAck _ 1 (by decide)) rfl) rfl))
  have r30 := r29.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.deliver (.ack 1 0 4 1))) _
    (LeaseStep.core _ _ _ (Step.deliverAck _ 1 0 4 1 1 (by decide) (by decide) (by decide) (by decide)) rfl) rfl))
  have r31 := r30.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.core (.commit 0)) _
    (LeaseStep.core _ _ _ (Step.commit _ 0 (thinks2 _ _ rfl rfl) (writable1 (r := 1) (by decide) (by decide) (by decide)) (by decide)
      (fun r h => by revert r; decide)) rfl) rfl))
  -- 9. n1 learns that offset 1 is committed, and releases the held read: `[0]`.
  have r32 := r31.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.sendData 0 1) _
    (LeaseStep.sendData _ 0 1 (by decide) (by decide)) rfl))
  have r33 := r32.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.deliver (.data 0 1 2 4 1 none)) _
    (LeaseStep.deliverData _ 0 1 2 4 1 none (by decide) (by decide) (by decide) (by decide)) rfl))
  have r34 := r33.stepR (ClientStepNoReadFence.releaseRead _ hrRead (by decide) (by decide))
  -- 10. n1 acknowledges, so n0 holds its lease from n1; client 1 reads from n0 and gets `[2]`.
  have r35 := r34.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.sendAck 1) _
    (LeaseStep.sendAck _ 1 (by decide)) rfl))
  have r36 := r35.stepR (ClientStepNoReadFence.step (ClientStep.lease _ (.deliver (.ack 1 0 2 4 4)) _
    (LeaseStep.deliverAck _ 1 0 2 4 4 (by decide) (by decide)) rfl))
  have r37 := r36.stepR (ClientStepNoReadFence.step (ClientStep.invokeRead _ 1 0))
  have r38 := r37.stepR (ClientStepNoReadFence.step (ClientStep.respondRead _ 3 1 0 (by decide)
    (Or.inl ⟨thinks2 _ _ rfl rfl, by unfold PrimLeaseValid; decide, by decide⟩)))
  exact ⟨_, r38, by decide, by decide⟩


/-- At `min-sync-replicas = 1` too, without the replication-ID check on release, a held
replica read returns a write that is not in the committed history, and the client history
is not linearizable, with `margin ≥ 2 · drift`. -/
theorem heldReadNoFence_unsafe_minSync1 : ∃ a : ClientState N2, NoReadFenceReachable 1 wP 0 a ∧
    2 * wP.drift ≤ wP.margin ∧ Event.res 1 1 (.log [0]) ∈ a.history ∧
      0 ∉ logOps a.written a.lease.core.hist ∧ ¬ Linearizable LogLegal a.history := by
  obtain ⟨a, ha, hh, hc⟩ := hr_run1
  exact ⟨a, ha, by decide, by rw [hh]; decide, by rw [hc]; decide, by rw [hh]; exact hrBadHistory_not_linearizable⟩

end run

end SyncReplication
