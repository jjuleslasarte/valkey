import SyncReplication.ClientProof

/-!
# Naming writes by offset and replication ID needs a fresh ID at each restart

The client layer names the write behind a log entry by the entry's offset and
replication ID (`written`, `logOps`). That is sound only if no two appends share a pair.
The replication model's restarts give the node a fresh ID (and `ClientStep.restart`
adds another), as a Valkey node takes a new ID at startup, and the linearizability proof
uses this. `ClientStepNoFreshen` is the client layer with restarts that keep every ID as
it was (`keepIds`); every other step is unchanged.

This file is about the abstraction, not about the protocol. In the run below, two
appends share the pair (offset 1, ID 1). n1's log is `[1]` before both reads, and so is
the committed history (`restartKeepsReplId_sameLog`). The reads' results differ only
because the lookup in `written` resolves the pair to the newer append. In the run's own
replication state nothing goes wrong: `NoStaleRead` holds at its end, and a log entry is
only an ID, so the two writes are the same entry there. In other runs a restart that
keeps its ID does break the replication state, under Valkey's PSYNC check
(`psyncKeepsId_unsafe`, `Counterexamples/PsyncRestartId.lean`).

The run, two nodes, `min-sync-replicas = 0`, at `wP` (`margin = 2 · drift`): n0 counts
n1 and makes it eligible, and n1 learns the configuration. Client 0 writes (operation
0); n0 appends it at offset 1 with ID 1, and n1 copies it (PSYNC, n0 streams the entry,
n1 applies it). n0 restarts from a file
that holds none of its log, keeping its incarnation and its ID. Four ticks pass and n1
takes over and commits the entry it holds. Client 1 reads from n1 (operation 1) and
gets `[0]`. n0 still thinks it is primary under its old configuration; client 0 writes
again (operation 2), and n0 appends it at offset 1 with ID 1 again. Client 1 reads from
n1 again (operation 3) and gets `[2]`. The recorded history is not linearizable
(`restartKeepsReplId_entryNamesAmbiguous`).
-/

open Cslib

namespace SyncReplication

open Lin

variable {Node : Type} [DecidableEq Node]

/-- The lease state `l` with the replication IDs (primary, secondary, used) of `a`: a
restart that leaves the IDs as they were. -/
def keepIds (a l : LeaseState Node) : LeaseState Node :=
  { l with core := { l.core with replId := a.core.replId, usedIds := a.core.usedIds, replId2 := a.core.replId2 } }

/-- `ClientStep`, except that a restart keeps the restarted node's replication ID. -/
inductive ClientStepNoFreshen (m : Nat) (P : LeaseParams) : ClientState Node → ClientAction Node → ClientState Node → Prop
  | lease (a μ l) : (hs : LeaseStep m P a.lease μ l) → (hμ : μ.isClientLease = true) →
      ClientStepNoFreshen m P a (.lease μ) (a.withLease l)
  /-- A restart; the restarted node keeps its replication ID. -/
  | restart (a μ l n) : (hs : LeaseStep m P a.lease μ l) → (hμ : μ.restarted = some n) →
      ClientStepNoFreshen m P a (.restart μ) { a with lease := keepIds a.lease l, held := dropHeld a.held n }
  | newId (a p) : ClientStepNoFreshen m P a (.newId p) { a with lease := freshen a.lease p }
  | invokeWrite (a c) : ClientStepNoFreshen m P a (.invokeWrite c)
      { a with history := a.history ++ [.inv a.nextOp c (.write a.nextOp)],
               nextOp := a.nextOp + 1, waiting := (a.nextOp, c) :: a.waiting }
  | append (a p op c) : (hw : (op, c) ∈ a.waiting) → (hp : ThinksPrimary a.lease.core p) →
      (hW : Writable m a.lease.core p) →
      ClientStepNoFreshen m P a (.append p op c)
        { a with lease := withCore a.lease (appendWrite a.lease.core p),
                 held := ⟨p, (a.lease.core.log p).length + 1, a.lease.core.replId p⟩ :: a.held,
                 written := ⟨(a.lease.core.log p).length + 1, a.lease.core.replId p, op, c⟩ :: a.written,
                 waiting := a.waiting.erase (op, c) }
  | release (a h x) : (hm : h ∈ a.held) → (hc : h.offset ≤ a.lease.core.commit h.primary) →
      (hf : ReplyFenced a.lease.core h) → (hx : entryOp a.written h.offset h.replId = some x) →
      ClientStepNoFreshen m P a (.release h)
        { a with held := a.held.erase h, acknowledged := (h.offset, h.replId) :: a.acknowledged,
                 history := a.history ++ [.res x.op x.client .ok] }
  | abort (a h) : (hm : h ∈ a.held) → (hf : ¬ ReplyFenced a.lease.core h) →
      ClientStepNoFreshen m P a (.abort h) { a with held := a.held.erase h }
  | invokeRead (a c n) : ClientStepNoFreshen m P a (.invokeRead c n)
      { a with history := a.history ++ [.inv a.nextOp c .read],
               nextOp := a.nextOp + 1, reading := (a.nextOp, c, n) :: a.reading }
  | respondRead (a op c n) : (hr : (op, c, n) ∈ a.reading) →
      (hcan : PrimCanRead P a.lease n ∨ ReplCanRead P a.lease n) →
      ClientStepNoFreshen m P a (.respondRead op c n)
        { a with history := a.history ++ [.res op c (.log (logOps a.written (a.lease.core.log n)))],
                 reading := a.reading.erase (op, c, n),
                 lin := a.lin ++ [(⟨op, c, .read, .log (logOps a.written (a.lease.core.log n))⟩,
                                   a.history.length)] }

/-- The weakened client layer as a transition system. -/
def clientTransitionSystemNoFreshen (m : Nat) (P : LeaseParams) : LTS (ClientState Node) (ClientAction Node) where
  Tr := ClientStepNoFreshen m P

/-- The states of the weakened client layer reachable from `clientInit i`. -/
def NoFreshenReachable (m : Nat) (P : LeaseParams) (i : Node) (a : ClientState Node) : Prop :=
  (clientTransitionSystemNoFreshen m P).CanReach (clientInit i) a

theorem NoFreshenReachable.stepR {m : Nat} {P : LeaseParams} {i : Node} {a a' : ClientState Node}
    {μ : ClientAction Node} (h : NoFreshenReachable m P i a) (hs : ClientStepNoFreshen m P a μ a') :
    NoFreshenReachable m P i a' :=
  let ⟨_, run⟩ := h; ⟨_, LTS.MTr.stepR (clientTransitionSystemNoFreshen m P) run hs⟩

/-! ## The run -/

section run

abbrev N2 := Fin 2

theorem thinks2 (s : State N2) (p : N2) (h1 : (s.localCfg p).primary = p)
    (h2 : (s.localCfg p).incarnation p = s.incarnation p) : ThinksPrimary s p := ⟨h1, h2⟩

theorem writable0 (s : State N2) (p : N2) : Writable 0 s p := by unfold Writable; simp

def x0 : ClientState N2 := clientInit 0
def x1 : ClientState N2 := x0.withLease (withCore x0.lease (addToSyncSet x0.lease.core 0 1))
def x2 : ClientState N2 := x1.withLease (withCore x1.lease (makeEligible x1.lease.core 0 1))
def x3 : ClientState N2 := x2.withLease (leaseLearn x2.lease 1)
def x4 : ClientState N2 :=
  { x3 with history := x3.history ++ [.inv x3.nextOp 0 (.write x3.nextOp)],
            nextOp := x3.nextOp + 1, waiting := (x3.nextOp, 0) :: x3.waiting }
def x5 : ClientState N2 :=
  { x4 with lease := withCore x4.lease (appendWrite x4.lease.core 0),
            held := ⟨0, (x4.lease.core.log 0).length + 1, x4.lease.core.replId 0⟩ :: x4.held,
            written := ⟨(x4.lease.core.log 0).length + 1, x4.lease.core.replId 0, 0, 0⟩ :: x4.written,
            waiting := x4.waiting.erase (0, 0) }
def x6a : ClientState N2 := x5.withLease (withCore x5.lease (reconnect x5.lease.core 1))
def x6b : ClientState N2 := x6a.withLease (withCore x6a.lease (streamNext x6a.lease.core 0 1 0))
def x6 : ClientState N2 :=
  x6b.withLease (withCore x6b.lease (applyData x6b.lease.core (.data 0 1 1 1 1) 1 1 1))
def x7 : ClientState N2 :=
  { x6 with lease := keepIds x6.lease (leaseRestart x6.lease 0 (restartPartialKeep x6.lease.core 0 0)),
            held := dropHeld x6.held 0 }
def x8 : ClientState N2 := x7.withLease (tick x7.lease)
def x9 : ClientState N2 := x8.withLease (tick x8.lease)
def x10 : ClientState N2 := x9.withLease (tick x9.lease)
def x11 : ClientState N2 := x10.withLease (tick x10.lease)
def x12 : ClientState N2 := x11.withLease (leaseTakeover x11.lease 1)
def x13 : ClientState N2 := x12.withLease (withCore x12.lease (commitNext x12.lease.core 1))
def x14 : ClientState N2 :=
  { x13 with history := x13.history ++ [.inv x13.nextOp 1 .read],
             nextOp := x13.nextOp + 1, reading := (x13.nextOp, 1, 1) :: x13.reading }
def x15 : ClientState N2 :=
  { x14 with history := x14.history ++ [.res 1 1 (.log (logOps x14.written (x14.lease.core.log 1)))],
             reading := x14.reading.erase (1, 1, 1),
             lin := x14.lin ++ [(⟨1, 1, .read, .log (logOps x14.written (x14.lease.core.log 1))⟩,
                                 x14.history.length)] }
def x16 : ClientState N2 :=
  { x15 with history := x15.history ++ [.inv x15.nextOp 0 (.write x15.nextOp)],
             nextOp := x15.nextOp + 1, waiting := (x15.nextOp, 0) :: x15.waiting }
def x17 : ClientState N2 :=
  { x16 with lease := withCore x16.lease (appendWrite x16.lease.core 0),
             held := ⟨0, (x16.lease.core.log 0).length + 1, x16.lease.core.replId 0⟩ :: x16.held,
             written := ⟨(x16.lease.core.log 0).length + 1, x16.lease.core.replId 0, 2, 0⟩ :: x16.written,
             waiting := x16.waiting.erase (2, 0) }
def x18 : ClientState N2 :=
  { x17 with history := x17.history ++ [.inv x17.nextOp 1 .read],
             nextOp := x17.nextOp + 1, reading := (x17.nextOp, 1, 1) :: x17.reading }
def x19 : ClientState N2 :=
  { x18 with history := x18.history ++ [.res 3 1 (.log (logOps x18.written (x18.lease.core.log 1)))],
             reading := x18.reading.erase (3, 1, 1),
             lin := x18.lin ++ [(⟨3, 1, .read, .log (logOps x18.written (x18.lease.core.log 1))⟩,
                                 x18.history.length)] }

/-- n1 may serve a linearizable read: it is primary and knows no eligible replica. -/
theorem canRead (a : ClientState N2) (h1 : (a.lease.core.localCfg 1).primary = 1)
    (h2 : (a.lease.core.localCfg 1).incarnation 1 = a.lease.core.incarnation 1)
    (h3 : ∀ r, (a.lease.core.localCfg 1).eligible r = false)
    (h4 : a.lease.core.commit 1 = (a.lease.core.log 1).length) : PrimCanRead wP a.lease 1 :=
  ⟨⟨h1, h2⟩, fun r hr _ => by rw [h3 r] at hr; exact absurd hr (by decide), h4⟩

theorem x19_reachable : NoFreshenReachable 0 wP (0 : N2) x19 := by
  have r0 : NoFreshenReachable 0 wP (0 : N2) x0 := LTS.CanReach.refl _ _
  have r1 := r0.stepR (ClientStepNoFreshen.lease x0 (.core (.addToSyncSet 0 1)) _
    (LeaseStep.core _ _ _ (Step.addToSyncSet _ 0 1 (thinks2 _ _ rfl rfl) (by decide) rfl rfl (by decide)) rfl) rfl)
  have r2 := r1.stepR (ClientStepNoFreshen.lease x1 (.core (.makeEligible 0 1)) _
    (LeaseStep.core _ _ _ (Step.makeEligible _ 0 1 (thinks2 _ _ rfl rfl) rfl rfl rfl) rfl) rfl)
  have r3 := r2.stepR (ClientStepNoFreshen.lease x2 (.learn 1) _
    (LeaseStep.learn _ 1 (by unfold KnowsLatest; decide)) rfl)
  have r4 := r3.stepR (ClientStepNoFreshen.invokeWrite x3 0)
  have r5 := r4.stepR (ClientStepNoFreshen.append x4 0 0 0 (by decide) (thinks2 _ _ rfl rfl) (writable0 _ _))
  have r6a := r5.stepR (ClientStepNoFreshen.lease x5 (.core (.psync 1)) _
    (LeaseStep.core _ _ _ (Step.psync _ 1 (by decide) (by decide) (by decide)) rfl) rfl)
  have r6b := r6a.stepR (ClientStepNoFreshen.lease x6a (.core (.sendData 0 1)) _
    (LeaseStep.core _ _ _ (Step.sendData _ 0 1 0 (by decide) (by decide)) rfl) rfl)
  have r6 := r6b.stepR (ClientStepNoFreshen.lease x6b (.core (.deliver (.data 0 1 1 1 1))) _
    (LeaseStep.core _ _ _ (Step.deliverData _ 0 1 1 1 1 (by decide) (by decide) (by decide) rfl) rfl) rfl)
  have r7 := r6.stepR (ClientStepNoFreshen.restart x6 (.restartPartial 0 0) _ 0
    (LeaseStep.restartPartialKeep _ 0 0 rfl (by decide) (by decide)) rfl)
  have r8 := r7.stepR (ClientStepNoFreshen.lease x7 .tick _ (LeaseStep.tick _) rfl)
  have r9 := r8.stepR (ClientStepNoFreshen.lease x8 .tick _ (LeaseStep.tick _) rfl)
  have r10 := r9.stepR (ClientStepNoFreshen.lease x9 .tick _ (LeaseStep.tick _) rfl)
  have r11 := r10.stepR (ClientStepNoFreshen.lease x10 .tick _ (LeaseStep.tick _) rfl)
  have r12 := r11.stepR (ClientStepNoFreshen.lease x11 (.takeover 1) _
    (LeaseStep.takeover _ 1 rfl rfl (by decide) rfl (by decide)) rfl)
  have r13 := r12.stepR (ClientStepNoFreshen.lease x12 (.core (.commit 1)) _
    (LeaseStep.core _ _ _ (Step.commit _ 1 (thinks2 _ _ rfl rfl) (writable0 _ _) (by decide)
      (fun r h => by revert r; decide)) rfl) rfl)
  have r14 := r13.stepR (ClientStepNoFreshen.invokeRead x13 1 1)
  have r15 := r14.stepR (ClientStepNoFreshen.respondRead x14 1 1 1 (by decide)
    (Or.inl (canRead _ rfl rfl (by decide) (by decide))))
  have r16 := r15.stepR (ClientStepNoFreshen.invokeWrite x15 0)
  have r17 := r16.stepR (ClientStepNoFreshen.append x16 0 2 0 (by decide) (thinks2 _ _ rfl rfl) (writable0 _ _))
  have r18 := r17.stepR (ClientStepNoFreshen.invokeRead x17 1 1)
  exact r18.stepR (ClientStepNoFreshen.respondRead x18 3 1 1 (by decide)
    (Or.inl (canRead _ rfl rfl (by decide) (by decide))))

/-- Between the two reads, n1's log and the committed history are both `[1]`; only the
lookup of the entry (offset 1, ID 1) in `written` changes, from operation 0 to
operation 2. -/
theorem restartKeepsReplId_sameLog :
    x14.lease.core.log 1 = [1] ∧ x18.lease.core.log 1 = [1] ∧
    x14.lease.core.hist = [1] ∧ x18.lease.core.hist = [1] ∧
    logOps x14.written [1] = [0] ∧ logOps x18.written [1] = [2] := by decide

/-- The run's client history. -/
def badHistory : ClientHistory :=
  [.inv 0 0 (.write 0), .inv 1 1 .read, .res 1 1 (.log [0]),
   .inv 2 0 (.write 2), .inv 3 1 .read, .res 3 1 (.log [2])]

theorem x19_history : x19.history = badHistory := by decide

/-- The two reads disagree on the write at offset 1, so the history is not linearizable. -/
theorem badHistory_not_linearizable : ¬ Linearizable LogLegal badHistory := by
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

/-- At the end of the run no node may serve a stale read: n1, the only node that may
read, holds the committed history. -/
theorem x19_noStaleRead : NoStaleRead wP x19.lease := by
  unfold NoStaleRead PrimCanRead ReplCanRead PrimLeaseValid ReadLeaseValid ThinksPrimary; decide

/-- In the client layer whose restarts keep the node's ID, the history it records can fail
to be linearizable, with `margin ≥ 2 · drift`, while `NoStaleRead` holds. The cause is
the naming of writes, not the replication state (`restartKeepsReplId_sameLog`). -/
theorem restartKeepsReplId_entryNamesAmbiguous : ∃ a : ClientState N2,
    NoFreshenReachable 0 wP 0 a ∧ 2 * wP.drift ≤ wP.margin ∧
    ¬ Linearizable LogLegal a.history ∧ NoStaleRead wP a.lease :=
  ⟨x19, x19_reachable, by decide, by rw [x19_history]; exact badHistory_not_linearizable,
   x19_noStaleRead⟩

end run

end SyncReplication
