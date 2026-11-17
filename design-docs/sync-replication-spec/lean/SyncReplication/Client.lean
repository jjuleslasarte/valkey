import SyncReplication.LeaseInvariant
import SyncReplication.Durability
import SyncReplication.Linearizable

/-!
# The client layer

The lease layer (`LeaseState`, which holds the replication state) plus the reply layer's
held replies, plus the clients: a history of invocation and response events
(`Lin.Event`), as `ReplyState` wraps `State`. Every client step is a lease step, a
reply step, both, or neither (for the events alone), so the lease and reply
invariants carry over unchanged.

## How a client history is recorded

- A client is a process, numbered by `Nat`; operation ids come from one counter
  (`nextOp`).
- **Writes.** `invokeWrite c` records `inv i c (write i)`: the value written is the
  operation id. `append p i c` is the primary `p` appending it (the reply layer's
  `write`, with its guards), which holds a reply. `release h` is the reply layer's
  release, and records `res i c ok`. `abort h` is the reply layer's abort: the client
  is told UNCOMMITTED, and no response event is recorded. A held reply dropped by a
  restart gets no response either. Both stay pending for ever.
- **Reads.** `invokeRead c n` records `inv i c read`, sent to node `n`. `respondRead
  i c n`, once `n` may serve a linearizable read (`PrimCanRead` or `ReplCanRead`),
  records `res i c (log ids)`, where `ids` is `n`'s log as operation ids.
- **Which write an entry is.** A log entry is the replication ID it was written with,
  and the model identifies a write by its offset and that ID (`Model.lean`). `written`
  records, for each append, the entry's offset and ID and the operation that made it;
  a read turns each entry of `n`'s log into that operation's id (`logOps`). No two
  appends share an offset and ID (`ClientInvariant.keysNodup` in `ClientProof.lean`),
  so this names the write that made the entry, not just an equal value.
- **Restarts take a fresh replication ID.** A restart here is the lease layer's restart
  followed by the reply layer's `newId` on the restarted node, as a Valkey primary
  takes a new ID at startup (README §5). Without it, a primary restored from a short
  file could append a second write at an offset and ID that a replica already holds
  from the first, and the two would be indistinguishable.
- **Every log entry is a client write.** The lease layer's `core (append p)` is not a
  client step; appends happen only through `append`.

`lin` is a ghost variable, like `hist`: the operations linearized so far, each with the
history length at its linearization point. A write is linearized when its entry joins
the committed history, a read when it responds.
-/

open Cslib

namespace SyncReplication

open Lin

/-- An appended write: its entry's offset (1-based) and replication ID, and the client
operation and client it came from. -/
structure Written where
  offset : Nat
  replId : Nat
  op : Nat
  client : Nat
  deriving DecidableEq, Repr

/-- Client histories: clients are numbered, values are operation ids. -/
abbrev ClientHistory := History Nat (LogOp Nat) (LogRes Nat)

/-- A client operation. -/
abbrev ClientOp := Operation Nat (LogOp Nat) (LogRes Nat)

/-- The completed write operation of an appended write. -/
def Written.toOp (x : Written) : ClientOp := ⟨x.op, x.client, .write x.op, .ok⟩

variable {Node : Type} [DecidableEq Node]

/-- The lease and reply layers plus the clients. -/
structure ClientState (Node : Type) [DecidableEq Node] where
  /-- The lease layer, which holds the replication state. -/
  lease : LeaseState Node
  /-- The replies not yet released or aborted (as `ReplyState.held`). -/
  held : List (Held Node)
  /-- The `(offset, value)` pairs released as OK (as `ReplyState.acknowledged`). -/
  acknowledged : List (Nat × Nat)
  /-- The client history, oldest event first. -/
  history : ClientHistory
  /-- The next operation id. -/
  nextOp : Nat
  /-- Every append so far, newest first. -/
  written : List Written
  /-- Writes invoked and not yet appended: (operation, client). -/
  waiting : List (Nat × Nat)
  /-- Reads invoked and not yet answered: (operation, client, node). -/
  reading : List (Nat × Nat × Node)
  /-- Ghost variable: the operations linearized so far, in order, each with the
  history length at its linearization point. -/
  lin : List (ClientOp × Nat)

/-- The reply layer inside a client state. -/
def ClientState.reply (a : ClientState Node) : ReplyState Node :=
  ⟨a.lease.core, a.held, a.acknowledged⟩

/-- The append that made the entry `v` at offset `o`, if any. -/
def entryOp (w : List Written) (o v : Nat) : Option Written :=
  w.find? fun x => x.offset == o && x.replId == v

/-- The append that made the entry `v` at offset `o`, or a placeholder with operation 0 if
there is none (the proof shows there always is). -/
def entryOf (w : List Written) (o v : Nat) : Written := (entryOp w o v).getD ⟨o, v, 0, 0⟩

/-- A log as operation ids: each entry, at its offset, as the operation that appended it. -/
def logOps (w : List Written) (L : List Nat) : List Nat :=
  (L.zipIdx 1).map fun e => (entryOf w e.2 e.1).op

/-- The writes linearized when the committed history grows from `old` to `new`: the
operation of each new entry, in order, at linearization point `mark`. -/
def commitsOf (w : List Written) (old new : List Nat) (mark : Nat) : List (ClientOp × Nat) :=
  ((new.drop old.length).zipIdx (old.length + 1)).map fun e => ((entryOf w e.2 e.1).toOp, mark)

/-- A lease step's effect on the client state: the new lease state, and every write
whose entry joined the committed history linearized now. -/
def ClientState.withLease (a : ClientState Node) (l : LeaseState Node) : ClientState Node :=
  { a with lease := l, lin := a.lin ++ commitsOf a.written a.lease.core.hist l.core.hist a.history.length }

/-- `n` takes a fresh replication ID (the reply layer's `newId`, on the lease layer's
replication state). -/
def freshen (l : LeaseState Node) (n : Node) : LeaseState Node :=
  { l with core := { l.core with replId := update l.core.replId n (freshId l.core),
                                 usedIds := insert (freshId l.core) l.core.usedIds } }

/-- The lease actions the client layer takes as they are: all but the restarts (which
take a fresh ID here) and the replication layer's append (which is a client write). -/
def LeaseAction.isClientLease : LeaseAction Node → Bool
  | .core (.append _) => false
  | .restartEmpty _ | .restartKeep _ | .restartPartial _ _ => false
  | _ => true

/-- The node a restart action restarts. -/
def LeaseAction.restarted : LeaseAction Node → Option Node
  | .restartEmpty n | .restartKeep n | .restartPartial n _ => some n
  | _ => none

/-- The actions of the client layer. -/
inductive ClientAction (Node : Type)
  | lease (μ : LeaseAction Node)
  | restart (μ : LeaseAction Node)
  | newId (p : Node)
  | invokeWrite (c : Nat)
  | append (p : Node) (op c : Nat)
  | release (h : Held Node)
  | abort (h : Held Node)
  | invokeRead (c : Nat) (n : Node)
  | respondRead (op c : Nat) (n : Node)

/-- The client layer's step relation. `m` is `min-sync-replicas`, `P` the lease
parameters. -/
inductive ClientStep (m : Nat) (P : LeaseParams) : ClientState Node → ClientAction Node → ClientState Node → Prop
  /-- A lease step other than a restart or an append; held replies are unchanged. A
  write whose entry joins the committed history is linearized. -/
  | lease (a μ l) : (hs : LeaseStep m P a.lease μ l) → (hμ : μ.isClientLease = true) →
      ClientStep m P a (.lease μ) (a.withLease l)
  /-- A restart, then a fresh replication ID for the restarted node; its held replies
  are dropped with its client connections. -/
  | restart (a μ l n) : (hs : LeaseStep m P a.lease μ l) → (hμ : μ.restarted = some n) →
      ClientStep m P a (.restart μ) { a with lease := freshen l n, held := dropHeld a.held n }
  /-- A node takes a fresh replication ID without a restart (the reply layer's `newId`). -/
  | newId (a p) : ClientStep m P a (.newId p) { a with lease := freshen a.lease p }
  /-- Client `c` sends a write; its value is its operation id. -/
  | invokeWrite (a c) : ClientStep m P a (.invokeWrite c)
      { a with history := a.history ++ [.inv a.nextOp c (.write a.nextOp)],
               nextOp := a.nextOp + 1, waiting := (a.nextOp, c) :: a.waiting }
  /-- A primary appends a waiting write and holds its reply (the reply layer's
  `write`, with the replication layer's append guards). -/
  | append (a p op c) : (hw : (op, c) ∈ a.waiting) → (hp : ThinksPrimary a.lease.core p) →
      (hW : Writable m a.lease.core p) →
      ClientStep m P a (.append p op c)
        { a with lease := withCore a.lease (appendWrite a.lease.core p),
                 held := ⟨p, (a.lease.core.log p).length + 1, a.lease.core.replId p⟩ :: a.held,
                 written := ⟨(a.lease.core.log p).length + 1, a.lease.core.replId p, op, c⟩ :: a.written,
                 waiting := a.waiting.erase (op, c) }
  /-- A held reply is released as OK (the reply layer's guards); the write responds OK. -/
  | release (a h x) : (hm : h ∈ a.held) → (hc : h.offset ≤ a.lease.core.commit h.primary) →
      (hf : ReplyFenced a.lease.core h) → (hx : entryOp a.written h.offset h.replId = some x) →
      ClientStep m P a (.release h)
        { a with held := a.held.erase h, acknowledged := (h.offset, h.replId) :: a.acknowledged,
                 history := a.history ++ [.res x.op x.client .ok] }
  /-- A held reply is answered UNCOMMITTED: no response event. -/
  | abort (a h) : (hm : h ∈ a.held) → (hf : ¬ ReplyFenced a.lease.core h) →
      ClientStep m P a (.abort h) { a with held := a.held.erase h }
  /-- Client `c` sends a read to node `n`. -/
  | invokeRead (a c n) : ClientStep m P a (.invokeRead c n)
      { a with history := a.history ++ [.inv a.nextOp c .read],
               nextOp := a.nextOp + 1, reading := (a.nextOp, c, n) :: a.reading }
  /-- Node `n` answers a read with its log once it may serve a linearizable read; the
  read is linearized now. -/
  | respondRead (a op c n) : (hr : (op, c, n) ∈ a.reading) →
      (hcan : PrimCanRead P a.lease n ∨ ReplCanRead P a.lease n) →
      ClientStep m P a (.respondRead op c n)
        { a with history := a.history ++ [.res op c (.log (logOps a.written (a.lease.core.log n)))],
                 reading := a.reading.erase (op, c, n),
                 lin := a.lin ++ [(⟨op, c, .read, .log (logOps a.written (a.lease.core.log n))⟩,
                                   a.history.length)] }

/-- The initial state: the lease layer's, no replies, no client events. -/
def clientInit (i : Node) : ClientState Node := ⟨leaseInit i, [], [], [], 0, [], [], [], []⟩

/-- The client layer as a labelled transition system. -/
def clientTransitionSystem (m : Nat) (P : LeaseParams) : LTS (ClientState Node) (ClientAction Node) where
  Tr := ClientStep m P

/-- The states reachable from `clientInit i`. -/
def ClientReachable (m : Nat) (P : LeaseParams) (i : Node) (a : ClientState Node) : Prop :=
  (clientTransitionSystem m P).CanReach (clientInit i) a

theorem ClientReachable.init {m : Nat} {P : LeaseParams} (i : Node) :
    ClientReachable m P i (clientInit i) :=
  LTS.CanReach.refl (clientTransitionSystem m P) _

theorem ClientReachable.stepR {m : Nat} {P : LeaseParams} {i : Node} {a a' : ClientState Node}
    {μ : ClientAction Node} (h : ClientReachable m P i a) (hs : ClientStep m P a μ a') :
    ClientReachable m P i a' :=
  let ⟨_, run⟩ := h; ⟨_, LTS.MTr.stepR (clientTransitionSystem m P) run hs⟩

end SyncReplication

namespace SyncReplication

open Lin

/-! ## A reachable history with a write and a read that returns it

One node, `min-sync-replicas = 0`. Client 0 writes (operation 0); node 0 appends and
commits it, and releases the reply; client 0 then reads from node 0 (operation 1) and
gets `[0]`, the write. -/

section witness

/-- Any lease parameters: with no eligible replica a primary's lease condition is empty. -/
def wP : LeaseParams := ⟨5, 3, 1, 2⟩

def w0 : ClientState (Fin 1) := clientInit 0
def w1 : ClientState (Fin 1) :=
  { w0 with history := w0.history ++ [.inv w0.nextOp 0 (.write w0.nextOp)],
            nextOp := w0.nextOp + 1, waiting := (w0.nextOp, 0) :: w0.waiting }
def w2 : ClientState (Fin 1) :=
  { w1 with lease := withCore w1.lease (appendWrite w1.lease.core 0),
            held := ⟨0, (w1.lease.core.log 0).length + 1, w1.lease.core.replId 0⟩ :: w1.held,
            written := ⟨(w1.lease.core.log 0).length + 1, w1.lease.core.replId 0, 0, 0⟩ :: w1.written,
            waiting := w1.waiting.erase (0, 0) }
def w3 : ClientState (Fin 1) := w2.withLease (withCore w2.lease (commitNext w2.lease.core 0))
def wh : Held (Fin 1) := ⟨0, 1, 1⟩
def wx : Written := ⟨1, 1, 0, 0⟩
def w4 : ClientState (Fin 1) :=
  { w3 with held := w3.held.erase wh, acknowledged := (wh.offset, wh.replId) :: w3.acknowledged,
            history := w3.history ++ [.res wx.op wx.client .ok] }
def w5 : ClientState (Fin 1) :=
  { w4 with history := w4.history ++ [.inv w4.nextOp 0 .read],
            nextOp := w4.nextOp + 1, reading := (w4.nextOp, 0, 0) :: w4.reading }
def w6 : ClientState (Fin 1) :=
  { w5 with history := w5.history ++ [.res 1 0 (.log (logOps w5.written (w5.lease.core.log 0)))],
            reading := w5.reading.erase (1, 0, 0),
            lin := w5.lin ++ [(⟨1, 0, .read, .log (logOps w5.written (w5.lease.core.log 0))⟩,
                               w5.history.length)] }

theorem w_thinks (a : ClientState (Fin 1)) (h1 : (a.lease.core.localCfg 0).primary = 0)
    (h2 : (a.lease.core.localCfg 0).incarnation 0 = a.lease.core.incarnation 0) :
    ThinksPrimary a.lease.core 0 := ⟨h1, h2⟩

/-- A reachable client history in which a write is released as OK and a later read
returns it. -/
theorem client_writeRead_reachable : ∃ a : ClientState (Fin 1), ClientReachable 0 wP 0 a ∧
    a.history = [.inv 0 0 (.write 0), .res 0 0 .ok, .inv 1 0 .read, .res 1 0 (.log [0])] := by
  have hW : ∀ s : State (Fin 1), Writable 0 s 0 := fun s => by unfold Writable; simp
  have r1 : ClientReachable 0 wP 0 w1 := (ClientReachable.init 0).stepR (ClientStep.invokeWrite w0 0)
  have r2 : ClientReachable 0 wP 0 w2 :=
    r1.stepR (ClientStep.append w1 0 0 0 (by decide) (w_thinks _ rfl rfl) (hW _))
  have r3 : ClientReachable 0 wP 0 w3 :=
    r2.stepR (ClientStep.lease w2 (.core (.commit 0)) _
      (LeaseStep.core _ _ _ (Step.commit _ _ (w_thinks _ rfl rfl) (hW _) (by decide)
        (fun r h => by revert h; decide +revert)) rfl) rfl)
  have r4 : ClientReachable 0 wP 0 w4 :=
    r3.stepR (ClientStep.release w3 wh wx (by decide) (by decide) ⟨⟨rfl, rfl⟩, rfl⟩ (by decide))
  have r5 : ClientReachable 0 wP 0 w5 := r4.stepR (ClientStep.invokeRead w4 0 0)
  have hcan : PrimCanRead wP w5.lease 0 :=
    ⟨w_thinks _ rfl rfl, fun r h => by revert h; decide +revert, by decide⟩
  exact ⟨w6, r5.stepR (ClientStep.respondRead w5 1 0 0 (by decide) (Or.inl hcan)), by decide⟩

end witness

end SyncReplication
