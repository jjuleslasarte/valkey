import SyncReplication.Safety

/-! # Held client replies

The replication model (`SyncReplication.Step`, replication delayed) plus the replies a primary holds for
its clients (design §5, "Write behavior during faults"). A write's reply is held until
the write commits; it is then released as OK, or answered UNCOMMITTED. A restart drops
the held replies of the restarted node: they are lost with the client connections, so
they are neither acknowledged nor answered.

A held reply (`Held`) names the primary that accepted the write, the write's 1-based
offset, and the primary's replication ID at the append. A log entry is the appending
primary's ID, so the ID is also the value written. `acknowledged` holds the acknowledged
`(offset, value)` pairs.

`ReplyStep.core` allows every replication step other than a restart with `held`/`acknowledged`
unchanged, including `AppendWrite` without a reply, so the layer has more behaviours
than a real primary; a safety theorem for it covers the real one. -/

open Cslib

namespace SyncReplication


/-- A reply a primary holds for a client until the write commits or the primaryship
ends. -/
structure Held (Node : Type) where
  /-- The primary that accepted the write. -/
  primary : Node
  /-- The write's 1-based offset in `primary`'s log. -/
  offset  : Nat
  /-- `primary`'s replication ID at the append, which is also the value written. -/
  replId    : Nat
  deriving DecidableEq

/-- The replication state plus the reply layer: the replies still held, and the
`(offset, value)` pairs released as OK. -/
structure ReplyState (Node : Type) [DecidableEq Node] where
  /-- The replication state. -/
  core : State Node
  /-- The replies not yet released or aborted. -/
  held : List (Held Node)
  /-- The `(offset, value)` pairs released as OK. -/
  acknowledged : List (Nat × Nat)

variable {Node : Type} [DecidableEq Node]

def replyInit (i : Node) : ReplyState Node := ⟨init i, [], []⟩

/-- `write a p`: `appendWrite` plus a held reply at the new length. -/
def write (a : ReplyState Node) (p : Node) : ReplyState Node :=
  ⟨appendWrite a.core p, ⟨p, (a.core.log p).length + 1, a.core.replId p⟩ :: a.held, a.acknowledged⟩

/-- The reply fence: the primaryship that accepted the write is still current. A reply
may be released as OK only while this holds. (Unrelated to `DeposedFenced`, the log
fence of a deposed primary.) -/
def ReplyFenced (s : State Node) (h : Held Node) : Prop :=
  ThinksPrimary s h.primary ∧ s.replId h.primary = h.replId

/-- `release a h`: the client is told OK. -/
def release (a : ReplyState Node) (h : Held Node) : ReplyState Node :=
  ⟨a.core, a.held.erase h, (h.offset, h.replId) :: a.acknowledged⟩

/-- `abort a h`: the client is told UNCOMMITTED. -/
def abort (a : ReplyState Node) (h : Held Node) : ReplyState Node :=
  ⟨a.core, a.held.erase h, a.acknowledged⟩

/-- `newId a p`: `p` takes a fresh replication ID without a takeover (Valkey's
`changeReplicationId` when a primary creates or frees its backlog, on
`DEBUG change-repl-id`, and at a primary's restart). -/
def newId (a : ReplyState Node) (p : Node) : ReplyState Node :=
  ⟨{ a.core with replId := update a.core.replId p (freshId a.core),
                 usedIds := insert (freshId a.core) a.core.usedIds }, a.held, a.acknowledged⟩

/-- The held replies left after `n` restarts. -/
def dropHeld (held : List (Held Node)) (n : Node) : List (Held Node) :=
  held.filter (fun x => x.primary != n)

/-- The actions of the acknowledgement layer: a replication action, or one of the layer's
own actions on held replies. -/
inductive ReplyAction (Node : Type)
  | core (μ : Action Node) | write (p : Node) | release (h : Held Node) | abort (h : Held Node)
  | restartEmpty (n : Node) | restartKeep (n : Node) | restartPartial (n : Node) (k : Nat)
  /-- `p` takes a fresh replication ID without a takeover. -/
  | newId (p : Node)

/-- The layer's `Next`. `m` = MinSync. A reply is released as OK only once its offset
is committed and while the primaryship that accepted the write is still current. -/
inductive ReplyStep (m : Nat) : ReplyState Node → ReplyAction Node → ReplyState Node → Prop
  /-- A replication action other than a restart; held replies are unchanged (`Keep`). -/
  | core (a : ReplyState Node) (μ : Action Node) (c : State Node) : Step m a.core μ c →
      μ.isRestart = false → ReplyStep m a (.core μ) ⟨c, a.held, a.acknowledged⟩
  | write (a : ReplyState Node) (p : Node) : ThinksPrimary a.core p → Writable m a.core p →
      ReplyStep m a (.write p) (write a p)
  | release (a : ReplyState Node) (h : Held Node) : h ∈ a.held → h.offset ≤ a.core.commit h.primary →
      ReplyFenced a.core h → ReplyStep m a (.release h) (release a h)
  | abort (a : ReplyState Node) (h : Held Node) : h ∈ a.held → ¬ ReplyFenced a.core h →
      ReplyStep m a (.abort h) (abort a h)
  /-- Any node may take a fresh replication ID at any time. -/
  | newId (a : ReplyState Node) (p : Node) : ReplyStep m a (.newId p) (newId a p)
  | restartEmpty (a : ReplyState Node) (n : Node) : (hKnowsLatest : KnowsLatest a.core n) → (hSurvivor : ∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      ReplyStep m a (.restartEmpty n) ⟨restartEmpty a.core n, dropHeld a.held n, a.acknowledged⟩
  | restartKeep (a : ReplyState Node) (n : Node) : (hKnowsLatest : KnowsLatest a.core n) →
      ReplyStep m a (.restartKeep n) ⟨restartKeep a.core n, dropHeld a.held n, a.acknowledged⟩
  /-- RestartPartial, keeping the incarnation; `n`'s held replies are dropped with its
  client connections, as for the other restarts. -/
  | restartPartialKeep (a : ReplyState Node) (n : Node) (k : Nat) : (hKnowsLatest : KnowsLatest a.core n) →
      (hFileShorter : k < (a.core.log n).length) → (hCoversAcks : a.core.ackHigh n ≤ k) →
      ReplyStep m a (.restartPartial n k) ⟨restartPartialKeep a.core n k, dropHeld a.held n, a.acknowledged⟩
  /-- RestartPartial, taking a new incarnation. -/
  | restartPartialFresh (a : ReplyState Node) (n : Node) (k : Nat) : (hKnowsLatest : KnowsLatest a.core n) →
      (hFileShorter : k < (a.core.log n).length) → (hMissesAcks : k < a.core.ackHigh n) → (hSurvivor : ∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      ReplyStep m a (.restartPartial n k) ⟨restartPartialFresh a.core n k, dropHeld a.held n, a.acknowledged⟩

/-- The acknowledgement layer as a labelled transition system. -/
def replyTransitionSystem (m : Nat) : LTS (ReplyState Node) (ReplyAction Node) where
  Tr := ReplyStep m

/-- The layer states reachable from `replyInit i` by any finite run. -/
def ReplyReachable (m : Nat) (i : Node) (a : ReplyState Node) : Prop :=
  (replyTransitionSystem m).CanReach (replyInit i) a

theorem ReplyReachable.init {m : Nat} (i : Node) : ReplyReachable m i (replyInit i) :=
  LTS.CanReach.refl (replyTransitionSystem m) _

theorem ReplyReachable.stepR {m : Nat} {i : Node} {a a' : ReplyState Node} {μ : ReplyAction Node}
    (h : ReplyReachable m i a) (hs : ReplyStep m a μ a') : ReplyReachable m i a' :=
  let ⟨_, run⟩ := h; ⟨_, LTS.MTr.stepR (replyTransitionSystem m) run hs⟩

/-- AckedDurable: every acknowledged `(o, v)` is the committed history's entry at offset `o`
(1-based, so `getD (o-1)`). -/
def AckedDurable (a : ReplyState Node) : Prop :=
  ∀ x ∈ a.acknowledged, 1 ≤ x.1 ∧ x.1 ≤ a.core.hist.length ∧ a.core.hist.getD (x.1 - 1) 0 = x.2

/-- AckedHeld: every authoritative node holds every acknowledged write. -/
def AckedHeld (a : ReplyState Node) : Prop :=
  ∀ x ∈ a.acknowledged, ∀ n, IsAuthoritative a.core n →
    x.1 ≤ (a.core.log n).length ∧ (a.core.log n).getD (x.1 - 1) 0 = x.2

end SyncReplication
