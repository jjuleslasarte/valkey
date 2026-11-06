import SyncReplication.Safety

/-! # Held client replies

The replication model (`SyncReplication.Step`) plus the replies a primary holds for
its clients (design §5, "Write behavior during faults"). A write's reply is held until
the write commits; it is then released as OK, or answered UNCOMMITTED. A restart drops
the held replies of the restarted node: they are lost with the client connections, so
they are neither acknowledged nor answered.

A held reply is `(p, o, t)`: primary `p`, 1-based offset `o`, tag `t = term[p]` at the
append. A log entry is the appending primary's term, so `t` is also the value written.
`okd` holds the acknowledged `(offset, value)` pairs.

`AStep.core` allows every replication step other than a restart with `held`/`okd`
unchanged, including `AppendWrite` without a reply, so the layer has more behaviours
than a real primary; a safety theorem for it covers the real one. -/

open Cslib

namespace SyncReplication


/-- (primary, offset, tag) -/
abbrev Held (Node : Type) := Node × Nat × Nat

structure AState (Node : Type) [DecidableEq Node] where
  core : State Node
  held : List (Held Node)
  okd  : List (Nat × Nat)

variable {Node : Type} [DecidableEq Node]

def ainit (i : Node) : AState Node := ⟨init i, [], []⟩

/-- `Write(p)`: AppendWrite plus a held reply at the new length. -/
def write (a : AState Node) (p : Node) : AState Node :=
  ⟨appendWrite a.core p, (p, (a.core.log p).length + 1, a.core.term p) :: a.held, a.okd⟩

/-- `Fenced(h)`: the primaryship that accepted the write is still current. A reply
may be released as OK only while this holds. -/
def fenced (s : State Node) (h : Held Node) : Prop := ThinksPrimary s h.1 ∧ s.term h.1 = h.2.2

/-- `Release(h)`: OK. -/
def release (a : AState Node) (h : Held Node) : AState Node :=
  ⟨a.core, a.held.erase h, (h.2.1, h.2.2) :: a.okd⟩

/-- `Abort(h)`: UNCOMMITTED. -/
def abort (a : AState Node) (h : Held Node) : AState Node :=
  ⟨a.core, a.held.erase h, a.okd⟩

/-- The held replies left after `n` restarts. -/
def dropHeld (held : List (Held Node)) (n : Node) : List (Held Node) :=
  held.filter (fun x => x.1 != n)

/-- The actions of the acknowledgement layer: a replication action, or one of the layer's
own actions on held replies. -/
inductive AAction (Node : Type)
  | core (μ : Action Node) | write (p : Node) | release (h : Held Node) | abort (h : Held Node)
  | restartE (n : Node) | restartK (n : Node) | restartP (n : Node) (k : Nat)

/-- The layer's `Next`. `m` = MinSync. A reply is released as OK only once its offset
is committed and while the primaryship that accepted the write is still current. -/
inductive AStep (m : Nat) : AState Node → AAction Node → AState Node → Prop
  /-- A replication action other than a restart; held replies are unchanged (`Keep`). -/
  | core (a : AState Node) (μ : Action Node) (c : State Node) : Step m a.core μ c →
      μ.isRestart = false → AStep m a (.core μ) ⟨c, a.held, a.okd⟩
  | write (a : AState Node) (p : Node) : ThinksPrimary a.core p → Writable m a.core p →
      Reconciled a.core p → AStep m a (.write p) (write a p)
  | release (a : AState Node) (h : Held Node) : h ∈ a.held → h.2.1 ≤ a.core.commit h.1 →
      fenced a.core h → AStep m a (.release h) (release a h)
  | abort (a : AState Node) (h : Held Node) : h ∈ a.held → ¬ fenced a.core h →
      AStep m a (.abort h) (abort a h)
  | restartE (a : AState Node) (n : Node) : KnowsLatest a.core n → (∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      AStep m a (.restartE n) ⟨restartEmpty a.core n, dropHeld a.held n, a.okd⟩
  | restartK (a : AState Node) (n : Node) : KnowsLatest a.core n →
      AStep m a (.restartK n) ⟨restartKeep a.core n, dropHeld a.held n, a.okd⟩
  /-- RestartPartial, keeping the incarnation; `n`'s held replies are dropped with its
  client connections, as for the other restarts. -/
  | restartPK (a : AState Node) (n : Node) (k : Nat) : KnowsLatest a.core n →
      k < (a.core.log n).length → a.core.ackHigh n ≤ k →
      AStep m a (.restartP n k) ⟨restartPartialKeep a.core n k, dropHeld a.held n, a.okd⟩
  /-- RestartPartial, taking a new incarnation. -/
  | restartPF (a : AState Node) (n : Node) (k : Nat) : KnowsLatest a.core n →
      k < (a.core.log n).length → k < a.core.ackHigh n → (∃ m, m ≠ n ∧ IsAuthoritative a.core m) →
      AStep m a (.restartP n k) ⟨restartPartialFresh a.core n k, dropHeld a.held n, a.okd⟩

/-- The acknowledgement layer as a labelled transition system. -/
def alts (m : Nat) : LTS (AState Node) (AAction Node) where
  Tr := AStep m

/-- The layer states reachable from `ainit i` by any finite run. -/
def AReachable (m : Nat) (i : Node) (a : AState Node) : Prop :=
  (alts m).CanReach (ainit i) a

theorem AReachable.init {m : Nat} (i : Node) : AReachable m i (ainit i) :=
  LTS.CanReach.refl (alts m) _

theorem AReachable.stepR {m : Nat} {i : Node} {a a' : AState Node} {μ : AAction Node}
    (h : AReachable m i a) (hs : AStep m a μ a') : AReachable m i a' :=
  let ⟨_, run⟩ := h; ⟨_, LTS.MTr.stepR (alts m) run hs⟩

/-- AckedDurable: every acknowledged `(o, v)` is the committed history's entry at offset `o`
(1-based, so `getD (o-1)`). -/
def AckedDurable (a : AState Node) : Prop :=
  ∀ x ∈ a.okd, 1 ≤ x.1 ∧ x.1 ≤ a.core.hist.length ∧ a.core.hist.getD (x.1 - 1) 0 = x.2

/-- AckedHeld: every authoritative node holds every acknowledged write. -/
def AckedHeld (a : AState Node) : Prop :=
  ∀ x ∈ a.okd, ∀ n, IsAuthoritative a.core n →
    x.1 ≤ (a.core.log n).length ∧ (a.core.log n).getD (x.1 - 1) 0 = x.2

end SyncReplication
