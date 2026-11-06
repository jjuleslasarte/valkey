import CoreProof

/-! Encoding of `spec/CoreAck.tla`: Core plus held client replies.

A held reply is `(p, o, t)`: primary `p`, 1-based offset `o`, tag `t = term[p]` at the
append. In Core a log entry is the appending primary's term, so `t` is also the value
written. `okd` holds the acknowledged `(offset, value)` pairs.

`AStep.core` allows every Core step with `held`/`okd` unchanged, including Core's
`AppendWrite` without a reply. CoreAck.tla always records a reply on append (`Write`),
so this model has more behaviours than the TLA+ one; a safety theorem for it covers
CoreAck.tla. As in CoreProof, `MaxLen` / `MaxVer` are dropped. -/

open Cslib

namespace AckProof

open CoreProof

/-- (primary, offset, tag) -/
abbrev Held (Node : Type) := Node × Nat × Nat

structure AState (Node : Type) [DecidableEq Node] where
  core : State Node
  held : List (Held Node)
  okd  : List (Nat × Nat)

variable {Node : Type} [DecidableEq Node]

def ainit (i : Node) : AState Node := ⟨init i, [], []⟩

/-- `Write(p)`: Core's AppendWrite plus a held reply at the new length. -/
def write (a : AState Node) (p : Node) : AState Node :=
  ⟨appendWrite a.core p, (p, (a.core.log p).length + 1, a.core.term p) :: a.held, a.okd⟩

/-- `Fenced(h)`: the primaryship that set the reply boundary is still current
(F2 fix). -/
def fenced (s : State Node) (h : Held Node) : Prop := ThinksPrimary s h.1 ∧ s.term h.1 = h.2.2

/-- `Release(h)`: OK. -/
def release (a : AState Node) (h : Held Node) : AState Node :=
  ⟨a.core, a.held.erase h, (h.2.1, h.2.2) :: a.okd⟩

/-- `Abort(h)`: UNCOMMITTED. -/
def abort (a : AState Node) (h : Held Node) : AState Node :=
  ⟨a.core, a.held.erase h, a.okd⟩

/-- The actions of the acknowledgement layer: a replication action, or one of the layer's
own actions on held replies. -/
inductive AAction (Node : Type)
  | core (μ : Action Node) | write (p : Node) | release (h : Held Node) | abort (h : Held Node)

/-- `rf` = ReconcileFirst, `ed` = EarlyDrop, `nf` = NoReplyFence. -/
inductive AStep (rf ed nf : Bool) : AState Node → AAction Node → AState Node → Prop
  | core (a : AState Node) (μ : Action Node) (c : State Node) : Step rf ed a.core μ c →
      AStep rf ed nf a (.core μ) ⟨c, a.held, a.okd⟩
  | write (a : AState Node) (p : Node) : ThinksPrimary a.core p → Reconciled rf a.core p →
      AStep rf ed nf a (.write p) (write a p)
  | release (a : AState Node) (h : Held Node) : h ∈ a.held → h.2.1 ≤ a.core.commit h.1 →
      (nf = false → fenced a.core h) → AStep rf ed nf a (.release h) (release a h)
  | abort (a : AState Node) (h : Held Node) : h ∈ a.held → ¬ fenced a.core h →
      AStep rf ed nf a (.abort h) (abort a h)

/-- The acknowledgement layer as a labelled transition system. -/
def alts (rf ed nf : Bool) : LTS (AState Node) (AAction Node) where
  Tr := AStep rf ed nf

/-- The layer states reachable from `ainit i` by any finite run. -/
def AReachable (rf ed nf : Bool) (i : Node) (a : AState Node) : Prop :=
  (alts rf ed nf).CanReach (ainit i) a

/-- AckedDurable: `Len(hist) >= o /\ hist[o] = v` (TLA `hist[o]` is `getD (o-1)`). -/
def AckedDurable (a : AState Node) : Prop :=
  ∀ x ∈ a.okd, 1 ≤ x.1 ∧ x.1 ≤ a.core.hist.length ∧ a.core.hist.getD (x.1 - 1) 0 = x.2

/-- AckedHeld: the primary and every eligible replica hold every acknowledged write. -/
def AckedHeld (a : AState Node) : Prop :=
  ∀ x ∈ a.okd, ∀ n, (a.core.cfg.elig n = true ∨ n = a.core.cfg.prim) →
    x.1 ≤ (a.core.log n).length ∧ (a.core.log n).getD (x.1 - 1) 0 = x.2

end AckProof
