import AckProof.Model
import CoreProof.Safety
import ReconProof.AckProof
import Cslib.Foundations.Semantics.LTS.Simulation
import Cslib.Foundations.Semantics.LTS.MapHom

/-! Unbounded proof that no acknowledged write is lost in CoreAck (ReconcileFirst =
TRUE, EarlyDrop = FALSE, NoReplyFence = FALSE). Derived from `ReconProof.ackSafety`
at MinSync 0: a CoreAck state is a CoreRecon state with held replies (`atoRecon`),
and every CoreAck step is a CoreRecon step (`astep_toRecon`). `ReconProof.ackSafety`
is in turn derived from `RestartProof.ackSafety`. -/

open Cslib

namespace AckProof

open CoreProof

variable {Node : Type} [DecidableEq Node]

def atoRecon (a : AState Node) : ReconProof.AState Node := ⟨toRecon a.core, a.held, a.okd⟩

theorem fenced_toRecon {s : State Node} {h : Held Node} :
    ReconProof.fenced (toRecon s) h ↔ fenced s h := Iff.rfl

/-- Each layer action as a CoreRecon layer action. -/
def AAction.toRecon : AAction Node → ReconProof.AAction Node
  | .core μ => .core μ.toRecon | .write p => .write p | .release h => .release h
  | .abort h => .abort h

theorem astep_toRecon {a a' : AState Node} {μ : AAction Node} (h : AStep true false false a μ a') :
    ReconProof.AStep 0 true false (atoRecon a) μ.toRecon (atoRecon a') := by
  cases h with
  | core _ c hc => exact .core (atoRecon a) _ (toRecon c) (step_toRecon hc)
  | write p hp hr => exact .write (atoRecon a) p hp (writable_zero _ p) hr
  | release x hm hc hf => exact .release (atoRecon a) x hm hc hf
  | abort x hm hf => exact .abort (atoRecon a) x hm hf

/-- `atoRecon` is a simulation of CoreAck by CoreRecon's acknowledgement layer. -/
theorem atoRecon_isSimulation :
    (alts true false false).IsSimulation ((ReconProof.alts 0 true false).mapLabel AAction.toRecon)
      (fun a b => b = atoRecon (Node := Node) a) :=
  fun _ _ hb _ a' hs => ⟨atoRecon a', hb ▸ LTS.mapLabel_tr.2 (astep_toRecon hs), rfl⟩

theorem areach_toRecon {i : Node} {a : AState Node} (h : AReachable true false false i a) :
    ReconProof.AReachable 0 true false i (atoRecon a) :=
  let ⟨μs, run⟩ := h
  let ⟨_, run', hb⟩ := atoRecon_isSimulation.sim_trace rfl μs a run
  ⟨μs.map AAction.toRecon, hb ▸ LTS.mapLabel_mTr.1 run'⟩

/-- No acknowledged write is lost, for any number of nodes, log length and
configuration changes; with the F1 fix (ReconcileFirst) and the F2 fix (reply fence),
without any lease or `cfg.prim = p` fence (F8). -/
theorem ackSafety {i : Node} {a : AState Node} (h : AReachable true false false i a) :
    AckedDurable a ∧ Safety a.core :=
  ReconProof.ackSafety (areach_toRecon h)

/-- The primary and every eligible replica hold every acknowledged write. -/
theorem ackedHeld {i : Node} {a : AState Node} (h : AReachable true false false i a) :
    AckedHeld a :=
  ReconProof.ackedHeld (areach_toRecon h)

end AckProof
