import CoreProof.Model
import ReconProof.Model
import Cslib.Foundations.Semantics.LTS.Simulation
import Cslib.Foundations.Semantics.LTS.MapHom

/-! Core's rule is CoreRecon's strict rule at MinSync 0, and every strict step is an
A1 step. `CoreProof.State` and `ReconProof.State` have the same fields, so `toRecon`
is the identity field by field, and:

- AppendWrite and Commit: `Writable` at MinSync 0 always holds (the empty list).
- Count: Core requires Reconciled(p) and `commit[p] <= acked[p][r]`. Reconciled means
  `CatchUpPoint(p) = commit[p]`, so this is A1's `CatchUpPoint(p) <= acked[p][r]`.
- Resync: Core requires Reconciled(PrimOf(r)) and truncates to `commit`; under
  Reconciled that is A1's truncation to `CatchUpPoint`.
- EarlyUncount needs EarlyDrop = TRUE, so it has no Core step with `ed = false`.

So with ReconcileFirst = TRUE and EarlyDrop = FALSE, every Core step is a CoreRecon
step at MinSync 0 (`step_toRecon`), every Core reachable state is a CoreRecon
reachable state (`reach_toRecon`), and Safety reads the same (`safety_of_toRecon`). -/

open Cslib

namespace CoreProof

variable {Node : Type} [DecidableEq Node]

def cfgToRecon (c : Cfg Node) : ReconProof.Cfg Node := ⟨c.ver, c.prim, c.elig⟩

def toRecon (s : State Node) : ReconProof.State Node where
  log    := s.log
  cfg    := cfgToRecon s.cfg
  known  := fun n => cfgToRecon (s.known n)
  sync   := s.sync
  acked  := s.acked
  commit := s.commit
  recon  := s.recon
  term   := s.term
  hist   := s.hist

theorem toRecon_init (i : Node) : toRecon (init i) = ReconProof.init i := rfl

theorem cfgToRecon_upd (f : Node → Cfg Node) (p : Node) (c : Cfg Node) :
    (fun n => cfgToRecon (upd f p c n)) =
      ReconProof.upd (fun n => cfgToRecon (f n)) p (cfgToRecon c) := by
  funext n
  by_cases h : n = p
  · subst h; simp [upd, ReconProof.upd]
  · simp [upd, ReconProof.upd, h]

/-- The strict reconciliation rule: once `p` is reconciled, CatchUpPoint is the commit. -/
theorem catchUpPoint_of_reconciled {s : State Node} {p : Node} (h : Reconciled true s p) :
    ReconProof.catchUpPoint true (toRecon s) p = s.commit p := by
  have := h rfl
  simp only [ReconProof.catchUpPoint, toRecon]
  split
  · omega
  · rfl

theorem writable_zero (s : ReconProof.State Node) (p : Node) : ReconProof.Writable 0 s p := by
  simp [ReconProof.Writable]

/-! ### Post-states commute with `toRecon` -/

section
variable (s : State Node)

theorem toRecon_appendWrite (p : Node) :
    toRecon (appendWrite s p) = ReconProof.appendWrite (toRecon s) p := rfl
theorem toRecon_replicate (r : Node) :
    toRecon (replicate s r) = ReconProof.replicate (toRecon s) r := rfl
theorem toRecon_ack (r : Node) : toRecon (ack s r) = ReconProof.ack (toRecon s) r := rfl
theorem toRecon_commitNext (p : Node) :
    toRecon (commitNext s p) = ReconProof.commitNext (toRecon s) p := rfl
theorem toRecon_count (p r : Node) :
    toRecon (count s p r) = ReconProof.count (toRecon s) p r := rfl

theorem toRecon_learn (n : Node) : toRecon (learn s n) = ReconProof.learn (toRecon s) n := by
  simp only [toRecon, learn, ReconProof.learn, cfgToRecon_upd]; rfl

theorem toRecon_makeElig (p r : Node) :
    toRecon (makeElig s p r) = ReconProof.makeElig (toRecon s) p r := by
  have hc : ReconProof.makeEligCfg (toRecon s) r true = cfgToRecon (makeEligCfg s r true) := rfl
  simp only [ReconProof.makeElig, hc]
  simp only [toRecon, makeElig, cfgToRecon_upd]

theorem toRecon_makeInelig (p r : Node) :
    toRecon (makeInelig s p r) = ReconProof.makeInelig (toRecon s) p r := by
  have hc : ReconProof.makeEligCfg (toRecon s) r false = cfgToRecon (makeEligCfg s r false) := rfl
  simp only [ReconProof.makeInelig, hc]
  simp only [toRecon, makeInelig, cfgToRecon_upd]; rfl

theorem toRecon_takeover (n : Node) :
    toRecon (takeover s n) = ReconProof.takeover (toRecon s) n := by
  have hc : ReconProof.takeoverCfg (toRecon s) n = cfgToRecon (takeoverCfg s n) := rfl
  simp only [ReconProof.takeover, hc]
  simp only [toRecon, takeover, cfgToRecon_upd]; rfl

theorem toRecon_resync {r : Node} (h : Reconciled true s (primaryOf s r)) :
    toRecon (resync s r) = ReconProof.resync true (toRecon s) r := by
  have hc := catchUpPoint_of_reconciled h
  simp only [ReconProof.resync]
  rw [show ReconProof.primaryOf (toRecon s) r = primaryOf s r from rfl, hc]
  rfl

end

/-! ### Steps, reachability and Safety -/

/-- Each Core action as a CoreRecon action. EarlyUncount has no counterpart; it is
disabled in the embedded instance (EarlyDrop = FALSE), so its image is never used and
is set to `learn p` arbitrarily. -/
def Action.toRecon : Action Node → ReconProof.Action Node
  | .append p => .append p | .replicate r => .replicate r | .ack r => .ack r
  | .commit p => .commit p | .count p r => .count p r | .makeElig p r => .makeElig p r
  | .makeInelig p r => .makeInelig p r | .earlyUncount p _ => .learn p | .learn n => .learn n
  | .takeover n => .takeover n | .resync r => .resync r

/-- Every Core step (ReconcileFirst = TRUE, EarlyDrop = FALSE) is a CoreRecon step
at MinSync 0 under the A1 rule, with the action of the same name. -/
theorem step_toRecon {s s' : State Node} {μ : Action Node} (h : Step true false s μ s') :
    ReconProof.Step 0 true (toRecon s) μ.toRecon (toRecon s') := by
  cases h with
  | append p hp hr =>
    rw [toRecon_appendWrite]; exact .append _ p hp (writable_zero _ p) hr
  | replicate r h1 h2 h3 => rw [toRecon_replicate]; exact .replicate _ r h1 h2 h3
  | ack r h1 h2 h3 => rw [toRecon_ack]; exact .ack _ r h1 h2 h3
  | commit p hp h1 h2 =>
    rw [toRecon_commitNext]; exact .commit _ p hp (writable_zero _ p) h1 h2
  | count p r hp hr h1 h2 h3 h4 =>
    rw [toRecon_count]
    exact .count _ p r hp h1 h2 h3 (by rw [catchUpPoint_of_reconciled hr]; exact h4)
  | makeElig p r hp hk h1 h2 => rw [toRecon_makeElig]; exact .makeElig _ p r hp hk h1 h2
  | makeInelig p r hp hk h1 => rw [toRecon_makeInelig]; exact .makeInelig _ p r hp hk h1
  | earlyUncount _ _ hed _ _ => exact absurd hed (by decide)
  | learn n hk => rw [toRecon_learn]; exact .learn _ n hk
  | takeover n hk h1 h2 => rw [toRecon_takeover]; exact .takeover _ n hk h1 h2
  | resync r h1 h2 h3 h4 hr => rw [toRecon_resync s hr]; exact .resync _ r h1 h2 h3 h4

/-- `toRecon` is a simulation of Core by CoreRecon, in CSLib's sense. -/
theorem toRecon_isSimulation :
    (lts true false).IsSimulation ((ReconProof.lts 0 true).mapLabel Action.toRecon)
      (fun s t => t = toRecon (Node := Node) s) :=
  fun _ _ ht _ s' hs => ⟨toRecon s', ht ▸ LTS.mapLabel_tr.2 (step_toRecon hs), rfl⟩

theorem reach_toRecon {i : Node} {s : State Node} (h : Reachable true false i s) :
    ReconProof.Reachable 0 true i (toRecon s) :=
  let ⟨μs, run⟩ := h
  let ⟨_, run', ht⟩ := toRecon_isSimulation.sim_trace (toRecon_init i).symm μs s run
  ⟨μs.map Action.toRecon, ht ▸ LTS.mapLabel_mTr.1 run'⟩

theorem safety_of_toRecon {s : State Node} (h : ReconProof.Safety (toRecon s)) : Safety s := h

end CoreProof
