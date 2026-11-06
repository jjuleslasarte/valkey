import RestartProof.Preserve.Replication
import RestartProof.Preserve.Commit
import RestartProof.Preserve.Config
import RestartProof.Preserve.Failover
import RestartProof.Preserve.Restart

/-!
# Every step preserves the invariant

One line per action, each pointing at the subsystem file that proves it:

| Action | File |
|---|---|
| AppendWrite, Replicate, Ack, Resync | `Preserve/Replication.lean` |
| Commit, Count | `Preserve/Commit.lean` |
| Learn, MakeEligible, MakeIneligible | `Preserve/Config.lean` |
| Takeover | `Preserve/Failover.lean` |
| RestartEmpty, RestartKeep | `Preserve/Restart.lean` |
-/

open Cslib

namespace RestartProof

variable {Node : Type} [DecidableEq Node]

theorem inv_step {m : Nat} {s s' : State Node} {μ : Action Node} (h : Inv s) (hs : Step m true true s μ s') :
    Inv s' := by
  cases hs with
  | append p _ _ _ => exact inv_append h p
  | replicate r _ _ _ => exact inv_replicate h r
  | ack r hne hpre hlt => exact inv_ack h r hne hpre hlt
  | commit p hp _ hlen hcap => exact inv_commit h p hp hlen hcap
  | count p r hp hrp hf _ _ hle => exact inv_count h p r hp hrp hf hle
  | makeElig p r hp hk hsy he => exact inv_makeElig h hp hk hsy he
  | makeInelig p r hp hk he => exact inv_makeInelig h hp hk he
  | learn n hk => exact inv_learn h n hk
  | takeover n hk he hnp hin => exact inv_takeover h n hk he hnp hin
  | resync r hne _ hsy hke => exact inv_resync h r hne hsy hke
  | restartEmpty n hk hsv => exact inv_restartEmpty h n hk hsv
  | restartKeep n hk => exact inv_restartKeep h n hk

/-- `Inv` is a one-step invariant of the protocol, in CSLib's sense. -/
theorem inv_trInv {m : Nat} : (lts m true true (Node := Node)).TrInv Inv :=
  fun _ _ _ hs h => inv_step h hs

/-- Hence it holds in every reachable state: a one-step invariant is a run invariant
(`LTS.mtrInv_of_trInv`), and `init i` satisfies it. -/
theorem inv_reachable {m : Nat} {i : Node} {s : State Node} (h : Reachable m true true i s) : Inv s :=
  let ⟨_, run⟩ := h
  LTS.mtrInv_of_trInv inv_trInv _ _ _ run (inv_init i)

end RestartProof
