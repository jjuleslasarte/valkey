import SyncReplication.Preserve.Replication
import SyncReplication.Preserve.Commit
import SyncReplication.Preserve.Config
import SyncReplication.Preserve.Failover
import SyncReplication.Preserve.Restart

/-!
# Every step preserves the invariant

One line per action, each pointing at the subsystem file that proves it:

| Action | File |
|---|---|
| AppendWrite, Replicate, Ack, Resync | `Preserve/Replication.lean` |
| Commit, Count, Uncount | `Preserve/Commit.lean` |
| Learn, MakeEligible, MakeIneligible | `Preserve/Config.lean` |
| Takeover | `Preserve/Failover.lean` |
| RestartEmpty, RestartKeep, RestartPartial | `Preserve/Restart.lean` |
-/

open Cslib

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

theorem invariant_step {m : Nat} {s s' : State Node} {μ : Action Node} (h : Invariant s) (hs : Step m s μ s') :
    Invariant s' := by
  cases hs with
  | append p _ _ _ => exact invariant_append h p
  | replicate r _ _ _ => exact invariant_replicate h r
  | ack r hne hpre hlt => exact invariant_ack h r hne hpre hlt
  | commit p hp _ hlen hcap => exact invariant_commit h p hp hlen hcap
  | count p r hp hrp hf _ hle => exact invariant_count h p r hp hrp hf hle
  | uncount p r hp hk hs he => exact invariant_uncount h p r hp hk hs he
  | makeElig p r hp hk hsy he => exact invariant_makeElig h hp hk hsy he
  | makeInelig p r hp hk he => exact invariant_makeInelig h hp hk he
  | learn n hk => exact invariant_learn h n hk
  | takeover n hk he hnp hin => exact invariant_takeover h n hk he hnp hin
  | resync r hne _ hsy hke => exact invariant_resync h r hne hsy hke
  | restartEmpty n hk hsv => exact invariant_restartEmpty h n hk hsv
  | restartKeep n hk => exact invariant_restartKeep h n hk
  | restartPartialKeep n k hkl hk hkeep => exact invariant_restartPartialKeep h n k hkl hk hkeep
  | restartPartialFresh n k hkl hk hfresh hsv => exact invariant_restartPartialFresh h n k hkl hsv hk hfresh

/-- `Invariant` is a one-step invariant of the protocol, in CSLib's sense. -/
theorem invariant_trInv {m : Nat} : (lts m (Node := Node)).TrInv Invariant :=
  fun _ _ _ hs h => invariant_step h hs

/-- Hence it holds in every reachable state: a one-step invariant is a run invariant
(`LTS.mtrInv_of_trInv`), and `init i` satisfies it. -/
theorem invariant_reachable {m : Nat} {i : Node} {s : State Node} (h : Reachable m i s) : Invariant s :=
  let ⟨_, run⟩ := h
  LTS.mtrInv_of_trInv invariant_trInv _ _ _ run (invariant_init i)

end SyncReplication
