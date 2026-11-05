import ReconProof.Actions3

/-! Main theorem: every reachable state of CoreRecon's replication part
(ReconcileFirst = TRUE, inherited-log reconciliation, EarlyDrop = FALSE) satisfies
Safety, for EVERY MinSync `m`, any node type, unbounded logs and versions.
`writable m` only restricts AppendWrite and Commit, so the invariant never reads it. -/

namespace ReconProof

variable {Node : Type} [DecidableEq Node]

theorem inv_step {m : Nat} {s s' : State Node} (h : Inv s) (hs : Step m true s s') : Inv s' := by
  cases hs with
  | append p _ _ _ => exact inv_append h p
  | replicate r _ _ _ => exact inv_replicate h r
  | ack r hne hpre hlt => exact inv_ack h r hne hpre hlt
  | commit p hp _ hlen hcap => exact inv_commit h p hp hlen hcap
  | count p r hp hrp hf _ hle => exact inv_count h p r hp hrp hf hle
  | makeElig p r hp hk hsy he => exact inv_makeElig h hp hk hsy he
  | makeInelig p r hp hk he => exact inv_makeInelig h hp hk he
  | learn n hk => exact inv_learn h n hk
  | takeover n hk he hnp => exact inv_takeover h n hk he hnp
  | resync r hne _ hsy hke => exact inv_resync h r hne hsy hke

theorem inv_reachable {m : Nat} {i : Node} {s : State Node} (h : Reachable m true i s) : Inv s := by
  induction h with
  | init => exact inv_init i
  | step _ hs ih => exact inv_step ih hs

/-- Safety for every min-sync-replicas value `m`. -/
theorem safety {m : Nat} {i : Node} {s : State Node} (h : Reachable m true i s) : Safety s :=
  inv_safety (inv_reachable h)

end ReconProof
