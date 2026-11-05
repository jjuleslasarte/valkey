import CoreProof.Actions3

/-! Main theorem: every reachable state of Core (ReconcileFirst = TRUE,
EarlyDrop = FALSE) satisfies Safety, for any node type and unbounded logs/versions. -/

namespace CoreProof

variable {Node : Type} [DecidableEq Node]

theorem inv_step {s s' : State Node} (h : Inv s) (hs : Step true false s s') : Inv s' := by
  cases hs with
  | append p _ _ => exact inv_append h p
  | replicate r _ _ _ => exact inv_replicate h r
  | ack r hne hpre hlt => exact inv_ack h r hne hpre hlt
  | commit p hp hlen hcap => exact inv_commit h p hp hlen hcap
  | count p r hp hrec hrp hf _ hle => exact inv_count h true rfl p r hp hrec hrp hf hle
  | makeElig p r hp hk hsy he => exact inv_makeElig h hp hk hsy he
  | makeInelig p r hp hk he => exact inv_makeInelig h hp hk he
  | earlyUncount _ _ hed _ _ => exact absurd hed (by decide)
  | learn n hk => exact inv_learn h n hk
  | takeover n hk he hnp => exact inv_takeover h n hk he hnp
  | resync r hne _ hsy hke _ => exact inv_resync h r hne hsy hke

theorem inv_reachable {i : Node} {s : State Node} (h : Reachable true false i s) : Inv s := by
  induction h with
  | init => exact inv_init i
  | step _ hs ih => exact inv_step ih hs

/-- Core_safe, unbounded: any number of nodes (any type with decidable equality),
any log length, any number of configuration changes. -/
theorem safety {i : Node} {s : State Node} (h : Reachable true false i s) : Safety s :=
  inv_safety (inv_reachable h)

end CoreProof
