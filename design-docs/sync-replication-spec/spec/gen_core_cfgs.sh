#!/usr/bin/env bash
# Generates Core_*.cfg.
cd "$(dirname "$0")"
cfg() {  # name MaxLen MaxVer ReconcileFirst EarlyDrop invariant...
  local n=$1 l=$2 v=$3 rf=$4 ed=$5; shift 5
  { echo "CONSTANTS"; echo "    Nodes = {n1, n2, n3}"; echo "    InitPrim = n1"
    echo "    MaxLen = $l"; echo "    MaxVer = $v"
    echo "    ReconcileFirst = $rf"; echo "    EarlyDrop = $ed"
    echo "SPECIFICATION Spec"; echo "INVARIANTS $*"; } > "Core_$n.cfg"
}
cfg safe 2 6 TRUE FALSE TypeOK EligibleHoldsCommitted CommittedAgree
cfg safeBig 3 7 TRUE FALSE TypeOK EligibleHoldsCommitted CommittedAgree
cfg noReconcile 2 6 FALSE FALSE EligibleHoldsCommitted CommittedAgree
cfg earlyDrop 2 6 TRUE TRUE EligibleHoldsCommitted CommittedAgree
cfg ReachTakeoverAfterCommit 2 6 TRUE FALSE Reach_TakeoverAfterCommit
cfg ReachResync 2 6 TRUE FALSE Reach_Resync
