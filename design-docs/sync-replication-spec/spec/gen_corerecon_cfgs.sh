#!/usr/bin/env bash
# Generates CoreRecon_*.cfg (CoreAck bounds: 3 nodes, MaxLen 2, MaxVer 6).
cd "$(dirname "$0")"
cfg() {  # name MinSync ReconcileFirst NoReplyFence StrictRecon EarlyDrop invariant...
  local n=$1 m=$2 rf=$3 nf=$4 sr=$5 ed=$6; shift 6
  { echo "CONSTANTS"; echo "    Nodes = {n1, n2, n3}"; echo "    InitPrim = n1"
    echo "    MaxLen = 2"; echo "    MaxVer = 6"; echo "    MinSync = $m"
    echo "    ReconcileFirst = $rf"; echo "    EarlyDrop = $ed"
    echo "    NoReplyFence = $nf"; echo "    StrictRecon = $sr"
    echo "SPECIFICATION Spec"; echo "INVARIANTS $*"; } > "CoreRecon_$n.cfg"
}
ALL="TypeOK EligibleHoldsCommitted CommittedAgree AckedDurable AckedHeld SyncNew ReconLen"
cfg safeMin0 0 TRUE FALSE FALSE FALSE $ALL
cfg safeMin1 1 TRUE FALSE FALSE FALSE $ALL
cfg strictMin0 0 TRUE FALSE TRUE FALSE TypeOK EligibleHoldsCommitted CommittedAgree AckedDurable AckedHeld
cfg strictMin1 1 TRUE FALSE TRUE FALSE TypeOK EligibleHoldsCommitted CommittedAgree AckedDurable AckedHeld
cfg noReconcileMin0 0 FALSE FALSE FALSE FALSE EligibleHoldsCommitted CommittedAgree AckedDurable AckedHeld
cfg noReconcileMin1 1 FALSE FALSE FALSE FALSE EligibleHoldsCommitted CommittedAgree AckedDurable AckedHeld
cfg noReplyFenceMin1 1 TRUE TRUE FALSE FALSE AckedDurable AckedHeld
cfg earlyDropMin1 1 TRUE FALSE FALSE TRUE EligibleHoldsCommitted CommittedAgree
cfg ReachLoneMin1 1 TRUE FALSE FALSE FALSE Reach_Lone
cfg ReachLoneReconMin1 1 TRUE FALSE FALSE FALSE Reach_LoneReconcile
cfg strictReachLoneMin1 1 TRUE FALSE TRUE FALSE Reach_Lone
cfg strictReachLoneReconMin1 1 TRUE FALSE TRUE FALSE Reach_LoneReconcile
cfg strictReachReconMin1 1 TRUE FALSE TRUE FALSE Reach_Reconcile
cfg ReachAckMin1 1 TRUE FALSE FALSE FALSE Reach_Ack
