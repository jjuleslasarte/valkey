#!/usr/bin/env bash
# Generates CoreAck_*.cfg (same bounds as Core_safe: 3 nodes, MaxLen 2, MaxVer 6).
cd "$(dirname "$0")"
cfg() {  # name MaxLen MaxVer ReconcileFirst NoReplyFence invariant...
  local n=$1 l=$2 v=$3 rf=$4 nf=$5; shift 5
  { echo "CONSTANTS"; echo "    Nodes = {n1, n2, n3}"; echo "    InitPrim = n1"
    echo "    MaxLen = $l"; echo "    MaxVer = $v"
    echo "    ReconcileFirst = $rf"; echo "    EarlyDrop = FALSE"
    echo "    NoReplyFence = $nf"
    echo "SPECIFICATION ASpec"; echo "INVARIANTS $*"; } > "CoreAck_$n.cfg"
}
cfg safe 2 6 TRUE FALSE TypeOK EligibleHoldsCommitted CommittedAgree AckedDurable AckedHeld HeldInv TermLe
cfg noReplyFence 2 6 TRUE TRUE AckedDurable AckedHeld
cfg noReconcile 2 6 FALSE FALSE AckedDurable AckedHeld
cfg ReachAck 2 6 TRUE FALSE Reach_Ack
cfg ReachDeposedAck 2 6 TRUE FALSE Reach_DeposedAck
cfg ReachDeposedCommit 2 6 TRUE FALSE Reach_DeposedCommit
