#!/usr/bin/env bash
# Generates CoreRestart_*.cfg (CoreRecon bounds: 3 nodes, MaxLen 2, MaxVer 6,
# plus MaxRestarts).
cd "$(dirname "$0")"
cfg() {  # name MinSync MaxRestarts ReconcileFirst NoReplyFence EarlyDrop NoSurvivor RebuildSync IncCheck kind invariant...
  local n=$1 m=$2 mr=$3 rf=$4 nf=$5 ed=$6 ns=$7 rs=$8 ic=$9 kind=${10}; shift 10
  { echo "CONSTANTS"; echo "    Nodes = {n1, n2, n3}"; echo "    InitPrim = n1"
    echo "    MaxLen = 2"; echo "    MaxVer = 6"; echo "    MinSync = $m"
    echo "    MaxRestarts = $mr"
    echo "    ReconcileFirst = $rf"; echo "    EarlyDrop = $ed"
    echo "    NoReplyFence = $nf"; echo "    NoSurvivor = $ns"
    echo "    RebuildSync = $rs"; echo "    IncCheck = $ic"
    echo "SPECIFICATION Spec"; echo "$kind $*"; } > "CoreRestart_$n.cfg"
}
ALL="TypeOK EligibleHoldsCommitted CommittedAgree AckedDurable AckedHeld SyncNew ReconLen EligSync IncLe"
#   name                  m r  RF    NF    ED    NS    RS    IC
cfg safeMin0              0 1 TRUE  FALSE FALSE FALSE TRUE  TRUE  INVARIANTS $ALL
cfg safeMin1              1 1 TRUE  FALSE FALSE FALSE TRUE  TRUE  INVARIANTS $ALL
cfg twoCopiesMin1         1 1 TRUE  FALSE FALSE FALSE TRUE  TRUE  PROPERTIES TwoCopies
cfg noSurvivorMin0        0 1 TRUE  FALSE FALSE TRUE  TRUE  TRUE  INVARIANTS AckedDurable
cfg noSurvivorMin1        1 1 TRUE  FALSE FALSE TRUE  TRUE  TRUE  INVARIANTS AckedDurable
cfg noRebuildMin0         0 1 TRUE  FALSE FALSE FALSE FALSE TRUE  INVARIANTS EligibleHoldsCommitted
cfg noRebuildMin1         1 1 TRUE  FALSE FALSE FALSE FALSE TRUE  INVARIANTS EligibleHoldsCommitted
cfg noRebuildMin1Ack      1 1 TRUE  FALSE FALSE FALSE FALSE TRUE  INVARIANTS AckedDurable AckedHeld
cfg noRebuildMin1Loss     1 1 TRUE  FALSE FALSE FALSE FALSE TRUE  INVARIANTS AckedDurable
cfg noIncMin1             1 1 TRUE  FALSE FALSE FALSE TRUE  FALSE INVARIANTS EligibleHoldsCommitted CommittedAgree AckedDurable AckedHeld
cfg noReconcileMin1       1 1 FALSE FALSE FALSE FALSE TRUE  TRUE  INVARIANTS EligibleHoldsCommitted CommittedAgree AckedDurable AckedHeld
cfg noReplyFenceMin1      1 1 TRUE  TRUE  FALSE FALSE TRUE  TRUE  INVARIANTS AckedDurable AckedHeld
cfg earlyDropMin1         1 1 TRUE  FALSE TRUE  FALSE TRUE  TRUE  INVARIANTS EligibleHoldsCommitted CommittedAgree
cfg ReachRestartEmptyMin1 1 1 TRUE  FALSE FALSE FALSE TRUE  TRUE  INVARIANTS Reach_RestartEmpty
cfg ReachTakeoverAfterEmptyMin1 1 1 TRUE FALSE FALSE FALSE TRUE TRUE INVARIANTS Reach_TakeoverAfterEmpty
cfg ReachReEligibleMin1   1 1 TRUE  FALSE FALSE FALSE TRUE  TRUE  INVARIANTS Reach_ReEligible
cfg ReachKeepCommitMin1   1 1 TRUE  FALSE FALSE FALSE TRUE  TRUE  INVARIANTS Reach_KeepCommit
cfg ReachAckSurvivesEmptyPrimMin1 1 1 TRUE FALSE FALSE FALSE TRUE TRUE INVARIANTS Reach_AckSurvivesEmptyPrim
