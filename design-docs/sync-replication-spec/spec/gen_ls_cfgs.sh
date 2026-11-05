#!/usr/bin/env bash
# Generates Leases_*.cfg.
cd "$(dirname "$0")"
NODES=${NODES:-"{n1, n2, n3}"}; T=${T:-40}; OPS=${OPS:-1}; CFG=${CFG:-3}
# cfg name Drift Margin WaitPrim WaitRead WaitOld StopGrant ResetOnLearn StopAck
cfg() {
  cat > "Leases_$1.cfg" <<X
CONSTANTS
    Nodes = $NODES
    InitPrim = n1
    PrimDur = ${PD:-5}
    ReadDur = ${RD:-2}
    Drift = $2
    Margin = $3
    MaxTime = $T
    MaxOps = $OPS
    MaxCfg = $CFG
    WaitPrimLease = $4
    WaitReadLease = $5
    WaitOldLeases = $6
    StopGrant = $7
    ResetOnLearn = $8
    StopAckOnExpiry = $9
    EchoOnlySync = ${10:-TRUE}
    None = None
SPECIFICATION Spec
VIEW View
ALIAS Alias
X
}
add() { echo "$2" >> "Leases_$1.cfg"; }
INV="INVARIANTS TypeOK NoStaleLinRead CommittedAgree EligibleHoldsCommitted"
PROPS="PROPERTIES AckOnlyByCurrentPrimary Refinement"
# Safe configs: MaxOps = 2 so a client read can follow a write (Refinement).
OPS=2 cfg safe 1 2 TRUE TRUE TRUE TRUE TRUE TRUE;           add safe "$INV"; add safe "$PROPS"
OPS=2 NODES="{n1, n2}" cfg safe2 1 2 TRUE TRUE TRUE TRUE TRUE TRUE; add safe2 "$INV"; add safe2 "$PROPS"
NODES="{n1, n2}" cfg docAckF8two 1 2 TRUE TRUE TRUE TRUE TRUE FALSE; add docAckF8two "PROPERTIES AckOnlyByCurrentPrimary"
cfg docAsWritten 1 2 TRUE TRUE TRUE TRUE TRUE FALSE;  add docAsWritten "$INV"
cfg docAckF8 1 2 TRUE TRUE TRUE TRUE TRUE FALSE;      add docAckF8 "PROPERTIES AckOnlyByCurrentPrimary"
cfg smallMargin 1 1 TRUE TRUE TRUE TRUE TRUE TRUE;    add smallMargin "INVARIANTS TypeOK NoStaleLinRead"
cfg noWaitPrim 1 2 FALSE TRUE TRUE TRUE TRUE TRUE;    add noWaitPrim "INVARIANTS TypeOK NoStaleLinRead"
cfg noWaitRead 1 2 TRUE FALSE TRUE TRUE TRUE TRUE;    add noWaitRead "INVARIANTS TypeOK NoStaleLinRead"
cfg noWaitOld 1 2 TRUE TRUE FALSE TRUE TRUE TRUE;     add noWaitOld "INVARIANTS TypeOK NoStaleLinRead"
cfg noStopGrant 1 2 TRUE TRUE TRUE FALSE TRUE TRUE;   add noStopGrant "INVARIANTS TypeOK NoStaleLinRead"
cfg noReset 1 2 TRUE TRUE TRUE TRUE FALSE TRUE;       add noReset "INVARIANTS TypeOK NoStaleLinRead"
for r in Takeover Demote ReplRead NewPrimRead OKAfterTakeover; do
  cfg "Reach$r" 1 2 TRUE TRUE TRUE TRUE TRUE TRUE; add "Reach$r" "INVARIANTS Reach_$r"; done
cfg noEchoSync 1 2 TRUE TRUE TRUE TRUE TRUE TRUE FALSE; add noEchoSync "INVARIANTS TypeOK NoStaleLinRead"
# T=7 variants of safe and safe2 (shorter horizon, same leases).
OPS=2 PD=5 RD=2 T=7 cfg safeT7 1 2 TRUE TRUE TRUE TRUE TRUE TRUE;  add safeT7 "$INV"; add safeT7 "$PROPS"
OPS=2 PD=5 RD=2 T=7 NODES="{n1, n2}" cfg safe2T7 1 2 TRUE TRUE TRUE TRUE TRUE TRUE; add safe2T7 "$INV"; add safe2T7 "$PROPS"
# Refinement to DurableShard on the known bugs (MaxOps = 2: one write and
# one client read, invoked after the write committed: CONSTRAINT ReadAfterCommit).
# Each must violate Refinement, not only NoStaleLinRead.
OPS=2 cfg smallMarginRef 1 1 TRUE TRUE TRUE TRUE TRUE TRUE;    add smallMarginRef "CONSTRAINT ReadAfterCommit"; add smallMarginRef "PROPERTIES Refinement"
OPS=2 cfg noWaitPrimRef 1 2 FALSE TRUE TRUE TRUE TRUE TRUE;    add noWaitPrimRef "CONSTRAINT ReadAfterCommit"; add noWaitPrimRef "PROPERTIES Refinement"
OPS=2 cfg noWaitReadRef 1 2 TRUE FALSE TRUE TRUE TRUE TRUE;    add noWaitReadRef "CONSTRAINT ReadAfterCommit"; add noWaitReadRef "PROPERTIES Refinement"
OPS=2 cfg noEchoSyncRef 1 2 TRUE TRUE TRUE TRUE TRUE TRUE FALSE; add noEchoSyncRef "CONSTRAINT ReadAfterCommit"; add noEchoSyncRef "PROPERTIES Refinement"
OPS=2 cfg ReachReplReadOp 1 2 TRUE TRUE TRUE TRUE TRUE TRUE;   add ReachReplReadOp "CONSTRAINT ReadAfterCommit"; add ReachReplReadOp "INVARIANTS Reach_ReplReadOp"
