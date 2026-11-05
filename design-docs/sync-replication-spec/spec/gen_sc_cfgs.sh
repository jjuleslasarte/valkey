#!/usr/bin/env bash
# Generates SyncCommit_*.cfg.  Usage: gen_sc_cfgs.sh [small|big]
# Each safe config enables one feature group (EnabledKinds) to bound the state space.
cd "$(dirname "$0")"
SIZE=${1:-small}
if [ "$SIZE" = big ]; then K="{k1, k2}"; V="{v1, v2}"; OPS=4; R="{r1, r2, r3}"
else K="{k1}"; V="{v1}"; OPS=3; R="{r1, r2}"; fi
SYS=1
CORE='{"W", "R", "S"}'
SETNX='{"W", "C", "R"}'
DBSIZE='{"W", "K", "KS"}'

# cfg NAME KINDS MinSync TargetSync AOF AtomicPromote TrackDirty SPEC [MaxOps] [Replicas] -- then lines
cfg() {
  local name=$1 kinds=$2 mn=$3 tg=$4 aof=$5 ap=$6 td=$7 spec=$8 ops=${9:-$OPS} reps=${10:-$R}
  shift 10 2>/dev/null || shift $#
  {
    echo "CONSTANTS"
    echo "    Keys = $K"
    echo "    Values = $V"
    echo "    Nil = Nil"
    echo "    None = None"
    echo "    NoReader = NoReader"
    echo "    MaxOps = $ops"
    echo "    MaxSystemWrites = $SYS"
    echo "    Replicas = $reps"
    echo "    MinSync = $mn"
    echo "    TargetSync = $tg"
    echo "    AOF = $aof"
    echo "    AtomicPromote = $ap"
    echo "    TrackDirty = $td"
    echo "    EnabledKinds = $kinds"
    echo "SPECIFICATION $spec"
    # Replicas are interchangeable; symmetry only for safety (Spec) configs.
    [ "$spec" = Spec ] && echo "SYMMETRY Sym"
    echo "ALIAS Alias"
  } > "SyncCommit_$name.cfg"
}
add() { echo "$2" >> "SyncCommit_$1.cfg"; }

INV="INVARIANTS TypeOK SyncHoldsCommitted ReplicaViewNotAhead AckedLeReceived CommitLeFsync"

for g in core:"$CORE" SetNX:"$SETNX" DbSize:"$DBSIZE"; do
  n=${g%%:*}; k=${g#*:}; s=safe; [ "$n" != core ] && s=safe$n
  cfg "$s" "$k" 1 2 FALSE TRUE TRUE Spec "$OPS" "$R"; add "$s" "$INV"; add "$s" "PROPERTIES Refinement"
done
# With one key and one value, DBSIZE (0/1) is isomorphic to GET (Nil/v1):
# safeDbSize then has exactly the state count of safe and tests nothing new.
# safeDbSize2 uses two keys so that DBSIZE counts something GET cannot see.
K0=$K; K="{k1, k2}"
cfg safeDbSize2 '{"W", "K"}' 1 2 FALSE TRUE TRUE Spec "$OPS" "$R"; add safeDbSize2 "$INV"; add safeDbSize2 "PROPERTIES Refinement"
cfg nodirtyDbSize2 '{"W", "K"}' 1 2 FALSE TRUE FALSE Spec "$OPS" "$R"; add nodirtyDbSize2 "INVARIANTS TypeOK"; add nodirtyDbSize2 "PROPERTIES Refinement"
K=$K0
cfg min0 "$CORE" 0 1 FALSE TRUE TRUE Spec "$OPS" "$R"; add min0 "$INV"; add min0 "PROPERTIES Refinement"
cfg aof '{"W", "R"}' 1 1 TRUE TRUE TRUE Spec "$OPS" "$R"; add aof "$INV"; add aof "PROPERTIES Refinement"

cfg nonatomic "$CORE" 1 2 FALSE FALSE TRUE Spec "$OPS" "$R"; add nonatomic "INVARIANTS TypeOK SyncHoldsCommitted"
cfg nonatomicRefines "$CORE" 1 2 FALSE FALSE TRUE Spec "$OPS" "$R"; add nonatomicRefines "INVARIANTS TypeOK"; add nonatomicRefines "PROPERTIES Refinement"
cfg nodirty '{"W", "R"}' 1 2 FALSE TRUE FALSE Spec "$OPS" "$R"; add nodirty "INVARIANTS TypeOK"; add nodirty "PROPERTIES Refinement"
cfg nodirtySetNX '{"W", "C"}' 1 2 FALSE TRUE FALSE Spec "$OPS" "$R"; add nodirtySetNX "INVARIANTS TypeOK"; add nodirtySetNX "PROPERTIES Refinement"
cfg nodirtyDbSize '{"W", "K"}' 1 2 FALSE TRUE FALSE Spec "$OPS" "$R"; add nodirtyDbSize "INVARIANTS TypeOK"; add nodirtyDbSize "PROPERTIES Refinement"

cfg live "$SETNX" 1 1 FALSE TRUE TRUE HealthySpec 2 "{r1}"; add live "PROPERTIES AllAnswered AcceptedWritesOK"
cfg liveNeg "$CORE" 1 1 FALSE TRUE TRUE HealthySpec 2 "{r1}"; add liveNeg "PROPERTIES NeverOK"

for r in ClusterDown UncommittedWrite LateCommit HeldPrimaryRead HeldReplicaRead UncommittedRead DemotedAhead; do
  cfg "Reach$r" "$CORE" 1 2 FALSE TRUE TRUE Spec "$OPS" "$R"; add "Reach$r" "INVARIANTS Reach_$r"
done
for r in HeldSetNXNoop SetNXSet; do
  cfg "Reach$r" "$SETNX" 1 2 FALSE TRUE TRUE Spec "$OPS" "$R"; add "Reach$r" "INVARIANTS Reach_$r"
done
cfg ReachHeldDbSize "$DBSIZE" 1 2 FALSE TRUE TRUE Spec "$OPS" "$R"; add ReachHeldDbSize "INVARIANTS Reach_HeldDbSize"
cfg ReachAofBinds '{"W", "R"}' 1 1 TRUE TRUE TRUE Spec "$OPS" "$R"; add ReachAofBinds "INVARIANTS Reach_AofBinds"
