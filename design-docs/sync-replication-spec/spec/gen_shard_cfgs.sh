#!/usr/bin/env bash
# Generates Shard_*.cfg. Every config gets SYMMETRY Sym (no property names a
# non-initial node) and ALIAS Alias; TypeOK is checked by every non-Reach
# config that checks invariants.
#
# Shard_m_*: step 2 scope (former Membership.tla): MaxOps=2, no restarts, no
#   forced failover, and none of the step 3/4 defences (no catch-up re-check
#   at step 4, no lease fence), so membership alone is checked.
# Shard_f_*: step 3 scope (former Failover.tla): MaxOps=1, one restart.
cd "$(dirname "$0")"

# cfg NAME k=v ...   Writes Shard_NAME.cfg; the k=v pairs override defaults.
cfg() {
  local name=$1; shift
  local -A c=(
    [MaxOps]=1 [MinSync]=1 [TargetSync]=2 [MaxCfg]=5 [MaxCrashes]=1 [MaxRestarts]=1
    [AtomicPromote]=TRUE [EarlyDrop]=FALSE [EligibleFirst]=FALSE
    [ReconcileFirst]=TRUE [StepDownRelease]=TRUE
    [IncCheck]=TRUE [AllowForce]=FALSE [RestoreSync]=TRUE
    [CatchUpAtEligible]=TRUE [LeaseFence]=TRUE)
  local kv; for kv in "$@"; do c[${kv%%=*}]=${kv#*=}; done
  {
    echo "CONSTANTS"
    echo "    Keys = {k1}"
    echo "    Values = {v1}"
    echo "    Nil = Nil"
    echo "    None = None"
    echo "    NoReader = NoReader"
    echo "    Nodes = {n1, n2, n3}"
    echo "    InitPrim = n1"
    local k
    for k in MaxOps MinSync TargetSync MaxCfg MaxCrashes MaxRestarts \
             AtomicPromote EarlyDrop EligibleFirst ReconcileFirst StepDownRelease \
             IncCheck AllowForce RestoreSync CatchUpAtEligible LeaseFence; do
      echo "    $k = ${c[$k]}"
    done
    echo "SPECIFICATION Spec"
    echo "SYMMETRY Sym"
    echo "ALIAS Alias"
  } > "Shard_$name.cfg"
}
add() { echo "$2" >> "Shard_$1.cfg"; }

# Step 2 scope.
M=(MaxOps=2 MaxRestarts=0 AllowForce=FALSE CatchUpAtEligible=FALSE LeaseFence=FALSE)
m() { local n=$1; shift; cfg "m_$n" "${M[@]}" "$@"; }
MINV="INVARIANTS TypeOK AckedDurable EligibleHoldsCommitted CommittedAgree"
m safe;                         add m_safe "$MINV"; add m_safe "PROPERTIES Refinement"
m safeMin0 MinSync=0;           add m_safeMin0 "$MINV"; add m_safeMin0 "PROPERTIES Refinement"
m safeCfg7 MaxCfg=7;            add m_safeCfg7 "$MINV"; add m_safeCfg7 "PROPERTIES Refinement"
m nonatomic AtomicPromote=FALSE;     add m_nonatomic "INVARIANTS TypeOK AckedDurable EligibleHoldsCommitted"
# Loss shows only once the new primary commits over the lost write: one
# more config change than the state-level check needs.
m nonatomicLoss AtomicPromote=FALSE MaxCfg=6; add m_nonatomicLoss "INVARIANTS TypeOK AckedDurable"
m earlydrop EarlyDrop=TRUE;          add m_earlydrop "INVARIANTS TypeOK AckedDurable EligibleHoldsCommitted"
m earlydropLoss EarlyDrop=TRUE;      add m_earlydropLoss "INVARIANTS TypeOK AckedDurable"
m eligfirst EligibleFirst=TRUE;      add m_eligfirst "INVARIANTS TypeOK AckedDurable EligibleHoldsCommitted"
m eligfirstLoss EligibleFirst=TRUE;  add m_eligfirstLoss "INVARIANTS TypeOK AckedDurable"
m docAsWritten ReconcileFirst=FALSE; add m_docAsWritten "INVARIANTS TypeOK AckedDurable EligibleHoldsCommitted"
m docAsWrittenLoss ReconcileFirst=FALSE; add m_docAsWrittenLoss "INVARIANTS TypeOK AckedDurable"
# F1 with the lease fence on, so the loss cannot come from a deposed primary
# committing late (that is F8): one more config change lets the empty new
# primary become writable and commit over the lost write.
m docAsWrittenLossFenced ReconcileFirst=FALSE LeaseFence=TRUE MaxCfg=6
add m_docAsWrittenLossFenced "INVARIANTS TypeOK AckedDurable"
m noStepDown MinSync=0 StepDownRelease=FALSE; add m_noStepDown "INVARIANTS TypeOK AckedDurable"
for r in Eligible Takeover AckSurvivesTakeover NewPrimCommits Demoted Resync Reconcile; do
  m "Reach$r"; add "m_Reach$r" "INVARIANTS Reach_$r"
done

# Step 3 scope.
f() { local n=$1; shift; cfg "f_$n" "$@"; }
FINV="INVARIANTS TypeOK AckedDurable CommittedAgree EligibleHoldsCommitted"
f safe;                  add f_safe "$FINV"; add f_safe "PROPERTIES Refinement UnavailableWithoutAuthority"
f safeMin0 MinSync=0;    add f_safeMin0 "$FINV"; add f_safeMin0 "PROPERTIES Refinement UnavailableWithoutAuthority"
f force AllowForce=TRUE; add f_force "$FINV"
f forceResurrect AllowForce=TRUE; add f_forceResurrect "PROPERTIES Refinement"
f forceLoss AllowForce=TRUE;      add f_forceLoss "INVARIANTS TypeOK AckedDurable"
f noInc IncCheck=FALSE;           add f_noInc "INVARIANTS TypeOK AckedDurable"
f noIncHolds IncCheck=FALSE;      add f_noIncHolds "INVARIANTS TypeOK EligibleHoldsCommitted"
for r in RestartEmpty TakeoverAfterRestart Stuck RejoinEligible; do
  f "Reach$r"; add "f_Reach$r" "INVARIANTS Reach_$r"
done
f ReachForcedLoss AllowForce=TRUE; add f_ReachForcedLoss "INVARIANTS Reach_ForcedLoss"
f noRestore MinSync=0 RestoreSync=FALSE;     add f_noRestore "INVARIANTS TypeOK EligibleHoldsCommitted"
f noRestoreLoss MinSync=0 RestoreSync=FALSE; add f_noRestoreLoss "INVARIANTS TypeOK AckedDurable"
f noRestoreMin1 RestoreSync=FALSE;     add f_noRestoreMin1 "INVARIANTS TypeOK AckedDurable EligibleHoldsCommitted"
f noRestoreMin1Loss RestoreSync=FALSE; add f_noRestoreMin1Loss "INVARIANTS TypeOK AckedDurable"
f noCatchUp CatchUpAtEligible=FALSE;     add f_noCatchUp "INVARIANTS TypeOK EligibleHoldsCommitted"
f noCatchUpLoss CatchUpAtEligible=FALSE; add f_noCatchUpLoss "INVARIANTS TypeOK AckedDurable"
f noFence LeaseFence=FALSE;              add f_noFence "INVARIANTS TypeOK AckedDurable"
