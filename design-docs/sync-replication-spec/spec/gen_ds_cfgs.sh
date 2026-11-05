#!/usr/bin/env bash
# Generates the DurableShard_*.cfg files.
cd "$(dirname "$0")"
hdr() { cat <<X
CONSTANTS
    Keys = {k1, k2}
    Values = {v1, v2}
    Nil = Nil
    None = None
    NoReader = NoReader
    Readers = {r1}
    MaxOps = 3
    MaxSystemWrites = 1
    AllowLossyOps = $1
SPECIFICATION Spec
X
}
{ hdr FALSE; echo "INVARIANTS TypeOK AckedWritesDurable RejectedNeverCommitted NoDuplicateCommit ReadsSeeOnlyCommitted SetNXOnlyWhenAbsent"; echo "PROPERTIES AppendOnly"; } > DurableShard_safe.cfg
{ hdr TRUE; echo "INVARIANTS AckedWritesDurableStrict"; } > DurableShard_lossy.cfg
for r in AckedWrite ReadSeesWrite CommitAfterUncommitted ReadAfterExpiry StaleRead SetNXNoop SetNXSet DbSize; do
  { hdr FALSE; echo "INVARIANTS Reach_$r"; } > DurableShard_Reach$r.cfg; done
