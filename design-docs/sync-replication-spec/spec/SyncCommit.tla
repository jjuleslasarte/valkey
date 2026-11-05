----------------------------- MODULE SyncCommit -----------------------------
(***************************************************************************)
(* Step 1 (rev 2, after review): commit rule and reply blocking  *)
(* on one primary. Milestone II: the sync replica set lives on the primary *)
(* only; no Cluster V2, failover or leases (steps 2-4).                    *)
(*                                                                         *)
(* Source: ../../sync-replication.md sections 1 and 2.                     *)
(*                                                                         *)
(* Modelled:                                                               *)
(*   - Replication stream `plog`; an offset is an index into it.           *)
(*   - Writes (SET/DEL) and SETNX execute at once against applied state;   *)
(*     replies are held in the output buffer until the commit offset       *)
(*     passes their boundary.                                              *)
(*   - Commit rule: committed = min over durability sources (sync replica  *)
(*     acks; local AOF fsync offset when AOF = TRUE); never moves back;    *)
(*     advances only while |sync| >= MinSync. Empty set + MinSync = 0:     *)
(*     primary's own offset (or fsync offset).                             *)
(*   - Dirty key tracking on every node, against that node's committed     *)
(*     view: GET and SETNX-returning-0 wait for the last write to the key; *)
(*     DBSIZE (keyspace-wide) waits until committed >= applied offset at   *)
(*     execution.                                                          *)
(*   - Expiry/eviction deletes are replicated writes.                      *)
(*   - Sync replicas get the whole stream; others only up to `commit`.     *)
(*   - REPLCONF ACK / REPLCONF COMMIT; per-replica committed view.         *)
(*   - Primary-local promotion and demotion.                               *)
(*   - Below MinSync: new writes CLUSTERDOWN; executed writes and held     *)
(*     primary reads of dirty keys released UNCOMMITTED.                   *)
(*                                                                         *)
(* Refinement mapping to DurableShard:                                     *)
(*   log    = plog[1..commit]                                              *)
(*   cursor = per replica, highest prefix returned by a completed read     *)
(* A held read linearizes at prefix m = min(applied-at-exec, commit),      *)
(* which lies in [lo, commit] and has the same value (see ReadEffect in    *)
(* DurableShard). No scheduling constraint is needed (rev 1 had one).      *)
(*                                                                         *)
(* Bug switches (negative checks):                                         *)
(*   AtomicPromote = FALSE: catch-up check and "count its acks" in two     *)
(*     steps (doc s4 requires one).                                        *)
(*   TrackDirty = FALSE: primary reads and SETNX do not wait for dirty     *)
(*     keys / applied offset.                                              *)
(*                                                                         *)
(* Not modelled: replica-side AOF (ack after fsync), crashes (no node      *)
(* fails in this step), message loss/reordering, MULTI/EXEC.               *)
(***************************************************************************)
EXTENDS ShardCommon, TLC

CONSTANTS
    Keys, Values, Nil, None, NoReader, MaxOps, MaxSystemWrites,
    Replicas, MinSync, TargetSync, AOF, AtomicPromote, TrackDirty,
    EnabledKinds   \* client op kinds this config invokes (bounds the state space)

ASSUME Nil \notin Values /\ None \notin Values \cup {Nil}
ASSUME MinSync \in Nat /\ TargetSync \in Nat
ASSUME MinSync <= TargetSync /\ TargetSync <= Cardinality(Replicas)
ASSUME AOF \in BOOLEAN /\ AtomicPromote \in BOOLEAN /\ TrackDirty \in BOOLEAN

OpIds    == 1..MaxOps
SystemId == 0
Primary  == "primary"
Nodes    == {Primary} \cup Replicas

WriteKinds == {"W", "C"}
LinKinds   == {"R", "K"}
SerKinds   == {"S", "KS"}
ReadKinds  == LinKinds \cup SerKinds
GetKinds   == {"R", "S"}

Entry == [id : OpIds \cup {SystemId}, key : Keys, val : Values \cup {Nil}]

\* Must equal DurableShard!UnusedOp.
UnusedOp == [kind |-> "unused", key |-> CHOOSE k \in Keys : TRUE, val |-> Nil,
             reader |-> NoReader, lo |-> 0, at |-> None, resp |-> None, seen |-> None]

\* Per-op implementation state, invisible to clients.
\*   node  where it runs        exec  has executed
\*   off   reply boundary: write offset; for reads/SETNX-noop the dirty point
\*   app   applied offset on that node at execution
\*   rv    value computed at execution (reads, SETNX-noop)
\*   set   SETNX took the "set" path
\*   held  reply was held at execution (ghost, reachability only)
NoMeta == [node |-> Primary, exec |-> FALSE, off |-> 0, app |-> 0,
           rv |-> None, set |-> FALSE, held |-> FALSE]

VARIABLES
    plog, commit, sync, pending, recv, acked, rcommit, fsynced,
    ops, meta, nextOp, sysExec

\* Variable groups: each variable is in exactly one group.
primaryVars == <<plog, commit, fsynced, sysExec>>   \* stream, commit, AOF
memberVars  == <<sync, pending>>                    \* sync replica set
replicaVars == <<recv, acked, rcommit>>             \* per-replica stream state
clientVars  == <<ops, meta, nextOp>>                \* client ops + impl metadata

repl == <<primaryVars, memberVars, replicaVars>>
vars == <<repl, clientVars>>

---------------------------------------------------------------------------
(* Helpers *)

LastIdx(k, n) == LastIdxWhere(plog, n, LAMBDA e : e.key = k)

ValAt(k, n)  == IF LastIdx(k, n) = 0 THEN Nil ELSE plog[LastIdx(k, n)].val
SizeAt(n)    == Cardinality({k \in Keys : ValAt(k, n) # Nil})

Writable == Cardinality(sync) >= MinSync

AckCap == IF sync = {} THEN Len(plog) ELSE SetMin({acked[r] : r \in sync})
CommitCap == IF AOF THEN Min2(AckCap, fsynced) ELSE AckCap

View(n) == IF n = Primary THEN commit ELSE rcommit[n]
Applied(n) == IF n = Primary THEN Len(plog) ELSE recv[n]

\* Refinement helper: cursor of the abstract spec.
AbsCursor(r) ==
    LET ats == {ops[id].at : id \in {i \in OpIds : ops[i].kind \in SerKinds
                                     /\ ops[i].reader = r /\ ops[i].resp = "VALUE"}}
    IN  IF ats = {} THEN 0 ELSE SetMax(ats)

---------------------------------------------------------------------------

Init ==
    /\ plog    = << >>
    /\ commit  = 0
    /\ sync    = {}
    /\ pending = {}
    /\ recv    = [r \in Replicas |-> 0]
    /\ acked   = [r \in Replicas |-> 0]
    /\ rcommit = [r \in Replicas |-> 0]
    /\ fsynced = 0
    /\ ops     = [id \in OpIds |-> UnusedOp]
    /\ meta    = [id \in OpIds |-> NoMeta]
    /\ nextOp  = 1
    /\ sysExec = 0

---------------------------------------------------------------------------
(* Clients *)

InvokeWrite(kind, k, v) ==
    /\ kind \in EnabledKinds
    /\ nextOp \in OpIds
    /\ ops'    = [ops EXCEPT ![nextOp] = [UnusedOp EXCEPT
                    !.kind = kind, !.key = k, !.val = v, !.lo = commit]]
    /\ meta'   = [meta EXCEPT ![nextOp] = NoMeta]
    /\ nextOp' = nextOp + 1
    /\ UNCHANGED repl

\* Primary reads are linearizable; replica reads serializable.
InvokeRead(get, k, n) ==
    /\ (IF n = Primary THEN (IF get THEN "R" ELSE "K")
                        ELSE (IF get THEN "S" ELSE "KS")) \in EnabledKinds
    /\ nextOp \in OpIds
    /\ ops' = [ops EXCEPT ![nextOp] =
                 IF n = Primary
                 THEN [UnusedOp EXCEPT !.kind = IF get THEN "R" ELSE "K",
                                       !.key = k, !.lo = commit]
                 ELSE [UnusedOp EXCEPT !.kind = IF get THEN "S" ELSE "KS",
                                       !.key = k, !.reader = n, !.lo = AbsCursor(n)]]
    /\ meta'   = [meta EXCEPT ![nextOp] = [NoMeta EXCEPT !.node = n]]
    /\ nextOp' = nextOp + 1
    /\ UNCHANGED repl

---------------------------------------------------------------------------
(* Primary: writes *)

ExecWrite(id) ==
    /\ ops[id].kind = "W"
    /\ ~meta[id].exec
    /\ Writable
    /\ plog' = Append(plog, [id |-> id, key |-> ops[id].key, val |-> ops[id].val])
    /\ meta' = [meta EXCEPT ![id].exec = TRUE, ![id].off = Len(plog) + 1,
                            ![id].app = Len(plog) + 1, ![id].held = TRUE]
    /\ UNCHANGED <<memberVars, replicaVars, commit, fsynced, sysExec, ops, nextOp>>

\* SETNX against the applied state. Absent: it writes (a replicated entry).
\* Present: no entry; the reply "0" depends on the last write to the key,
\* so it waits for that write like a read does (unless ~TrackDirty).
ExecSetNX(id) ==
    LET k == ops[id].key
        a == Len(plog)
        w == LastIdx(k, a)
    IN  /\ ops[id].kind = "C"
        /\ ~meta[id].exec
        /\ Writable
        /\ IF ValAt(k, a) = Nil
           THEN /\ plog' = Append(plog, [id |-> id, key |-> k, val |-> ops[id].val])
                /\ meta' = [meta EXCEPT ![id].exec = TRUE, ![id].off = a + 1,
                                        ![id].app = a + 1, ![id].set = TRUE,
                                        ![id].held = TRUE]
           ELSE /\ plog' = plog
                /\ meta' = [meta EXCEPT ![id].exec = TRUE,
                                        ![id].off = IF TrackDirty THEN w ELSE 0,
                                        ![id].app = a, ![id].rv = ValAt(k, a),
                                        ![id].held = w > commit]
        /\ UNCHANGED <<memberVars, replicaVars, commit, fsynced, sysExec, ops, nextOp>>

RejectWrite(id) ==
    /\ ops[id].kind \in WriteKinds
    /\ ~meta[id].exec
    /\ ~Writable
    /\ ops'  = [ops EXCEPT ![id].resp = "CLUSTERDOWN"]
    /\ meta' = [meta EXCEPT ![id].exec = TRUE]
    /\ UNCHANGED <<repl, nextOp>>

\* W or SETNX-set: reply released once its entry committed.
RespondWriteOK(id) ==
    /\ ops[id].kind \in WriteKinds
    /\ ops[id].resp = None
    /\ meta[id].exec
    /\ (ops[id].kind = "W" \/ meta[id].set)
    /\ meta[id].off \in 1..commit
    /\ ops' = [ops EXCEPT ![id].resp = "OK"]
    /\ UNCHANGED <<repl, meta, nextOp>>

\* SETNX-noop: linearize once its dirty point is committed, then reply 0.
LinearizeSetNXNoop(id) ==
    /\ ops[id].kind = "C"
    /\ meta[id].exec /\ ~meta[id].set
    /\ ops[id].resp = None
    /\ ops[id].seen = None
    /\ meta[id].off <= commit
    /\ ops' = [ops EXCEPT ![id].seen = meta[id].rv,
                          ![id].at = Min2(meta[id].app, commit)]
    /\ UNCHANGED <<repl, meta, nextOp>>

RespondSetNXNoop(id) ==
    /\ ops[id].kind = "C"
    /\ ~meta[id].set
    /\ ops[id].resp = None
    /\ ops[id].seen \notin {None, Nil}
    /\ ops' = [ops EXCEPT ![id].resp = "OK"]
    /\ UNCHANGED <<repl, meta, nextOp>>

\* Below MinSync: executed writes (and held SETNX-noops) are released with
\* UNCOMMITTED. A write stays in the stream and may still commit.
ReleaseWriteUncommitted(id) ==
    /\ ops[id].kind \in WriteKinds
    /\ ops[id].resp = None
    /\ ops[id].seen = None
    /\ meta[id].exec
    /\ meta[id].off > commit
    /\ ~Writable
    /\ ops' = [ops EXCEPT ![id].resp = "UNCOMMITTED"]
    /\ UNCHANGED <<repl, meta, nextOp>>

Expire(k) ==
    /\ sysExec < MaxSystemWrites
    /\ ValAt(k, Len(plog)) # Nil
    /\ plog'    = Append(plog, [id |-> SystemId, key |-> k, val |-> Nil])
    /\ sysExec' = sysExec + 1
    /\ UNCHANGED <<memberVars, replicaVars, clientVars, commit, fsynced>>

---------------------------------------------------------------------------
(* Reads on any node, with dirty tracking against that node's view *)

ExecRead(id) ==
    LET nd  == meta[id].node
        k   == ops[id].key
        a   == Applied(nd)
        get == ops[id].kind \in GetKinds
        dp  == IF get THEN LastIdx(k, a) ELSE a      \* dirty point
        noWait == nd = Primary /\ ~TrackDirty
    IN  /\ ops[id].kind \in ReadKinds
        /\ ~meta[id].exec
        /\ meta' = [meta EXCEPT ![id].exec = TRUE,
                                ![id].off = IF noWait THEN 0 ELSE dp,
                                ![id].app = a,
                                ![id].rv  = IF get THEN ValAt(k, a) ELSE SizeAt(a),
                                ![id].held = dp > View(nd)]
        /\ UNCHANGED <<repl, ops, nextOp>>

\* The node's committed view has passed the dirty point.
LinearizeRead(id) ==
    /\ ops[id].kind \in ReadKinds
    /\ meta[id].exec
    /\ ops[id].resp = None
    /\ ops[id].seen = None
    /\ meta[id].off <= View(meta[id].node)
    /\ ops' = [ops EXCEPT ![id].seen = meta[id].rv,
                          ![id].at = Min2(meta[id].app, commit)]
    /\ UNCHANGED <<repl, meta, nextOp>>

RespondRead(id) ==
    /\ ops[id].kind \in ReadKinds
    /\ ops[id].resp = None
    /\ ops[id].seen # None
    /\ ops' = [ops EXCEPT ![id].resp = "VALUE"]
    /\ UNCHANGED <<repl, meta, nextOp>>

\* Doc fault table: below min, reads of keys with uncommitted writes are
\* released with UNCOMMITTED. Primary only: a replica cannot tell that the
\* primary's set fell below the minimum (doc gap, see README).
ReleaseReadUncommitted(id) ==
    /\ ops[id].kind \in LinKinds
    /\ ops[id].resp = None
    /\ ops[id].seen = None
    /\ meta[id].exec
    /\ meta[id].off > commit
    /\ ~Writable
    /\ ops' = [ops EXCEPT ![id].resp = "UNCOMMITTED"]
    /\ UNCHANGED <<repl, meta, nextOp>>

---------------------------------------------------------------------------
(* Commit rule and durability sources *)

\* When the committed entry belongs to a SETNX, that is its effect point:
\* record it (abstract CommitSetNX).
AdvanceCommit ==
    /\ Writable
    /\ commit < CommitCap
    /\ commit' = commit + 1
    /\ LET e == plog[commit + 1]
       IN  ops' = IF e.id # SystemId /\ ops[e.id].kind = "C"
                  THEN [ops EXCEPT ![e.id].seen = Nil, ![e.id].at = commit]
                  ELSE ops
    /\ UNCHANGED <<memberVars, replicaVars, plog, fsynced, sysExec, meta, nextOp>>

\* Background AOF write + fsync (doc s1: off the main thread).
Fsync ==
    /\ AOF
    /\ fsynced < Len(plog)
    /\ fsynced' = fsynced + 1
    /\ UNCHANGED <<memberVars, replicaVars, clientVars, plog, commit, sysExec>>

---------------------------------------------------------------------------
(* Replication stream *)

Receive(r) ==
    /\ recv[r] < Len(plog)
    /\ r \in sync \/ recv[r] < commit
    /\ recv' = [recv EXCEPT ![r] = @ + 1]
    /\ UNCHANGED <<primaryVars, memberVars, clientVars, acked, rcommit>>

Ack(r) ==
    /\ acked[r] < recv[r]
    /\ acked' = [acked EXCEPT ![r] = recv[r]]
    /\ UNCHANGED <<primaryVars, memberVars, clientVars, recv, rcommit>>

SendCommit(r) ==
    /\ rcommit[r] < commit
    /\ rcommit' = [rcommit EXCEPT ![r] = commit]
    /\ UNCHANGED <<primaryVars, memberVars, clientVars, recv, acked>>

---------------------------------------------------------------------------
(* Primary-local sync set membership *)

Promote(r) ==
    /\ AtomicPromote
    /\ r \notin sync
    /\ Cardinality(sync) < TargetSync
    /\ acked[r] >= commit
    /\ sync' = sync \cup {r}
    /\ UNCHANGED <<primaryVars, replicaVars, clientVars, pending>>

StartPromote(r) ==
    /\ ~AtomicPromote
    /\ r \notin sync \cup pending
    /\ Cardinality(sync \cup pending) < TargetSync
    /\ acked[r] >= commit
    /\ pending' = pending \cup {r}
    /\ UNCHANGED <<primaryVars, replicaVars, clientVars, sync>>

FinishPromote(r) ==
    /\ r \in pending
    /\ sync'    = sync \cup {r}
    /\ pending' = pending \ {r}
    /\ UNCHANGED <<primaryVars, replicaVars, clientVars>>

Demote(r) ==
    /\ r \in sync
    /\ sync' = sync \ {r}
    /\ UNCHANGED <<primaryVars, replicaVars, clientVars, pending>>

---------------------------------------------------------------------------

OpStep(id) ==
    \/ ExecWrite(id) \/ ExecSetNX(id) \/ RejectWrite(id) \/ RespondWriteOK(id)
    \/ LinearizeSetNXNoop(id) \/ RespondSetNXNoop(id) \/ ReleaseWriteUncommitted(id)
    \/ ExecRead(id) \/ LinearizeRead(id) \/ RespondRead(id) \/ ReleaseReadUncommitted(id)

NextNoDemote ==
    \/ \E kd \in WriteKinds, k \in Keys, v \in Values \cup {Nil} :
          (kd = "C" => v # Nil) /\ InvokeWrite(kd, k, v)
    \/ \E g \in BOOLEAN, k \in Keys, n \in Nodes : InvokeRead(g, k, n)
    \/ \E id \in OpIds : OpStep(id)
    \/ \E k \in Keys : Expire(k)
    \/ AdvanceCommit \/ Fsync
    \/ \E r \in Replicas :
          Receive(r) \/ Ack(r) \/ SendCommit(r)
          \/ Promote(r) \/ StartPromote(r) \/ FinishPromote(r)

Next == NextNoDemote \/ \E r \in Replicas : Demote(r)

Spec == Init /\ [][Next]_vars

\* Healthy shard: no demotions; everything that can progress does,
\* including promotion up to the target.
Fairness ==
    /\ \A id \in OpIds :
          /\ WF_vars(ExecWrite(id) \/ ExecSetNX(id) \/ RejectWrite(id))
          /\ WF_vars(RespondWriteOK(id))
          /\ WF_vars(LinearizeSetNXNoop(id)) /\ WF_vars(RespondSetNXNoop(id))
          /\ WF_vars(ExecRead(id)) /\ WF_vars(LinearizeRead(id))
          /\ WF_vars(RespondRead(id))
    /\ WF_vars(AdvanceCommit) /\ WF_vars(Fsync)
    /\ \A r \in Replicas :
          /\ WF_vars(Receive(r)) /\ WF_vars(Ack(r)) /\ WF_vars(SendCommit(r))
          /\ WF_vars(Promote(r))

HealthySpec == Init /\ [][NextNoDemote]_vars /\ Fairness

---------------------------------------------------------------------------
(* Refinement *)

AbsLog    == SubSeq(plog, 1, commit)
AbsEverIn == {plog[i].id : i \in 1..commit} \ {SystemId}
AbsSys    == Cardinality({i \in 1..commit : plog[i].id = SystemId})

DS == INSTANCE DurableShard
        WITH log <- AbsLog, everIn <- AbsEverIn, sysWrites <- AbsSys,
             lossy <- FALSE, AllowLossyOps <- FALSE, Readers <- Replicas,
             cursor <- [r \in Replicas |-> AbsCursor(r)]

Refinement  == DS!Spec
AllAnswered == DS!AllOpsAnswered

\* Every write the primary executed while writable eventually gets OK.
AcceptedWritesOK ==
    \A id \in OpIds :
        (ops[id].kind = "W" /\ meta[id].off > 0) ~> (ops[id].resp = "OK")

\* Negative control for liveness: must be VIOLATED under HealthySpec.
NeverOK == [](\A id \in OpIds : ops[id].resp # "OK")

---------------------------------------------------------------------------
(* Invariants *)

MetaRec == [node : Nodes, exec : BOOLEAN, off : Nat, app : Nat,
            rv : DS!Observed \cup {None}, set : BOOLEAN, held : BOOLEAN]

TypeOK ==
    /\ plog \in Seq(Entry)
    /\ commit \in 0..Len(plog)
    /\ sync \subseteq Replicas /\ pending \subseteq Replicas /\ sync \cap pending = {}
    /\ recv \in [Replicas -> 0..Len(plog)]
    /\ acked \in [Replicas -> Nat] /\ rcommit \in [Replicas -> Nat]
    /\ fsynced \in 0..Len(plog)
    /\ ops \in [OpIds -> DS!OpRec]
    /\ meta \in [OpIds -> MetaRec]
    /\ nextOp \in 1..(MaxOps + 1)
    /\ sysExec \in 0..MaxSystemWrites

SyncHoldsCommitted   == \A r \in sync : acked[r] >= commit
ReplicaViewNotAhead  == \A r \in Replicas : rcommit[r] <= commit
AckedLeReceived      == \A r \in Replicas : acked[r] <= recv[r]
CommitLeFsync        == AOF => commit <= fsynced

---------------------------------------------------------------------------
(* TLC: trace alias and replica symmetry *)

\* Trace view: replication state plus each op's client-visible fields.
Alias == [plog |-> plog, commit |-> commit, fsynced |-> fsynced,
          sync |-> sync, pending |-> pending,
          recv |-> recv, acked |-> acked, rcommit |-> rcommit,
          ops |-> [id \in OpIds |-> [kind |-> ops[id].kind, key |-> ops[id].key,
                                     resp |-> ops[id].resp, seen |-> ops[id].seen,
                                     at |-> ops[id].at, node |-> meta[id].node,
                                     off |-> meta[id].off]],
          absLog |-> AbsLog]

\* Replicas are interchangeable: nothing names or CHOOSEs a specific one.
Sym == Permutations(Replicas)

---------------------------------------------------------------------------
(* Reachability checks: each must be VIOLATED. *)

Reach_ClusterDown      == ~(\E id \in OpIds : ops[id].resp = "CLUSTERDOWN")
Reach_UncommittedWrite == ~(\E id \in OpIds : ops[id].kind = "W" /\ ops[id].resp = "UNCOMMITTED")
Reach_LateCommit ==
    ~(\E id \in OpIds : ops[id].kind = "W" /\ ops[id].resp = "UNCOMMITTED"
                        /\ meta[id].off \in 1..commit)
Reach_HeldPrimaryRead ==
    ~(\E id \in OpIds : ops[id].kind = "R" /\ meta[id].held /\ ops[id].resp = "VALUE")
Reach_HeldReplicaRead ==
    ~(\E id \in OpIds : ops[id].kind = "S" /\ meta[id].held /\ ops[id].resp = "VALUE")
Reach_HeldDbSize ==
    ~(\E id \in OpIds : ops[id].kind \in {"K", "KS"} /\ meta[id].held /\ ops[id].resp = "VALUE")
Reach_HeldSetNXNoop ==
    ~(\E id \in OpIds : ops[id].kind = "C" /\ ~meta[id].set /\ meta[id].held
                        /\ ops[id].resp = "OK")
Reach_SetNXSet ==
    ~(\E id \in OpIds : ops[id].kind = "C" /\ meta[id].set /\ ops[id].resp = "OK")
Reach_UncommittedRead == ~(\E id \in OpIds : ops[id].kind \in LinKinds /\ ops[id].resp = "UNCOMMITTED")
Reach_DemotedAhead    == ~(\E r \in Replicas : r \notin sync /\ recv[r] > commit)
\* AOF is the binding durability source: acks are ahead of fsync.
Reach_AofBinds ==
    ~(AOF /\ sync # {} /\ fsynced < AckCap /\ commit = fsynced /\ commit < Len(plog))
=============================================================================
