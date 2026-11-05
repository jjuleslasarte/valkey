---------------------------- MODULE DurableShard ----------------------------
(***************************************************************************)
(* Step 0: abstract client contract of a durable Valkey shard.             *)
(*                                                                         *)
(* Source: "Valkey Durability: Synchronous Replication Architecture"       *)
(* (../../sync-replication.md): Requirements, section 1, "Write behavior   *)
(* during faults", "Consistency and Durability Properties".                *)
(*                                                                         *)
(* WHAT the shard promises, not HOW: no primaries, offsets, leases, Raft.  *)
(* Every concrete model must refine this spec.                             *)
(*                                                                         *)
(* State: one totally ordered history `log` of committed writes, which     *)
(* only grows (except through the explicit lossy action).                  *)
(*                                                                         *)
(* Operations (rev 3, after review):                             *)
(*   W  write (SET; a DEL is a write of Nil)                               *)
(*   C  conditional write SETNX: sets only if the key is absent; its reply *)
(*      (1 or 0) depends on state, so it must never reflect uncommitted    *)
(*      data (doc s1, "non-replicating replies, such as SETNX returning 0")*)
(*   R  linearizable GET    (primary; sync replica holding a read lease)   *)
(*   S  serializable GET    (async replica; sync replica without a lease)  *)
(*   K  linearizable DBSIZE (keyspace-wide read)                           *)
(*   KS serializable DBSIZE                                                *)
(*                                                                         *)
(* Reads. A read stamps lo at invocation. Its effect observes the state at *)
(* some committed prefix n with lo <= n <= Len(log), and records n in at.  *)
(*   - Linearizable reads: lo = Len(log) at invocation. Since log grows    *)
(*     one entry at a time, prefix n existed at an instant between invoke  *)
(*     and effect, so this is exactly linearizability for this object.     *)
(*   - Serializable reads: lo = cursor[reader], the highest prefix that    *)
(*     reader has returned in an earlier COMPLETED read. So reads from one *)
(*     endpoint never go backwards across non-overlapping calls, but may   *)
(*     lag arbitrarily. Overlapping reads may be ordered either way.       *)
(*   Uncommitted writes are never in log, so no read observes them.        *)
(*                                                                         *)
(* Write outcomes (doc "Write behavior during faults"):                    *)
(*   OK          committed before the reply.                               *)
(*   CLUSTERDOWN rejected before execution; it never takes effect.         *)
(*   UNCOMMITTED outcome unknown: it may commit later, or never. NOTE: a   *)
(*               commit after an UNCOMMITTED reply puts the effect after   *)
(*               the response, so such writes are not linearizable. The    *)
(*               doc allows this deliberately ("treat it like a timeout"). *)
(* Read outcomes: VALUE, or UNCOMMITTED (doc fault table; no data).        *)
(*                                                                         *)
(* Data loss only through LossyTruncate (forced failover to an ineligible  *)
(* node, operator recovery after correlated loss), off unless              *)
(* AllowLossyOps = TRUE.                                                   *)
(*                                                                         *)
(* Decisions recorded (2026-11-03): min-sync-replicas = 0    *)
(* and the primary loses its data -> shard unavailable, not an allowed     *)
(* loss. MULTI/EXEC and Lua deferred. Liveness stated as AllOpsAnswered,   *)
(* checked by concrete models under a healthy-shard assumption.            *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Keys, Values, Nil,
    None,             \* model value: "not yet" (no reply, nothing observed)
    NoReader,         \* model value: op has no reader endpoint
    Readers,          \* endpoints that serve serializable reads (replica ids)
    MaxOps, MaxSystemWrites,
    AllowLossyOps

ASSUME Nil \notin Values
ASSUME None \notin Values \cup {Nil}
ASSUME MaxOps \in Nat /\ MaxSystemWrites \in Nat
ASSUME AllowLossyOps \in BOOLEAN

OpIds    == 1..MaxOps
SystemId == 0

WriteKinds == {"W", "C"}
LinKinds   == {"R", "K"}
SerKinds   == {"S", "KS"}
ReadKinds  == LinKinds \cup SerKinds
GetKinds   == {"R", "S"}
SizeKinds  == {"K", "KS"}

WriteResults == {"OK", "CLUSTERDOWN", "UNCOMMITTED"}
ReadResults  == {"VALUE", "UNCOMMITTED"}

Entry == [id : OpIds \cup {SystemId}, key : Keys, val : Values \cup {Nil}]

Observed == Values \cup {Nil} \cup (0..Cardinality(Keys))

OpRec == [kind   : {"unused"} \cup WriteKinds \cup ReadKinds,
          key    : Keys,
          val    : Values \cup {Nil},        \* value written (W, C)
          reader : Readers \cup {NoReader},
          lo     : Nat,                       \* lowest prefix allowed (reads)
          at     : Nat \cup {None},           \* prefix observed (reads, C noop)
          resp   : WriteResults \cup ReadResults \cup {None},
          seen   : Observed \cup {None}]      \* value observed; for C: Nil = set, else no-op

VARIABLES
    log,        \* Seq(Entry): committed history
    ops,        \* [OpIds -> OpRec]
    nextOp,
    everIn,     \* ghost: ids ever committed
    sysWrites,
    lossy,      \* ghost: an explicit lossy action ran
    cursor      \* [Readers -> Nat]: highest prefix returned by a completed S/KS read

vars == <<log, ops, nextOp, everIn, sysWrites, lossy, cursor>>

---------------------------------------------------------------------------
(* Helpers *)

Committed(id) == \E i \in 1..Len(log) : log[i].id = id

ValueAt(k, n) ==
    LET idx == {i \in 1..n : log[i].key = k}
    IN  IF idx = {} THEN Nil
        ELSE log[CHOOSE i \in idx : \A j \in idx : j <= i].val

ValueOf(k) == ValueAt(k, Len(log))

SizeAt(n) == Cardinality({k \in Keys : ValueAt(k, n) # Nil})

Observe(kind, k, n) == IF kind \in GetKinds THEN ValueAt(k, n) ELSE SizeAt(n)

UnusedOp == [kind |-> "unused", key |-> CHOOSE k \in Keys : TRUE, val |-> Nil,
             reader |-> NoReader, lo |-> 0, at |-> None, resp |-> None, seen |-> None]

---------------------------------------------------------------------------

Init ==
    /\ log       = << >>
    /\ ops       = [id \in OpIds |-> UnusedOp]
    /\ nextOp    = 1
    /\ everIn    = {}
    /\ sysWrites = 0
    /\ lossy     = FALSE
    /\ cursor    = [r \in Readers |-> 0]

---------------------------------------------------------------------------
(* Writes: W and C *)

InvokeWrite(kind, k, v) ==
    /\ nextOp \in OpIds
    /\ ops'    = [ops EXCEPT ![nextOp] = [UnusedOp EXCEPT
                    !.kind = kind, !.key = k, !.val = v, !.lo = Len(log)]]
    /\ nextOp' = nextOp + 1
    /\ UNCHANGED <<log, everIn, sysWrites, lossy, cursor>>

\* Effect of a W: join the history. Allowed before any reply or after
\* UNCOMMITTED; never after CLUSTERDOWN, never twice.
CommitWrite(id) ==
    /\ ops[id].kind = "W"
    /\ ops[id].resp \in {None, "UNCOMMITTED"}
    /\ id \notin everIn
    /\ log'    = Append(log, [id |-> id, key |-> ops[id].key, val |-> ops[id].val])
    /\ everIn' = everIn \cup {id}
    /\ UNCHANGED <<ops, nextOp, sysWrites, lossy, cursor>>

\* Effect of a C that sets: the key is absent in the CURRENT history.
CommitSetNX(id) ==
    /\ ops[id].kind = "C"
    /\ ops[id].resp \in {None, "UNCOMMITTED"}
    /\ ops[id].seen = None
    /\ id \notin everIn
    /\ ValueOf(ops[id].key) = Nil
    /\ log'    = Append(log, [id |-> id, key |-> ops[id].key, val |-> ops[id].val])
    /\ everIn' = everIn \cup {id}
    /\ ops'    = [ops EXCEPT ![id].seen = Nil, ![id].at = Len(log)]
    /\ UNCHANGED <<nextOp, sysWrites, lossy, cursor>>

\* Effect of a C that does nothing: the key is present at a committed
\* prefix between invocation and now (linearizable, like R).
NoopSetNX(id) ==
    /\ ops[id].kind = "C"
    /\ ops[id].resp = None
    /\ ops[id].seen = None
    /\ \E n \in ops[id].lo..Len(log) :
          /\ ValueAt(ops[id].key, n) # Nil
          /\ ops' = [ops EXCEPT ![id].seen = ValueAt(ops[id].key, n), ![id].at = n]
    /\ UNCHANGED <<log, nextOp, everIn, sysWrites, lossy, cursor>>

\* OK only after the effect, and (if it wrote) only once committed. "Has
\* committed" (everIn), not "is in log now": a write can commit and then be
\* lost by an explicit lossy event before its reply is delivered.
RespondWriteOK(id) ==
    /\ ops[id].kind \in WriteKinds
    /\ ops[id].resp = None
    /\ \/ ops[id].kind = "W" /\ id \in everIn
       \/ ops[id].kind = "C" /\ ops[id].seen = Nil /\ id \in everIn
       \/ ops[id].kind = "C" /\ ops[id].seen \notin {None, Nil}
    /\ ops' = [ops EXCEPT ![id].resp = "OK"]
    /\ UNCHANGED <<log, nextOp, everIn, sysWrites, lossy, cursor>>

RespondWriteRejected(id) ==
    /\ ops[id].kind \in WriteKinds
    /\ ops[id].resp = None
    /\ ops[id].seen = None
    /\ id \notin everIn
    /\ ops' = [ops EXCEPT ![id].resp = "CLUSTERDOWN"]
    /\ UNCHANGED <<log, nextOp, everIn, sysWrites, lossy, cursor>>

\* A C that already took effect as a no-op has a definite outcome, so it
\* is answered OK, never UNCOMMITTED.
RespondWriteUncommitted(id) ==
    /\ ops[id].kind \in WriteKinds
    /\ ops[id].resp = None
    /\ ops[id].seen \in {None, Nil}
    /\ ops' = [ops EXCEPT ![id].resp = "UNCOMMITTED"]
    /\ UNCHANGED <<log, nextOp, everIn, sysWrites, lossy, cursor>>

---------------------------------------------------------------------------
(* Reads *)

InvokeLinRead(kind, k) ==
    /\ kind \in LinKinds
    /\ nextOp \in OpIds
    /\ ops'    = [ops EXCEPT ![nextOp] = [UnusedOp EXCEPT
                    !.kind = kind, !.key = k, !.lo = Len(log)]]
    /\ nextOp' = nextOp + 1
    /\ UNCHANGED <<log, everIn, sysWrites, lossy, cursor>>

InvokeSerRead(kind, k, r) ==
    /\ kind \in SerKinds
    /\ nextOp \in OpIds
    /\ ops'    = [ops EXCEPT ![nextOp] = [UnusedOp EXCEPT
                    !.kind = kind, !.key = k, !.reader = r, !.lo = cursor[r]]]
    /\ nextOp' = nextOp + 1
    /\ UNCHANGED <<log, everIn, sysWrites, lossy, cursor>>

ReadEffect(id) ==
    /\ ops[id].kind \in ReadKinds
    /\ ops[id].resp = None
    /\ ops[id].seen = None
    /\ \E n \in ops[id].lo..Len(log) :
          ops' = [ops EXCEPT ![id].seen = Observe(ops[id].kind, ops[id].key, n),
                             ![id].at = n]
    /\ UNCHANGED <<log, nextOp, everIn, sysWrites, lossy, cursor>>

RespondReadValue(id) ==
    /\ ops[id].kind \in ReadKinds
    /\ ops[id].resp = None
    /\ ops[id].seen # None
    /\ ops'    = [ops EXCEPT ![id].resp = "VALUE"]
    /\ cursor' = IF ops[id].kind \in SerKinds
                 THEN [cursor EXCEPT ![ops[id].reader] =
                          IF ops[id].at > @ THEN ops[id].at ELSE @]
                 ELSE cursor
    /\ UNCHANGED <<log, nextOp, everIn, sysWrites, lossy>>

RespondReadUncommitted(id) ==
    /\ ops[id].kind \in ReadKinds
    /\ ops[id].resp = None
    /\ ops[id].seen = None
    /\ ops' = [ops EXCEPT ![id].resp = "UNCOMMITTED"]
    /\ UNCHANGED <<log, nextOp, everIn, sysWrites, lossy, cursor>>

---------------------------------------------------------------------------
(* Server writes and explicit loss *)

SystemDelete(k) ==
    /\ sysWrites < MaxSystemWrites
    /\ ValueOf(k) # Nil
    /\ log'       = Append(log, [id |-> SystemId, key |-> k, val |-> Nil])
    /\ sysWrites' = sysWrites + 1
    /\ UNCHANGED <<ops, nextOp, everIn, lossy, cursor>>

LossyTruncate ==
    /\ AllowLossyOps
    /\ Len(log) > 0
    /\ \E n \in 0..(Len(log) - 1) : log' = SubSeq(log, 1, n)
    /\ lossy' = TRUE
    /\ UNCHANGED <<ops, nextOp, everIn, sysWrites, cursor>>

---------------------------------------------------------------------------

Next ==
    \/ \E kd \in WriteKinds, k \in Keys, v \in Values \cup {Nil} :
          (kd = "C" => v # Nil) /\ InvokeWrite(kd, k, v)
    \/ \E kd \in LinKinds, k \in Keys : InvokeLinRead(kd, k)
    \/ \E kd \in SerKinds, k \in Keys, r \in Readers : InvokeSerRead(kd, k, r)
    \/ \E id \in OpIds :
          \/ CommitWrite(id) \/ CommitSetNX(id) \/ NoopSetNX(id)
          \/ RespondWriteOK(id) \/ RespondWriteRejected(id)
          \/ RespondWriteUncommitted(id)
          \/ ReadEffect(id) \/ RespondReadValue(id) \/ RespondReadUncommitted(id)
    \/ \E k \in Keys : SystemDelete(k)
    \/ LossyTruncate

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Properties *)

TypeOK ==
    /\ log \in Seq(Entry)
    /\ ops \in [OpIds -> OpRec]
    /\ nextOp \in 1..(MaxOps + 1)
    /\ everIn \subseteq OpIds
    /\ sysWrites \in 0..MaxSystemWrites
    /\ lossy \in BOOLEAN
    /\ cursor \in [Readers -> Nat]

AckedWrite(id) ==
    /\ ops[id].resp = "OK"
    /\ (ops[id].kind = "W" \/ (ops[id].kind = "C" /\ ops[id].seen = Nil))

AckedWritesDurable       == ~lossy => \A id \in OpIds : AckedWrite(id) => Committed(id)
AckedWritesDurableStrict == \A id \in OpIds : AckedWrite(id) => Committed(id)

RejectedNeverCommitted ==
    \A id \in OpIds : ops[id].resp = "CLUSTERDOWN" => id \notin everIn

NoDuplicateCommit ==
    \A i, j \in 1..Len(log) :
        (i # j /\ log[i].id # SystemId) => log[i].id # log[j].id

\* A GET only ever returns a value some committed write put there.
ReadsSeeOnlyCommitted ==
    \A id \in OpIds :
        (ops[id].kind \in GetKinds /\ ops[id].seen \in Values) =>
            \E w \in everIn : ops[w].key = ops[id].key /\ ops[w].val = ops[id].seen

\* SETNX never sets a key that is present in the committed history.
SetNXOnlyWhenAbsent ==
    \A i \in 1..Len(log) :
        (log[i].id # SystemId /\ ops[log[i].id].kind = "C") =>
            ValueAt(log[i].key, i - 1) = Nil

AppendOnly ==
    [][ \/ (Len(log') >= Len(log) /\ SubSeq(log', 1, Len(log)) = log)
        \/ LossyTruncate ]_vars

---------------------------------------------------------------------------
(* Reachability checks: each must be VIOLATED. *)

Reach_AckedWrite == ~(\E id \in OpIds : ops[id].kind = "W" /\ ops[id].resp = "OK")
Reach_ReadSeesWrite ==
    ~(\E id \in OpIds : ops[id].kind = "R" /\ ops[id].resp = "VALUE" /\ ops[id].seen \in Values)
Reach_CommitAfterUncommitted ==
    ~(\E id \in OpIds : ops[id].resp = "UNCOMMITTED" /\ Committed(id))
Reach_ReadAfterExpiry ==
    ~(\E id \in OpIds : ops[id].kind = "R" /\ ops[id].resp = "VALUE"
                        /\ ops[id].seen = Nil /\ sysWrites > 0)
Reach_StaleRead ==
    ~(\E id \in OpIds : ops[id].kind = "S" /\ ops[id].resp = "VALUE"
                        /\ ops[id].seen # ValueOf(ops[id].key))
Reach_SetNXNoop ==
    ~(\E id \in OpIds : ops[id].kind = "C" /\ ops[id].resp = "OK" /\ ops[id].seen \in Values)
Reach_SetNXSet ==
    ~(\E id \in OpIds : ops[id].kind = "C" /\ ops[id].resp = "OK" /\ ops[id].seen = Nil)
Reach_DbSize ==
    ~(\E id \in OpIds : ops[id].kind = "K" /\ ops[id].resp = "VALUE" /\ ops[id].seen = 1)

---------------------------------------------------------------------------
(* Liveness, for concrete models under a healthy-shard assumption. *)

AllOpsAnswered ==
    \A id \in OpIds : (ops[id].kind # "unused") ~> (ops[id].resp # None)
=============================================================================
