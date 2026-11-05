------------------------------- MODULE Leases -------------------------------
(***************************************************************************)
(* Step 4: bidirectional leases with real time, clock drift, message       *)
(* delay and loss. Focused model: membership is reduced to demotion and    *)
(* takeover (step 2/3 covered promotion, restarts and reconciliation).     *)
(*                                                                         *)
(* Source: ../../sync-replication.md section 5 "Leases", "Lease            *)
(* durations", "When a lease can't be renewed", "Leases across a           *)
(* failover"; section 4 demotion step 2.                                   *)
(*                                                                         *)
(* Time. `now` is real time (integer ticks, bounded by MaxTime). Leases   *)
(* are measured on local monotonic clocks whose rate may differ from real  *)
(* time; over one lease interval the local elapsed time differs from real  *)
(* elapsed time by at most Drift ticks. Worst cases, in real time:         *)
(*   holder believes its lease valid while  now - start < Dur - Margin + Drift *)
(*   grantor's promise is over once         now - recv  >= Dur - Drift     *)
(* where `start` is when the holder SENT the message the grantor's reply   *)
(* confirms, and `recv` is when the grantor RECEIVED it (start <= recv).   *)
(* Margin is the doc's clock-drift margin; the doc's argument needs        *)
(* Margin >= 2 * Drift.                                                    *)
(*                                                                         *)
(* Leases (doc table):                                                     *)
(*   primary lease   holder primary, grantor each eligible replica,        *)
(*                   renewed by REPLCONF ACK; protects primary reads.      *)
(*   read lease      holder sync replica, grantor primary, renewed by      *)
(*                   REPLCONF COMMIT echoing the replica's latest ack;     *)
(*                   protects linearizable sync-replica reads.             *)
(*                                                                         *)
(* Channels: at most one in-flight message per direction per replica (a    *)
(* newer send replaces an older one; messages can also be dropped).       *)
(*                                                                         *)
(* Reads are checked two ways. (1) State predicate NoStaleLinRead: in     *)
(* every state, any node that may serve a linearizable read of the key     *)
(* must return the latest committed value. (2) Explicit client reads       *)
(* (InvokeRead / ReadEffect / RespondRead) and a refinement mapping to     *)
(* DurableShard (Refinement), the contract every other step refines.       *)
(* Reads and writes share OpIds (bounded by MaxOps).                       *)
(*                                                                         *)
(* Refinement mapping to DurableShard (key K1, Values = OpIds, Nil = 0):  *)
(*   log    = clog; entry i = [id, key, val] = [clog[i], K1, clog[i]]      *)
(*   ops    = writes (kind W, val = own id) and reads (kind R; a read by a *)
(*            lease-holding replica is linearizable in this model)         *)
(*   ExecWrite -> InvokeWrite; clog append -> CommitWrite;                 *)
(*   RespondOK -> RespondWriteOK. No CLUSTERDOWN, UNCOMMITTED, system      *)
(*   writes, lossy steps or serializable reads in this step.               *)
(*                                                                         *)
(* Rule switches (TRUE = the doc's rule):                                  *)
(*   WaitPrimLease  takeover waits until the old primary's lease expired   *)
(*   WaitReadLease  demotion waits until the replica's read lease expired  *)
(*   WaitOldLeases  a new primary waits ReadDur + Margin after takeover    *)
(*                  before demoting a replica of the old configuration     *)
(*   StopGrant      a primary stops renewing read leases once any primary  *)
(*                  lease it holds has expired                             *)
(*   ResetOnLearn   takeover timers restart when a config change is learned*)
(*   EchoOnlySync   (finding F10, not in the doc) REPLCONF COMMIT renews   *)
(*                  the read lease only of replicas in the sync set        *)
(*   StopAckOnExpiry  (hypothesis F8, not in the doc) a primary stops      *)
(*                  committing and releasing write replies once its lease  *)
(*                  may have expired                                       *)
(***************************************************************************)
EXTENDS Integers, ShardCommon

CONSTANTS
    Nodes, InitPrim,
    PrimDur,       \* primary lease duration
    ReadDur,       \* replica read lease duration (shorter)
    Drift, Margin,
    MaxTime, MaxOps, MaxCfg,
    WaitPrimLease, WaitReadLease, WaitOldLeases, StopGrant, ResetOnLearn,
    StopAckOnExpiry,
    EchoOnlySync,
    None           \* model value: "no response / no writer"

ASSUME InitPrim \in Nodes
ASSUME ReadDur + Margin < PrimDur          \* doc "Lease durations" (bus delay 0)
\* A granted read lease must be usable for at least one tick, or the
\* replica half of NoStaleLinRead is vacuous (step 4 review: a config with
\* ReadDur = 1, Margin = 2, Drift = 1 made it unreachable).
ASSUME ReadDur - Margin + Drift > 0

ASSUME None \notin Nodes

\* "No lease / never received". An integer, not a model value, because it
\* takes part in Max2 and arithmetic. It must lie below every reachable
\* time (time starts at 0), so Max2(Never, t) = t for any timestamp t.
Never == -100
ASSUME Never < 0
OpIds == 1..MaxOps
NoMsg == [ok |-> FALSE]

VARIABLES
    now,
    nlog,        \* [Nodes -> Seq(OpIds)]: each write writes its id as the new value
    cfgLog,      \* Seq([prim, elig])
    kver,        \* [Nodes -> Nat]
    commitL,     \* [Nodes -> Nat]: primary-side committed offset
    rview,       \* [Nodes -> Nat]: replica-side committed view (REPLCONF COMMIT)
    sync,        \* [Nodes -> SUBSET Nodes]: replicas a primary counts
    acked,       \* [Nodes -> [Nodes -> Nat]]
    tko,         \* [Nodes -> Int]: time the node's takeover committed
    \* leases
    pl,          \* [Nodes -> [Nodes -> Int]]: primary-lease start held by p from r (send time of acked data)
    ackRecv,     \* [Nodes -> [Nodes -> Int]]: when p last received an ack from r (read-lease grantor)
    ackEcho,     \* [Nodes -> [Nodes -> Int]]: send time of r's latest ack p received (echoed in COMMIT)
    rl,          \* [Nodes -> Int]: read-lease start held by replica r
    primRecv,    \* [Nodes -> Int]: when r last received traffic from its primary (primary-lease grantor)
    dataT,       \* [Nodes -> Int]: send time of the latest data message r received
    \* channels
    p2r,         \* [Nodes -> message or None]
    r2p,         \* [Nodes -> message or None]
    \* clients and ghosts
    resp,        \* [OpIds -> {None, "OK", "VALUE"}]
    wnode,       \* [OpIds -> Nodes \cup {None}]: node that executed write id
    rnode,       \* [OpIds -> Nodes \cup {None}]: node a read id was invoked at
    olo,         \* [OpIds -> Nat]: Len(clog) when op id was invoked
    rat,         \* [OpIds -> Nat \cup {None}]: committed prefix the read observed
    rseen,       \* [OpIds -> 0..MaxOps \cup {None}]: value the read returned (0 = none)
    nextOp,
    clog         \* ghost committed history

\* Variable groups; together with `now` they cover every variable exactly once.
stateVars  == <<nlog, cfgLog, kver, commitL, rview, sync, acked, tko>>
leaseVars  == <<pl, ackRecv, ackEcho, rl, primRecv, dataT>>
chanVars   == <<p2r, r2p>>
clientVars == <<resp, wnode, rnode, olo, rat, rseen, nextOp, clog>>
readVars   == <<rnode, rat, rseen>>
vars == <<now, stateVars, leaseVars, chanVars, clientVars>>

---------------------------------------------------------------------------
(* Helpers (Min2, Max2, SetMin, IsPrefix come from ShardCommon) *)

CurCfg  == cfgLog[Len(cfgLog)]
CurPrim == CurCfg.prim
PrimOf(n) == cfgLog[kver[n]].prim
EligOf(n) == cfgLog[kver[n]].elig
ThinksPrim(p) == PrimOf(p) = p
KnowsLatest(n) == kver[n] = Len(cfgLog)
CanCas == Len(cfgLog) < MaxCfg

\* Value of the key after the first k entries of a log.
ValAt(s, k) == IF k = 0 THEN 0 ELSE s[k]
Latest == ValAt(clog, Len(clog))

\* Holder-side checks (worst case: holder's clock runs slow by Drift).
HolderValid(start, dur) == start # Never /\ now - start < dur - Margin + Drift
\* Grantor-side: the promise is over (worst case: grantor's clock fast).
GrantorOver(recv, dur) == recv = Never \/ now - recv >= dur - Drift

\* The primary's lease from every eligible replica it knows of.
PrimLeaseValid(p) == \A r \in EligOf(p) \ {p} : HolderValid(pl[p][r], PrimDur)

ReadLeaseValid(r) == HolderValid(rl[r], ReadDur)

---------------------------------------------------------------------------

InitCfg == [prim |-> InitPrim, elig |-> Nodes \ {InitPrim}]

Init ==
    /\ now     = 0
    /\ nlog    = [n \in Nodes |-> << >>]
    /\ cfgLog  = << InitCfg >>
    /\ kver    = [n \in Nodes |-> 1]
    /\ commitL = [n \in Nodes |-> 0]
    /\ rview   = [n \in Nodes |-> 0]
    /\ sync    = [n \in Nodes |-> IF n = InitPrim THEN Nodes \ {InitPrim} ELSE {}]
    /\ acked   = [n \in Nodes |-> [r \in Nodes |-> 0]]
    /\ tko     = [n \in Nodes |-> Never]
    \* leases established at time 0
    /\ pl      = [n \in Nodes |-> [r \in Nodes |-> IF n = InitPrim THEN 0 ELSE Never]]
    /\ ackRecv = [n \in Nodes |-> [r \in Nodes |-> IF n = InitPrim THEN 0 ELSE Never]]
    /\ ackEcho = [n \in Nodes |-> [r \in Nodes |-> Never]]
    /\ rl      = [n \in Nodes |-> IF n = InitPrim THEN Never ELSE 0]
    /\ primRecv = [n \in Nodes |-> 0]
    /\ dataT   = [n \in Nodes |-> 0]
    /\ p2r     = [n \in Nodes |-> NoMsg]
    /\ r2p     = [n \in Nodes |-> NoMsg]
    /\ resp    = [id \in OpIds |-> None]
    /\ wnode   = [id \in OpIds |-> None]
    /\ rnode   = [id \in OpIds |-> None]
    /\ olo     = [id \in OpIds |-> 0]
    /\ rat     = [id \in OpIds |-> None]
    /\ rseen   = [id \in OpIds |-> None]
    /\ nextOp  = 1
    /\ clog    = << >>

---------------------------------------------------------------------------
(* Time *)

Tick ==
    /\ now < MaxTime
    /\ now' = now + 1
    /\ UNCHANGED <<stateVars, leaseVars, chanVars, clientVars>>

---------------------------------------------------------------------------
(* Writes on a node that believes it is primary *)

Writable(p) == sync[p] \cap EligOf(p) # {} \/ EligOf(p) \ {p} = {}

ExecWrite(p) ==
    /\ nextOp \in OpIds
    /\ ThinksPrim(p) /\ Writable(p)
    /\ nlog'   = [nlog EXCEPT ![p] = Append(@, nextOp)]
    /\ wnode'  = [wnode EXCEPT ![nextOp] = p]
    /\ olo'    = [olo EXCEPT ![nextOp] = Len(clog)]
    /\ nextOp' = nextOp + 1
    /\ UNCHANGED <<now, cfgLog, kver, commitL, rview, sync, acked, tko, leaseVars, chanVars,
                   resp, readVars, clog>>

AckFence(p) == StopAckOnExpiry => PrimLeaseValid(p)

CommitCap(p) == IF sync[p] = {} THEN Len(nlog[p]) ELSE SetMin({acked[p][r] : r \in sync[p]})

AdvanceCommit(p) ==
    /\ ThinksPrim(p) /\ AckFence(p)
    /\ commitL[p] < Min2(Len(nlog[p]), CommitCap(p))
    /\ commitL' = [commitL EXCEPT ![p] = @ + 1]
    /\ clog' = IF commitL[p] = Len(clog) THEN Append(clog, nlog[p][commitL[p] + 1]) ELSE clog
    /\ UNCHANGED <<now, nlog, cfgLog, kver, rview, sync, acked, tko, leaseVars, chanVars,
                   resp, wnode, olo, readVars, nextOp>>

\* The write's position in its primary's log.
Pos(id, p) == CHOOSE i \in 1..Len(nlog[p]) : nlog[p][i] = id

RespondOK(id) ==
    LET p == wnode[id] IN
    /\ p # None /\ resp[id] = None
    /\ ThinksPrim(p) /\ AckFence(p)
    /\ \E i \in 1..commitL[p] : nlog[p][i] = id
    /\ resp' = [resp EXCEPT ![id] = "OK"]
    /\ UNCHANGED <<now, stateVars, leaseVars, chanVars, wnode, olo, readVars, nextOp, clog>>

---------------------------------------------------------------------------
(* Client reads (linearizable GET of the single key). PrimCanRead and      *)
(* ReplCanRead are defined below, with the properties.                     *)

InvokeRead(n) ==
    /\ nextOp \in OpIds
    /\ rnode'  = [rnode EXCEPT ![nextOp] = n]
    /\ olo'    = [olo EXCEPT ![nextOp] = Len(clog)]
    /\ nextOp' = nextOp + 1
    /\ UNCHANGED <<now, stateVars, leaseVars, chanVars, resp, wnode, rat, rseen, clog>>

\* Committed offset a node serves reads from.
ReadOff(n) == IF ThinksPrim(n) THEN commitL[n] ELSE rview[n]

---------------------------------------------------------------------------
(* Replication traffic. Both leases ride on it. *)

\* Primary -> replica: stream data + REPLCONF COMMIT. The COMMIT echoes the
\* replica's latest ack, renewing its read lease, unless StopGrant applies.
SendData(p, r) ==
    /\ ThinksPrim(p) /\ r # p
    /\ LET grant == /\ ~(StopGrant /\ ~PrimLeaseValid(p))
                    /\ (EchoOnlySync => r \in sync[p])
       IN  p2r' = [p2r EXCEPT ![r] = [ok |-> TRUE, t |-> now, from |-> p, log |-> nlog[p],
                                      commit |-> commitL[p],
                                      echo |-> IF grant THEN ackEcho[p][r] ELSE Never]]
    /\ UNCHANGED <<now, stateVars, leaseVars, r2p, clientVars>>

\* Replica receives from the primary it follows (config epoch check: traffic
\* from any other node is dropped).
RecvData(r) ==
    LET m == p2r[r] IN
    /\ m.ok
    /\ p2r' = [p2r EXCEPT ![r] = NoMsg]
    /\ IF m.from = PrimOf(r) /\ r # PrimOf(r) /\ IsPrefix(nlog[r], m.log)
       THEN /\ nlog'     = [nlog EXCEPT ![r] = m.log]
            /\ rview'    = [rview EXCEPT ![r] = Max2(@, Min2(m.commit, Len(m.log)))]
            /\ primRecv' = [primRecv EXCEPT ![r] = now]
            /\ dataT'    = [dataT EXCEPT ![r] = m.t]
            /\ rl'       = [rl EXCEPT ![r] = IF m.echo # Never THEN Max2(@, m.echo) ELSE @]
       ELSE UNCHANGED <<nlog, rview, primRecv, dataT, rl>>
    /\ UNCHANGED <<now, cfgLog, kver, commitL, sync, acked, tko, pl, ackRecv, ackEcho,
                   r2p, clientVars>>

\* REPLCONF ACK: confirms receipt of the data sent at time dataT[r].
SendAck(r) ==
    /\ r # PrimOf(r)
    /\ r2p' = [r2p EXCEPT ![r] = [ok |-> TRUE, t |-> now, to |-> PrimOf(r), len |-> Len(nlog[r]),
                                  data |-> dataT[r]]]
    /\ UNCHANGED <<now, stateVars, leaseVars, p2r, clientVars>>

RecvAck(r) ==
    LET m == r2p[r]
        p == m.to
    IN
    /\ m.ok
    /\ r2p' = [r2p EXCEPT ![r] = NoMsg]
    /\ IF ThinksPrim(p) /\ IsPrefix(SubSeq(nlog[r], 1, Min2(m.len, Len(nlog[r]))), nlog[p])
       THEN /\ acked'   = [acked EXCEPT ![p][r] = Max2(@, m.len)]
            /\ pl'      = [pl EXCEPT ![p][r] = Max2(@, m.data)]
            /\ ackRecv' = [ackRecv EXCEPT ![p][r] = now]
            /\ ackEcho' = [ackEcho EXCEPT ![p][r] = m.t]
       ELSE UNCHANGED <<acked, pl, ackRecv, ackEcho>>
    /\ UNCHANGED <<now, nlog, cfgLog, kver, commitL, rview, sync, tko, rl, primRecv,
                   dataT, p2r, clientVars>>


---------------------------------------------------------------------------
(* Cluster V2 *)

AppendCfg(c, n) ==
    /\ cfgLog' = Append(cfgLog, c)
    /\ kver'   = [kver EXCEPT ![n] = Len(cfgLog) + 1]

Learn(n) ==
    /\ ~KnowsLatest(n)
    /\ kver' = [kver EXCEPT ![n] = Len(cfgLog)]
    \* Doc: a replica starts timing a new primary's lease when it learns of
    \* the configuration change, as if it had just received traffic from it.
    /\ primRecv' = IF ResetOnLearn /\ CurPrim # n THEN [primRecv EXCEPT ![n] = now] ELSE primRecv
    /\ sync' = [sync EXCEPT ![n] = IF CurPrim = n THEN @ ELSE {}]
    /\ UNCHANGED <<now, nlog, cfgLog, commitL, rview, acked, tko, pl, ackRecv, ackEcho,
                   rl, dataT, chanVars, clientVars>>

\* Demotion (doc s4 steps 1-3): wait out the replica's read lease, measured
\* from the last ack received from it; a new primary also waits ReadDur +
\* Margin after its takeover for replicas of the old configuration. Then
\* CAS to ineligible and stop counting, in one step.
Demote(p, r) ==
    /\ ThinksPrim(p) /\ KnowsLatest(p) /\ CanCas
    /\ r \in CurCfg.elig
    /\ WaitReadLease => GrantorOver(ackRecv[p][r], ReadDur)
    /\ WaitOldLeases => (tko[p] = Never \/ now - tko[p] >= ReadDur + Margin - Drift)
    /\ AppendCfg([CurCfg EXCEPT !.elig = @ \ {r}], p)
    /\ sync' = [sync EXCEPT ![p] = @ \ {r}]
    /\ UNCHANGED <<now, nlog, commitL, rview, acked, tko, leaseVars, chanVars,
                   clientVars>>

\* Takeover (doc s5 fault detection): an eligible replica whose view of the
\* primary's lease has expired CASes itself to primary. It counts the other
\* eligible replicas and starts from its committed view.
Takeover(n) ==
    /\ KnowsLatest(n) /\ CanCas
    /\ n \in CurCfg.elig /\ n # CurPrim
    /\ WaitPrimLease => GrantorOver(primRecv[n], PrimDur)
    /\ LET newElig == CurCfg.elig \ {n} IN
         /\ AppendCfg([prim |-> n, elig |-> newElig], n)
         /\ sync'    = [sync EXCEPT ![n] = newElig]
         /\ acked'   = [acked EXCEPT ![n] = [r \in Nodes |-> 0]]
         /\ commitL' = [commitL EXCEPT ![n] = rview[n]]
         /\ tko'     = [tko EXCEPT ![n] = now]
         \* It has heard nothing from its replicas yet: no primary lease.
         /\ pl'      = [pl EXCEPT ![n] = [r \in Nodes |-> Never]]
         /\ ackRecv' = [ackRecv EXCEPT ![n] = [r \in Nodes |-> Never]]
         /\ ackEcho' = [ackEcho EXCEPT ![n] = [r \in Nodes |-> Never]]
         /\ rl'      = [rl EXCEPT ![n] = Never]
    /\ UNCHANGED <<now, nlog, rview, primRecv, dataT, chanVars, clientVars>>

---------------------------------------------------------------------------
(* Linearizable-read guards (doc s5). Used by ReadEffect and NoStaleLinRead.*)

\* A primary may serve a linearizable read when it believes it is primary
\* and holds its lease (doc: stops serving reads before its lease from any
\* eligible replica expires); dirty tracking: only when nothing is pending.
PrimCanRead(p) == ThinksPrim(p) /\ PrimLeaseValid(p) /\ commitL[p] = Len(nlog[p])
\* A sync replica may serve a linearizable read while it holds a read lease
\* and has nothing uncommitted (dirty tracking, single key).
ReplCanRead(r) == ~ThinksPrim(r) /\ ReadLeaseValid(r) /\ rview[r] = Len(nlog[r])

\* The read takes effect at its node only while that node may serve a
\* linearizable read; it returns the node's committed value.
ReadEffect(id) ==
    LET n == rnode[id] IN
    /\ n # None /\ rseen[id] = None
    /\ PrimCanRead(n) \/ ReplCanRead(n)
    /\ rat'   = [rat EXCEPT ![id] = ReadOff(n)]
    /\ rseen' = [rseen EXCEPT ![id] = ValAt(nlog[n], ReadOff(n))]
    /\ UNCHANGED <<now, stateVars, leaseVars, chanVars, resp, wnode, rnode, olo, nextOp, clog>>

RespondRead(id) ==
    /\ rnode[id] # None /\ rseen[id] # None /\ resp[id] = None
    /\ resp' = [resp EXCEPT ![id] = "VALUE"]
    /\ UNCHANGED <<now, stateVars, leaseVars, chanVars, wnode, olo, readVars, nextOp, clog>>

---------------------------------------------------------------------------

Next ==
    \/ Tick
    \/ \E p \in Nodes : ExecWrite(p) \/ AdvanceCommit(p)
    \/ \E id \in OpIds : RespondOK(id) \/ ReadEffect(id) \/ RespondRead(id)
    \/ \E n \in Nodes : InvokeRead(n)
    \/ \E p, r \in Nodes : SendData(p, r) \/ Demote(p, r)
    \* Message loss needs no action: a message may never be delivered, and a
    \* later send overwrites it.
    \/ \E r \in Nodes : RecvData(r) \/ SendAck(r) \/ RecvAck(r)
                        \/ Learn(r) \/ Takeover(r)

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Properties *)

NoStaleLinRead ==
    /\ \A p \in Nodes : PrimCanRead(p) => ValAt(nlog[p], commitL[p]) = Latest
    /\ \A r \in Nodes : ReplCanRead(r) => ValAt(nlog[r], rview[r]) = Latest

\* Committed history agrees across primaries.
CommittedAgree ==
    \A p \in Nodes : SubSeq(nlog[p], 1, Min2(commitL[p], Len(clog))) =
                     SubSeq(clog, 1, Min2(commitL[p], Len(clog)))

\* F8 premise: only the current primary acknowledges writes.
AckOnlyByCurrentPrimary ==
    [][\A id \in OpIds : (resp'[id] = "OK" /\ resp[id] = None) => wnode[id] = CurPrim]_vars

\* Committed history is held by the current primary and eligible replicas.
EligibleHoldsCommitted ==
    \A n \in CurCfg.elig \cup {CurPrim} : IsPrefix(clog, nlog[n])

TimeOrNever == {Never} \cup 0..MaxTime
CfgRec  == [prim : Nodes, elig : SUBSET Nodes]
DataMsg == [ok : {TRUE}, t : 0..MaxTime, from : Nodes, log : Seq(OpIds),
            commit : Nat, echo : TimeOrNever]
AckMsg  == [ok : {TRUE}, t : 0..MaxTime, to : Nodes, len : Nat, data : TimeOrNever]

TypeOK ==
    /\ now      \in 0..MaxTime
    /\ nlog     \in [Nodes -> Seq(OpIds)]
    /\ cfgLog   \in Seq(CfgRec) /\ Len(cfgLog) \in 1..MaxCfg
    /\ kver     \in [Nodes -> 1..Len(cfgLog)]
    /\ commitL  \in [Nodes -> Nat]
    /\ rview    \in [Nodes -> Nat]
    /\ sync     \in [Nodes -> SUBSET Nodes]
    /\ acked    \in [Nodes -> [Nodes -> Nat]]
    /\ tko      \in [Nodes -> TimeOrNever]
    /\ pl       \in [Nodes -> [Nodes -> TimeOrNever]]
    /\ ackRecv  \in [Nodes -> [Nodes -> TimeOrNever]]
    /\ ackEcho  \in [Nodes -> [Nodes -> TimeOrNever]]
    /\ rl       \in [Nodes -> TimeOrNever]
    /\ primRecv \in [Nodes -> TimeOrNever]
    /\ dataT    \in [Nodes -> TimeOrNever]
    /\ p2r      \in [Nodes -> {NoMsg} \cup DataMsg]
    /\ r2p      \in [Nodes -> {NoMsg} \cup AckMsg]
    /\ resp     \in [OpIds -> {None, "OK", "VALUE"}]
    /\ wnode    \in [OpIds -> Nodes \cup {None}]
    /\ rnode    \in [OpIds -> Nodes \cup {None}]
    /\ olo      \in [OpIds -> Nat]
    /\ rat      \in [OpIds -> Nat \cup {None}]
    /\ rseen    \in [OpIds -> 0..MaxOps \cup {None}]
    /\ \A id \in OpIds : ~(wnode[id] # None /\ rnode[id] # None)
    /\ nextOp   \in 1..(MaxOps + 1)
    /\ clog     \in Seq(OpIds)

---------------------------------------------------------------------------
(* State-space view. Every timing check compares `now - t` with a          *)
(* threshold below Cap, so only the capped age of each timestamp matters.  *)
(* TLC fingerprints states by this view; with it the state space is        *)
(* finite even though `now` grows, and MaxTime is only a safety bound.     *)

Cap == PrimDur + Margin + Drift + 1
Age(x) == IF x = Never THEN Never ELSE Min2(now - x, Cap)
AgeF(f) == [k \in DOMAIN f |-> Age(f[k])]
AgeFF(f) == [k \in DOMAIN f |-> AgeF(f[k])]
MsgView(m) == IF ~m.ok THEN m
              ELSE IF "echo" \in DOMAIN m
                   THEN [m EXCEPT !.t = Age(m.t), !.echo = Age(m.echo)]
                   ELSE [m EXCEPT !.t = Age(m.t), !.data = Age(m.data)]

\* View lists every variable except `now`, whose role is taken by the ages.
\* No SYMMETRY: TLC does not combine it with VIEW, and InitPrim is distinguished.
View == <<nlog, cfgLog, kver, commitL, rview, sync, acked, AgeF(tko), AgeFF(pl),
          AgeFF(ackRecv), AgeFF(ackEcho), AgeF(rl), AgeF(primRecv), AgeF(dataT),
          [r \in Nodes |-> MsgView(p2r[r])], [r \in Nodes |-> MsgView(r2p[r])],
          resp, wnode, rnode, olo, rat, rseen, nextOp, clog>>

\* Trace display (ALIAS); does not affect state fingerprints.
Alias == [now |-> now, nlog |-> nlog, clog |-> clog, cfgLog |-> cfgLog, kver |-> kver,
          commitL |-> commitL, rview |-> rview, rl |-> rl, pl |-> pl,
          primRecv |-> primRecv, ackRecv |-> ackRecv, p2r |-> p2r, r2p |-> r2p,
          resp |-> resp, wnode |-> wnode, rnode |-> rnode, olo |-> olo, rat |-> rat,
          rseen |-> rseen]

---------------------------------------------------------------------------
(* Refinement of the abstract client contract (see header).                *)

K1 == "k"
DsNil == 0                       \* "no committed write"; 0 \notin OpIds
AbsLog == [i \in 1..Len(clog) |-> [id |-> clog[i], key |-> K1, val |-> clog[i]]]
AbsOp(id) ==
    IF wnode[id] # None
    THEN [kind |-> "W", key |-> K1, val |-> id, reader |-> None, lo |-> olo[id],
          at |-> None, resp |-> resp[id], seen |-> None]
    ELSE IF rnode[id] # None
    THEN [kind |-> "R", key |-> K1, val |-> DsNil, reader |-> None, lo |-> olo[id],
          at |-> rat[id], resp |-> resp[id], seen |-> rseen[id]]
    ELSE [kind |-> "unused", key |-> K1, val |-> DsNil, reader |-> None, lo |-> 0,
          at |-> None, resp |-> None, seen |-> None]

DS == INSTANCE DurableShard
        WITH Keys <- {K1}, Values <- OpIds, Nil <- DsNil, NoReader <- None,
             Readers <- {}, MaxSystemWrites <- 0, AllowLossyOps <- FALSE,
             log <- AbsLog, ops <- [id \in OpIds |-> AbsOp(id)],
             everIn <- {clog[i] : i \in 1..Len(clog)}, sysWrites <- 0,
             lossy <- FALSE, cursor <- [r \in {} |-> 0]

Refinement == DS!Spec

\* Search restriction for the negative Refinement configs only (CONSTRAINT):
\* op 1 is the only write, and a client read is invoked only after a write
\* committed. It removes behaviors whose reads cannot be stale, so the bugs
\* are found within the CI limit. A violation found under it is a behavior
\* of Spec, so it stays a valid counterexample. Never used in a config that
\* is expected to pass.
ReadAfterCommit == \A id \in OpIds : /\ (id > 1 => wnode[id] = None)
                                    /\ (rnode[id] # None => olo[id] > 0)

\* Reachability: each must be VIOLATED.
Reach_Takeover   == ~(CurPrim # InitPrim)
Reach_Demote     == ~(\E v \in 1..Len(cfgLog) : cfgLog[v].prim = InitPrim
                          /\ cfgLog[v].elig # Nodes \ {InitPrim})
Reach_ReplRead   == ~(\E r \in Nodes : ReplCanRead(r) /\ Len(clog) > 0)
Reach_NewPrimRead == ~(\E p \in Nodes : p # InitPrim /\ PrimCanRead(p) /\ Len(clog) > 0)
\* A client read invoked at a node other than InitPrim returns a committed write.
Reach_ReplReadOp == ~(\E id \in OpIds : rnode[id] # None /\ rnode[id] # InitPrim
                         /\ resp[id] = "VALUE" /\ rseen[id] # 0)
Reach_OKAfterTakeover == ~(CurPrim # InitPrim /\ \E id \in OpIds : resp[id] = "OK"
                              /\ wnode[id] = CurPrim)
=============================================================================
