------------------------------- MODULE Shard -------------------------------
(***************************************************************************)
(* Steps 2 and 3: sync replica set membership committed to Cluster V2,     *)
(* takeover, restarts and forced failover. Single source for the           *)
(* membership + failover protocol (replaces Membership.tla and             *)
(* Failover.tla, which were divergent copies).                             *)
(*                                                                         *)
(* Source: ../../sync-replication.md section 4 (shard configuration,       *)
(* promotion, demotion), section 5 (fault detection, failover,             *)
(* reconciliation, no eligible replica, forced failover, restarts) and     *)
(* section 6 (CAS, incarnation IDs, restarted nodes rejoin ineligible,     *)
(* correlated loss).                                                       *)
(*                                                                         *)
(* Cluster V2 is a linearizable CAS register holding a log of shard        *)
(* configurations cfgLog: [prim, elig, inc]. A node learns new configs     *)
(* asynchronously (kver = highest version it knows). Each node has its own *)
(* replication log nlog[n]; a node that believes it is primary executes    *)
(* writes, counts sync replicas (sync[p]), collects acks (acked[p][r]) and *)
(* advances its committed offset commitL[p] by the step 1 commit rule.     *)
(*                                                                         *)
(* Ordering rules of section 4:                                            *)
(*   (O1) a replica counts toward commits before it becomes eligible;      *)
(*   (O2) a replica is ineligible before any write commits without it.     *)
(*                                                                         *)
(* Scopes:                                                                 *)
(*   step 2 (former Membership.tla): MaxRestarts = 0, AllowForce = FALSE.  *)
(*   step 3 (former Failover.tla):   restarts and forced failover.         *)
(*                                                                         *)
(* The fixed protocol (all switches at their non-bug value):               *)
(*   - promotion steps 1+2 are one step (Count); step 4 CAS needs counting *)
(*     and re-checks catch-up;                                             *)
(*   - demotion CAS and "stop counting" are one step (MakeIneligible);     *)
(*   - after a takeover, catch-up and full resync are measured against the *)
(*     inherited log (CatchUpPoint); the new primary serves writes only    *)
(*     once it has committed that log, by the normal commit rule (never    *)
(*     below MinSync);                                                     *)
(*   - REPLCONF COMMIT: replicas keep a committed view rcommit; a new      *)
(*     primary starts from it;                                             *)
(*   - held replies are fenced by the primaryship term that set them;      *)
(*   - the committed history is a ghost append-only sequence clog that     *)
(*     only grows when an authoritative node holds the new prefix.         *)
(*                                                                         *)
(* Bug switches (value that reproduces the bug):                           *)
(*   AtomicPromote = FALSE   catch-up check and counting in two steps.     *)
(*   EarlyDrop = TRUE        the primary may stop counting an eligible     *)
(*                           replica before the ineligible CAS (breaks O2).*)
(*   EligibleFirst = TRUE    CAS to eligible without catch-up/counting     *)
(*                           first (breaks O1).                            *)
(*   ReconcileFirst = FALSE  the doc as written (F1): catch-up and resync  *)
(*                           use the primary's own committed offset.       *)
(*   StepDownRelease = FALSE held replies are not fenced by term (F2).     *)
(*   IncCheck = FALSE        config does not check incarnations.           *)
(*   AllowForce = TRUE       operator forced failover to ineligible (F7).  *)
(*   RestoreSync = FALSE     restarted primary starts with an empty sync   *)
(*                           set (F5).                                     *)
(*   CatchUpAtEligible = FALSE  no catch-up re-check at step 4 (F6).       *)
(*   LeaseFence = FALSE      a deposed primary keeps committing and        *)
(*                           releasing replies (F8).                       *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC, ShardCommon

CONSTANTS
    Keys, Values, Nil, None, NoReader, MaxOps,
    Nodes, InitPrim, MinSync, TargetSync,
    MaxCfg, MaxCrashes, MaxRestarts,
    AtomicPromote, EarlyDrop, EligibleFirst, ReconcileFirst, StepDownRelease,
    IncCheck, AllowForce,
    RestoreSync,  \* a restarted node rebuilds its sync set from the config's eligible set
    CatchUpAtEligible, \* promotion step 4 re-checks catch-up
    LeaseFence    \* abstraction of step 4: a deposed primary stops committing/acking

ASSUME InitPrim \in Nodes
ASSUME MinSync <= TargetSync /\ TargetSync < Cardinality(Nodes)
ASSUME \A b \in {AtomicPromote, EarlyDrop, EligibleFirst, ReconcileFirst,
                 StepDownRelease, IncCheck, AllowForce, RestoreSync,
                 CatchUpAtEligible, LeaseFence} : b \in BOOLEAN

OpIds    == 1..MaxOps
SystemId == 0
Entry    == [id : OpIds \cup {SystemId}, key : Keys, val : Values \cup {Nil}]

UnusedOp == [kind |-> "unused", key |-> CHOOSE k \in Keys : TRUE, val |-> Nil,
             reader |-> NoReader, lo |-> 0, at |-> None, resp |-> None, seen |-> None]
NoMeta   == [node |-> InitPrim, exec |-> FALSE, off |-> 0, term |-> 0]

VARIABLES
    nlog, alive, inc,
    cfgLog,    \* Seq([prim, elig, inc]): Cluster V2 shard configuration
    kver, commitL, rcommit, sync,
    pending,   \* passed catch-up, not yet counted (AtomicPromote = FALSE only)
    acked, recon, term,
    clog,      \* ghost: append-only committed history (abstract log)
    everC,     \* ghost: ids ever committed
    lossy,     \* ghost: an explicit lossy operator action dropped history
    unfenced,  \* ghost: primaries deposed by a forced failover (not lease-fenced)
    ops, meta, nextOp, crashes, restarts

\* Variable groups; together they cover every variable exactly once.
logVars     == <<nlog, commitL, rcommit, acked>>
nodeVars    == <<alive, inc, crashes, restarts>>
cfgVars     == <<cfgLog, kver>>
primaryVars == <<sync, pending, recon, term>>
ghostVars   == <<clog, everC, lossy, unfenced>>
clientVars  == <<ops, meta, nextOp>>

\* Everything except the client-side variables.
repl == <<logVars, nodeVars, cfgVars, primaryVars, ghostVars>>
vars == <<repl, clientVars>>

---------------------------------------------------------------------------
(* Helpers *)

\* Min2, SetMin, IsPrefix and LCP come from ShardCommon.
Ids(s) == {s[i].id : i \in 1..Len(s)} \ {SystemId}

CurCfg   == cfgLog[Len(cfgLog)]
CurPrim  == CurCfg.prim
CfgAt(v) == cfgLog[v]
PrimOf(n) == CfgAt(kver[n]).prim
EligOf(n) == CfgAt(kver[n]).elig
KnowsLatest(n) == kver[n] = Len(cfgLog)
CanCas == Len(cfgLog) < MaxCfg

\* The config still names this incarnation of n.
IncOK(c, n) == ~IncCheck \/ c.inc[n] = inc[n]

ThinksPrim(p) == alive[p] /\ PrimOf(p) = p /\ IncOK(CfgAt(kver[p]), p)

Writable(p) == Cardinality(sync[p] \cap EligOf(p)) >= MinSync
CommitCap(p) == IF sync[p] = {} THEN Len(nlog[p])
                ELSE SetMin({acked[p][r] : r \in sync[p]})
Reconciled(p) == commitL[p] >= recon[p]

\* F1 fix (ReconcileFirst): after a takeover, promotion catch-up and full
\* resync are measured against the log the new primary inherited
\* (PacificA: it holds every committed write), not only its own possibly
\* stale committed offset. ReconcileFirst = FALSE is the doc as written.
CatchUpPoint(p) ==
    IF ~ReconcileFirst \/ Reconciled(p) THEN commitL[p]
    ELSE Min2(recon[p], Len(nlog[p]))

\* LeaseFence abstracts what step 4 must provide: a takeover happens only
\* after the old primary's lease expired, and (hypothesis F8) a primary
\* stops committing and releasing replies before its lease expires. So
\* only the current primary commits. Without it, a deposed primary can
\* commit using acks collected before the takeover.
\* Forced failover does not wait for the old primary's lease (doc s5), so
\* the primary it deposes is not fenced (ghost `unfenced`).
Fenced(p) == LeaseFence => (p = CurPrim \/ p \in unfenced)

Authoritative == {n \in CurCfg.elig \cup {CurPrim} : CurCfg.inc[n] = inc[n]}
AuthHolds(s) == \E n \in Authoritative : IsPrefix(s, nlog[n])

---------------------------------------------------------------------------

Init ==
    /\ nlog    = [n \in Nodes |-> << >>]
    /\ alive   = [n \in Nodes |-> TRUE]
    /\ inc     = [n \in Nodes |-> 1]
    /\ cfgLog  = << [prim |-> InitPrim, elig |-> {}, inc |-> [n \in Nodes |-> 1]] >>
    /\ kver    = [n \in Nodes |-> 1]
    /\ commitL = [n \in Nodes |-> 0]
    /\ rcommit = [n \in Nodes |-> 0]
    /\ sync    = [n \in Nodes |-> {}]
    /\ pending = [n \in Nodes |-> {}]
    /\ acked   = [n \in Nodes |-> [r \in Nodes |-> 0]]
    /\ recon   = [n \in Nodes |-> 0]
    /\ term    = [n \in Nodes |-> IF n = InitPrim THEN 1 ELSE 0]
    /\ clog    = << >>
    /\ everC   = {}
    /\ lossy   = FALSE
    /\ unfenced = {}
    /\ ops     = [id \in OpIds |-> UnusedOp]
    /\ meta    = [id \in OpIds |-> NoMeta]
    /\ nextOp  = 1
    /\ crashes = 0
    /\ restarts = 0

---------------------------------------------------------------------------
(* Clients *)

InvokeWrite(k, v) ==
    /\ nextOp \in OpIds
    /\ ops'    = [ops EXCEPT ![nextOp] = [UnusedOp EXCEPT
                    !.kind = "W", !.key = k, !.val = v, !.lo = Len(clog)]]
    /\ nextOp' = nextOp + 1
    /\ UNCHANGED <<repl, meta>>

\* Doc s2: a new primary serves clients only once it has reconciled.
ExecWrite(id, p) ==
    /\ ops[id].kind = "W" /\ ~meta[id].exec
    /\ ThinksPrim(p) /\ Writable(p) /\ Reconciled(p)
    /\ nlog' = [nlog EXCEPT ![p] = Append(@, [id |-> id, key |-> ops[id].key,
                                              val |-> ops[id].val])]
    /\ meta' = [meta EXCEPT ![id] = [node |-> p, exec |-> TRUE,
                                     off |-> Len(nlog[p]) + 1, term |-> term[p]]]
    /\ UNCHANGED <<nodeVars, cfgVars, primaryVars, ghostVars, commitL, rcommit, acked,
                   ops, nextOp>>

RejectWrite(id, p) ==
    /\ ops[id].kind = "W" /\ ~meta[id].exec
    /\ ThinksPrim(p) /\ ~Writable(p)
    /\ ops'  = [ops EXCEPT ![id].resp = "CLUSTERDOWN"]
    /\ meta' = [meta EXCEPT ![id].exec = TRUE, ![id].node = p]
    /\ UNCHANGED <<repl, nextOp>>

\* F2: the reply boundary carries the primaryship term that set it.
RespondOK(id) ==
    LET p == meta[id].node IN
    /\ ops[id].kind = "W" /\ ops[id].resp = None /\ meta[id].off > 0
    /\ ThinksPrim(p) /\ Fenced(p)
    /\ (StepDownRelease => meta[id].term = term[p])
    /\ meta[id].off <= commitL[p]
    /\ ops' = [ops EXCEPT ![id].resp = "OK"]
    /\ UNCHANGED <<repl, meta, nextOp>>

ReleaseUncommitted(id) ==
    LET p == meta[id].node IN
    /\ ops[id].kind = "W" /\ ops[id].resp = None /\ meta[id].off > 0
    /\ alive[p]
    /\ meta[id].off > commitL[p]
    /\ (~ThinksPrim(p) \/ ~Writable(p) \/ meta[id].term # term[p])
    /\ ops' = [ops EXCEPT ![id].resp = "UNCOMMITTED"]
    /\ UNCHANGED <<repl, meta, nextOp>>

---------------------------------------------------------------------------
(* Commit rule, with the ghost committed history *)

\* The first primary to commit an offset fixes clog at that offset. A later
\* commit of the same offset (by any primary) must agree: CommittedAgree.
\* Reconciliation uses this same rule: it never commits below MinSync.
AdvanceCommit(p) ==
    /\ ThinksPrim(p) /\ Writable(p) /\ Fenced(p)
    /\ commitL[p] < Len(nlog[p])
    /\ commitL[p] < CommitCap(p)
    /\ commitL' = [commitL EXCEPT ![p] = @ + 1]
    \* The committed history only grows when an authoritative node (named by
    \* the current config, matching incarnation) holds the extended prefix.
    \* A commit nobody authoritative holds leaves clog unchanged, so its OK
    \* violates AckedDurable (review).
    /\ IF /\ commitL[p] = Len(clog)
          /\ AuthHolds(Append(clog, nlog[p][commitL[p] + 1]))
       THEN /\ clog'  = Append(clog, nlog[p][commitL[p] + 1])
            /\ everC' = everC \cup Ids(<< nlog[p][commitL[p] + 1] >>)
       ELSE UNCHANGED <<clog, everC>>
    /\ UNCHANGED <<nodeVars, cfgVars, primaryVars, clientVars, nlog, rcommit, acked,
                   lossy, unfenced>>

---------------------------------------------------------------------------
(* Replication *)

Link(r, p) == alive[r] /\ alive[p] /\ p # r /\ PrimOf(r) = p

Receive(r) ==
    LET p == PrimOf(r) IN
    /\ Link(r, p)
    /\ IsPrefix(nlog[r], nlog[p]) /\ Len(nlog[r]) < Len(nlog[p])
    /\ (r \in sync[p] \cup pending[p] \/ Len(nlog[r]) < commitL[p])
    /\ nlog' = [nlog EXCEPT ![r] = Append(@, nlog[p][Len(nlog[r]) + 1])]
    /\ UNCHANGED <<nodeVars, cfgVars, primaryVars, ghostVars, clientVars,
                   commitL, rcommit, acked>>

Ack(r) ==
    LET p == PrimOf(r) IN
    /\ Link(r, p)
    /\ IsPrefix(nlog[r], nlog[p])
    /\ acked[p][r] < Len(nlog[r])
    /\ acked' = [acked EXCEPT ![p][r] = Len(nlog[r])]
    /\ UNCHANGED <<nodeVars, cfgVars, primaryVars, ghostVars, clientVars,
                   nlog, commitL, rcommit>>

\* REPLCONF COMMIT.
SendCommit(r) ==
    LET p == PrimOf(r) IN
    /\ Link(r, p)
    /\ IsPrefix(nlog[r], nlog[p])
    /\ rcommit[r] < Min2(commitL[p], Len(nlog[r]))
    /\ rcommit' = [rcommit EXCEPT ![r] = Min2(commitL[p], Len(nlog[r]))]
    /\ UNCHANGED <<nodeVars, cfgVars, primaryVars, ghostVars, clientVars,
                   nlog, commitL, acked>>

\* A replica whose log diverged from its primary's, and that the primary
\* does not count, is fully resynced (doc s5 "Reconciliation").
Resync(r) ==
    LET p == PrimOf(r) IN
    /\ Link(r, p)
    /\ ~IsPrefix(nlog[r], nlog[p])
    /\ r \notin sync[p] \cup pending[p] \cup EligOf(p)
    /\ nlog'    = [nlog EXCEPT ![r] = SubSeq(nlog[p], 1, CatchUpPoint(p))]
    /\ acked'   = [acked EXCEPT ![p][r] = 0]
    /\ commitL' = [commitL EXCEPT ![r] = Min2(@, commitL[p])]
    /\ rcommit' = [rcommit EXCEPT ![r] = Min2(@, commitL[p])]
    /\ UNCHANGED <<nodeVars, cfgVars, primaryVars, ghostVars, clientVars>>

---------------------------------------------------------------------------
(* Cluster V2 *)

\* A node that learns it is no longer primary drops its primary-side state.
Learn(n) ==
    /\ alive[n] /\ ~KnowsLatest(n)
    /\ kver'    = [kver EXCEPT ![n] = Len(cfgLog)]
    /\ sync'    = [sync EXCEPT ![n] = IF CurPrim = n THEN @ ELSE {}]
    /\ pending' = [pending EXCEPT ![n] = IF CurPrim = n THEN @ ELSE {}]
    /\ UNCHANGED <<logVars, nodeVars, ghostVars, clientVars, cfgLog, recon, term>>

CasOK(p) == ThinksPrim(p) /\ KnowsLatest(p) /\ CanCas

AppendCfg(c, n) ==
    /\ cfgLog' = Append(cfgLog, c)
    /\ kver'   = [kver EXCEPT ![n] = Len(cfgLog) + 1]

---------------------------------------------------------------------------
(* Promotion (doc s4, steps 1-4) *)

\* Steps 1+2 atomically: caught up, start counting.
Count(p, r) ==
    /\ AtomicPromote /\ ~EligibleFirst
    /\ ThinksPrim(p) /\ Link(r, p)
    /\ r \notin sync[p]
    /\ Cardinality(sync[p]) < TargetSync
    /\ acked[p][r] >= CatchUpPoint(p)
    /\ sync' = [sync EXCEPT ![p] = @ \cup {r}]
    /\ UNCHANGED <<logVars, nodeVars, cfgVars, ghostVars, clientVars,
                   pending, recon, term>>

\* AtomicPromote = FALSE: step 1 (catch-up check) and step 2 (counting) are
\* separate; the primary keeps streaming to a pending replica.
StartCount(p, r) ==
    /\ ~AtomicPromote /\ ~EligibleFirst
    /\ ThinksPrim(p) /\ Link(r, p)
    /\ r \notin sync[p] \cup pending[p]
    /\ Cardinality(sync[p] \cup pending[p]) < TargetSync
    /\ acked[p][r] >= CatchUpPoint(p)
    /\ pending' = [pending EXCEPT ![p] = @ \cup {r}]
    /\ UNCHANGED <<logVars, nodeVars, cfgVars, ghostVars, clientVars,
                   sync, recon, term>>

FinishCount(p, r) ==
    /\ ThinksPrim(p) /\ r \in pending[p]
    /\ sync'    = [sync EXCEPT ![p] = @ \cup {r}]
    /\ pending' = [pending EXCEPT ![p] = @ \ {r}]
    /\ UNCHANGED <<logVars, nodeVars, cfgVars, ghostVars, clientVars, recon, term>>

\* Step 4: CAS ineligible -> eligible. O1: it must already be counted.
\* EligibleFirst: CAS first, with no catch-up check, counted in the same step.
MakeEligible(p, r) ==
    /\ CasOK(p) /\ r # p /\ r \notin CurCfg.elig
    /\ IF EligibleFirst
       THEN /\ Link(r, p) /\ Cardinality(CurCfg.elig) < TargetSync
            /\ sync' = [sync EXCEPT ![p] = @ \cup {r}]
       ELSE /\ r \in sync[p]
            \* Step 4 relies on step 2's invariant (commit never passes a
            \* counted replica's ack). A counted replica that restarted empty
            \* breaks it, so re-check catch-up here (finding F6).
            /\ (CatchUpAtEligible => acked[p][r] >= CatchUpPoint(p))
            /\ UNCHANGED sync
    /\ AppendCfg([CurCfg EXCEPT !.elig = @ \cup {r}, !.inc[r] = inc[r]], p)
    /\ UNCHANGED <<logVars, nodeVars, ghostVars, clientVars, pending, recon, term>>

---------------------------------------------------------------------------
(* Demotion (doc s4, steps 1-3; the read-lease wait is step 4) *)

\* Doc s4 demotion steps 2+3: once the CAS commits, the primary stops
\* counting the replica (review: one step, not two).
MakeIneligible(p, r) ==
    /\ CasOK(p) /\ r \in CurCfg.elig
    /\ AppendCfg([CurCfg EXCEPT !.elig = @ \ {r}], p)
    /\ sync' = [sync EXCEPT ![p] = @ \ {r}]
    /\ UNCHANGED <<logVars, nodeVars, ghostVars, clientVars, pending, recon, term>>

\* A counted replica that is not eligible in the config p knows (counted
\* but never made eligible, or demoted in a config p learned) stops counting.
Uncount(p, r) ==
    /\ ThinksPrim(p) /\ r \in sync[p] /\ r \notin EligOf(p)
    /\ sync' = [sync EXCEPT ![p] = @ \ {r}]
    /\ UNCHANGED <<logVars, nodeVars, cfgVars, ghostVars, clientVars,
                   pending, recon, term>>

\* EarlyDrop: the primary stops counting a replica that is still eligible,
\* before the ineligible CAS commits (breaks O2).
EarlyUncount(p, r) ==
    /\ EarlyDrop
    /\ ThinksPrim(p) /\ r \in sync[p] /\ r \in EligOf(p)
    /\ sync' = [sync EXCEPT ![p] = @ \ {r}]
    /\ UNCHANGED <<logVars, nodeVars, cfgVars, ghostVars, clientVars,
                   pending, recon, term>>

---------------------------------------------------------------------------
(* Failures *)

Crash(n) ==
    /\ alive[n] /\ crashes < MaxCrashes
    /\ alive'   = [alive EXCEPT ![n] = FALSE]
    /\ crashes' = crashes + 1
    /\ UNCHANGED <<logVars, cfgVars, primaryVars, ghostVars, clientVars, inc, restarts>>

\* keep = TRUE: local persistence (AOF) brings the log back. keep = FALSE:
\* the node comes back empty with a new incarnation. Either way volatile
\* state is gone, the node first syncs the Cluster V2 log (doc s6), held
\* replies on it are dropped, and every primary forgets its old acks.
Restart(n, keep) ==
    /\ ~alive[n] /\ restarts < MaxRestarts
    /\ alive'    = [alive EXCEPT ![n] = TRUE]
    /\ restarts' = restarts + 1
    /\ nlog'     = IF keep THEN nlog ELSE [nlog EXCEPT ![n] = << >>]
    /\ inc'      = IF keep THEN inc ELSE [inc EXCEPT ![n] = @ + 1]
    /\ kver'     = [kver EXCEPT ![n] = Len(cfgLog)]
    /\ commitL'  = [commitL EXCEPT ![n] = 0]
    /\ rcommit'  = [rcommit EXCEPT ![n] = 0]
    \* Doc s4: a replica that fails before it is eligible is simply removed
    \* from the commit calculation. An eligible one stays counted (O2) until
    \* the primary demotes it.
    /\ sync'     = [p \in Nodes |->
                      IF p = n THEN (IF RestoreSync THEN CurCfg.elig \ {n} ELSE {})
                      ELSE IF n \in EligOf(p) THEN sync[p] ELSE sync[p] \ {n}]
    /\ pending'  = [p \in Nodes |-> IF p = n THEN {} ELSE pending[p] \ {n}]
    /\ acked'    = [p \in Nodes |-> IF p = n THEN [r \in Nodes |-> 0]
                                    ELSE [acked[p] EXCEPT ![n] = 0]]
    \* A node that restarts as primary (kept data, config unchanged) must
    \* reconcile its log again before serving.
    /\ recon'    = [recon EXCEPT ![n] = IF keep THEN Len(nlog[n]) ELSE 0]
    /\ meta'     = [id \in OpIds |->
                      IF meta[id].node = n /\ ops[id].resp = None
                      THEN [meta[id] EXCEPT !.off = 0] ELSE meta[id]]
    \* Doc s6 "Correlated data loss": if this restart removes the last
    \* authoritative copy of the history, committed writes are lost. The doc
    \* accepts this (the shard then stays unavailable until an operator
    \* recovers it), so it is an explicit lossy event: the abstract history
    \* is cut to what an authoritative node still holds (nothing).
    /\ LET authAfter == {m \in CurCfg.elig \cup {CurPrim} :
                           CurCfg.inc[m] = inc'[m] /\ IsPrefix(clog, nlog'[m])}
       IN  IF authAfter = {} /\ Len(clog) > 0
           THEN /\ clog'  = << >>
                /\ lossy' = TRUE
           ELSE UNCHANGED <<clog, lossy>>
    /\ UNCHANGED <<cfgLog, term, everC, unfenced, ops, nextOp, crashes>>

\* Ordinary takeover by an eligible replica (CAS checks its incarnation).
\* The new primary moves the old one to ineligible and counts the other
\* eligible replicas (it must reconcile before serving).
Takeover(n) ==
    /\ alive[n] /\ KnowsLatest(n) /\ CanCas
    /\ n \in CurCfg.elig /\ n # CurPrim
    /\ IncOK(CurCfg, n)
    /\ LET newElig == CurCfg.elig \ {CurPrim, n} IN
         /\ AppendCfg([CurCfg EXCEPT !.prim = n, !.elig = newElig], n)
         /\ sync'    = [sync EXCEPT ![n] = newElig]
         /\ pending' = [pending EXCEPT ![n] = {}]
         /\ acked'   = [acked EXCEPT ![n] = [r \in Nodes |-> 0]]
         /\ commitL' = [commitL EXCEPT ![n] = rcommit[n]]
         /\ recon'   = [recon EXCEPT ![n] = Len(nlog[n])]
         /\ term'    = [term EXCEPT ![n] = Len(cfgLog) + 1]
    /\ unfenced' = unfenced \ {n}
    /\ UNCHANGED <<nodeVars, clientVars, nlog, rcommit, clog, everC, lossy>>

\* Operator forced failover to an ineligible node (doc s5 "Forced
\* failover"). Committed writes it lacks are lost, explicitly.
ForceTakeover(n) ==
    /\ AllowForce
    /\ alive[n] /\ KnowsLatest(n) /\ CanCas
    /\ n # CurPrim /\ n \notin CurCfg.elig
    /\ LET cp == LCP(clog, nlog[n]) IN
         /\ AppendCfg([prim |-> n, elig |-> {}, inc |-> [CurCfg.inc EXCEPT ![n] = inc[n]]], n)
         /\ sync'    = [sync EXCEPT ![n] = {}]
         /\ pending' = [pending EXCEPT ![n] = {}]
         /\ acked'   = [acked EXCEPT ![n] = [r \in Nodes |-> 0]]
         \* The target starts from its own committed view, like Takeover. (Rev 1
         \* used cp, the ghost history's common prefix, which a real node
         \* cannot know.) cp only drives the ghost bookkeeping below.
         /\ commitL' = [commitL EXCEPT ![n] = Min2(rcommit[n], cp)]
         /\ recon'   = [recon EXCEPT ![n] = Len(nlog[n])]
         /\ term'    = [term EXCEPT ![n] = Len(cfgLog) + 1]
         /\ clog'    = SubSeq(clog, 1, cp)
         /\ lossy'   = (lossy \/ cp < Len(clog))
         /\ unfenced' = (unfenced \cup {CurPrim}) \ {n}
    /\ UNCHANGED <<nodeVars, clientVars, nlog, rcommit, everC>>

---------------------------------------------------------------------------

Next ==
    \/ \E k \in Keys, v \in Values : InvokeWrite(k, v)
    \/ \E id \in OpIds :
          \/ RespondOK(id) \/ ReleaseUncommitted(id)
          \/ \E p \in Nodes : ExecWrite(id, p) \/ RejectWrite(id, p)
    \/ \E n \in Nodes :
          \/ AdvanceCommit(n) \/ Receive(n) \/ Ack(n) \/ SendCommit(n) \/ Resync(n)
          \/ Learn(n) \/ Crash(n) \/ Takeover(n) \/ ForceTakeover(n)
          \/ \E keep \in BOOLEAN : Restart(n, keep)
    \/ \E p, r \in Nodes :
          \/ Count(p, r) \/ StartCount(p, r) \/ FinishCount(p, r)
          \/ MakeEligible(p, r) \/ MakeIneligible(p, r)
          \/ Uncount(p, r) \/ EarlyUncount(p, r)

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Refinement *)

DS == INSTANCE DurableShard
        WITH log <- clog, everIn <- everC, sysWrites <- 0,
             AllowLossyOps <- TRUE, Readers <- {},
             cursor <- [r \in {} |-> 0], MaxSystemWrites <- 0

Refinement   == DS!Spec
AckedDurable == DS!AckedWritesDurable          \* unless an explicit lossy action ran

---------------------------------------------------------------------------
(* Invariants *)

\* A node that acts as primary agrees with the committed history up to its
\* commit offset (no split-brain commit of a different entry).
CommittedAgree ==
    \A p \in Nodes : ThinksPrim(p) =>
        LET c == Min2(commitL[p], Len(clog))
        IN  SubSeq(nlog[p], 1, c) = SubSeq(clog, 1, c)

\* Core PacificA invariant with incarnations: the primary and every eligible
\* replica whose incarnation the config still names hold the committed
\* history (alive or not: a crashed node with data still has it).
EligibleHoldsCommitted ==
    \A n \in CurCfg.elig \cup {CurPrim} :
        CurCfg.inc[n] = inc[n] => IsPrefix(clog, nlog[n])

\* With no authoritative copy of the history left (doc s6, correlated data
\* loss), nothing new commits until an explicit forced failover. An OK for a
\* write that committed before the loss may still be delivered: that write
\* was durable when it committed and is lost by the correlated failure the
\* doc accepts, which is why AckedDurable is stated over clog.
NoAuthority == ~AuthHolds(clog)
UnavailableWithoutAuthority ==
    [][NoAuthority /\ ~(\E n \in Nodes : ForceTakeover(n)) => clog' = clog]_vars

Cfg   == [prim : Nodes, elig : SUBSET Nodes, inc : [Nodes -> Nat]]
OpRec == [kind : {"unused", "W"}, key : Keys, val : Values \cup {Nil},
          reader : {NoReader}, lo : Nat, at : {None},
          resp : {None, "OK", "UNCOMMITTED", "CLUSTERDOWN"}, seen : {None}]
Meta  == [node : Nodes, exec : BOOLEAN, off : Nat, term : Nat]

TypeOK ==
    /\ nlog     \in [Nodes -> Seq(Entry)]
    /\ alive    \in [Nodes -> BOOLEAN]
    /\ inc      \in [Nodes -> 1..(MaxRestarts + 1)]
    /\ cfgLog   \in Seq(Cfg) /\ 1 <= Len(cfgLog) /\ Len(cfgLog) <= MaxCfg
    /\ kver     \in [Nodes -> 1..MaxCfg]
    /\ commitL  \in [Nodes -> Nat]
    /\ rcommit  \in [Nodes -> Nat]
    /\ sync     \in [Nodes -> SUBSET Nodes]
    /\ pending  \in [Nodes -> SUBSET Nodes]
    /\ \A n \in Nodes : n \notin sync[n] \cup pending[n]
    /\ acked    \in [Nodes -> [Nodes -> Nat]]
    /\ recon    \in [Nodes -> Nat]
    /\ term     \in [Nodes -> 0..MaxCfg]
    /\ clog     \in Seq(Entry)
    /\ everC    \subseteq OpIds
    /\ lossy    \in BOOLEAN
    /\ unfenced \subseteq Nodes
    /\ ops      \in [OpIds -> OpRec]
    /\ meta     \in [OpIds -> Meta]
    /\ nextOp   \in 1..(MaxOps + 1)
    /\ crashes  \in 0..MaxCrashes
    /\ restarts \in 0..MaxRestarts

\* Trace view for counterexamples.
Alias == [nlog |-> nlog, alive |-> alive, inc |-> inc, cfgLog |-> cfgLog,
          kver |-> kver, commitL |-> commitL, rcommit |-> rcommit,
          sync |-> sync, pending |-> pending, acked |-> acked, term |-> term,
          clog |-> clog, lossy |-> lossy, unfenced |-> unfenced,
          resp |-> [id \in OpIds |-> ops[id].resp]]

\* Non-initial nodes are interchangeable (no Reach_* names one).
Sym == Permutations(Nodes \ {InitPrim})

---------------------------------------------------------------------------
(* Reachability: each must be VIOLATED. *)

\* Step 2 (membership).
Reach_Eligible   == ~(CurCfg.elig # {})
Reach_Takeover   == ~(CurPrim # InitPrim)
\* A write acknowledged before a takeover is still there afterwards.
Reach_AckSurvivesTakeover ==
    ~(CurPrim # InitPrim /\ \E id \in OpIds : ops[id].resp = "OK" /\ meta[id].node = InitPrim)
Reach_NewPrimCommits ==
    ~(CurPrim # InitPrim /\ commitL[CurPrim] > 0)
Reach_Demoted == ~(\E v \in 1..Len(cfgLog) : \E v2 \in 1..Len(cfgLog) :
                      v < v2 /\ cfgLog[v].prim = cfgLog[v2].prim
                      /\ cfgLog[v2].elig \subseteq cfgLog[v].elig
                      /\ cfgLog[v2].elig # cfgLog[v].elig)
\* A new primary completes reconciliation: it commits, by the normal rule,
\* past the committed view it inherited, up to the end of its inherited log.
Reach_Reconcile ==
    ~(\E n \in Nodes : n # InitPrim /\ ThinksPrim(n) /\ recon[n] > rcommit[n]
                       /\ Reconciled(n))
Reach_Resync == ~(\E n \in Nodes : n # CurPrim /\ alive[n]
                      /\ ~IsPrefix(nlog[n], nlog[CurPrim]))

\* Step 3 (failover).
Reach_RestartEmpty    == ~(\E n \in Nodes : inc[n] > 1)
Reach_TakeoverAfterRestart ==
    ~(restarts > 0 /\ CurPrim # InitPrim /\ commitL[CurPrim] > 0)
\* Correlated loss: the last authoritative copy is gone (only lossy event
\* possible when AllowForce = FALSE).
Reach_Stuck == ~lossy
Reach_ForcedLoss == ~lossy
Reach_RejoinEligible ==
    ~(\E n \in Nodes : inc[n] > 1 /\ n \in CurCfg.elig /\ CurCfg.inc[n] = inc[n])
=============================================================================
