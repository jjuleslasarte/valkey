---------------------------- MODULE CoreRestart ----------------------------
(***************************************************************************)
(* CoreRecon (A1 reconciliation, F2 reply fence, every MinSync) with node  *)
(* restarts, with and without data, and incarnations (design-doc s5        *)
(* "Restarts", s6 "Restarted nodes rejoin as ineligible", FINDINGS F5).    *)
(*                                                                         *)
(* Incarnations (as in Shard.tla with IncCheck = TRUE):                    *)
(*   - inc[n] changes when n restarts without its data;                    *)
(*   - the config records cfg.inc[r] for each replica r when it is made    *)
(*     eligible (and for the initial primary); a takeover keeps it;        *)
(*   - Takeover(n) checks cfg.inc[n] = inc[n];                             *)
(*   - ThinksPrim(p) checks the incarnation the config p knows records     *)
(*     for p, so a primary that came back empty is not a primary;          *)
(*   - Auth: the primary and the eligible replicas whose recorded          *)
(*     incarnation is their current one. These are the nodes that must     *)
(*     hold the committed history (EligibleHoldsCommitted).                *)
(*   - "Primaries ack-count only replicas of the matching incarnation":    *)
(*     Writable counts only eligible sync members with a matching          *)
(*     incarnation; Count does not count an eligible replica whose         *)
(*     incarnation does not match; Takeover counts only the matching       *)
(*     eligible replicas; when an eligible replica restarts empty the      *)
(*     current primary stops counting it (it no longer holds anything and  *)
(*     can no longer take over). It rejoins through demotion and the       *)
(*     promotion flow, which records its new incarnation.                  *)
(*                                                                         *)
(* Restarts. A node first syncs the Cluster V2 log (doc s6), so both       *)
(* restart actions require KnowsLatest(n): a node that does not know the   *)
(* latest config takes a Learn step first, which is the same state as a    *)
(* restart that learns. Volatile state is lost: commit = 0, own acks = 0,  *)
(* held replies on n are dropped with the client connections (no OK and    *)
(* no UNCOMMITTED reply; the client sees a closed connection).             *)
(*   RestartEmpty(n): log = <<>>, inc[n] + 1, no primaryship (its old     *)
(*     incarnation stays recorded in cfg until it is demoted, but it can   *)
(*     neither act as primary nor take over), empty sync set, recon = 0;   *)
(*     the current primary forgets n's ack and stops counting it.          *)
(*     Survival assumption (guard): another authoritative node exists,     *)
(*     \E m \in Auth : m # n, i.e. the restart does not remove the last    *)
(*     node of Auth. NoSurvivor = TRUE drops the guard; then, as in        *)
(*     Shard.tla, a restart that leaves no authoritative holder of the     *)
(*     history is an explicit loss and cuts the ghost history to << >>;    *)
(*     it must fail AckedDurable. With the guard the cut never fires       *)
(*     (EligibleHoldsCommitted).                                           *)
(*   RestartKeep(n): log and incarnation kept, recon = Len(log) (it must   *)
(*     commit its log again before serving). If n is the primary, F5 fix   *)
(*     (RebuildSync): its sync set is rebuilt from the eligible replicas   *)
(*     of its config whose incarnation matches, with no cached acks, so    *)
(*     it commits nothing until fresh acks arrive. RebuildSync = FALSE is  *)
(*     the doc as written (empty sync set) and must fail                   *)
(*     EligibleHoldsCommitted (Shard_f_noRestoreMin1).                     *)
(*     Other primaries keep their ack from n: n's log is unchanged.        *)
(*                                                                         *)
(* Switches (bug value):                                                   *)
(*   ReconcileFirst = FALSE (F1), NoReplyFence = TRUE (F2),                *)
(*   EarlyDrop = TRUE (O2): as in CoreRecon.                               *)
(*   NoSurvivor = TRUE: no survival guard, must fail AckedDurable.         *)
(*   RebuildSync = FALSE: F5, must fail EligibleHoldsCommitted.            *)
(*   IncCheck = FALSE: no incarnation checks (takeover, primaryship).      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, InitPrim, MaxLen, MaxVer, MinSync, MaxRestarts,
          ReconcileFirst, EarlyDrop, NoReplyFence,
          NoSurvivor, RebuildSync, IncCheck

ASSUME InitPrim \in Nodes /\ MinSync \in Nat /\ MaxRestarts \in Nat

VARIABLES
    log, inc, cfg, known, sync, acked, commit, recon, term,
    hist,     \* ghost: committed history
    held,     \* held replies [n, o, t]
    okd,      \* ghost: acknowledged <<offset, value>>
    restarts  \* bound for model checking

vars == <<log, inc, cfg, known, sync, acked, commit, recon, term, hist, held, okd, restarts>>

Min2(a, b) == IF a <= b THEN a ELSE b
IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s
Prefix(s, k) == SubSeq(s, 1, Min2(k, Len(s)))

IncOK(c, n) == ~IncCheck \/ c.inc[n] = inc[n]
ThinksPrim(p) == known[p].prim = p /\ IncOK(known[p], p)
KnowsLatest(n) == known[n].ver = cfg.ver
PrimOf(n) == known[n].prim
Reconciled(p) == ~ReconcileFirst \/ commit[p] >= recon[p]
CanCas == cfg.ver < MaxVer

Auth == {n \in cfg.elig \cup {cfg.prim} : cfg.inc[n] = inc[n]}

\* Matching eligible replicas of a config.
MatchElig(c) == {r \in c.elig : c.inc[r] = inc[r]}

Writable(p) == Cardinality(sync[p] \cap MatchElig(known[p])) >= MinSync

CatchUpPoint(p) ==
    IF Reconciled(p) THEN commit[p] ELSE Min2(recon[p], Len(log[p]))

CommitCap(p) ==
    IF sync[p] = {} THEN Len(log[p])
    ELSE CHOOSE m \in {acked[p][r] : r \in sync[p]} :
             \A r \in sync[p] : m <= acked[p][r]

Init0 == [ver |-> 1, prim |-> InitPrim, elig |-> {}, inc |-> [n \in Nodes |-> 1]]

Init ==
    /\ log    = [n \in Nodes |-> << >>]
    /\ inc    = [n \in Nodes |-> 1]
    /\ cfg    = Init0
    /\ known  = [n \in Nodes |-> Init0]
    /\ sync   = [n \in Nodes |-> {}]
    /\ acked  = [n \in Nodes |-> [r \in Nodes |-> 0]]
    /\ commit = [n \in Nodes |-> 0]
    /\ recon  = [n \in Nodes |-> 0]
    /\ term   = [n \in Nodes |-> IF n = InitPrim THEN 1 ELSE 0]
    /\ hist   = << >>
    /\ held   = {}
    /\ okd    = {}
    /\ restarts = 0

Keep == UNCHANGED <<held, okd, inc, restarts>>

---------------------------------------------------------------------------

Write(p) ==
    /\ ThinksPrim(p) /\ Writable(p) /\ Reconciled(p) /\ Len(log[p]) < MaxLen
    /\ log' = [log EXCEPT ![p] = Append(@, term[p])]
    /\ held' = held \cup {[n |-> p, o |-> Len(log[p]) + 1, t |-> term[p]]}
    /\ UNCHANGED <<inc, cfg, known, sync, acked, commit, recon, term, hist, okd, restarts>>

Replicate(r) ==
    LET p == PrimOf(r) IN
    /\ p # r /\ IsPrefix(log[r], log[p]) /\ Len(log[r]) < Len(log[p])
    /\ log' = [log EXCEPT ![r] = Append(@, log[p][Len(log[r]) + 1])]
    /\ UNCHANGED <<cfg, known, sync, acked, commit, recon, term, hist>> /\ Keep

Ack(r) ==
    LET p == PrimOf(r) IN
    /\ p # r /\ IsPrefix(log[r], log[p]) /\ acked[p][r] < Len(log[r])
    /\ acked' = [acked EXCEPT ![p][r] = Len(log[r])]
    /\ UNCHANGED <<log, cfg, known, sync, commit, recon, term, hist>> /\ Keep

Commit(p) ==
    /\ ThinksPrim(p) /\ Writable(p)
    /\ commit[p] < Len(log[p]) /\ commit[p] < CommitCap(p)
    /\ commit' = [commit EXCEPT ![p] = @ + 1]
    /\ hist' = IF commit[p] = Len(hist) THEN Append(hist, log[p][commit[p] + 1]) ELSE hist
    /\ UNCHANGED <<log, cfg, known, sync, acked, recon, term>> /\ Keep

\* An eligible replica whose incarnation does not match is not counted.
Count(p, r) ==
    /\ ThinksPrim(p) /\ r # p /\ PrimOf(r) = p
    /\ r \in known[p].elig => known[p].inc[r] = inc[r]
    /\ r \notin sync[p] /\ acked[p][r] >= CatchUpPoint(p)
    /\ sync' = [sync EXCEPT ![p] = @ \cup {r}]
    /\ UNCHANGED <<log, cfg, known, acked, commit, recon, term, hist>> /\ Keep

CasOK(p) == ThinksPrim(p) /\ KnowsLatest(p) /\ CanCas

SetCfg(c, n) ==
    /\ cfg' = c
    /\ known' = [known EXCEPT ![n] = c]

\* Records the replica's current incarnation (doc s6).
MakeEligible(p, r) ==
    /\ CasOK(p) /\ r \in sync[p] /\ r \notin cfg.elig
    /\ SetCfg([cfg EXCEPT !.ver = @ + 1, !.elig = @ \cup {r}, !.inc[r] = inc[r]], p)
    /\ UNCHANGED <<log, sync, acked, commit, recon, term, hist>> /\ Keep

MakeIneligible(p, r) ==
    /\ CasOK(p) /\ r \in cfg.elig
    /\ SetCfg([cfg EXCEPT !.ver = @ + 1, !.elig = @ \ {r}], p)
    /\ sync' = [sync EXCEPT ![p] = @ \ {r}]
    /\ UNCHANGED <<log, acked, commit, recon, term, hist>> /\ Keep

EarlyUncount(p, r) ==
    /\ EarlyDrop /\ ThinksPrim(p) /\ r \in sync[p]
    /\ sync' = [sync EXCEPT ![p] = @ \ {r}]
    /\ UNCHANGED <<log, cfg, known, acked, commit, recon, term, hist>> /\ Keep

Learn(n) ==
    /\ ~KnowsLatest(n)
    /\ known' = [known EXCEPT ![n] = cfg]
    /\ sync'  = [sync EXCEPT ![n] = IF cfg.prim = n THEN @ ELSE {}]
    /\ UNCHANGED <<log, cfg, acked, commit, recon, term, hist>> /\ Keep

\* The takeover CAS checks the incarnation (doc s6).
Takeover(n) ==
    /\ KnowsLatest(n) /\ CanCas /\ n \in cfg.elig /\ n # cfg.prim
    /\ IncOK(cfg, n)
    /\ LET newElig == cfg.elig \ {cfg.prim, n}
           c == [ver |-> cfg.ver + 1, prim |-> n, elig |-> newElig, inc |-> cfg.inc] IN
         /\ SetCfg(c, n)
         /\ sync'   = [sync EXCEPT ![n] = IF IncCheck THEN MatchElig(c) ELSE newElig]
         /\ acked'  = [acked EXCEPT ![n] = [r \in Nodes |-> 0]]
         /\ commit' = [commit EXCEPT ![n] = 0]
         /\ recon'  = [recon EXCEPT ![n] = Len(log[n])]
         /\ term'   = [term EXCEPT ![n] = cfg.ver + 1]
    /\ UNCHANGED <<log, hist>> /\ Keep

Resync(r) ==
    LET p == PrimOf(r) IN
    /\ p # r /\ ~IsPrefix(log[r], log[p])
    /\ r \notin sync[p] /\ r \notin known[p].elig
    /\ log'    = [log EXCEPT ![r] = Prefix(log[p], CatchUpPoint(p))]
    /\ acked'  = [acked EXCEPT ![p][r] = 0]
    /\ commit' = [commit EXCEPT ![r] = Min2(@, commit[p])]
    /\ UNCHANGED <<cfg, known, sync, recon, term, hist>> /\ Keep

Fenced(h) == ThinksPrim(h.n) /\ term[h.n] = h.t

Release(h) ==
    /\ h \in held /\ commit[h.n] >= h.o
    /\ NoReplyFence \/ Fenced(h)
    /\ okd'  = okd \cup {<<h.o, h.t>>}
    /\ held' = held \ {h}
    /\ UNCHANGED <<log, inc, cfg, known, sync, acked, commit, recon, term, hist, restarts>>

Abort(h) ==
    /\ h \in held /\ ~Fenced(h)
    /\ held' = held \ {h}
    /\ UNCHANGED <<log, inc, cfg, known, sync, acked, commit, recon, term, hist, okd, restarts>>

ReleaseSome == \E h \in held : Release(h)
AbortSome == \E h \in held : Abort(h)

---------------------------------------------------------------------------
(* Restarts *)

DropHeld(n) == {h \in held : h.n # n}

RestartEmpty(n) ==
    /\ restarts < MaxRestarts /\ KnowsLatest(n)
    /\ NoSurvivor \/ \E m \in Auth : m # n
    /\ log'    = [log EXCEPT ![n] = << >>]
    /\ inc'    = [inc EXCEPT ![n] = @ + 1]
    /\ commit' = [commit EXCEPT ![n] = 0]
    /\ recon'  = [recon EXCEPT ![n] = 0]
    /\ sync'   = [p \in Nodes |-> IF p = n THEN {}
                                  ELSE IF p = cfg.prim THEN sync[p] \ {n} ELSE sync[p]]
    /\ acked'  = [p \in Nodes |-> IF p = n THEN [r \in Nodes |-> 0]
                                  ELSE IF p = cfg.prim THEN [acked[p] EXCEPT ![n] = 0]
                                  ELSE acked[p]]
    /\ held'   = DropHeld(n)
    \* Explicit loss (NoSurvivor only): no authoritative holder of the history.
    /\ LET authAfter == {m \in cfg.elig \cup {cfg.prim} :
                           cfg.inc[m] = inc'[m] /\ IsPrefix(hist, log'[m])}
       IN  hist' = IF authAfter = {} THEN << >> ELSE hist
    /\ restarts' = restarts + 1
    /\ UNCHANGED <<cfg, known, term, okd>>

RestartKeep(n) ==
    /\ restarts < MaxRestarts /\ KnowsLatest(n)
    /\ commit' = [commit EXCEPT ![n] = 0]
    /\ recon'  = [recon EXCEPT ![n] = Len(log[n])]
    /\ acked'  = [acked EXCEPT ![n] = [r \in Nodes |-> 0]]
    /\ sync'   = [sync EXCEPT ![n] =
                    IF ThinksPrim(n) /\ RebuildSync THEN MatchElig(known[n]) \ {n} ELSE {}]
    /\ held'   = DropHeld(n)
    /\ restarts' = restarts + 1
    /\ UNCHANGED <<log, inc, cfg, known, term, hist, okd>>

Next ==
    \/ \E n \in Nodes : Write(n) \/ Replicate(n) \/ Ack(n) \/ Commit(n)
                        \/ Learn(n) \/ Takeover(n) \/ Resync(n)
                        \/ RestartEmpty(n) \/ RestartKeep(n)
    \/ \E p, r \in Nodes : Count(p, r) \/ MakeEligible(p, r)
                           \/ MakeIneligible(p, r) \/ EarlyUncount(p, r)
    \/ ReleaseSome \/ AbortSome

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Properties *)

\* Restated for authoritative nodes.
EligibleHoldsCommitted == \A n \in Auth : IsPrefix(hist, log[n])

CommittedAgree ==
    \A p \in Nodes : commit[p] <= Len(log[p]) /\ Prefix(log[p], commit[p]) = Prefix(hist, commit[p])

AckedDurable == \A a \in okd : Len(hist) >= a[1] /\ hist[a[1]] = a[2]

AckedHeld ==
    \A a \in okd : \A n \in Auth : Len(log[n]) >= a[1] /\ log[n][a[1]] = a[2]

TypeOK ==
    /\ log \in [Nodes -> Seq(Nat)] /\ inc \in [Nodes -> Nat]
    /\ cfg.ver \in 1..MaxVer /\ cfg.prim \in Nodes /\ cfg.elig \subseteq Nodes
    /\ cfg.inc \in [Nodes -> Nat]
    /\ sync \in [Nodes -> SUBSET Nodes]
    /\ acked \in [Nodes -> [Nodes -> Nat]] /\ commit \in [Nodes -> Nat]
    /\ hist \in Seq(Nat)

\* Lean invariant conjuncts (RestartProof.Inv) that differ from ReconProof.
SyncNew ==
    \A r \in sync[cfg.prim] : r \notin cfg.elig =>
        PrimOf(r) = cfg.prim /\ recon[cfg.prim] <= acked[cfg.prim][r]
ReconLen == recon[cfg.prim] <= Len(log[cfg.prim])
\* O1 restated: a primary counts every matching eligible replica it knows.
EligSync == \A p \in Nodes : ThinksPrim(p) => MatchElig(known[p]) \ {p} \subseteq sync[p]
\* Recorded incarnations are never ahead of the node.
IncLe == \A n \in Nodes : cfg.inc[n] <= inc[n] /\ \A m \in Nodes : known[m].inc[n] <= inc[n]

\* MinSync >= 1: while an eligible replica exists the current primary only
\* commits with one, so the history is on two authoritative nodes after
\* every commit by the current primary (checked as an action property).
TwoCopies ==
    [][\A p \in Nodes :
         (MinSync >= 1 /\ Commit(p) /\ p = cfg.prim) =>
            \E e \in Auth' : e # p /\ IsPrefix(hist', log'[e]) /\ IsPrefix(hist', log'[p])]_vars

\* Reachability (must be violated where reachable).
Reach_RestartEmpty == \A n \in Nodes : inc[n] = 1
\* A primary that came back empty was replaced by an eligible survivor.
Reach_TakeoverAfterEmpty == ~(inc[InitPrim] > 1 /\ cfg.prim # InitPrim /\ Len(hist) > 0)
\* A node that came back empty became eligible again with its new incarnation.
Reach_ReEligible == ~(\E n \in Nodes : inc[n] > 1 /\ n \in cfg.elig /\ cfg.inc[n] = inc[n])
\* A primary that restarted with its data commits again with a rebuilt sync set.
Reach_KeepCommit ==
    ~(/\ restarts > 0 /\ (\A n \in Nodes : inc[n] = 1) /\ cfg.prim = InitPrim
      /\ cfg.elig # {} /\ commit[InitPrim] > 0 /\ commit[InitPrim] = Len(log[InitPrim]))
\* An acknowledged write survives the primary coming back empty.
Reach_AckSurvivesEmptyPrim == ~(okd # {} /\ inc[InitPrim] > 1 /\ cfg.prim # InitPrim)
=============================================================================
