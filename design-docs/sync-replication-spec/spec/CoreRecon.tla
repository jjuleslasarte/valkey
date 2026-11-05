----------------------------- MODULE CoreRecon -----------------------------
(***************************************************************************)
(* CoreAck with min-sync-replicas and Shard's reconciliation rule (A1).   *)
(*                                                                         *)
(* Core forbids Count and Resync until a new primary has reconciled        *)
(* (commit >= recon). With MinSync >= 1 a new primary whose sync set is    *)
(* empty after takeover can then never commit, so never reconcile: safe   *)
(* but unavailable. Shard.tla instead measures catch-up and resync against *)
(* the inherited log while unreconciled:                                   *)
(*   CatchUpPoint(p) = IF Reconciled(p) THEN commit[p]                     *)
(*                     ELSE Min(recon[p], Len(log[p]))                     *)
(* This module is CoreAck (replies, F2 fence, okd) with:                   *)
(*   - CONSTANT MinSync; Writable(p) == Cardinality(sync[p] \cap           *)
(*     known[p].elig) >= MinSync, as Shard's Writable (EligOf(p) is the    *)
(*     eligible set of the config p knows);                                *)
(*   - AppendWrite needs Writable and Reconciled (serve only once          *)
(*     reconciled); Commit needs Writable;                                 *)
(*   - Count: acked[p][r] >= CatchUpPoint(p), no Reconciled gate;          *)
(*   - Resync: copies Prefix(log[p], CatchUpPoint(p)), no Reconciled gate. *)
(*                                                                         *)
(* Switches:                                                               *)
(*   ReconcileFirst = FALSE  must fail (F1): no reconciliation at all,     *)
(*                           CatchUpPoint = commit, AppendWrite ungated.   *)
(*   NoReplyFence = TRUE     must fail (F2).                               *)
(*   EarlyDrop = TRUE        must fail (O2), kept from Core.               *)
(*   StrictRecon = TRUE      Core's blocking rule: Count and Resync need   *)
(*                           Reconciled, catch-up and resync use commit.   *)
(*                           Safe, but deadlocks at MinSync >= 1.          *)
(*                                                                         *)
(* Ghost `lone`: nodes whose current primaryship began by a takeover with  *)
(* a non-empty inherited log and an empty sync set (no eligible survivor). *)
(* Reach_LoneReconcile: such a primary later reconciles. Reachable with    *)
(* the A1 rule at MinSync = 1, unreachable with StrictRecon (deadlock).    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, InitPrim, MaxLen, MaxVer, MinSync,
          ReconcileFirst, EarlyDrop, NoReplyFence, StrictRecon

ASSUME InitPrim \in Nodes /\ MinSync \in Nat

VARIABLES
    log, cfg, known, sync, acked, commit, recon, term,
    hist,    \* ghost: committed history
    held,    \* held replies [n, o, t]
    okd,     \* ghost: acknowledged <<offset, value>>
    lone     \* ghost: see header

vars == <<log, cfg, known, sync, acked, commit, recon, term, hist, held, okd, lone>>

Min2(a, b) == IF a <= b THEN a ELSE b
IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s
Prefix(s, k) == SubSeq(s, 1, Min2(k, Len(s)))

ThinksPrim(p) == known[p].prim = p
KnowsLatest(n) == known[n].ver = cfg.ver
PrimOf(n) == known[n].prim
Reconciled(p) == ~ReconcileFirst \/ commit[p] >= recon[p]
CanCas == cfg.ver < MaxVer

\* Shard.tla: Cardinality(sync[p] \cap EligOf(p)) >= MinSync.
Writable(p) == Cardinality(sync[p] \cap known[p].elig) >= MinSync

CatchUpPoint(p) ==
    IF StrictRecon \/ Reconciled(p) THEN commit[p]
    ELSE Min2(recon[p], Len(log[p]))

\* Commit rule: the min ack over the sync set, or the whole log if it is empty.
CommitCap(p) ==
    IF sync[p] = {} THEN Len(log[p])
    ELSE CHOOSE m \in {acked[p][r] : r \in sync[p]} :
             \A r \in sync[p] : m <= acked[p][r]

Init0 == [ver |-> 1, prim |-> InitPrim, elig |-> {}]

Init ==
    /\ log    = [n \in Nodes |-> << >>]
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
    /\ lone   = {}

Keep == UNCHANGED <<held, okd, lone>>

---------------------------------------------------------------------------

\* AppendWrite with its held reply (CoreAck's Write).
Write(p) ==
    /\ ThinksPrim(p) /\ Writable(p) /\ Reconciled(p) /\ Len(log[p]) < MaxLen
    /\ log' = [log EXCEPT ![p] = Append(@, term[p])]
    /\ held' = held \cup {[n |-> p, o |-> Len(log[p]) + 1, t |-> term[p]]}
    /\ UNCHANGED <<cfg, known, sync, acked, commit, recon, term, hist, okd, lone>>

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

\* Promotion steps 1+2: caught up to the catch-up point, start counting.
Count(p, r) ==
    /\ ThinksPrim(p) /\ r # p /\ PrimOf(r) = p
    /\ StrictRecon => Reconciled(p)
    /\ r \notin sync[p] /\ acked[p][r] >= CatchUpPoint(p)
    /\ sync' = [sync EXCEPT ![p] = @ \cup {r}]
    /\ UNCHANGED <<log, cfg, known, acked, commit, recon, term, hist>> /\ Keep

CasOK(p) == ThinksPrim(p) /\ KnowsLatest(p) /\ CanCas

SetCfg(c, n) ==
    /\ cfg' = c
    /\ known' = [known EXCEPT ![n] = c]

MakeEligible(p, r) ==
    /\ CasOK(p) /\ r \in sync[p] /\ r \notin cfg.elig
    /\ SetCfg([cfg EXCEPT !.ver = @ + 1, !.elig = @ \cup {r}], p)
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

Takeover(n) ==
    /\ KnowsLatest(n) /\ CanCas /\ n \in cfg.elig /\ n # cfg.prim
    /\ LET newElig == cfg.elig \ {cfg.prim, n} IN
         /\ SetCfg([ver |-> cfg.ver + 1, prim |-> n, elig |-> newElig], n)
         /\ sync'   = [sync EXCEPT ![n] = newElig]
         /\ acked'  = [acked EXCEPT ![n] = [r \in Nodes |-> 0]]
         /\ commit' = [commit EXCEPT ![n] = 0]
         /\ recon'  = [recon EXCEPT ![n] = Len(log[n])]
         /\ term'   = [term EXCEPT ![n] = cfg.ver + 1]
         /\ lone'   = IF newElig = {} /\ Len(log[n]) > 0 THEN lone \cup {n} ELSE lone \ {n}
    /\ UNCHANGED <<log, hist, held, okd>>

Resync(r) ==
    LET p == PrimOf(r) IN
    /\ p # r /\ ~IsPrefix(log[r], log[p])
    /\ r \notin sync[p] /\ r \notin known[p].elig
    /\ StrictRecon => Reconciled(p)
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
    /\ UNCHANGED <<log, cfg, known, sync, acked, commit, recon, term, hist, lone>>

Abort(h) ==
    /\ h \in held /\ ~Fenced(h)
    /\ held' = held \ {h}
    /\ UNCHANGED <<log, cfg, known, sync, acked, commit, recon, term, hist, okd, lone>>

ReleaseSome == \E h \in held : Release(h)
AbortSome == \E h \in held : Abort(h)

Next ==
    \/ \E n \in Nodes : Write(n) \/ Replicate(n) \/ Ack(n) \/ Commit(n)
                        \/ Learn(n) \/ Takeover(n) \/ Resync(n)
    \/ \E p, r \in Nodes : Count(p, r) \/ MakeEligible(p, r)
                           \/ MakeIneligible(p, r) \/ EarlyUncount(p, r)
    \/ ReleaseSome \/ AbortSome

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Properties *)

EligibleHoldsCommitted ==
    \A n \in cfg.elig \cup {cfg.prim} : IsPrefix(hist, log[n])

CommittedAgree ==
    \A p \in Nodes : commit[p] <= Len(log[p]) /\ Prefix(log[p], commit[p]) = Prefix(hist, commit[p])

AckedDurable == \A a \in okd : Len(hist) >= a[1] /\ hist[a[1]] = a[2]

AckedHeld ==
    \A a \in okd : \A n \in cfg.elig \cup {cfg.prim} :
        Len(log[n]) >= a[1] /\ log[n][a[1]] = a[2]

TypeOK ==
    /\ log \in [Nodes -> Seq(Nat)]
    /\ cfg.ver \in 1..MaxVer /\ cfg.prim \in Nodes /\ cfg.elig \subseteq Nodes
    /\ sync \in [Nodes -> SUBSET Nodes]
    /\ acked \in [Nodes -> [Nodes -> Nat]] /\ commit \in [Nodes -> Nat]
    /\ hist \in Seq(Nat) /\ lone \subseteq Nodes

\* The Lean invariant's changed conjuncts (ReconProof.Inv.syncNew, reconLen).
SyncNew ==
    \A r \in sync[cfg.prim] : r \notin cfg.elig =>
        PrimOf(r) = cfg.prim /\ recon[cfg.prim] <= acked[cfg.prim][r]
ReconLen == recon[cfg.prim] <= Len(log[cfg.prim])

\* Reachability (must be violated where reachable).
\* A new primary with a non-empty inherited log later reconciles.
Reach_Reconcile ==
    ~(cfg.prim # InitPrim /\ recon[cfg.prim] > 0 /\ commit[cfg.prim] >= recon[cfg.prim])
\* ... and it took over with an empty sync set (the MinSync >= 1 deadlock case).
Reach_LoneReconcile ==
    ~(cfg.prim \in lone /\ commit[cfg.prim] >= recon[cfg.prim])
\* A lone primary exists at all (the deadlock precondition is reachable).
Reach_Lone == lone = {}
Reach_Ack == okd = {}
=============================================================================
