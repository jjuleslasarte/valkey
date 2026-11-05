-------------------------------- MODULE Core --------------------------------
(***************************************************************************)
(* Iteration 3: the minimal core of the sync replication membership        *)
(* protocol, as a target for an unbounded proof (Apalache inductive        *)
(* invariant, Lean).                                                       *)
(*                                                                         *)
(* Kept from Shard.tla (steps 2-3), protocol as fixed by the findings:     *)
(*   - per-node logs; an entry is the term (config version) of the primary *)
(*     that appended it, so a deposed primary's entries differ            *)
(*   - Cluster V2 as one versioned configuration [ver, prim, elig];        *)
(*     each node knows some version, possibly stale (known[n])             *)
(*   - a node that believes it is primary appends, collects acks, and      *)
(*     commits by the commit rule (min ack over its sync set)              *)
(*   - promotion: catch-up + count in one step (O1 via MakeEligible only   *)
(*     for counted replicas); demotion: ineligible CAS + stop counting in  *)
(*     one step (O2)                                                       *)
(*   - takeover by an eligible replica that knows the latest config        *)
(*   - reconciliation (F1 fix): after takeover nothing is appended,        *)
(*     promoted or resynced until the inherited log has committed          *)
(*   - full resync of a diverged, uncounted, ineligible replica            *)
(* Left out: clients and replies, reads and leases, restarts and           *)
(* incarnations, forced failover, min-sync-replicas (MinSync = 0 is the    *)
(* weakest case for this invariant: a primary may commit alone).           *)
(*                                                                         *)
(* Ghost: hist, the committed history: the first commit of each offset     *)
(* fixes it.                                                               *)
(*                                                                         *)
(* Property to prove: EligibleHoldsCommitted (the core PacificA claim:     *)
(* the primary and every eligible replica hold the committed history) and  *)
(* CommittedAgree (no node commits an entry that differs from the history).*)
(*                                                                         *)
(* Bug switches (must fail): ReconcileFirst = FALSE (F1), EarlyDrop = TRUE *)
(* (break O2: stop counting before the ineligible CAS).                    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, InitPrim, MaxLen, MaxVer, ReconcileFirst, EarlyDrop

ASSUME InitPrim \in Nodes

VARIABLES
    log,     \* [Nodes -> Seq(Nat)]
    cfg,     \* [ver : Nat, prim : Nodes, elig : SUBSET Nodes]: Cluster V2
    known,   \* [Nodes -> config record]: the config each node knows
    sync,    \* [Nodes -> SUBSET Nodes]: replicas a would-be primary counts
    acked,   \* [Nodes -> [Nodes -> Nat]]
    commit,  \* [Nodes -> Nat]
    recon,   \* [Nodes -> Nat]: log length at takeover
    term,    \* [Nodes -> Nat]: config version at which the node became primary
    hist     \* ghost: Seq(Nat), committed history

vars == <<log, cfg, known, sync, acked, commit, recon, term, hist>>

Min2(a, b) == IF a <= b THEN a ELSE b
IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s
Prefix(s, k) == SubSeq(s, 1, Min2(k, Len(s)))

ThinksPrim(p) == known[p].prim = p
KnowsLatest(n) == known[n].ver = cfg.ver
PrimOf(n) == known[n].prim
Reconciled(p) == ~ReconcileFirst \/ commit[p] >= recon[p]
CanCas == cfg.ver < MaxVer

\* Commit rule with min-sync-replicas = 0: the min ack over the sync set,
\* or the whole log if the set is empty.
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

---------------------------------------------------------------------------

AppendWrite(p) ==
    /\ ThinksPrim(p) /\ Reconciled(p) /\ Len(log[p]) < MaxLen
    /\ log' = [log EXCEPT ![p] = Append(@, term[p])]
    /\ UNCHANGED <<cfg, known, sync, acked, commit, recon, term, hist>>

Replicate(r) ==
    LET p == PrimOf(r) IN
    /\ p # r /\ IsPrefix(log[r], log[p]) /\ Len(log[r]) < Len(log[p])
    /\ log' = [log EXCEPT ![r] = Append(@, log[p][Len(log[r]) + 1])]
    /\ UNCHANGED <<cfg, known, sync, acked, commit, recon, term, hist>>

Ack(r) ==
    LET p == PrimOf(r) IN
    /\ p # r /\ IsPrefix(log[r], log[p]) /\ acked[p][r] < Len(log[r])
    /\ acked' = [acked EXCEPT ![p][r] = Len(log[r])]
    /\ UNCHANGED <<log, cfg, known, sync, commit, recon, term, hist>>

Commit(p) ==
    /\ ThinksPrim(p)
    /\ commit[p] < Len(log[p]) /\ commit[p] < CommitCap(p)
    /\ commit' = [commit EXCEPT ![p] = @ + 1]
    /\ hist' = IF commit[p] = Len(hist) THEN Append(hist, log[p][commit[p] + 1]) ELSE hist
    /\ UNCHANGED <<log, cfg, known, sync, acked, recon, term>>

\* Promotion steps 1+2: caught up to the commit offset, start counting.
Count(p, r) ==
    /\ ThinksPrim(p) /\ Reconciled(p) /\ r # p /\ PrimOf(r) = p
    /\ r \notin sync[p] /\ acked[p][r] >= commit[p]
    /\ sync' = [sync EXCEPT ![p] = @ \cup {r}]
    /\ UNCHANGED <<log, cfg, known, acked, commit, recon, term, hist>>

CasOK(p) == ThinksPrim(p) /\ KnowsLatest(p) /\ CanCas

SetCfg(c, n) ==
    /\ cfg' = c
    /\ known' = [known EXCEPT ![n] = c]

\* Promotion step 4 (O1: only a counted replica becomes eligible).
MakeEligible(p, r) ==
    /\ CasOK(p) /\ r \in sync[p] /\ r \notin cfg.elig
    /\ SetCfg([cfg EXCEPT !.ver = @ + 1, !.elig = @ \cup {r}], p)
    /\ UNCHANGED <<log, sync, acked, commit, recon, term, hist>>

\* Demotion steps 2+3 (O2: stop counting only together with the CAS).
MakeIneligible(p, r) ==
    /\ CasOK(p) /\ r \in cfg.elig
    /\ SetCfg([cfg EXCEPT !.ver = @ + 1, !.elig = @ \ {r}], p)
    /\ sync' = [sync EXCEPT ![p] = @ \ {r}]
    /\ UNCHANGED <<log, acked, commit, recon, term, hist>>

\* Bug: stop counting a replica that is still eligible.
EarlyUncount(p, r) ==
    /\ EarlyDrop /\ ThinksPrim(p) /\ r \in sync[p]
    /\ sync' = [sync EXCEPT ![p] = @ \ {r}]
    /\ UNCHANGED <<log, cfg, known, acked, commit, recon, term, hist>>

Learn(n) ==
    /\ ~KnowsLatest(n)
    /\ known' = [known EXCEPT ![n] = cfg]
    /\ sync'  = [sync EXCEPT ![n] = IF cfg.prim = n THEN @ ELSE {}]
    /\ UNCHANGED <<log, cfg, acked, commit, recon, term, hist>>

Takeover(n) ==
    /\ KnowsLatest(n) /\ CanCas /\ n \in cfg.elig /\ n # cfg.prim
    /\ LET newElig == cfg.elig \ {cfg.prim, n} IN
         /\ SetCfg([ver |-> cfg.ver + 1, prim |-> n, elig |-> newElig], n)
         /\ sync'   = [sync EXCEPT ![n] = newElig]
         /\ acked'  = [acked EXCEPT ![n] = [r \in Nodes |-> 0]]
         /\ commit' = [commit EXCEPT ![n] = 0]
         /\ recon'  = [recon EXCEPT ![n] = Len(log[n])]
         /\ term'   = [term EXCEPT ![n] = cfg.ver + 1]
    /\ UNCHANGED <<log, hist>>

Resync(r) ==
    LET p == PrimOf(r) IN
    /\ p # r /\ ~IsPrefix(log[r], log[p])
    /\ r \notin sync[p] /\ r \notin known[p].elig /\ Reconciled(p)
    /\ log'    = [log EXCEPT ![r] = Prefix(log[p], commit[p])]
    /\ acked'  = [acked EXCEPT ![p][r] = 0]
    /\ commit' = [commit EXCEPT ![r] = Min2(@, commit[p])]
    /\ UNCHANGED <<cfg, known, sync, recon, term, hist>>

Next ==
    \/ \E n \in Nodes : AppendWrite(n) \/ Replicate(n) \/ Ack(n) \/ Commit(n)
                        \/ Learn(n) \/ Takeover(n) \/ Resync(n)
    \/ \E p, r \in Nodes : Count(p, r) \/ MakeEligible(p, r)
                           \/ MakeIneligible(p, r) \/ EarlyUncount(p, r)

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Properties *)

EligibleHoldsCommitted ==
    \A n \in cfg.elig \cup {cfg.prim} : IsPrefix(hist, log[n])

CommittedAgree ==
    \A p \in Nodes : commit[p] <= Len(log[p]) /\ Prefix(log[p], commit[p]) = Prefix(hist, commit[p])

Safety == EligibleHoldsCommitted /\ CommittedAgree

TypeOK ==
    /\ log \in [Nodes -> Seq(Nat)]
    /\ cfg.ver \in 1..MaxVer /\ cfg.prim \in Nodes /\ cfg.elig \subseteq Nodes
    /\ sync \in [Nodes -> SUBSET Nodes]
    /\ acked \in [Nodes -> [Nodes -> Nat]] /\ commit \in [Nodes -> Nat]
    /\ hist \in Seq(Nat)

\* Reachability (must be violated): a takeover after a commit, and a resync.
Reach_TakeoverAfterCommit == ~(cfg.prim # InitPrim /\ Len(hist) > 0 /\ commit[cfg.prim] > 0)
Reach_Resync == ~(\E n \in Nodes : Len(log[n]) > 0 /\ \E m \in Nodes : m # n /\ ~IsPrefix(log[n], log[m]) /\ ~IsPrefix(log[m], log[n]))
=============================================================================
