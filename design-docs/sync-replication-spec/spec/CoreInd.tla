------------------------------ MODULE CoreInd ------------------------------
(***************************************************************************)
(* Iteration 3A: an inductive invariant for Core.tla.                      *)
(*                                                                         *)
(* Core is used unchanged through INSTANCE: this module only re-declares   *)
(* its variables with Apalache type annotations and fixes InitPrim = n1.  *)
(* Nodes and the other parameters are constants set by a .cfg file.       *)
(* TLC can run this module too (to test candidate lemmas on reachable      *)
(* states); CoreApalache.tla adds the Apalache-only IndInit.               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Nodes,
    \* @type: Int;
    MaxLen,
    \* @type: Int;
    MaxVer,
    \* @type: Bool;
    ReconcileFirst,
    \* @type: Bool;
    EarlyDrop

VARIABLES
    \* @type: Str -> Seq(Int);
    log,
    \* @type: { ver: Int, prim: Str, elig: Set(Str) };
    cfg,
    \* @type: Str -> { ver: Int, prim: Str, elig: Set(Str) };
    known,
    \* @type: Str -> Set(Str);
    sync,
    \* @type: Str -> (Str -> Int);
    acked,
    \* @type: Str -> Int;
    commit,
    \* @type: Str -> Int;
    recon,
    \* @type: Str -> Int;
    term,
    \* @type: Seq(Int);
    hist

ASSUME "n1" \in Nodes

C == INSTANCE Core WITH Nodes <- Nodes, InitPrim <- "n1"

Init   == C!Init
Next   == C!Next
Spec   == Init /\ [][Next]_C!vars
Safety == C!Safety

---------------------------------------------------------------------------
(* Inductive invariant *)

P  == cfg.prim
H  == cfg.elig \cup {P}                          \* the nodes Safety talks about
Stale(q) == C!ThinksPrim(q) /\ q # P             \* a deposed primary that has not learned it
Follows(r, q) == known[r].prim = q

\* q's and h's logs agree on their first k entries.
Agree(q, h, k) ==
    /\ k <= Len(log[q]) /\ k <= Len(log[h])
    /\ SubSeq(log[q], 1, k) = SubSeq(log[h], 1, k)

\* Bounded type: every state Apalache considers lies in this finite space.
TypeB ==
    /\ \A n \in Nodes :
        /\ Len(log[n]) <= MaxLen
        /\ \A i \in 1..MaxLen : i <= Len(log[n]) => log[n][i] \in 0..MaxVer
        /\ known[n].ver \in 1..MaxVer /\ known[n].prim \in Nodes
        /\ known[n].elig \subseteq Nodes
        /\ sync[n] \subseteq Nodes
        /\ \A r \in Nodes : acked[n][r] \in 0..MaxLen
        /\ commit[n] \in 0..MaxLen /\ recon[n] \in 0..MaxLen
        /\ term[n] \in 0..MaxVer
    /\ cfg.ver \in 1..MaxVer /\ cfg.prim \in Nodes /\ cfg.elig \subseteq Nodes
    /\ Len(hist) <= MaxLen
    /\ \A i \in 1..MaxLen : i <= Len(hist) => hist[i] \in 0..MaxVer

\* L1: configurations. Nobody knows a future config; whoever knows the
\* latest version knows the latest config; the primary knows it.
LemCfg ==
    /\ \A n \in Nodes : known[n].ver <= cfg.ver
    /\ \A n \in Nodes : known[n].ver = cfg.ver => known[n] = cfg
    /\ known[P] = cfg
    /\ P \notin cfg.elig

\* L2: a primary never counts itself.
LemSync == \A n \in Nodes : n \notin sync[n]

\* L3 (O1/O2 + F1): the primary counts every eligible replica; a replica
\* counted but not eligible follows the primary and was counted after
\* reconciliation.
LemCount ==
    /\ cfg.elig \subseteq sync[P]
    /\ \A r \in sync[P] \ cfg.elig : Follows(r, P) /\ C!Reconciled(P)

\* L4: the primary's acks are sound: an ack covers a common prefix, and only
\* a current follower has a non-zero ack.
LemAck ==
    \A r \in Nodes :
        /\ Agree(P, r, acked[P][r])
        /\ acked[P][r] > 0 => Follows(r, P)
        \* (CTI 2) the commit rule keeps commit below every counted ack
        /\ r \in sync[P] => commit[P] <= acked[P][r]

\* L5: an eligible replica that follows a deposed primary was eligible in
\* that primary's last config (so the deposed primary cannot resync it).
LemFollowElig ==
    \A r \in cfg.elig : r \in known[known[r].prim].elig

\* L6: a deposed primary is not eligible and, either
\*   Unrec: no promotion has happened since: every holder is still in its
\*          sync set and holds what it acked to it, and the current
\*          primary inherited at least that much (recon), or
\*   Rec:   some replica in its sync set no longer follows it (so its
\*          commit cap is frozen there) and that frozen prefix is committed.
Unrec(q) ==
    /\ \A h \in H : h \in sync[q] /\ Agree(q, h, acked[q][h])
    /\ acked[q][P] <= recon[P]
Rec(q) ==
    \E s \in sync[q] :
        /\ ~Follows(s, q)
        /\ acked[q][s] <= Len(log[q])
        /\ C!IsPrefix(SubSeq(log[q], 1, acked[q][s]), hist)
LemStale ==
    \A q \in Nodes : Stale(q) => q \notin cfg.elig /\ (Unrec(q) \/ Rec(q))

\* L7: the history is no longer than what the primary has committed, or,
\* before it has reconciled, than what it inherited. (Found by CTI 1: a
\* reconciled primary with commit 0 could otherwise promote an empty node.)
LemHist == Len(hist) <= IF C!Reconciled(P) THEN commit[P] ELSE recon[P]

IndInv ==
    /\ TypeB
    /\ LemCfg
    /\ LemSync
    /\ LemCount
    /\ LemAck
    /\ LemFollowElig
    /\ LemStale
    /\ LemHist
    /\ C!EligibleHoldsCommitted
    /\ C!CommittedAgree

\* For TLC: Init => IndInv and IndInv holds on reachable states.
IndInvImpliesSafety == IndInv => Safety
=============================================================================
