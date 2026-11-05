---------------------------- MODULE CoreApalache ----------------------------
(***************************************************************************)
(* Apalache harness for the inductive invariant of Core (see CoreInd.tla   *)
(* and APALACHE.md). IndInit is an arbitrary state of the bounded type     *)
(* that satisfies IndInv; `check --init=IndInit --length=1 --inv=IndInv`   *)
(* then proves IndInv /\ Next => IndInv'.                                  *)
(***************************************************************************)
EXTENDS CoreInd, Apalache

\* A sequence of length l <= MaxLen read off a function on 1..MaxLen.
\* @type: (Int -> Int, Int) => Seq(Int);
SeqOf(f, l) == SubSeq(FunAsSeq(f, MaxLen, MaxLen), 1, l)

Cfgs == [ver : 1..MaxVer, prim : Nodes, elig : SUBSET Nodes]

TypeInit ==
    /\ \E L \in [Nodes -> 0..MaxLen], V \in [Nodes -> [1..MaxLen -> 0..MaxVer]] :
          log = [n \in Nodes |-> SeqOf(V[n], L[n])]
    /\ \E l \in 0..MaxLen, v \in [1..MaxLen -> 0..MaxVer] : hist = SeqOf(v, l)
    /\ cfg    \in Cfgs
    /\ known  \in [Nodes -> Cfgs]
    /\ sync   \in [Nodes -> SUBSET Nodes]
    /\ acked  \in [Nodes -> [Nodes -> 0..MaxLen]]
    /\ commit \in [Nodes -> 0..MaxLen]
    /\ recon  \in [Nodes -> 0..MaxLen]
    /\ term   \in [Nodes -> 0..MaxVer]

IndInit == TypeInit /\ IndInv

\* Sanity (must be violated, so IndInit is not vacuous): states with a
\* deposed primary in each of the two modes exist in IndInit.
NoStaleUnrec == ~\E q \in Nodes : Stale(q) /\ Unrec(q) /\ ~Rec(q)
NoStaleRec   == ~\E q \in Nodes : Stale(q) /\ Rec(q) /\ ~Unrec(q)
NoTwoStale   == ~\E q1, q2 \in Nodes : q1 # q2 /\ Stale(q1) /\ Stale(q2) /\ Len(hist) > 0



\* Ablation: IndInv without one lemma (is that lemma load-bearing?).
Without_LemCfg == TypeB /\ LemSync /\ LemCount /\ LemAck /\ LemFollowElig /\ LemStale /\ LemHist /\ C!EligibleHoldsCommitted /\ C!CommittedAgree
Init_LemCfg == TypeInit /\ Without_LemCfg
Without_LemSync == TypeB /\ LemCfg /\ LemCount /\ LemAck /\ LemFollowElig /\ LemStale /\ LemHist /\ C!EligibleHoldsCommitted /\ C!CommittedAgree
Init_LemSync == TypeInit /\ Without_LemSync
Without_LemCount == TypeB /\ LemCfg /\ LemSync /\ LemAck /\ LemFollowElig /\ LemStale /\ LemHist /\ C!EligibleHoldsCommitted /\ C!CommittedAgree
Init_LemCount == TypeInit /\ Without_LemCount
Without_LemAck == TypeB /\ LemCfg /\ LemSync /\ LemCount /\ LemFollowElig /\ LemStale /\ LemHist /\ C!EligibleHoldsCommitted /\ C!CommittedAgree
Init_LemAck == TypeInit /\ Without_LemAck
Without_LemFollowElig == TypeB /\ LemCfg /\ LemSync /\ LemCount /\ LemAck /\ LemStale /\ LemHist /\ C!EligibleHoldsCommitted /\ C!CommittedAgree
Init_LemFollowElig == TypeInit /\ Without_LemFollowElig
Without_LemStale == TypeB /\ LemCfg /\ LemSync /\ LemCount /\ LemAck /\ LemFollowElig /\ LemHist /\ C!EligibleHoldsCommitted /\ C!CommittedAgree
Init_LemStale == TypeInit /\ Without_LemStale
Without_LemHist == TypeB /\ LemCfg /\ LemSync /\ LemCount /\ LemAck /\ LemFollowElig /\ LemStale /\ C!EligibleHoldsCommitted /\ C!CommittedAgree
Init_LemHist == TypeInit /\ Without_LemHist

\* Proof obligations:
\*  (a) check --init=Init    --length=0 --inv=IndInv
\*  (b) check --init=IndInit --length=1 --inv=IndInv
\*  (c) check --init=IndInit --length=0 --inv=Safety
=============================================================================
