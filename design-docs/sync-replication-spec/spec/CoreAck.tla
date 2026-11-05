------------------------------ MODULE CoreAck ------------------------------
(***************************************************************************)
(* Core.tla plus client replies: is an acknowledged write ever lost?      *)
(*                                                                         *)
(* Core's actions are reused unchanged (EXTENDS Core). Only AppendWrite    *)
(* is wrapped: when primary p appends, it records a held reply            *)
(* [n |-> p, o |-> new length, t |-> term[p]]. In Core a log entry is the  *)
(* term of the primary that appended it, so the value written at offset o *)
(* is term[p]; the pair <<o, term>> identifies the write, because a        *)
(* primaryship writes each offset once and never truncates its own log.   *)
(*                                                                         *)
(*   Release(h)  OK: commit[p] >= o and, per the F2 fix, p still believes *)
(*               it is primary (ThinksPrim) with the same term as the tag. *)
(*   Abort(h)    UNCOMMITTED: once the primaryship that set the boundary  *)
(*               has ended (optional, may fire late).                      *)
(*                                                                         *)
(* Ghost okd: the acknowledged <<offset, value>> pairs.                    *)
(*                                                                         *)
(* AckedDurable: every acknowledged <<o, v>> is in the committed history,  *)
(*   hist[o] = v. hist only grows, so the write is never lost.             *)
(* AckedHeld: the primary and every eligible replica hold every            *)
(*   acknowledged write at its offset (follows from AckedDurable and       *)
(*   EligibleHoldsCommitted).                                              *)
(*                                                                         *)
(* F8: there is NO lease and NO "cfg.prim = p" fence on Commit or Release. *)
(* A deposed primary (ThinksPrim(p) with a stale config) may still commit  *)
(* and release OK (Reach_DeposedAck shows it happens). AckedDurable holds  *)
(* anyway, because Core's CommittedAgree covers deposed primaries: a       *)
(* deposed primary can only commit through a sync replica that no longer  *)
(* follows it, whose acked prefix the new primary holds (Wit in the Lean   *)
(* proof).                                                                 *)
(*                                                                         *)
(* Out of scope:                                                           *)
(*   - forced failover (F7): an operator CAS to an ineligible node, whose  *)
(*     losses the doc accepts; the F8 loss trace (Shard_f_noFence) needs   *)
(*     it.                                                                 *)
(*   - lossy or correlated events: crashes that lose a log, restarts with  *)
(*     empty state, disk loss.                                             *)
(* min-sync-replicas > 0 is not needed: Core uses MinSync = 0, so a        *)
(* primary with an empty sync set commits alone. That is safe here because *)
(* no action destroys the log of the primary or of an eligible replica:    *)
(* the only truncation (Resync) needs an ineligible, uncounted replica.    *)
(* min-sync > 0 protects against losing the only copy, which needs a lossy *)
(* event.                                                                  *)
(*                                                                         *)
(* Bug switches (must fail):                                               *)
(*   NoReplyFence = TRUE   F2 bug: release on commit[p] >= o alone.        *)
(*   ReconcileFirst = FALSE  F1 bug (Core switch).                         *)
(***************************************************************************)
EXTENDS Core

CONSTANT NoReplyFence

VARIABLES held, okd

avars == <<vars, held, okd>>

AInit == Init /\ held = {} /\ okd = {}

Write(p) ==
    /\ AppendWrite(p)
    /\ held' = held \cup {[n |-> p, o |-> Len(log[p]) + 1, t |-> term[p]]}
    /\ UNCHANGED okd

Fenced(h) == ThinksPrim(h.n) /\ term[h.n] = h.t

Release(h) ==
    /\ h \in held /\ commit[h.n] >= h.o
    /\ NoReplyFence \/ Fenced(h)
    /\ okd'  = okd \cup {<<h.o, h.t>>}
    /\ held' = held \ {h}
    /\ UNCHANGED vars

Abort(h) ==
    /\ h \in held /\ ~Fenced(h)
    /\ held' = held \ {h}
    /\ UNCHANGED <<vars, okd>>

Keep == UNCHANGED <<held, okd>>

\* Core's other actions, unchanged (one name each, for TLC coverage).
CReplicate(n) == Replicate(n) /\ Keep
CAck(n) == Ack(n) /\ Keep
CCommit(n) == Commit(n) /\ Keep
CLearn(n) == Learn(n) /\ Keep
CTakeover(n) == Takeover(n) /\ Keep
CResync(n) == Resync(n) /\ Keep
CCount(p, r) == Count(p, r) /\ Keep
CMakeEligible(p, r) == MakeEligible(p, r) /\ Keep
CMakeIneligible(p, r) == MakeIneligible(p, r) /\ Keep
CEarlyUncount(p, r) == EarlyUncount(p, r) /\ Keep

ReleaseSome == \E h \in held : Release(h)
AbortSome == \E h \in held : Abort(h)

ANext ==
    \/ \E n \in Nodes : Write(n) \/ CReplicate(n) \/ CAck(n) \/ CCommit(n)
                        \/ CLearn(n) \/ CTakeover(n) \/ CResync(n)
    \/ \E p, r \in Nodes : CCount(p, r) \/ CMakeEligible(p, r)
                           \/ CMakeIneligible(p, r) \/ CEarlyUncount(p, r)
    \/ ReleaseSome \/ AbortSome

ASpec == AInit /\ [][ANext]_avars

---------------------------------------------------------------------------

AckedDurable == \A a \in okd : Len(hist) >= a[1] /\ hist[a[1]] = a[2]

AckedHeld ==
    \A a \in okd : \A n \in cfg.elig \cup {cfg.prim} :
        Len(log[n]) >= a[1] /\ log[n][a[1]] = a[2]

\* The Lean proof's held-reply invariant.
HeldInv ==
    \A h \in held :
        /\ h.t <= cfg.ver
        /\ Fenced(h) => h.o >= 1 /\ Len(log[h.n]) >= h.o /\ log[h.n][h.o] = h.t

TermLe == \A n \in Nodes : term[n] <= cfg.ver

\* Reachability (must be violated).
Reach_Ack == okd = {}
\* A deposed primary (stale config) may release OK right now: the step the
\* F8 fix forbids.
Reach_DeposedAck ==
    ~(\E h \in held : Fenced(h) /\ known[h.n].ver < cfg.ver /\ commit[h.n] >= h.o)
\* A deposed primary may advance its committed offset right now.
Reach_DeposedCommit ==
    ~(\E p \in Nodes : ThinksPrim(p) /\ known[p].ver < cfg.ver
                      /\ commit[p] < Len(log[p]) /\ commit[p] < CommitCap(p))
=============================================================================
