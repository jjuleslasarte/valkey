----------------------------- MODULE ShardCommon -----------------------------
(***************************************************************************)
(* Operators shared by every module of the Valkey sync replication spec.   *)
(* Pure operators only: no constants, no variables. Modules EXTEND it.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

Min2(a, b) == IF a <= b THEN a ELSE b
Max2(a, b) == IF a >= b THEN a ELSE b

\* Smallest / largest element of a non-empty finite set of numbers.
SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y
SetMax(S) == CHOOSE x \in S : \A y \in S : x >= y

\* s is a prefix of t.
IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

\* Length of the longest common prefix of s and t.
LCP(s, t) ==
    LET cs == {i \in 0..Min2(Len(s), Len(t)) : SubSeq(s, 1, i) = SubSeq(t, 1, i)}
    IN  SetMax(cs)

\* Index of the last element of s[1..n] satisfying P, or 0 if none.
LastIdxWhere(s, n, P(_)) ==
    LET idx == {i \in 1..n : P(s[i])}
    IN  IF idx = {} THEN 0 ELSE SetMax(idx)
=============================================================================
