# Iteration 3A: an inductive invariant for Core, checked with Apalache

## What is proven

For `Core.tla` with `ReconcileFirst = TRUE, EarlyDrop = FALSE`, Apalache 0.62.4
proves the three obligations

- (a) `Init => IndInv`
- (b) `IndInv /\ Next => IndInv'`
- (c) `IndInv => Safety` (`Safety` is `EligibleHoldsCommitted /\ CommittedAgree`)

for these fixed parameters:

| Nodes | MaxLen | MaxVer | (a) | (b) | (c) |
|---|---|---|---|---|---|
| 3 | 2 | 6 | 5 s | 160 s | 10 s |
| 3 | 3 | 7 | 6 s | 166 s | 9 s |
| 3 | 4 | 10 | 7 s | 185 s | 10 s |
| 4 | 2 | 6 | 8 s | 826 s | 11 s |

Times are wall clock, including about 3 s of container and JVM start.

So `Safety` holds in every reachable state, for behaviours of **any length**,
for each parameter set in the table. TLC covers only what it enumerates: for
`Core_safe` that is 1,153,352 states at depth 40. The proof is not
parameterised. `MaxLen` bounds the log length and `MaxVer` bounds the number
of config changes. Both bound the state, not the behaviour: `Replicate`, `Ack`,
`Commit`, `Learn`, `Resync` and `Count` steps can still repeat without end.
Generalising to any N, MaxLen and MaxVer is the Lean workstream's job. Nothing
in `IndInv` depends on the numbers. (b) is a satisfiability check over the
bounded type in `TypeB` (`IndInit` = arbitrary `TypeB` state with `IndInv`),
and `IndInv'` includes `TypeB`, so successor states stay in that space.

Core's actions are not restated. `CoreInd.tla` declares typed variables and
runs Core through `C == INSTANCE Core WITH Nodes <- Nodes, InitPrim <- "n1"`.
`Init`, `Next` and `Safety` are `C!Init`, `C!Next` and `C!Safety`. Nodes are
strings, not TLC model values, which is equivalent up to renaming. Core
needed no change for Apalache. `CommitCap` uses `CHOOSE`, which Apalache
accepts; the chosen value (the minimum) is unique, so its CHOOSE semantics
are exact here.

**Non-vacuity.** `IndInit` is satisfiable, and it contains states with a
deposed primary in each mode, and states with two deposed primaries and a
non-empty history: `NoStaleUnrec`, `NoStaleRec` and `NoTwoStale` are each
violated at `--length=0`. TLC confirms that `IndInv` holds on all 1,153,352
reachable states of `Core_safe` (16 s), so it is not stronger than the
protocol.

**Dependence on the fixes.** With `ReconcileFirst = FALSE` (F1) or
`EarlyDrop = TRUE` (O2 broken), `IndInv` is neither inductive (Apalache gives
a CTI) nor an invariant (TLC violates it at depth 9 and depth 4, before
`Safety` itself fails at depth 12 and depth 6):

- noRec: the CTI is a `Commit`. With `Reconciled` always true, `LemHist`
  demands `Len(hist) <= commit[P]` immediately after a takeover, when
  `commit = 0`. The deeper break is that `Count` and `MakeEligible` stop
  implying that the primary has committed its inherited log. That
  implication is exactly what turns a deposed primary from `Unrec` into
  `Rec` (see L6 below).
- earlyDrop: the CTI is an `EarlyUncount` that breaks `elig \subseteq sync[P]`.

## The inductive invariant

Defined in `spec/CoreInd.tla`. Notation: `P == cfg.prim`,
`H == cfg.elig \cup {P}` (the nodes Safety talks about),
`Stale(q) == known[q].prim = q /\ q # P` (a deposed primary that has not
learned it), `Follows(r, q) == known[r].prim = q`, and
`Agree(q, h, k)` (the first k entries of log[q] and log[h] exist and are
equal).

```
IndInv == TypeB /\ LemCfg /\ LemSync /\ LemCount /\ LemAck
          /\ LemFollowElig /\ LemStale /\ LemHist
          /\ EligibleHoldsCommitted /\ CommittedAgree
```

- `TypeB`: bounded type. Logs and hist have at most MaxLen entries in
  0..MaxVer; versions in 1..MaxVer; acked, commit and recon in 0..MaxLen;
  term in 0..MaxVer.
- `LemCfg` (L1): `known[n].ver <= cfg.ver`; a node that knows the latest
  version knows the latest config; `known[P] = cfg`; `P \notin cfg.elig`.
- `LemSync` (L2): `n \notin sync[n]`.
- `LemCount` (L3, O1/O2 and F1): `cfg.elig \subseteq sync[P]`. Every
  `r \in sync[P] \ cfg.elig` follows P, and P is `Reconciled`.
- `LemAck` (L4): for all r, `Agree(P, r, acked[P][r])`;
  `acked[P][r] > 0 => Follows(r, P)`; and
  `r \in sync[P] => commit[P] <= acked[P][r]`.
- `LemFollowElig` (L5): `r \in cfg.elig => r \in known[known[r].prim].elig`.
  An eligible node that follows a deposed primary was eligible in that
  primary's last config, so the deposed primary cannot resync it.
- `LemStale` (L6), the core lemma: a deposed primary q is not eligible, and
  either
  - `Unrec(q)`: every holder h is in `sync[q]` with
    `Agree(q, h, acked[q][h])`, and `acked[q][P] <= recon[P]`. No promotion
    has happened since q was deposed, so its commit cap is held by all of H.
  - `Rec(q)`: some `s \in sync[q]` no longer follows q, and q's first
    `acked[q][s]` entries are a prefix of hist. q's commit cap is frozen at
    s and already committed.

  The step from Unrec to Rec is where F1 matters. A promotion (`Count`)
  needs `Reconciled(P)`. Then `acked[q][P] <= recon[P] <= commit[P]`, so by
  `CommittedAgree` q's frozen prefix is in hist.
- `LemHist` (L7): `Len(hist) <= IF Reconciled(P) THEN commit[P] ELSE recon[P]`.

**Ablation.** Each of the 7 lemmas is load-bearing: dropping any one makes
(b) fail (`Without_<Lem>` in `CoreApalache.tla`, all violated). Two lemmas
from an earlier draft turned out redundant and were removed:
`recon[P] <= Len(log[P])`, and a bound on the primary's term.

## Reproduce

From `spec/`. Each run writes `apalache/<name>.out` and appends a verdict
line to `apalache/results.txt`. Every counterexample
Apalache found is kept as `apalache/cti_<run>.tla`; the two CTIs from
building the invariant are `cti_b_step1.tla` and `cti_b_step2.tla`.

```
apalache/run.sh a apalache/CoreInd_safe.cfg --init=Init    --length=0 --inv=IndInv
apalache/run.sh b apalache/CoreInd_safe.cfg --init=IndInit --length=1 --inv=IndInv
apalache/run.sh c apalache/CoreInd_safe.cfg --init=IndInit --length=0 --inv=Safety
# other parameters: CoreInd_big (3/3/7), CoreInd_L4 (3/4/10), CoreInd_n4 (4 nodes)
# bug configs (must fail b): CoreInd_noRec, CoreInd_earlyDrop
# bounded model checking: --init=Init --length=N --inv=Safety
# TLC on reachable states:
java -cp ../tools/tla2tools.jar tlc2.TLC -config apalache/CoreInd_safe.cfg \
     -deadlock -metadir $SCRATCH/md CoreInd.tla
```

## Results

| Check | Config | Result | Wall |
|---|---|---|---|
| (a) Init ⇒ IndInv | safe, big, L4, n4 | holds | 5-8 s |
| (b) inductive step | safe 3/2/6 | holds | 160 s |
| (b) | big 3/3/7 | holds | 166 s |
| (b) | L4 3/4/10 | holds | 185 s |
| (b) | n4 4/2/6 | holds | 826 s |
| (c) IndInv ⇒ Safety | all four | holds | 9-11 s |
| non-vacuity (3 predicates) | safe | violated, as intended | 9-10 s |
| (b) | noRec | CTI (Commit vs LemHist) | 77 s |
| (b) | earlyDrop | CTI (EarlyUncount vs LemCount) | 132 s |
| ablation, 7 lemmas | safe | each CTI | 12-152 s |
| BMC Safety, length 6 | safe | holds | 57 s |
| BMC Safety, length 8 | safe | holds | 1452 s |
| BMC Safety, length 5 | earlyDrop | violated (agrees with TLC) | 17 s |
| BMC Safety, length 11 | noRec | see note | > 1 h |
| TLC IndInv on reachable states | safe | holds, 1,153,352 states | 16 s |
| TLC IndInv on reachable states | noRec / earlyDrop | violated at depth 9 / 4 | < 1 s |

Bounded model checking (BMC) agrees with TLC wherever it finished. Apalache
BMC is much slower than TLC on this model: length 8 took 24 minutes, while
TLC explores the whole state space (depth 40) in 5 s. The noRec violation
needs 11 steps. Apalache BMC at length 11 had reached only step 10 when it
was stopped after about 70 minutes (run `bmc_noRec_11` in
`apalache/results.txt`; the raw logs are not committed), so the F1 violation rests
on TLC plus the noRec CTI above. The inductive check (b) needs only one
step, which is why it stays cheap.

## Metrics (for the TLA+ vs Lean comparison)

- Time: about 1.5 h of work from reading Core.tla to the final proof,
  including roughly 25 minutes writing the hand argument before the first
  Apalache run. About 30 Apalache runs, plus 5 TLC runs.
- IndInv iterations: 3 inductive-step runs (2 CTIs, then pass), and one
  more pass after the 2 redundant conjuncts were removed. Before using
  Apalache, I checked the first draft on TLC reachable states; it passed
  first time.
- Lemmas: 7, plus TypeB and the 2 safety conjuncts (16 atomic conjuncts in
  total).
- Lines of TLA+ added: `CoreInd.tla` 150 (85 non-comment),
  `CoreApalache.tla` 58 (34 non-comment, including ablation). Core.tla is
  unchanged.
- What the tool caught: both CTIs were real gaps in my hand proof, not
  protocol bugs.
  1. A reconciled primary whose commit offset lags hist could promote an
     empty follower. Fix: `LemHist`, history length bounded by the
     primary's commit offset.
  2. The commit offset can exceed the ack of a counted replica. Fix: the
     commit rule keeps `commit[P] <= acked[P][r]` for `r \in sync[P]`.

  Ablation also flagged 2 conjuncts that were not needed.
- Pain points:
  - Apalache rejects `\A i \in 1..Len(s)`, because ranges must have
    constant bounds. I rewrote these as `\A i \in 1..MaxLen : i <= Len(s) => ...`.
  - Arbitrary bounded sequences in `IndInit` need `FunAsSeq` over
    `[1..MaxLen -> ...]` plus `SubSeq`, so `IndInit` lives in a separate
    module that `EXTENDS Apalache`. That keeps `CoreInd.tla` runnable by TLC.
  - Violation reports name invariants by number ("state invariant 25") and
    transitions by index (`_transition(8)` = the 9th disjunct of Next). The
    Skolemised `InvariantViolation` formula was enough to identify the
    failing conjunct. Both CTIs were small and readable.
  - BMC is slow on this model, so it is no substitute for TLC as a quick
    bug finder.
  - Type annotations were easy: INSTANCE with re-declared, annotated
    variables meant Core needed none. `CHOOSE` and records worked as written.

## Assessment

The safety property of the membership core (`EligibleHoldsCommitted`,
`CommittedAgree`) is proven inductively for 3 nodes with up to 4 log entries
and 10 config versions, and for 4 nodes with 2 entries and 6 versions. The
proof covers unbounded behaviours. It does not cover unbounded parameters.
The invariant explains why the protocol is safe:

- Eligibility implies counting (O1/O2).
- The primary's acks are sound.
- A deposed primary can extend the history only within what every current
  holder has (Unrec), until the new primary reconciles. After that, its cap
  is frozen inside the history (Rec).
- Reconcile-first (F1) is what makes the step from Unrec to Rec happen
  before any promotion.

No CTI suggested a real protocol bug in the safe configuration. Both CTIs
were missing lemmas, and the final IndInv holds on every TLC-reachable
state.
