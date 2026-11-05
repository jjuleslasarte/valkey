# TLC vs Apalache vs Lean on the same model

The question was whether Lean or TLA+ is the better tool here, and why. We
answered it by doing the same job three ways on `spec/Core.tla`. That model
is the membership core of the protocol: logs, the Cluster V2 config, the
commit rule, the promotion and demotion ordering rules, takeover with
reconciliation (the F1 fix), and resync. The property is the core PacificA
claim: the primary and every eligible replica hold the committed history,
and no node commits a different entry.

Every result below was re-run independently after the worker that produced
it reported.

## What each tool established

| | TLC (explicit-state) | Apalache (inductive invariant) | Lean 4 (proof) |
|---|---|---|---|
| Claim | Safety holds in every reachable state | Safety holds in every reachable state, for behaviours of **any length** | Safety holds in every reachable state |
| Nodes | 3 | 3 or 4, fixed | **any number** (any type with decidable equality) |
| Log length / config versions | ≤ 2 / ≤ 6 (≤ 3 / ≤ 7 in the large config) | ≤ 2–4 / ≤ 6–10, fixed per run | **unbounded** |
| Kind of result | Exhaustive search of a finite state space | Proof by SMT, for the bounded type | Machine-checked proof; only the standard axioms `propext`, `Quot.sound` and `Classical.choice` |
| Shows the F1 fix is needed | Counterexample trace (seconds) | Inductive step fails without it | Hand-written 11-step counterexample, checked by `decide` |

The three are now tied together mechanically. On the full TLC state graph of
`Core_xcheck.cfg` (45,284 states, 146,532 transitions), Lean checked the
following, using a step checker proven sound:
- every TLC transition is a Lean step with the same action;
- every Lean successor within the bounds is a TLC transition;
- the initial states are equal;
- every TLC state satisfies the Lean invariant.

There were 0 mismatches (`lean/XCheck`, 6 s). The Apalache invariant was also
confirmed by TLC on all 1,153,352 reachable states of `Core_safe`.

## What it cost

| | TLC | Apalache | Lean |
|---|---|---|---|
| Lines added for this model | `Core.tla` 197 | +208 (`CoreInd.tla`, `CoreApalache.tla`) | 1,421 (962 of them per-action preservation proofs) |
| Wall time | minutes | about 1.5 h, about 30 runs | about 20 min (worker), after deriving the invariant by hand |
| Invariant iterations | none needed | 3 attempts; 2 counterexamples to induction | 0 revisions, about 10 tactic-fix rounds |
| Check time | 5 s (`Core_safe`) to minutes | inductive step 2–3 min (3 nodes), 14 min (4 nodes) | clean build about 6 s |
| Bounded search speed | 1.15M states in seconds | 8-step bounded run took 24 min; the 11-step F1 run gave no verdict in 70 min | n/a |

The low Lean wall time is misleading if read alone. The invariant was
worked out by hand first, and Apalache had needed three iterations to find
essentially the same invariant. Lean gives no trace when an invariant is
wrong, only an unprovable goal, so a weak first guess costs far more there.

## What each tool is good at here

- **TLC** is for exploring the design. When a rule changes it gives an
  answer in seconds to minutes, and a readable trace when something
  breaks. Every finding (F1–F11) came from TLC. Its limit is the bound: it
  can only say "true up to 3 nodes and 2 writes", and the state space grows
  past what this host can hold (`Shard_m_safeCfg7` was stopped at 326M
  states).
- **Apalache** gives an inductive invariant without leaving TLA+. The proof
  is for all behaviour lengths, but only for a fixed type size. Its
  counterexamples to induction are what drive the invariant search.
  Drawbacks: bounded checking is far slower than TLC, there are syntax
  restrictions (range bounds must be constants, sequences have to be built
  with `FunAsSeq`), and violations are reported by number.
- **Lean** is the only one that removes the bounds: any number of nodes,
  any log length, any durations. It also shows exactly which guards the
  argument uses. The core proof never needed Resync's prefix check, the
  "not yet counted" checks, Replicate's prefix check, or the term values in
  the logs. Reconciliation mattered only before promotion. The lease proofs
  turned the drift rule into an exact condition and found that the doc's
  lease-duration rule leaves out the round-trip time (F12). The cost is
  that proofs are tied to the model: changing one action means re-proving
  that action's preservation obligations.

## Recommendation

Use them in layers, not one instead of another:

1. **TLC is the working tool.** Keep it for every model and every design
   change, with the regression and coverage gates. It is what finds bugs.
2. **Apalache is optional.** It is worth using when you want an inductive
   invariant without leaving TLA+, for example as the bridge to a Lean
   proof. For this project, Lean made it largely redundant once the
   invariant was known.
3. **Lean is for a few central claims, once the design is stable.** Use it
   where unbounded parameters matter: the core membership invariant (done),
   the lease timing conditions (done), and next the client-visible
   guarantee that an acknowledged write is never lost, with F2 reply
   fencing and min-sync-replicas > 0. Do that after the design doc
   settles F1, F2, F7 and F8.
4. **Keep the models linked.** The TLC-Lean cross-check is cheap, at 6 s
   after a one-off converter. It is what makes a Lean proof about "the same
   protocol" checkable rather than a claim. Re-run it whenever either side
   changes.

So: TLA+ (with TLC) for the design, Lean for the proof. Neither replaces the
other.
