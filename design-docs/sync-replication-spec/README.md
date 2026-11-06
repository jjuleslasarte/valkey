# Acknowledged writes survive failover and restarts: a Lean proof for Valkey synchronous replication

Lean 4 proofs for the synchronous replication design in
[`design-docs/sync-replication.md`](../sync-replication.md), proposed in
[valkey#5286](https://github.com/valkey-io/valkey/pull/5286).

Readers new to machine-checked proofs: [Appendix A](#appendix-a-reading-a-lean-proof)
explains what "proven" means here, what it does not mean, and the vocabulary used
below. [Appendix B](#appendix-b-issues-found-through-modelling) lists the issues the
modelling found in the design as written, with the run that fails without each fix.
[Appendix C](#appendix-c-the-tla-models-and-what-they-add) describes the TLA+ models
these proofs grew out of and the few results that rest on them alone. Below, "design
§N" refers to a section of the design doc.

## Summary

The design promises that acknowledged writes "survive as long as the primary or at
least one eligible sync replica survives" (Consistency and Durability Properties). We
prove this in Lean 4 for a model of the commit protocol, the Cluster V2 shard
configuration, failover and node restarts. The proof holds for any number of nodes,
any log length, any number of configuration changes and restarts, and every value of
`min-sync-replicas`.

The model is the design with the rules the guarantee needs. Five of those rules are
not in the design doc as currently written: reconciliation against the inherited log,
the reply fence, the rebuilt sync replica set after a restart, the incarnation check
on primaryship, and the incarnation rule for a restart from a stale persistence file.
This document describes the design with them in place; Appendix B lists each one with
the Lean run that loses a write without it, and the rule as it should read.

Separately, we prove the lease timing rules: exactly which clock-drift margin makes
the two leases safe, and a sufficient condition for the "Lease durations" rule.

The proof is about safety of the replication log. It does not cover reads, leases on
the failover path, forced failover, or liveness (that a held reply is ever released).
Section 5 lists every exclusion and every assumption that is stronger than the
design. Reads are the natural next step: the design's read guarantee needs the lease
protocol in the model and a linearizability property to prove against.

Every theorem is checked by Lean's kernel. There is no `sorry`, and the only axioms
are Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`).

## 1. The protocol as modelled

The model is `lean/SyncReplication/Model.lean`. It follows the design's terms (design
§2, §4, §5, §6).

- **Roles.** A shard has a **primary**, **eligible** replicas (sync replicas that are
  fully caught up and may be promoted) and **ineligible** replicas (async replicas and
  replicas still catching up).
- **Incarnation ID.** One lifetime of a node's data. A node takes a new incarnation
  when it restarts without its data. The shard configuration records an incarnation
  for every node, so a node that lost its data can be told apart from the node that
  earned eligibility or primaryship.
- **Shard configuration.** Cluster V2 stores the primary, the eligible set and the
  incarnation recorded for each node. Every change increments the
  configuration version. We assume the Cluster V2 implementation is correct and treat
  the configuration as a compare-and-set register: one totally ordered sequence of
  versions, each change a compare-and-set on the previous one (design §6). Each node
  also keeps the configuration it last learned, which may be stale.
- **Replication.** A replica receives its primary's replication stream, applies the
  entries in log order, and sends `REPLCONF ACK` with its replication offset.
- **Commit rule.** The primary's **committed offset** advances only past entries every
  member of its **sync replica set** has acknowledged, and only while at least
  `min-sync-replicas` of those members are eligible with a matching incarnation. Only a
  primary advances its committed offset; `REPLCONF COMMIT` and replicas' committed
  offsets are not modelled (they matter for reads, which are out of scope).
- **Promotion flow.** The primary first counts a caught-up replica's acknowledgements
  (design §4, step 2), then commits the replica as eligible to the cluster bus (step
  4). A
  replica is caught up when it follows the primary and has acknowledged up to the
  primary's catch-up point: the committed offset, or, for a primary that has not yet
  committed the log it holds (a new primary, or one that restarted with its data),
  the end of that log.
- **Demotion flow.** The primary commits the replica as ineligible and stops counting
  it, in one step.
- **Failover.** An eligible replica that knows the latest configuration takes over
  through the takeover compare-and-set, which checks that its incarnation matches the
  one recorded for it, and becomes the **current primary**: the one named in the
  latest configuration. The new configuration drops the old primary from the eligible
  set. The new primary starts with the eligible replicas
  with matching incarnations as its sync replica set, with no acknowledgements and
  committed offset 0, and writes with a new term. It first commits the log it
  inherited; until then it serves no writes and measures promotion catch-up and full
  resync (below) against the end of that log. The old primary is not stopped: it may keep
  acting on its stale configuration until it learns the new one, at which point it
  drops its sync replica set. A node acts as primary only while its configuration
  records its current incarnation.
- **Full resync.** A replica whose log has diverged from its primary's is replaced by
  the primary's log up to the catch-up point. This happens only after the replica is
  out of the sync replica set and ineligible. While a new primary is still committing
  its inherited log, the catch-up point is the end of that log, so a resync then
  copies inherited entries that are not yet committed.
- **Reply blocking.** A write's reply is held until it commits. Each held reply
  carries the term of the primaryship that accepted the write. The reply is released
  as OK only while the node that accepted it still considers itself primary, in that
  term; otherwise it is answered `UNCOMMITTED` (design §5, "Write behavior during
  faults"). We call this check the **reply fence**. It is the node's own view, which
  may be stale; a deposed primary that has not learned of the takeover passes it, and
  is kept safe by the commit rule instead.
- **Restarts.** A node may restart with its data, without it, or from a stale
  persistence file holding only a prefix of its log. A restart without data gives the
  node a new incarnation. It stays in the eligible set with a stale recorded
  incarnation, so it is neither counted nor promotable; once the primary demotes it,
  it can become eligible again only through the promotion flow (design §6). A restart
  from a stale file keeps the incarnation only if the file covers the node's
  acknowledgement high-water mark (`ackHigh`): the highest offset it has
  acknowledged, as a replica to its primary or as a primary to its clients.
  Otherwise it takes a new incarnation as after a restart without data, keeping the
  entries it has as a starting point for resynchronisation. A primary that restarts
  with its data rebuilds its
  sync replica set from the configuration it knows. Volatile state is lost in every
  case: the committed offset, the sync replica set, the acknowledgements, and the
  client connections with their held replies.

Messages are not modelled as separate objects. A replica reads its primary's log
directly, and an acknowledgement updates the primary's view directly, with the
replica's offset at that moment. A delayed message corresponds to the same step
taken later, and a lost connection corresponds to the step never being taken. This
assumes that a message is never delivered after the connection that carried it has
been closed by a full resync or a restart: an acknowledgement sent before a resync
cannot arrive after it. Steps interleave arbitrarily, so any order of events across
nodes is covered.

Each log entry records the **term** of the primary that wrote it: the version of the
shard configuration that made it primary. A write is identified by its offset and
term. This is what lets the model tell apart two primaries that wrote different data
at the same offset.

## 2. The guarantee

The statement uses two definitions.

- A node is **authoritative** if, in the latest shard configuration, it is the
  primary or an eligible replica, and the incarnation recorded for it is its current
  one. The distinction from *eligible* matters because the configuration can list a
  node as eligible after it has lost its data: a node that restarts empty stays in the
  eligible set until the primary demotes it, and in the meantime it holds nothing. No
  guarantee about its data can hold, and the design does not rely on it: it changes
  the node's incarnation so that the recorded one no longer matches, and the takeover
  compare-and-set checks exactly that. *Authoritative* is this check written out.
- The **committed history** is the sequence of entries committed so far: each entry is
  the one at that offset on the first node to commit the offset. It is the yardstick
  the properties are measured against. Without it, "no committed write is lost" would
  have to be stated as a relation between every pair of nodes' committed prefixes;
  with it, each property compares one node to the one history. No node stores it and
  no action reads it, so it changes no behaviour: a *ghost variable*, added for the
  proof only.

**Survival condition.** Whenever a node takes a new incarnation (a restart without
data, or from a stale file), some other authoritative node keeps its data. This is the design's "as long as the primary or at
least one eligible sync replica survives", required at each restart.

Under the survival condition, every reachable state satisfies:

| | Property | Lean theorem |
|---|---|---|
| **1** | **EligibleHoldsCommitted:** every authoritative node holds the whole committed history. | `SyncReplication.safety` |
| **2** | **CommittedAgree:** every node's committed prefix is a prefix of the committed history. In particular, no two nodes commit different entries at the same offset. | `SyncReplication.safety` |
| **3** | **AckedDurable:** every write released as OK is in the committed history, at its offset. | `SyncReplication.ackSafety` |
| **4** | **AckedHeld:** every authoritative node holds every write released as OK, at its offset. | `SyncReplication.ackedHeld` |
| **5** | With `min-sync-replicas ≥ 1`, when the current primary commits, the committed history is on at least two distinct authoritative nodes: the primary and an eligible sync replica. | `SyncReplication.commit_two_copies` |

The committed history only grows, so property 3 says that no acknowledged write is
ever lost or replaced. Property 1 establishes the data half of the design's failover
argument, "any eligible replica is safe to promote, because each one holds every
committed write" (design §5, fault detection); the other half, that the promoted
replica then reconciles before serving, is the reconciliation rule in section 1.

With `min-sync-replicas = 0` the primary may commit with an empty sync replica set.
The history may then be on the primary only, which matches the design's note that
such writes "exist only on the primary"; their durability is the primary's own, and
the survival condition then forbids the primary restarting empty, because no other
node is authoritative. So the design's accepted loss in that case, a primary with no
sync replicas coming back empty, is outside the model, and the theorems say nothing
about it. Property 5 is what `min-sync-replicas ≥ 1` adds.

## 3. Method

### 3.1 The inductive invariant

The proof is by induction over executions. We define a predicate `Invariant` on
states and show that it holds initially, that every step preserves it, and that it
implies properties 1 and 2. `Invariant` has 23 parts, grouped in five layers that
follow the design: configuration, replication, membership, commit and failover. Each
layer is stated in terms of the ones before it. The names are the field names in
`Invariant.lean`, where each has a docstring citing the design.

**Configuration** (`ConfigInvariant`, design §6). Cluster V2 holds one totally
ordered configuration; each node's copy may be behind it but never ahead.
- `knownLe`: no node has seen a configuration newer than the latest.
- `knownEq`: a node that has seen the latest version has the latest configuration.
- `primKnows`: the current primary knows the configuration that made it primary.
- `incLe`: a recorded incarnation is never newer than the node's own, so a node that
  came back empty never matches its old record.
- `knownIncLe`: the same for every node's copy of the configuration.

**Replication** (`ReplInvariant`, design §2). Acknowledgements are real.
- `noSelfSync`: a node is never in its own sync replica set.
- `ackedPrim`: the current primary has no acknowledgement recorded from a node that
  follows a different primary.
- `ackedLe`: a recorded acknowledgement is within the primary's own log.
- `ackHolds`: a follower holds its primary's log up to the acknowledged offset.
- `ackedHigh`: what a primary believes a replica acknowledged, the replica remembers
  having acknowledged (`ackHigh`).
- `syncCommit`: the commit rule, a primary never commits past a sync replica's
  acknowledgement.

**Membership** (`MembershipInvariant`, design §4). The ordering rules of promotion
and demotion.
- `eligSync`: every eligible replica with a matching incarnation is counted ("must
  count toward commits before it becomes eligible"). A restarted primary rebuilds its
  sync replica set so that this survives the restart.
- `syncNew`: a replica the current primary counts but has not made eligible follows
  it and has acknowledged at least the catch-up point.
- `eligFol`: an eligible replica that follows an old primary is still eligible in that
  primary's configuration. This is why a full resync never truncates an eligible
  replica.

**Commit** (`CommitInvariant`, design §2 and §5). Committed prefixes agree with the
committed history.
- `caLen`, `caHist`: a committed offset is within the node's log and within the
  history.
- `caEq`: what a node has committed is exactly the start of the history.
- `reconLen`: the current primary's catch-up point is within its log.
- `histLe`: while the current primary is authoritative, the whole history is below
  its committed offset or its catch-up point, so a new primary reconciles against all
  of it.
- `histAck`: every authoritative node has acknowledged the whole history. This is
  what makes a restart from a stale file safe when the file covers `ackHigh`.

**Failover** (`FailoverInvariant`, design §5, "Writes can't split-brain").
- `stale`: a node that still thinks it is primary under an old configuration is
  **fenced** (this is the log fence of a deposed primary, a different thing from the
  reply fence of section 1). Some members of its sync replica set have left it for a
  newer primary, so their acknowledgements are frozen; the smallest of them is its
  *fence*, and by
  the commit rule it can never commit past it. The current primary holds, and has
  acknowledged, the deposed primary's log up to the fence; every eligible replica
  either does the same or still follows the deposed primary. So a deposed primary may
  still commit, but only entries the new configuration already holds.
- `authEx`: some node is authoritative. The survival condition keeps this true.

**Goal.**
- `ehc`: EligibleHoldsCommitted itself, over authoritative nodes.

Facts about the current primary (`histLe` and the primary clauses of the fence) hold
only while it is authoritative: a primary that came back empty holds nothing, and
nothing new is committed until an authoritative eligible replica takes over.

The acknowledged-write properties (3 and 4) extend `Invariant` with three more parts
(`ReplyInvariant`, `Durability.lean`): terms never exceed the configuration version;
a held reply that passes the reply fence points at the write it was issued for; and
AckedDurable itself. A takeover gives the new primary a term larger than the term of
any held reply, so an old reply can never become releasable again.

### 3.2 Lease timing

The lease proofs (`Lease/`) are independent of the replication model. They model one
lease instance in real time. The holder sends at time `s` and the grantor receives at
`r ≥ s`, with unbounded delay. Clocks are arbitrary functions from real time to local
readings, under two drift models: additive (local elapsed time is within `D` of real
elapsed time) and rate-bounded (drift rate at most `ρ`). The main results:

- **Margin.** If the holder subtracts margin `M` and the grantor does not, the leases
  are safe exactly when `M ≥ 2D`, apart from the degenerate case where the margin is
  the whole lease (`asym_safe_iff`). In the rate model the condition is
  `M ≥ 2ρ·Dur/(1+ρ)` (`rate_asym_safe`, `rate_asym_tight`); its tightness holds up to
  a refinement of the real-time tick, since the overlap window can be shorter than
  one integer tick. If both sides subtract the margin, the leases are unsafe for every
  margin shorter than the lease as soon as there is any drift (`literal_unsafe`).
- **Durations.** `demotion_in_time` gives a sufficient condition for the read lease to
  have expired when a demotion commits: the read lease plus the commit delay, the
  acknowledgement round trip, the margin and two drift terms must be shorter than the
  primary lease. This is an availability property, not a safety one: if it fails the
  primary stops serving reads.

What these say about the design's own wording is in Appendix B.

## 4. Results

| Result | Lean theorem |
|---|---|
| Properties 1 and 2, every `min-sync-replicas`, with restarts | `SyncReplication.safety` |
| Properties 3 and 4 (no acknowledged write lost) | `SyncReplication.ackSafety`, `ackedHeld` |
| Property 5 (two copies with `min-sync-replicas ≥ 1`) | `SyncReplication.commit_two_copies` |
| Lease margin and durations | `Lease/` |
| Each rule in Appendix B is needed | `SyncReplication.noReconcile_unsafe`, `noReplyFence_unsafe`, `noRebuild_unsafe`, `noIncCheck_unsafe`, `noIncWritable_oneCopy`, `staleRestoreKeepsInc_unsafe`, `staleRestoreKeepsInc_loses`, `noSurvivor_loses` |

Size: the model is 535 lines (422 for the protocol, 113 for the held-reply layer),
the invariant and its lemmas 444, the per-action contracts 607, and the preservation
proofs 2,468, so the proof is about six lines per line of model. Lean checks the
whole of `SyncReplication` in about 15 seconds on a laptop-class machine.

[lean/LEAN.md](lean/LEAN.md) has every theorem statement and the details of the
encoding.

## 5. Scope and limitations

### Not modelled

- **Forced failover** (`CLUSTER FAILOVER FORCE`, `TAKEOVER`). The design accepts
  losses when the target is ineligible. Explored in TLA+ only (Appendix C).
- **Reads.** The proofs say nothing about linearizable reads from the primary or
  from sync replicas. Leases appear only in the timing lemmas of `Lease/`, which
  cover one lease instance, not the protocol: in the replication model a takeover
  needs no lease expiry and may pick any eligible replica. Stale reads are checked by
  TLA+ model checking only (Appendix C).
- **Liveness.** Nothing proves that a held reply is ever released, as OK or as
  `UNCOMMITTED`. The model's `UNCOMMITTED` (`abort`) fires only when the primaryship
  that took the write is no longer current. The design's other case, a healthy
  primary whose sync replica set fell below `min-sync-replicas` releasing held writes
  as `UNCOMMITTED`, is not modelled, and neither is the `CLUSTERDOWN` rejection path
  or client retry semantics.
- **Correlated data loss** is excluded by the survival condition. The design's
  detection of it (no eligible replica with a matching incarnation, so the shard
  stays unavailable) is not proven.
- AOF and `appendfsync`; async read replicas beyond being ineligible (in the model
  any follower may replicate uncommitted entries, while the design caps an async
  replica's stream at the committed offset); `target-sync-replicas` and the choice of
  which replica to promote (the model allows any promotion); replication lag
  thresholds; manual failover; slot migration and anything beyond a single shard;
  modules; dirty key tracking.
- **Replica committed offsets.** Only a primary advances its committed offset;
  `REPLCONF COMMIT` is not modelled. Property 2 therefore constrains committed
  offsets a node reached while it was primary.
- **Removing a counted replica before it is eligible.** Design §4 lets the primary
  drop a replica that falls behind between steps 2 and 4 from the commit calculation.
  The model has no such action: a counted replica leaves the sync replica set only by
  demotion, by the primary learning a new configuration or restarting, or by its own
  restart. The model has fewer behaviours here than the design.
- **The Cluster V2 bus is assumed correct** and modelled as a compare-and-set register
  (section 1).
- **Messages are abstracted** (section 1). An acknowledgement carries the replica's
  offset at delivery, so the model assumes no message is delivered after a full
  resync or restart has closed its connection.

### Assumptions stronger than the design

- **The survival condition** is required at every restart that takes a new
  incarnation (section 2).
- **Restarts carry four assumptions the design only implies.** (a) A node restarts
  only when it knows the latest configuration (`KnowsLatest`), justified by design
  §6's "syncs to the latest log before it re-enters the cluster"; a restart with a
  stale configuration is excluded, not proved equivalent. (b) A restart without data
  at once removes the node from the *current* primary's sync replica set and
  acknowledgement table; the design reaches that state only through the demotion flow
  (read-lease wait plus a committed demotion), so the model omits the window in which
  the primary is still waiting for the dead replica. (c) A restart with data forces
  the node to re-commit what it holds before serving (its catch-up point is set to
  the end of its log), and so does a takeover; the design does not specify this. A takeover also starts the new
  primary's sync replica set as the eligible replicas with matching incarnations,
  which the design implies through its ordering rules but does not state. (d) The acknowledgement high-water mark `ackHigh` survives a
  restart with data and is lost with a new incarnation; the model assumes the
  implementation persists it with the data it covers. A stale file is modelled as a
  prefix of the log; a file that is not a prefix (a diverged tail) is not modelled.
- **The incarnation checks** in `ThinksPrimary` and `Writable` are in the model as
  guards. The design states only the takeover compare-and-set. Appendix B shows both
  are needed: the first for safety, the second for the two-copies property.

### What the model is checked against

The Lean model is written by hand from the design. Nothing mechanical checks it
against the design doc itself; sections 1 and 5 are the argument, and reviewing them
is the step that needs a systems engineer (Appendix A.6). The model mirrors a TLA+
model of the same protocol (Appendix C), which was model-checked at small sizes, and
earlier versions of the Lean encoding were checked against that model's complete
state graph; that catches slips in how the Lean was written, not differences between
both models and the design.

"Any number of nodes" means any Lean type of node identifiers, including infinite
ones. `Writable` uses `Set.encard`, which is the usual cardinality on finite sets and
`⊤` on infinite ones. The theorems hold for infinite node types too, but only the
finite case corresponds to a real cluster.

### Future work

Reads: add the lease protocol to the model and prove a no-stale-read property. The
early removal of a counted, not-yet-eligible replica (section 5).

## 6. How the proof is organized in code

| Path | Contents | Lines |
|---|---|---|
| `lean/SyncReplication/Model.lean` | The protocol: state, actions, steps, properties | 422 |
| `lean/SyncReplication/Replies.lean` | Held client replies: the acknowledgement layer, AckedDurable, AckedHeld | 113 |
| `lean/SyncReplication/Invariant.lean` | The invariant in five layers; the fence; frame lemmas | 444 |
| `lean/SyncReplication/Contracts.lean` | Each action's effect in design terms, proved without the invariant | 607 |
| `lean/SyncReplication/Preserve/` | Preservation, one file per subsystem: `Replication`, `Commit`, `Config`, `Failover`, `Restart`; each action proved one layer at a time | 2,468 |
| `lean/SyncReplication/Safety.lean` | `safety`, `commit_two_copies` | 43 |
| `lean/SyncReplication/Durability.lean` | The held-reply invariant; `ackSafety`, `ackedHeld` | 246 |
| `lean/SyncReplication/Counterexamples/` | One file per rule in Appendix B, each in its own weakened step relation | 572 |
| `lean/SyncReplication/Lists.lean` | List-prefix lemmas | 68 |
| `lean/Lease/` | Lease timing (additive and rate clocks, durations) | 377 |
| `lean/Check.lean` | Prints the axioms of every theorem | |

Lean 4.35 with Mathlib `v4.35.0`, used for list-prefix lemmas and for `Set.encard`
in `Writable`, and CSLib for the transition-system vocabulary (Appendix A.8).

**Reading order.** `Model.lean` (the state machine), then `Invariant.lean` (the five
layers; each conjunct's docstring cites the design), then `Contracts.lean` (what each
action does), then `Preserve/Failover.lean` (Takeover, the hardest action, proved
layer by layer), then `Safety.lean`. `Preserve.lean` is the one-line-per-action
dispatch that ties preservation to the step relation.

**Conventions.** Actions are functions `State → State` using structure update, so
fields not mentioned are unchanged. Guards live in the `Step` constructors, and each
step carries the label of the action that fired (`Action`), so a run is a list of
actions. The protocol is packaged as a labelled transition system from CSLib
(`lts m : LTS (State Node) (Action Node)`, with `m` the `min-sync-replicas` value),
and `Reachable m i s` is CSLib's `CanReach` from `init i`: the existence of a run.
Names follow the design where it has one (`ThinksPrimary`, `KnowsLatest`,
`IsAuthoritative`, `Writable`, `catchUpPoint`). A counterexample is a concrete run on
`Fin 3` in a weakened step relation (the model's `Step` plus one action with a rule
removed), stated as a CSLib multi-step transition (`MTr`) whose label list is the
trace, with every guard evaluated by `decide`.

## 7. Reproducing

```
cd lean
../tools/lean.sh lake build                 # builds every proof
../tools/lean.sh lake env lean Check.lean   # prints the axioms of every theorem
```

`tools/lean.sh` runs the Lean toolchain in a container. Unpack the toolchain into
`tools/elan/`, build the image once
(`docker build -t valkey-lean:24.04 -f tools/Dockerfile.lean tools`), and fetch
Mathlib's prebuilt files once with `../tools/lean.sh lake exe cache get` (about
7 GB). A clean build then takes about 30 seconds.

## References

- Valkey Durability: Synchronous Replication Architecture,
  [`design-docs/sync-replication.md`](../sync-replication.md)
  ([valkey#5286](https://github.com/valkey-io/valkey/pull/5286)).
- The TLA+ models and the full findings list:
  [`sync-repl-formal-spec`](https://github.com/jjuleslasarte/valkey/tree/sync-repl-formal-spec)
  branch, `FINDINGS.md` and `spec/`.
- W. Lin, M. Yang, L. Zhang, L. Zhou. PacificA: Replication in Log-Based Distributed
  Storage Systems. Microsoft Research, MSR-TR-2008-25, 2008.
- J. Avigad, L. de Moura, S. Kong, S. Ullrich, with contributions from the Lean
  community. *Theorem Proving in Lean 4*.
  <https://lean-lang.org/theorem_proving_in_lean4/>. The reference for every Lean
  construct used here (Appendix A.7).
- F. Montesi and contributors. *CSLib: the Lean library for Computer Science*.
  <https://www.cslib.io>, <https://github.com/leanprover/cslib>, Apache 2.0. Used
  for labelled transition systems, runs and invariants (Appendix A.8).

---

## Appendix A: Reading a Lean proof

This appendix is for reviewers who know distributed systems and have not worked with
a proof assistant. It explains what the proof is, what "proven" means here, where the
trust actually sits, and the words used above.

### A.1 What a machine-checked proof is

A proof assistant is a type checker for arguments. You write a precise statement,
then a proof, and the tool checks every step against a small fixed set of logical
rules. There is no "the reviewer was convinced"; either the proof type-checks or it
does not. Lean 4 is one such tool. Its checker (the *kernel*) is a few thousand lines,
independently re-implemented several times, and every theorem in this repository
passes it.

The useful analogy is a test suite with infinite coverage. A test runs the system on
one input and checks one output. A proof is a single argument that covers every input
at once: here, every number of nodes, every log, every interleaving of every action,
every sequence of configuration changes and restarts. That is why a proof can say
"never" where a test can only say "not in the cases I tried".

### A.2 What was proven, in one sentence each

The statement proven is of the form: *every state the system can reach satisfies
property P*. "Can reach" means: start from the initial state and take any finite
sequence of steps the model allows. For the main theorem:

> For every type of node identifier, every `min-sync-replicas` value, every initial
> primary, and every reachable state: every authoritative node holds the whole
> committed history, and no node's committed prefix disagrees with it.

Lean's version of that sentence is `SyncReplication.safety`, and the words map one to
one onto its symbols (`∀ {Node} [DecidableEq Node] {m} {i} {s}, Reachable m i s →
Safety s`). Section 2 translates the five properties, proved by four named theorems,
the same way.

A counterexample theorem has the opposite form: *there is* a reachable state, in the
model with one rule removed, that violates the property (`Safety` or `AckedDurable`).
It proves the rule is needed, the way a failing test proves a bug exists. One of them,
`noSurvivor_loses`, states the loss directly instead, because with no authoritative
node left the property is vacuously true (Appendix B).

### A.3 What "proven" does not mean

A proof is only as good as the model and the statement. Three things to keep
separate:

1. **The model** (section 1 and `Model.lean`) is a simplified description of the
   protocol. The proof says nothing about behaviours the model leaves out (section
   5, "Not modelled"), and it is vacuous for behaviours the model forbids that the
   real system allows (section 5, "Assumptions stronger than the design"). Checking
   that the model matches the design is a human task.
2. **The statement** must say what you care about. "No committed write is lost" is
   encoded as EligibleHoldsCommitted plus the definition of *authoritative*. If that
   definition is too narrow, the theorem is true but uninteresting. The survival
   counterexample in Appendix B is an example: with no authoritative node left,
   property 1 is true and the data is gone. Read the definitions in section 2 as
   carefully as the theorems.
3. **The proof** is the part the machine checks, and the part you need not re-check.
   Its internal structure (section 3.1) matters only for understanding *why* the
   property holds, not for whether it does.

Also outside the proof: liveness (something good eventually happens), timing,
performance, and the correctness of the Valkey implementation. The proof is about
the protocol as designed, not as coded.

### A.4 Where the trust sits

From most to least trusted:

- **The Lean kernel and its three standard axioms** (`propext`, `Classical.choice`,
  `Quot.sound`). These are the same for every Lean proof, including all of Mathlib,
  and are not in question. The absence of `sorry` (a placeholder that lets an unproven
  statement type-check) is confirmed by `Check.lean`.
- **The theorem statements.** Short, and the thing to read. If a statement is wrong,
  the proof proves the wrong thing.
- **The definitions the statements use.** `Safety`, `IsAuthoritative`, `Reachable`,
  `Step`. A bug here is the most likely way for a correct proof to fail to mean what
  section 2 says. These are a few hundred lines (`Model.lean`).
- **The model's fidelity to the design.** Argued in sections 1 and 5, checked by
  hand, and the main residual risk.

### A.5 Vocabulary

- **State machine / transition system.** The model: a set of states, an initial
  state, and a relation saying which steps are allowed. Each step is an action with
  a guard (precondition) and an effect.
- **Invariant.** A property true of every reachable state. **Inductive** invariant:
  one that is also preserved by every single step, from any state where it holds.
  Finding one is the hard, creative part of the proof. `Invariant` (23 conjuncts) is
  the inductive strengthening of `Safety` (2 conjuncts). The extra 21 are the facts
  you must carry along for the induction to go through. Each one is there because
  some step broke the proof without it.
- **Preservation lemma.** "If `Invariant` holds before action X, it holds after." One
  per action, in `Preserve/`. This is where the bulk of the proof lives.
- **Ghost variable.** A variable added to the model for the proof's sake that no
  real node stores and that changes no behaviour. `hist`, the committed history, is
  one (section 2).
- **Counterexample.** A concrete run of the model that ends in a state violating the
  property. In Lean it is a list of steps whose guards the tool evaluates.
- **Vacuous.** True because there is nothing to check. "Every authoritative node
  holds the history" is vacuously true when no node is authoritative.
- **Axiom.** A statement accepted without proof. Lean's three standard ones are
  universally used; the thing to check is that a proof uses *only* those. `sorry`
  would appear as a fourth, `sorryAx`.
- **Decidable / `decide`.** A proposition the tool can evaluate to true or false by
  computation. The counterexamples rely on this: the guards and the properties are
  decidable on concrete finite states, so Lean checks them by running them.
- **Structure / `extends`.** Lean's record types. `Invariant` is a record with 23
  named fields grouped in five sub-records, so a proof of `Invariant` is built field
  by field and each field can be read, and cited, on its own.

### A.6 How to review this

1. Read section 2 and check the definitions of *authoritative*, *committed history*
   and the five properties against what you would want the protocol to guarantee.
   This is the step that needs a systems engineer, not a Lean expert.
2. Read section 1 and section 5 against the design doc. Anything the model leaves
   out or assumes is listed there; if something you rely on is missing, the proof
   does not cover it.
3. Spot-check `Model.lean` for one or two actions you know well (Takeover and
   RestartEmpty are good choices) against the design.
4. Trust the kernel for the rest. `lake build` with no errors and `Check.lean`
   printing only the three standard axioms is the whole verification; nothing else
   needs re-reading to confirm the theorems hold.

### A.7 The Lean used here, and where it is explained

The proofs use a small part of Lean 4. Each construct below is explained in *Theorem
Proving in Lean 4* by Jeremy Avigad, Leonardo de Moura, Soonho Kong and Sebastian
Ullrich, with contributions from the Lean community (open access,
<https://lean-lang.org/theorem_proving_in_lean4/>; hereafter *TPIL*, cited by
chapter). The book is the standard introduction and is written for readers who have
not used a proof assistant. The descriptions below are ours; the book is the
reference.

| In this proof | What it is | TPIL |
|---|---|---|
| `inductive Action`, `inductive Step` | `Action` is an ordinary enumeration, one case per protocol action. `Step` is a proposition defined by its introduction rules: a `Step m s μ s'` can only be built from the constructor for action `μ`, so a proof of it is a record of which action fired and evidence that its guards held. `Step` is an *inductively defined proposition*; because it is indexed by states and a label it is also an *inductive family*. | Ch. 7, Inductive Types (§7.3, §7.7) |
| `cases hs with \| append … \| replicate …` in `invariant_step` | Case analysis on which constructor built the step. Lean checks that every constructor is handled. This is the proof-side counterpart of `Step`'s definition. | Ch. 7 (§7.6, Tactics for Inductive Types) |
| `invariant_trInv`, `LTS.mtrInv_of_trInv` in `invariant_reachable` | "`Invariant` holds initially and every step keeps it" implies "`Invariant` holds in every reachable state". The induction over the run is CSLib's lemma (Appendix A.8); the proof here only supplies the one-step fact. | Ch. 7, Ch. 8 |
| `structure ConfigInvariant … `, `structure Invariant … extends …` | Record types whose fields are propositions. `Invariant` extends five sub-records, so each conjunct has a name (`h.knownEq`), can be cited alone, and the five layers can be proved separately and assembled with `where`. | Ch. 9, Structures and Records |
| `theorem invariant_takeover : Invariant … where toConfigInvariant := …` | A proof written as a term, field by field, rather than as a tactic script. TPIL contrasts term-style and tactic-style proofs and notes that tactic proofs are harder to read because the reader must predict the effect of each step; where a proof is an assembly of named parts we write it as a term. | Ch. 3, Ch. 5 (introduction) |
| `by … · … · …`, `show …`, `have …`, `refine ⟨…, ?_⟩`, `exact …` | Tactic proofs structured so each sub-goal is a bullet (`·`) that must be closed in place, with `show` stating the goal being proved. TPIL recommends this structure for readability and robustness, and recommends `exact` over `apply` where the term should close the goal exactly, because a failure then points at the real problem. | Ch. 5, Tactics (§5.4, Structuring Tactic Proofs) |
| `variable {Node : Type} [DecidableEq Node]`, section variables for guards in `Preserve/` | Parameters shared by every declaration in a section or file, so a theorem's statement shows only what is specific to it. | Ch. 6, Interacting with Lean (§6.3, §6.4) |
| `⟨…, …⟩` | Anonymous constructor notation, used to build a conjunction, an existential, or a structure in one expression. | Ch. 3, Ch. 9 |
| `by decide` in `Counterexamples/` | Lean evaluates a decidable proposition on concrete data and the evaluation is the proof. The guards and properties are decidable on `Fin 3` states, so each counterexample run is checked by running it. | Ch. 10, Type Classes (Decidable Propositions) |
| `noncomputable def fence … := sInf …` | A definition that uses classical reasoning and so has no executable code. Lean requires it to be marked. | Ch. 12, Axioms and Computation |
| `#print axioms` in `Check.lean`; `propext`, `Classical.choice`, `Quot.sound` | The command that lists what a theorem rests on, and the three axioms Lean's standard library and Mathlib build on. `Quot.sound` enters through function extensionality (`funext`), `Classical.choice` through `sInf` and `Set.encard`. A `sorry` would appear here as `sorryAx`. | Ch. 12, Axioms and Computation |

A note on reading proof bodies, for anyone who wants to. TPIL's point about tactic
proofs applies: the text alone does not show the goal at each step. Open the file in
VS Code with the Lean extension and the goal view shows the hypotheses and the goal
wherever the cursor is. That is how the proofs were written, and it is the only
practical way to read `Preserve/`. The theorem statements, `Model.lean`, and the
docstrings in `Invariant.lean` are written to be read without it.

### A.8 CSLib: the transition-system vocabulary comes from a library

The notions of run, reachability and invariant are not defined in this project. They
are imported from CSLib, the Lean library for computer science (Fabrizio Montesi and
contributors, Apache 2.0, <https://www.cslib.io>, modules
`Cslib.Foundations.Semantics.LTS.*`), pinned in `lakefile.lean` to a revision built
on the same Lean and Mathlib versions as this project. What this buys a reviewer is
that the words below have one published, checked definition each, which can be
compared with textbook ones, and that the glue lemmas are the library's rather than
ours.

| CSLib | What it is | Where this proof uses it |
|---|---|---|
| `LTS State Label` | A *labelled transition system*: a relation `Tr : State → Label → State → Prop`. The whole protocol is one value of this type, `lts m`, whose relation is `Step m`. | `Model.lean`, `Replies.lean` |
| `MTr s μs s'` | A *run*: a finite sequence of transitions from `s` to `s'` whose labels are the list `μs`. Built from `refl` (the empty run) and `stepL` (one transition in front of a run); `comp` joins two runs. | Every counterexample is an `MTr` from `init 0`, and its label list is the trace in the statement. |
| `CanReach s s'` | *Reachability*: some run leads from `s` to `s'`. `Reachable m i s` is defined as `(lts m).CanReach (init i) s`. | The hypothesis of every safety theorem |
| `TrInv p`, `MTrInv p`, `mtrInv_of_trInv` | A *one-step invariant* (every transition preserves `p`), a *run invariant* (every run preserves `p`), and the lemma that the first implies the second. The library does the induction over the run. | `invariant_reachable`, `replyInvariant_reachable` |

Nothing about the protocol comes from CSLib; the model, invariant and preservation
proofs are entirely this project's. CSLib's `#print axioms` for the lemmas used
shows the same three standard axioms as the rest of the proof.

---

## Appendix B: Issues found through modelling

The body of this document describes the design with the rules the guarantee needs.
This appendix lists the rules that the design doc, as currently written, does not
state, and what goes wrong without each. The numbering is that of the full findings
list, `FINDINGS.md` on the
[`sync-repl-formal-spec`](https://github.com/jjuleslasarte/valkey/tree/sync-repl-formal-spec)
branch, which also records the findings that are explored in TLA+ only.

Each item has a Lean counterexample (`lean/SyncReplication/Counterexamples/`): a run
of the model with the rule removed, every guard checked by `decide`, ending in a
state that violates the guarantee, or, for the survival condition and the F13 loss
run, a state where no node's log holds the committed history. The weakened step relation is named in the
theorem (`StepNoReconcile`, `AStepNoFence`, ...), so the statement says exactly which
rule the run does without.

**F1: reconcile against the inherited log** (`Counterexamples/Reconcile.lean`).
Promotion step 1, as written, waits until the replica has acknowledged up to the
primary's committed offset. Right after a failover, the new primary's committed
offset can be behind writes the old primary already committed. Scenario: n0 commits a
write with n1 as its only sync replica. n1 takes over with committed offset 0. n1
promotes n2, whose log is empty. n2 is now eligible without the committed write.
Rule: until the new primary has committed its inherited log, promotion catch-up and
full resync are measured against the end of that log, and the primary serves no
writes. Counterexample: `noReconcile_unsafe` (11 steps, `min-sync-replicas = 1`). The
run removes only the catch-up part of the rule, in Count; that the write block and
the resync bound are each needed on their own is not shown.

**F2: fence held replies by primaryship** (`Counterexamples/ReplyFence.lean`).
Releasing a held reply once the committed offset passes its offset is not enough,
because the offset can be reused by a later primaryship. Scenario: n0 writes at
offset 1 and holds the reply. n1 takes over with an empty log and n0 is fully
resynced. n0 is promoted, takes over again, writes different data at offset 1 and
commits it. The old reply is then released as OK for a write that was replaced.
Rule: release OK only while the node still considers itself primary, in the term the
write was tagged with; otherwise answer `UNCOMMITTED`. Counterexample:
`noReplyFence_unsafe` (14 steps, `min-sync-replicas = 0`). No run shows the fence is
needed at `min-sync-replicas ≥ 1`; the proof uses it there too.

**F5: a restarted primary rebuilds its sync replica set**
(`Counterexamples/Rebuild.lean`). A primary that restarts with its data loses its
in-memory sync replica set. If it starts from an empty set, it can commit without an
eligible replica. Scenario: n0 promotes n1 and writes, restarts with its data, counts
and promotes n2 (which has the write), and commits with n2's acknowledgement only. n1
is eligible and authoritative but lacks the committed write. Rule: on restart, the
primary's sync replica set is the eligible replicas whose recorded incarnation
matches, so it commits nothing until they acknowledge. Counterexample:
`noRebuild_unsafe` (9 steps, `min-sync-replicas = 1`).

**Incarnation check on primaryship** (`Counterexamples/Incarnation.lean`). Design §6
says the takeover compare-and-set checks the incarnation, so a node that came back
empty cannot be promoted. That is not enough: the node may already be the primary.
Scenario: a write commits on n0 and n1, and n0 restarts empty with a new incarnation.
Its configuration is current, and still names it primary under its old incarnation,
so n0 keeps acting as primary. It counts n2, whose log is empty, and makes it
eligible. n2 is now authoritative without the committed write. Rule: a node acts as
primary only if its configuration records its current incarnation (`ThinksPrimary`
in the model). Counterexample: `noIncCheck_unsafe` (9 steps); the run drops the check
from Count and MakeEligible only.

**`min-sync-replicas` counts only matching incarnations**
(`Counterexamples/MinSyncIncarnation.lean`). The design says a node that restarts
without data rejoins as ineligible, but the configuration keeps listing it as eligible
until the primary demotes it. If `min-sync-replicas` counted it in the meantime, a
primary could satisfy the minimum with a replica that cannot take over. Scenario: a
write commits on n0 and n1; n1 restarts empty (n0 survives), copies the log back,
acknowledges and is counted again; n0 writes and n1 acknowledges. n0 may now commit
with n1 as its only sync member, and after the commit n0 is the only authoritative
node. Safety is not affected (n1 does hold the data); the two-copies property is.
Rule: a sync replica counts toward `min-sync-replicas` only if it is eligible with the
incarnation the configuration records for it (`Writable` in the model).
Counterexample: `noIncWritable_oneCopy` (14 steps). The model does not check the
incarnation when counting a replica into the sync replica set: the proof never needed
it, so the guard was dropped.

**F13: a stale restore must not keep the incarnation**
(`Counterexamples/StaleRestore.lean`). The design changes the incarnation only on a
restart without data. A replica acknowledges a write once it is applied in memory, so
without `appendfsync always` it can restart from a file that predates writes it
acknowledged, keep its incarnation and its eligibility, and be counted on
acknowledgements it no longer backs. Scenario: a write commits on n0 and n1; n1
restarts from a file holding none of its log and keeps its incarnation. n1 is
authoritative without the committed write. With one more step, n0 restarting empty
(allowed, since n1 is authoritative), the write is gone from every node
(`staleRestoreKeepsInc_loses`, 9 steps); its client had OK. Rule: a node keeps its
incarnation across a restart only if the restored data covers its acknowledgement
high-water mark, the highest offset it has acknowledged as a replica (Ack) or as a
primary (Commit); otherwise it takes a new incarnation and rejoins as after a restart
without data. The mark must be persisted with the data, or acknowledgements must
follow fsync. Two weaker rules were checked by TLC and fail: the node's own committed
offset (a replica's is 0) and the acknowledgements it sent as a replica (a primary's
commits are not among them; the initial primary has sent none). Counterexample:
`staleRestoreKeepsInc_unsafe` (8 steps) and `staleRestoreKeepsInc_loses` (9).

**Survival condition** (`Counterexamples/Survival.lean`). This is an assumption the
design already makes, recorded here because the guarantee depends on it. Without it,
both copies of a committed write can restart empty. Scenario: a write commits on n0
and n1, n1 restarts empty, then n0 restarts empty. No node holds the write, and no
node is authoritative. Because no node is authoritative, property 1 holds only
vacuously in that state, so the theorem states the loss directly: the committed
history is non-empty and no node's log holds it. Counterexample: `noSurvivor_loses`
(9 steps). The design calls this case correlated data loss.

**F11: the clock-drift margin** (`Lease/`). The design says "Both sides use monotonic
clocks and subtract a clock-drift margin". Read literally, with both sides
subtracting the margin, the leases are unsafe for every margin shorter than the lease
as soon as there is any drift (`literal_unsafe`). With the holder subtracting the
margin and the grantor not, they are safe exactly when the margin is at least twice
the drift bound (`asym_safe_iff`). The doc should state which side subtracts, and the
`2D` bound.

**F12: lease durations** (`Lease/Durations.lean`). The rule "read lease + time to
commit a demotion + clock-drift margin < primary lease" (design §5, "Lease
durations") is not sufficient. It must also cover the acknowledgement round trip and
a second drift term. `demotion_in_time` gives a sufficient condition;
`doc_condition_insufficient_drift` and `_rtt` give runs where the doc's condition
holds and the primary lease has already expired when the demotion commits. This is an
availability issue, not a safety one: the primary then stops serving reads.

## Appendix C: The TLA+ models and what they add

The findings were first found with TLA+ models of the design, checked with the TLC
model checker, on the
[`sync-repl-formal-spec`](https://github.com/jjuleslasarte/valkey/tree/sync-repl-formal-spec)
branch. TLC explores every reachable state of a model up to a size bound (here 3
nodes, logs of length 2, up to 6 configuration versions, 1 restart). It is fast to
iterate with and produces a concrete trace when something fails, but it says nothing
beyond the bound. The Lean model was then written to mirror the TLA+ model
`CoreRestart`, and Lean proves the properties without a bound.

For everything in sections 2 to 4, the Lean results stand on their own and the TLA+
runs are redundant: the bounded "safe" runs are subsumed by the Lean theorems, and
every "needed" result has a Lean counterexample. What TLA+ still contributes:

- **Stale reads.** `NoStaleLinRead` in `spec/Leases.tla` checks, under the lease
  rules, that no linearizable read returns stale data. There is no Lean counterpart.
- **Forced failover and the lease fence on acknowledgements** (findings F7 and F8)
  are explored in `spec/Shard.tla` and `spec/Leases.tla`. The Lean model has no forced
  failover.
- TLC's `CoreRestart_noIncMin1` disables the `ThinksPrimary`, `Count` and `Writable`
  incarnation checks at once and finds a loss. The Lean counterexamples isolate them:
  `ThinksPrimary` is needed for safety, `Writable` for the two-copies property, and
  `Count`'s check is not needed, so the Lean model no longer has it.
- **The weaker stale-restore rules** (Appendix B, F13) were ruled out by TLC
  configurations, not by Lean counterexamples.

The Lean model has the same variables, actions and guards as the replication part of
`spec/CoreRestart.tla`, except that the TLC bounds (`MaxLen`, `MaxVer`,
`MaxRestarts`) are dropped; TLA+'s `CommitCap`, a `CHOOSE` of the minimum
acknowledgement, is written as the equivalent universal statement; the TLA+ `NoSurvivor`
switch, which cuts the ghost history to empty on a restart that leaves no survivor,
has no counterpart, since the Lean survival counterexample states the loss directly;
the held-reply layer also admits an append that records no reply, a superset whose
safety theorem covers the original; and the fixes that the TLA+ models carry as
switches (`ReconcileFirst`, `RebuildSync`, `NoReplyFence`, `IncCheck`) are simply the
Lean model's rules, with each counterexample stated in its own weakened step
relation instead.

| Finding | TLC run(s) | Lean counterexample |
|---|---|---|
| F1 | `CoreRecon_noReconcileMin0`/`Min1`, `CoreRestart_noReconcileMin1` | `noReconcile_unsafe` |
| F2 | `CoreAck_noReplyFence`, `CoreRestart_noReplyFenceMin1` | `noReplyFence_unsafe` |
| F5 | `CoreRestart_noRebuildMin1` (10 states), `_noRebuildMin1Loss` (22) | `noRebuild_unsafe` |
| Incarnation checks | `CoreRestart_noIncMin1` (all three off) | `noIncCheck_unsafe` (`ThinksPrimary`), `noIncWritable_oneCopy` (`Writable`) |
| Survival | `CoreRestart_noSurvivorMin0`/`Min1` | `noSurvivor_loses` |
| F13 | `CoreRestart_staleKeepMin0` (5 states), `_staleKeepMin1` (9), `_staleKeepMin1Loss` (11); weaker rules `_staleCommitMin1`, `_staleAckOnlyMin0`/`Min1` | `staleRestoreKeepsInc_unsafe` |
| Safe runs | `CoreRestart_safeMin0`/`_safeMin1` (120.6 M and 78.8 M states), `CoreRestart_twoCopiesMin1` | subsumed by `safety`, `ackSafety`, `commit_two_copies` |
| Stale reads | `Leases.tla` (`NoStaleLinRead`) | none |
