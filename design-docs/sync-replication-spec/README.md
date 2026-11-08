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

We also prove the design's read guarantee, "leases prevent stale reads in both
directions": with the two leases of design §5 added to the model in real time,
whenever a node may serve a linearizable read, its log is exactly the committed
history. This needs the clock-drift margin to be at least twice the drift bound, and
we show by a run that a smaller margin loses it. Separately, the lease timing lemmas
give the exact margin condition and a sufficient condition for the "Lease durations"
rule.

The proofs are about safety: of the replication log, and of linearizable reads under
leases. They do not cover forced failover, liveness (that a held reply is ever
released, or that a read is ever served), or client-visible read operations as a
history. Section 5 lists every exclusion and every assumption that is stronger than
the design.

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
  primary advances its own committed offset; in the replication layer `REPLCONF COMMIT`
  is not a message. The lease layer models its payload as each replica's **committed
  view**, carried on data messages.
- **Promotion flow.** The primary first counts a caught-up replica's acknowledgements
  (design §4, step 2), then commits the replica as eligible to the cluster bus (step
  4). A
  replica is caught up when it follows the primary and has acknowledged up to the
  primary's catch-up point: the committed offset, or, for a primary that has not yet
  committed the log it holds (a new primary, or one that restarted with its data),
  the end of that log.
- **Early removal.** Between steps 2 and 4, the primary may drop the counted replica
  again if it falls behind or fails (design §4), but only a replica that is not eligible
  in the primary's own configuration; once a replica is eligible it leaves the sync
  replica set through demotion alone. A deposed primary that has not learned of a
  takeover may do this too: the replicas that fence it are ones it lists as eligible,
  and it cannot drop those. This relies on MakeEligible being atomic in the model
  (Appendix B).
- **Demotion flow.** The primary commits the replica as ineligible and stops counting
  it, in one step.
- **Failover.** An eligible replica that knows the latest configuration takes over
  through the takeover compare-and-set, which checks that its incarnation matches the
  one recorded for it, and becomes the **current primary**: the one named in the
  latest configuration. The new configuration drops the old primary from the eligible
  set. The new primary starts with the eligible replicas of the new configuration as
  its sync replica set, with no acknowledgements and
  committed offset 0, and writes with a new term. Until it has committed the log it
  inherited, it measures promotion catch-up and full resync (below) against the end of
  that log. It may accept client writes before then, which relaxes the design's "only
  then serves clients" (design §2) for writes; it serves no linearizable read until
  its whole log is committed (`PrimCanRead`). Its commit point reaches the end of the
  inherited log before it commits anything after it (`committed_inherited_first`);
  that an early write lands after the inherited log is not proven for a node whose log
  a Resync truncated below its inherited end. The old primary is not stopped: it may keep
  acting on its stale configuration until it learns the new one, at which point it
  drops its sync replica set. A node acts as primary only while its configuration
  records its current incarnation.
- **Full resync.** A replica whose log has diverged from its primary's is replaced by
  the primary's log up to the catch-up point. This happens only after the replica is
  out of the sync replica set and ineligible. While a new primary is still committing
  its inherited log, the catch-up point is the end of that log, so a resync then
  copies inherited entries that are not yet committed.
- **Leases** (design §5). Leases ride on replication traffic. The **primary lease** is
  held by the primary from each eligible replica: it runs from when the primary sent
  the data an acknowledgement confirms, and the replica promises not to take over
  until one lease duration after it last received traffic from the primary (or
  learned a new configuration, or restarted). The **read lease** is held by a sync
  replica from the primary: it runs from when the replica sent the acknowledgement
  that a `REPLCONF COMMIT` echoes, and the primary promises not to commit without the
  replica until one lease duration after it last received an acknowledgement from
  it. The primary echoes acknowledgements, and so renews read leases, only while it
  holds its own lease from every eligible replica it knows of, and only to sync
  members that are eligible with a matching incarnation. Clocks may drift by at most
  `drift` over a lease; each holder subtracts a `margin` from its lease and assumes
  its clock slow, each grantor assumes its clock fast. A takeover waits out the
  primary lease; a demotion waits out the read lease, and after a takeover the new
  primary also waits one read lease plus the margin before demoting a replica of the
  configuration it replaced (a replica it promoted itself needs no such wait). A
  restart clears a node's leases and committed view and restarts both waits, the
  takeover wait and the demotion wait, the latter for every replica since the node has
  forgotten which configuration it took over from; it does not otherwise delay reads.
  A grant also requires the granting node to think it is primary. The primary's
  promise not to commit without a lease-holding replica is enforced at demotion; the
  other ways a replica leaves the sync set are early removal, which never applies to
  an eligible replica and so never to a lease holder, and the replica's own restart.
- **Linearizable reads.** A primary may serve one while it holds its lease from every
  eligible replica it knows and has nothing uncommitted. A sync replica may serve one
  while it holds a read lease and its committed view (the offset the last `REPLCONF
  COMMIT` told it) covers its whole log. This is the single-key form of dirty key
  tracking: the model serves no linearizable read while any write is uncommitted,
  where the design holds only reads of keys with uncommitted writes. Property 6
  therefore says nothing about reads of clean keys made while other keys are dirty.
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
| **6** | **NoStaleRead:** with `margin ≥ 2 · drift`, any node that may serve a linearizable read has exactly the committed history as its log. (If `readDur + drift ≤ margin`, no read lease is ever valid and the replica half holds vacuously; `replCanRead_reachable` shows it is not vacuous at the parameters of Appendix B.) | `SyncReplication.noStaleRead` |

The committed history only grows, so property 3 says that no acknowledged write is
ever lost or replaced. Property 6 is the design's "leases prevent stale reads in both
directions": a node that may serve a linearizable read returns the latest committed
value, and nothing newer has committed anywhere. It is stated over the lease layer
(`Leases.lean`), the replication model with real time and the lease timestamps added;
properties 1 to 5 hold there too (`lease_safety`). Property 1 establishes the data half of the design's failover
argument, "any eligible replica is safe to promote, because each one holds every
committed write" (design §5, fault detection); the other half, that the promoted
replica then reconciles before serving, is the reconciliation rule in section 1, which
the model keeps for reads and relaxes for writes.

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
implies properties 1 and 2. `Invariant` has 21 parts, grouped in five layers that
follow the design: configuration, replication, membership, commit and failover. Each
layer is stated in terms of the ones before it. The names are the field names in
`Invariant.lean`, where each has a docstring citing the design.

**Configuration** (`ConfigInvariant`, design §6). Cluster V2 holds one totally
ordered configuration; each node's copy may be behind it but never ahead.
- `knownLe`: no node has seen a configuration newer than the latest.
- `knownEq`: a node that has seen the latest version has the latest configuration.
- `primKnows`: the current primary knows the configuration that made it primary.
- `knownIncLe`: no node's copy of the configuration records an incarnation newer than
  the node's own, so a node that came back empty never matches its old record. For the
  latest configuration this follows (`ConfigInvariant.incLe`).

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
- `eligibleCounted`: every eligible replica with a matching incarnation is counted ("must
  count toward commits before it becomes eligible"). A restarted primary rebuilds its
  sync replica set so that this survives the restart.
- `syncNew`: a replica the current primary counts but has not made eligible follows
  it and has acknowledged at least the catch-up point.
- `eligibleInOldConfig`: an eligible replica that follows an old primary is still eligible in that
  primary's configuration. This is why a full resync never truncates an eligible
  replica, and why early removal never drops one.

**Commit** (`CommitInvariant`, design §2 and §5). Committed prefixes agree with the
committed history.
- `commitWithinLog`: a committed offset is within the node's log; with the next one, it
  is also within the history (`CommitInvariant.commitWithinHistory`).
- `committedIsHistoryPrefix`: what a node has committed is exactly the start of the
  history.
- `inheritedEndWithinLog`: the end of the current primary's inherited log is within
  its log.
- `historyWithinCommitOrInherited`: while the current primary is authoritative, the
  whole history is below its committed offset or within its inherited log, so a new
  primary reconciles against all of it.
- `histAck`: every authoritative node has acknowledged the whole history. This is
  what makes a restart from a stale file safe when the file covers `ackHigh`.

**Failover** (`FailoverInvariant`, design §5, "Writes can't split-brain").
- `stale`: a node that still thinks it is primary under an old configuration is
  **fenced** (this is the log fence of a deposed primary, a different thing from the
  reply fence of section 1). Some members of its sync replica set that it lists as
  eligible have left it for a newer primary, so their acknowledgements are frozen; the
  smallest of them is its *fence* (early removal cannot drop these members), and by
  the commit rule it can never commit past it. The current primary holds, and has
  acknowledged, the deposed primary's log up to the fence; every eligible replica
  either does the same or still follows the deposed primary. So a deposed primary may
  still commit, but only entries the new configuration already holds.
- `authEx`: some node is authoritative. The survival condition keeps this true.

**Goal.**
- `eligibleHoldsCommitted`: EligibleHoldsCommitted itself, over authoritative nodes.

Facts about the current primary (`historyWithinCommitOrInherited` and the primary
clauses of the fence) hold
only while it is authoritative: a primary that came back empty holds nothing, and
nothing new is committed until an authoritative eligible replica takes over.

Property 6 extends `Invariant` with thirteen more parts (`LeaseInvariant`,
`LeaseInvariant.lean`). Seven are bookkeeping: every recorded traffic, acknowledgement
and primaryship time is in the past (so is every read lease's start, which follows); a
lease, and the data an acknowledgement confirms, is dated no later than the traffic it
is measured from; an acknowledgement a primary echoes was sent no later than it
arrived; every acknowledgement a primary holds arrived during its current primaryship
(this last one is what lets a read lease dated by a takeover be renewed into one dated
by an acknowledgement). Two carry the argument:
- **A deposed primary's lease is over for good** (`deposed`). A primary `p` was deposed
  by a takeover of some `t`. `p` was current then, so it knew the latest configuration,
  and `t`'s takeover checked `t`'s eligibility in that configuration: `t` is eligible in
  `p`'s own configuration. `t` waited until `p`'s lease must have expired, measured from
  the last traffic `t` received from `p`, and `p`'s lease from `t` started no later than
  that traffic; `t` now follows someone else, so the lease is never renewed. So `p` can
  never again hold a valid lease from every eligible replica it knows: only the current
  primary can. This is the primary half of the read rule, and it is also why a deposed
  primary cannot renew read leases.
- **A valid read lease makes its holder authoritative** (`leaseAuth`). A lease is
  granted only by a primary that holds its own lease, hence by the current primary,
  and only to an eligible replica with a matching incarnation. Demotion waits until
  the lease must have expired; every lease started no later than the current primary's
  last acknowledgement from its holder, or no later than the current primary's
  takeover (`leaseBound`), which is what the new primary's extra wait covers.
The rest: a replica's committed view is a committed prefix of its log, and a node whose
configuration names it primary holds no read lease (which keeps a deposed primary out
of the read-lease holders across a takeover). The theorem then follows from the
replication invariant: the current primary has the history below its committed offset
or inherited log (`historyWithinCommitOrInherited`), and an authoritative node holds
the history (`eligibleHoldsCommitted`).
Both halves use `margin ≥ 2 · drift`, in two places: to turn the taker's wait into the
invalidity of `p`'s lease from `t`, and to turn the demotion wait into the invalidity of
the demoted replica's read lease. A holder assumes its clock slow and a grantor its
clock fast, each by `drift`, so the two worst cases are `2 · drift` apart. That the
premises of property 6 are reachable at all (so the theorem is not vacuous) is checked
by `primCanRead_reachable` and `replCanRead_reachable`.

**Which conjuncts the proof needs.** Each conjunct was deleted in turn and the proof
rebuilt (Experiment B, a sweep of scratch builds not kept in the repository). None is dead. Three follow from the others and are lemmas now,
not conjuncts: `ConfigInvariant.incLe` (from `knownIncLe` at the current primary and
`primKnows`), `CommitInvariant.commitWithinHistory` (from `commitWithinLog` and
`committedIsHistoryPrefix`) and, in the lease layer, `LeaseInvariant.readLeaseLe` (from
`leaseBound`, `ackReceivedLe` and `primarySinceLe`). The rest are load-bearing. In the
table, the first action or theorem listed for each conjunct is where the build failed
without it; the others come from a map of the uses of the conjunct, leaving out uses
that only re-establish the same conjunct, so a listed use may still be replaceable by a
different proof, and an action may be missing where the map was incomplete. The map was made before early removal
dropped `KnowsLatest` and the fence counted only eligible members; the rows those
changes touch (`knownEq`, `primKnows`, `eligibleInOldConfig`) are corrected by hand.

| Conjunct | Layer | Needed by |
|---|---|---|
| `knownLe` | Config | Commit, MakeEligible, MakeIneligible, Takeover; NoStaleRead |
| `knownEq` | Config | MakeEligible, MakeIneligible, Takeover, the restarts; the reply and lease layers |
| `primKnows` | Config | Commit, MakeEligible, Learn, MakeIneligible, Takeover, Resync, Uncount; `commit_two_copies` |
| `knownIncLe` | Config | RestartEmpty, RestartPartialFresh |
| `noSelfSync` | Replication | Commit, MakeEligible, RestartKeep, RestartPartialKeep; `commit_two_copies` |
| `ackedPrim` | Replication | Commit, Takeover, Learn |
| `ackedLe` | Replication | AppendWrite, Replicate, Ack, Commit, Count, MakeEligible, Takeover |
| `ackHolds` | Replication | Commit, Learn, MakeEligible, Takeover |
| `ackedHigh` | Replication | Commit, MakeEligible, Learn, Takeover, RestartPartialKeep |
| `syncCommit` | Replication | MakeEligible |
| `eligibleCounted` | Membership | Commit, Takeover |
| `syncNew` | Membership | MakeEligible |
| `eligibleInOldConfig` | Membership | Resync, Learn, Uncount (the fence) |
| `commitWithinLog` | Commit | the `Safety` statement; Count, Resync, Commit, AppendWrite, Replicate |
| `committedIsHistoryPrefix` | Commit | the `Safety` statement; Commit, the reply layer's Release, NoStaleRead, data messages |
| `inheritedEndWithinLog` | Commit | Count, RestartKeep; NoStaleRead |
| `historyWithinCommitOrInherited` | Commit | MakeEligible; NoStaleRead |
| `histAck` | Commit | RestartPartialKeep |
| `stale` | Failover | Commit |
| `authEx` | Failover | Commit |
| `eligibleHoldsCommitted` | goal | the `Safety` statement; every action |
| `primaryTrafficLe` | Lease | Replicate, Heartbeat, Learn, the restarts |
| `ackReceivedLe` | Lease | HeartbeatGrant |
| `primarySinceLe` | Lease | Ack |
| `dataSentLe` | Lease | Ack |
| `primaryLeaseLe` | Lease | Takeover |
| `echoLe` | Lease | HeartbeatGrant |
| `primarySinceAck` | Lease | HeartbeatGrant |
| `deposed` | Lease | NoStaleRead, HeartbeatGrant |
| `leaseBound` | Lease | HeartbeatGrant, Demote |
| `leaseAuth` | Lease | NoStaleRead, Takeover |
| `selfPrimNoLease` | Lease | Learn, Takeover |
| `committedViewLen` | Lease | the steps that extend logs, data messages |
| `committedViewHist` | Lease | NoStaleRead |

"Needed by" is about the current proof. No counterexample state was built for any
conjunct (one that meets all the others, breaks this one, and reaches a violation in one
step); that is the strong form of "necessary", and it was not attempted.

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
| A new primary commits its inherited offsets before any later one, so it may accept writes before reconciling | `SyncReplication.committed_inherited_first` |
| Property 6 (no stale linearizable read, `margin ≥ 2 · drift`) | `SyncReplication.noStaleRead` |
| Properties 1 and 2 under the lease layer | `SyncReplication.lease_safety` |
| Lease margin and durations | `Lease/` |
| Each rule in Appendix B with a counterexample is needed | `SyncReplication.noReconcile_unsafe`, `noCatchUp_unsafe`, `resyncEligible_unsafe`, `noReplyFence_unsafe`, `noRebuild_unsafe`, `noIncCheck_unsafe`, `noIncWritable_oneCopy`, `uncountElig_unsafe`, `staleRestoreKeepsInc_unsafe`, `staleRestoreKeepsInc_loses`, `noSurvivor_loses`, `noWaitPrim_stale`, `noWaitRead_stale`, `grantAny_stale`, `grantSync_stale`, `grantNoIncRestart_stale`, `smallMargin_stale`, `restartKeepsReadLease_stale`, `restartNoDemotionWait_stale`, `restartForgetsTimer_stale`, `takeoverNoDemotionWait_stale`, `grantWithoutPrimaryLease_stale` |
| Property 6 is not vacuous: the primary holding its lease from an eligible replica may serve a read | `SyncReplication.primCanRead_reachable` |
| Property 6 is not vacuous: a replica holding a read lease may serve a read | `SyncReplication.replCanRead_reachable` |
| A new primary may demote a replica it promoted itself without the post-takeover wait | `SyncReplication.demoteNew_reachable` |
| Resync's guard that the replica is not counted excludes a reachable state (no counterexample without it) | `SyncReplication.countedDiverged_reachable` |

Size: the model is 902 lines (459 for the protocol, 129 for the held-reply layer,
314 for the lease layer), the invariants and their lemmas 1,514 (462 for replication,
1,052 for leases, which includes their preservation), the per-action contracts 616,
and the replication preservation proofs 2,519. Lean checks the whole of
`SyncReplication` in about 20 seconds on a laptop-class machine.

[lean/LEAN.md](lean/LEAN.md) has every theorem statement and the details of the
encoding.

## 5. Scope and limitations

### Not modelled

- **Forced failover** (`CLUSTER FAILOVER FORCE`, `TAKEOVER`). The design accepts
  losses when the target is ineligible. Explored in TLA+ only (Appendix C).
- **Reads as operations.** Property 6 is a state predicate: whenever a node *may*
  serve a linearizable read, its log is the history. Client read operations, with
  their invocation and response times, are not modelled, so no linearizability
  statement over a history of reads and writes is made. Serializable (non-lease)
  replica reads are not modelled.
- **Liveness.** Nothing proves that a held reply is ever released, as OK or as
  `UNCOMMITTED`, or that a lease is ever renewed, or that a read is ever served. The model's `UNCOMMITTED` (`abort`) fires only when the primaryship
  that took the write is no longer current. The design's other case, a healthy
  primary whose sync replica set fell below `min-sync-replicas` releasing held writes
  as `UNCOMMITTED`, is not modelled, and neither is the `CLUSTERDOWN` rejection path
  or client retry semantics.
- **Planned demotion** (design §4 step 2: the primary asks a healthy replica to drop
  its read lease and proceeds on its confirmation). Demotion always waits the read
  lease out.
- **Correlated data loss** is excluded by the survival condition. The design's
  detection of it (no eligible replica with a matching incarnation, so the shard
  stays unavailable) is not proven.
- AOF and `appendfsync`; async read replicas beyond being ineligible (in the model
  any follower may replicate uncommitted entries, while the design caps an async
  replica's stream at the committed offset); `target-sync-replicas` and the choice of
  which replica to promote (the model allows any promotion); replication lag
  thresholds; manual failover; slot migration and anything beyond a single shard;
  modules; dirty key tracking.
- **Replica committed offsets.** Only a primary advances its own committed offset
  (`commit`); property 2 constrains the offsets a node reached while it was primary.
  A replica's committed view (`committedView`, the lease layer's model of `REPLCONF
  COMMIT`) is separate, and is what a replica read is served from.
- **The Cluster V2 bus is assumed correct** and modelled as a compare-and-set register
  (section 1).
- **Messages are abstracted** (section 1). An acknowledgement carries the replica's
  offset at delivery, so the model assumes no message is delivered after a full
  resync or restart has closed its connection. In the lease layer a lease therefore
  starts at the real time of the event it is measured from; this is the tightest case
  for a lease argument, since delivery delay only widens the gap between a holder's
  expiry and the grantor's promise. The echo of an acknowledgement rides on a
  separate heartbeat rather than on every data message, which reaches the same
  states.
- **Clocks** follow the additive drift model: over one lease, a local clock's elapsed
  time is within `drift` of real elapsed time. `Lease/Additive.lean` shows the two
  worst cases the layer uses (holder slow, grantor fast) are exact for this model;
  rate-bounded drift is covered there too, but not in the layer.

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
  the node to re-commit what it holds before it serves reads (its catch-up point is set
  to the end of its log), and so does a takeover; for a takeover the design says so
  (§2, "only then serves clients"), for a restart it does not. Writes are not held
  back in either case (section 1). A takeover also starts the new
  primary's sync replica set as the eligible replicas of the new configuration. Leaving
  out those whose recorded incarnation is stale would be an availability choice, not
  needed for safety: the proof holds either way, since `Writable` never counts them.
  (d) The acknowledgement high-water mark
  `ackHigh` survives a restart with data and is lost with a new incarnation; the model
  assumes the implementation persists it with the data it covers. A stale file is
  modelled as a prefix of the log; a file that is not a prefix (a diverged tail) is not
  modelled.
- **Leases carry three assumptions.** (a) A restarted primary waits one read lease
  plus the margin before demoting anyone, as a new primary does after its takeover for
  replicas of the configuration it replaced. The design's restart rule covers takeover
  and serving reads; the model applies it to demotion too, because a restarted primary
  has forgotten when it last heard from each replica, and to every replica, because it
  has also forgotten which configuration it took over from. Appendix B shows the wait
  is needed. (b) Read leases are
  granted only to sync members that are eligible with a matching incarnation. The
  design says "sync replica". Appendix B shows that all three parts are needed, the
  incarnation match within the design's duration rule. (c) In the other direction, the design's restart rule delays reads for
  one lease after a restart; the model only clears the restarted node's leases, so it
  may read as soon as it holds a new one. The proof shows that suffices, so the read
  half of the restart rule is not needed for safety. The takeover half (a restarted
  node waits one lease before it attempts a takeover; the model restarts the takeover
  timer at the restart) is needed: a node that forgets the timer and treats its
  primary as long silent breaks property 6 (Appendix B).
- **The incarnation checks** in `ThinksPrimary` and `Writable` are in the model as
  guards. The design states only the takeover compare-and-set. Appendix B shows both
  are needed: the first for safety, the second for the two-copies property.

### What the model is checked against

The Lean model is written by hand from the design. Nothing mechanical checks it
against the design doc itself; sections 1 and 5 are the argument, and reviewing them
is the step that needs a systems engineer (Appendix A.6). The replication model
mirrors a TLA+ model of the same protocol (Appendix C), which was model-checked at
small sizes, and earlier versions of the Lean encoding were checked against that
model's complete state graph; that catches slips in how the Lean was written, not
differences between both models and the design. The lease layer mirrors
`spec/Leases.tla` but was not checked against its state graph, and differs from it in:
instant messages instead of one-slot lossy channels; the echo on a separate heartbeat;
restarts and incarnations, absent from `Leases.tla`; `MayGrant` requiring eligibility
and a matching incarnation where `EchoOnlySync` requires sync membership; traffic and
acknowledgements not gated on the sender thinking it is primary (which only adds
behaviours); no leases in the initial state where `Leases.tla` starts with every
replica eligible and both leases established; a takeover resetting the committed
offset to 0 where `Leases.tla` starts it at the replica's committed view.

"Any number of nodes" means any Lean type of node identifiers, including infinite
ones. `Writable` uses `Set.encard`, which is the usual cardinality on finite sets and
`⊤` on infinite ones. The theorems hold for infinite node types too, but only the
finite case corresponds to a real cluster.

### Future work

Client read operations and a linearizability statement over histories, for which
CSLib's `DistributedConsistency` definitions are the natural target.

## 6. How the proof is organized in code

| Path | Contents | Lines |
|---|---|---|
| `lean/SyncReplication/Model.lean` | The protocol: state, actions, steps, properties | 459 |
| `lean/SyncReplication/Replies.lean` | Held client replies: the acknowledgement layer, AckedDurable, AckedHeld | 129 |
| `lean/SyncReplication/Leases.lean` | The lease layer: real time, the two leases, the committed view, the read rule, NoStaleRead | 314 |
| `lean/SyncReplication/Invariant.lean` | The invariant in five layers; the fence; frame lemmas | 462 |
| `lean/SyncReplication/Contracts.lean` | Each action's effect in design terms, proved without the invariant | 616 |
| `lean/SyncReplication/Preserve/`, `Preserve.lean` | Preservation, one file per subsystem: `Replication`, `Commit`, `Config`, `Failover`, `Restart`; each action proved one layer at a time; `Preserve.lean` dispatches on the step | 2,519 |
| `lean/SyncReplication/Safety.lean` | `safety`, `commit_two_copies`, `committed_inherited_first` | 107 |
| `lean/SyncReplication/Durability.lean` | The held-reply invariant; `ackSafety`, `ackedHeld` | 249 |
| `lean/SyncReplication/LeaseInvariant.lean` | The lease invariant and its preservation; `noStaleRead`, `lease_safety` | 1,052 |
| `lean/SyncReplication/Counterexamples/` | One file per rule in Appendix B; each counterexample is in its own weakened step relation. Reachability witnesses, runs of the model itself, for the read rule, the narrowed demotion wait and the state Resync's counted guard excludes (`ResyncCounted.lean`, no weakened relation) | 1,718 |
| `lean/SyncReplication/Lists.lean` | List-prefix lemmas | 68 |
| `lean/Lease/` | Lease timing (additive and rate clocks, durations) | 377 |
| `lean/Check.lean` | Prints the axioms of the 33 `SyncReplication` theorems | |
| `lean/LeaseCheck.lean` | Prints the axioms of the 12 `Lease` theorems | |

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
../tools/lean.sh lake env lean Check.lean        # axioms of the 33 SyncReplication theorems
../tools/lean.sh lake env lean LeaseCheck.lean   # axioms of the 12 Lease theorems
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
Safety s`). Section 2 translates the six properties, proved by five named theorems,
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
  Finding one is the hard, creative part of the proof. `Invariant` (21 conjuncts) is
  the inductive strengthening of `Safety` (2 conjuncts). The extra 19 are the facts
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
run, a state where no node's log holds the committed history. The entries headed
"not shown needed" are the exceptions: the proof uses those rules, and no run without
them is known. The weakened step relation is named in the
theorem (`StepNoReconcile`, `ReplyStepNoFence`, ...), so the statement says exactly which
rule the run does without.

**F1: reconcile against the inherited log** (`Counterexamples/Reconcile.lean`).
Promotion step 1, as written, waits until the replica has acknowledged up to the
primary's committed offset. Right after a failover, the new primary's committed
offset can be behind writes the old primary already committed. Scenario: n0 commits a
write with n1 as its only sync replica. n1 takes over with committed offset 0. n1
promotes n2, whose log is empty. n2 is now eligible without the committed write.
Rule: until the new primary has committed its inherited log, promotion catch-up and
full resync are measured against the end of that log. Counterexample:
`noReconcile_unsafe` (11 steps, `min-sync-replicas = 1`). The run removes only the
catch-up part of the rule, in Count; that the resync bound is needed on its own is not
shown. The fix as first proposed also blocked client writes until the inherited log was
committed. That block is not needed for safety: with it removed every theorem still
holds, and `committed_inherited_first` shows the inherited offsets still commit first.
It does not say which offsets early writes take, and does not cover a deposed node
whose log a Resync truncated below its inherited end.

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
in-memory sync replica set. If it starts from an empty set, it can commit without
waiting for a replica that was eligible before the restart. Scenario: n0 promotes n1 and writes, restarts with its data, counts
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

**Early removal only before eligibility** (`Counterexamples/Uncount.lean`). Design §4
says a primary may drop a counted replica that falls behind or fails "before step 4".
The qualifier is load-bearing. Scenario: n0 promotes n1 and n2 and writes; n2
acknowledges; n0 drops n1 from its sync replica set and commits with n2's
acknowledgement only. n1 is eligible and authoritative without the committed write.
Rule: a replica that is already eligible leaves the sync replica set only through
demotion. This is the design's own second ordering rule; the entry records that early
removal must respect it. Counterexample: `uncountElig_unsafe` (9 steps,
`min-sync-replicas = 1`). The check is in the primary's own configuration, and early
removal does not require the primary to know the latest one: a deposed primary may
drop a member it does not list as eligible. An earlier version of the model required
the latest configuration; the proof does not need it (below).

**Survival condition** (`Counterexamples/Survival.lean`). This is an assumption the
design already makes, recorded here because the guarantee depends on it. Without it,
both copies of a committed write can restart empty. Scenario: a write commits on n0
and n1, n1 restarts empty, then n0 restarts empty. No node holds the write, and no
node is authoritative. Because no node is authoritative, property 1 holds only
vacuously in that state, so the theorem states the loss directly: the committed
history is non-empty and no node's log holds it. Counterexample: `noSurvivor_loses`
(9 steps). The design calls this case correlated data loss.

**Replication rules the proof uses, each shown needed.** These rules are in the design
or in the model as described in section 1; each entry deletes one and gives the run
that breaks property 1 without it.
- *Count waits for the catch-up point* (`Counterexamples/CatchUp.lean`): a primary
  counts a replica only once it has acknowledged up to the primary's catch-up point,
  which is the design's committed offset (promotion step 1) once the primary has
  reconciled. Scenario: a write commits on n0 and n1; n0 counts n2, which has
  acknowledged nothing, and makes it eligible. n2 is authoritative with an empty log.
  The design's own guard forbids the Count, so the run is about the design's half of
  the rule. Counterexample: `noCatchUp_unsafe` (8 steps, `min-sync-replicas = 1`).
  F1's run is a second one, for the reconciliation half: Count measured against the
  primary's own commit point is a special case of Count with no guard
  (`stepNoCatchUp_of_stepNoReconcile`).
- *Resync only a replica that is not eligible* (`Counterexamples/ResyncEligible.lean`):
  a primary that restarts from a stale persistence file can hold less than an
  eligible replica that still follows it. Scenario: a write commits on n0 and n1; n0
  restarts from a file holding none of its log and takes a new incarnation (n1
  survives); n1's log is no longer a prefix of n0's and n0 no longer counts it, so
  without the guard n1 resyncs to the empty log. n1 is still eligible with its
  recorded incarnation: authoritative without the write. Counterexample:
  `resyncEligible_unsafe` (8 steps, `min-sync-replicas = 1`). The guard is the design's
  ("replicas that are still eligible but ahead of the new primary" are demoted before a
  full resync, §5). In the run the resync source n0 no longer thinks it is primary
  (its recorded incarnation is stale), and the model's Resync does not ask that of the
  source. So the run shows that Resync needs one of two guards. The other also works:
  with Resync requiring a source that thinks it is primary and no eligibility guard,
  the proof holds (a scratch build, not in the repository), but it needs one more invariant
  conjunct, that a deposed primary's configuration records the current incarnation of
  each authoritative eligible replica that follows it. The model keeps the eligibility
  guard, which is the design's.

**Rules the model no longer has.** *Early removal only by a primary that knows the
latest configuration.* The model required it, and the proof used it to show that a
deposed primary never drops the member that fences it. With early removal checked in
the primary's own configuration instead of the latest one, the proof holds without it:
a deposed primary is fenced by departed members it lists as eligible, which early
removal cannot drop. A run with the requirement removed but the check left in the
latest configuration did break property 1, but only by reading a configuration the
deposed primary had not seen, so it was not a behaviour of the design and is not
kept. The model's MakeEligible updates the latest configuration and the primary's copy in one
step, so a primary always knows the outcome of its own promotion. In the real system the
compare-and-set can commit while the primary has not seen the result; a primary that
then drops the replica as "not eligible in my view" drops an eligible one, which is
`uncountElig_unsafe`. So the relaxed rule is safe only if a primary treats an
outstanding step-4 compare-and-set as possibly committed. The design's own wording, "before step 4" (before the primary
proposes the compare-and-set), is safe either way.

**Replication rules the proof uses, not shown needed.**
- *Resync only a replica its primary has not counted*
  (`Counterexamples/ResyncCounted.lean`). The preservation proof uses the guard:
  Resync resets the primary's record of the replica's acknowledgement to 0, and the
  invariant bounds the primary's commit point and catch-up obligations by its counted
  members' acknowledgements. The state the guard excludes is reachable:
  `countedDiverged_reachable` (5 steps, `min-sync-replicas = 0`) has n0 count n1 (a
  sync replica, so it may receive uncommitted writes, as the design allows), n0 write,
  n1 copy the write, n0 restart from a file holding none of its log (keeping its
  incarnation, as it has acknowledged nothing; n1 is not eligible, so its rebuilt sync
  replica set is empty), and n0 count n1 again at catch-up point 0, so n1 is counted
  and its log `[1]` is not a prefix of n0's empty log. No counterexample was found. In
  that state n0's record of n1's acknowledgement is already 0, so the forbidden Resync
  changes no acknowledgement and n0's commit point, bounded by it, is 0. The expected
  reason, not proven: a primary records an acknowledgement only while the replica's
  log is a prefix of its own. The actions that can end that while the replica stays
  counted are the primary's restarts, which truncate or empty its log, and each resets
  its acknowledgement table. The primary's own Resync also replaces its log, but needs
  it to follow another node, and a node follows another only after Learn, which
  empties its sync replica set. Takeover changes no log; it gives the new primary a
  fresh table. So a counted replica that has diverged would always have
  acknowledgement 0, and the guard would be redundant. Proving that would add a
  conjunct to the invariant. A bounded TLC check of `CoreRestart` with the guard
  removed (a scratch copy, not in `spec/`) reached about 108 million distinct states
  with no violation before it was stopped unfinished; the same setup with the eligible
  guard removed instead found the `EligibleHoldsCommitted` violation, so the check
  could detect a Resync defect.

**The lease rules, each needed** (`Counterexamples/Leases.lean`). Property 6 holds
with the design's lease rules; removing any one of these loses it, each shown by a
run ending in a stale linearizable read at `min-sync-replicas = 0`:
- *A replica waits out the primary lease before taking over* (`noWaitPrim_stale`, 8
  steps): without the wait, the deposed primary still holds a valid lease from the
  taker and serves a read of a log that misses the taker's committed write.
- *The primary waits out the read lease before demoting* (`noWaitRead_stale`, 9
  steps): without the wait, the demoted replica still holds a valid read lease and
  serves a read that misses the write committed without it.
- *Read leases go only to sync members* (`grantAny_stale`, 5 steps): a follower
  outside the sync set that receives an echo of its acknowledgement gets a read lease
  the primary never waits on. *And only to eligible ones* (`grantSync_stale`, 7
  steps): a counted replica that is not yet eligible can be dropped by early removal
  with no wait, then serve a stale read on its lease. The design says "sync replica";
  these two runs are the reason to read that as the eligible members. *And only to
  ones with a matching incarnation* (`grantNoIncRestart_stale`, 22 steps): a replica
  that restarted empty stays listed as eligible and may be counted again; granted a read
  lease, it keeps it when the primary restarts with its data, but the restarted
  primary's rebuilt sync replica set leaves it out (its recorded incarnation is stale),
  so the primary commits without it and it serves a stale read. The run is within the
  design's "Lease durations" rule (primary lease 6, read lease 3, drift 1, margin 2).
- *The margin is at least twice the drift* (`smallMargin_stale`, 12 steps): with
  margin 1 and drift 1 and every rule kept, the taker's wait ends while the deposed
  primary, its clock a drift slow, still believes its lease valid.
- *A restart clears the node's read lease* (`Counterexamples/RestartReadLease.lean`,
  `restartKeepsReadLease_stale`, 11 steps): a replica that holds a read lease and
  restarts empty, keeping the lease, comes back with an empty log and committed view
  0, so nothing is uncommitted and it serves a read of an empty log while the history
  is `[1]`.
- *A restarted primary waits one read lease plus the margin before demoting*
  (`Counterexamples/RestartDemotionWait.lean`, `restartNoDemotionWait_stale`, 10
  steps): a restart loses the primary's record of when it last heard from each
  replica, so the read-lease wait is vacuous. Without the restart wait, n0 restarts
  with its data while n1 holds a read lease from it, demotes n1 at once, and commits
  a write alone; n1 serves a read that misses it.
- *After a takeover, the new primary waits one read lease plus the margin before
  demoting a replica of the replaced configuration*
  (`Counterexamples/TakeoverDemotionWait.lean`, `takeoverNoDemotionWait_stale`, 22
  steps, within the duration rule at `P3`): the new primary has no acknowledgement
  from anyone, so the read-lease wait is vacuous. n0 grants n2 a read lease at the
  last tick it holds its lease from n1; one tick later n1 takes over, demotes n2 at
  once and commits a write alone; n2 serves a read that misses it. With a read lease
  of 2 (`P0`) the lease has expired by the earliest takeover, so the run needs
  `readDur ≥ 3`: the gap between the latest grant the old primary may make and the
  earliest takeover is only `margin - 2 · drift`, zero at the margin bound, whatever the
  primary lease is.
- *A restarted node does not treat its primary as long silent*
  (`Counterexamples/RestartTimer.lean`, `restartForgetsTimer_stale`, 13 steps): the
  model restarts the takeover timer at the restart. With the timer set to "long ago"
  instead, n1 restarts with its data while n0 holds a fresh lease from it, takes over at
  once and commits a write alone; the deposed n0 still holds its lease and serves a read
  that misses it. This is the design's restart rule ("waits one full lease duration
  before it attempts a takeover", §5) shown needed. Keeping the timer's old value
  across the restart instead also kept every theorem in a scratch build (not in the
  repository), but only because the model has one clock that keeps running across a
  restart; a monotonic clock does not survive a host reboot.
- *Only a primary holding its primary lease grants read leases*
  (`Counterexamples/GrantPrimaryLease.lean`, `grantWithoutPrimaryLease_stale`, 18
  steps): n0 promotes n1 and n2; n1 waits out n0's lease, takes over, waits out the
  post-takeover window, demotes n2 and commits a write alone. n0 and n2 have not
  learned of it, so n2 still follows n0 and n0 still thinks it is primary; n2
  acknowledges and n0, holding no valid lease, echoes it. n2 serves a read of an empty log.
That the design's narrower form of the post-takeover wait is what the model has, so
that a new primary may demote a replica it promoted itself inside the window, is
checked by `demoteNew_reachable`.

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

- **Stale reads as client operations.** `spec/Leases.tla` also models explicit client
  reads and checks a refinement to a linearizable shard (`Refinement`). The Lean
  property 6 is the state-predicate form, `NoStaleLinRead`.
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
| Lease rules | `Leases_noWaitPrim`, `_noWaitRead`, `_noEchoSync`, `_smallMargin` (each violates `NoStaleLinRead`); the safe runs never finished | `noWaitPrim_stale`, `noWaitRead_stale`, `grantAny_stale` (the `EchoOnlySync` rule), `grantSync_stale` (eligibility, which `Leases.tla` has no switch for), `smallMargin_stale`; `noStaleRead` is the first proof that the rules suffice |
