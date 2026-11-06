# Findings on the design doc

Source: [Valkey Durability: Synchronous Replication Architecture](https://docs.google.com/document/d/15-VWM9KR2dfG4Y05RVF3tOnaVoYgKhmiFQ8jJZtxirg/edit?tab=t.0#heading=h.2sacx7to1xu)
(`design-docs/sync-replication.md` in
[valkey#5286](https://github.com/valkey-io/valkey/pull/5286)). F1-F12 were
independently reviewed by three reviewers.

The findings come from bounded model checking. Each TLC result is a named
configuration in `spec/`; `spec/expected.tsv` records its expected outcome and
`spec/regress.sh` re-checks it. The TLC output files are not kept in the
repository, so rerun a configuration to see its trace. F3 and F4 are
observations from writing the model and have no counterexample.

Where a fix is also proven in Lean without bounds, the entry names the theorem:
F1, F2, F5, the incarnation check, and the lease timing (F11, F12). For F1, F2,
F5, the incarnation check and the survival condition there is also a Lean
counterexample: a run of the model with that item removed, every step checked
by Lean. Bounds are stated with each result.

Lean theorem names (`SyncReplication.safety`, `noRebuild_unsafe`, ...) refer to
the Lean proof branch (`sync-repl-lean`,
`design-docs/sync-replication-spec/lean/SyncReplication/`). This branch's
`lean/` is an older snapshot of the same proofs under the `RestartProof`,
`ReconProof`, `CoreProof` and `AckProof` namespaces, without the restart
counterexamples.

## F1. Promotion after takeover can lose an acknowledged write

**Status:** confirmed by TLC. 2 of 3 reviewers call it a doc gap. The third
calls it an ambiguity, because the PacificA sentence in section 2 can be read
as covering it.

**Doc text involved**
- Section 4, promotion step 1: the primary waits until the replica's acked
  offset is "at or past the primary's committed offset".
- Section 2: after promotion, a new primary's local view "can be behind
  writes the old primary had already acknowledged". The new primary "treats
  every write in its log as committed once it has reconciled with the
  remaining sync replicas, and only then serves clients."
- Section 5, "Committing the new primary's tail": the tail "commits the
  normal way: once every replica in the new sync replica set has
  acknowledged it".
- Section 2, commit rule: the committed offset advances only while the sync
  set has at least min-sync-replicas members.

**Counterexample** (`Shard_m_docAsWrittenLossFenced`, 25 states, no crash, lease fence on so the deposed primary cannot contribute):
1. n1 is the primary and n2 is a sync replica. A write commits and the
   client gets OK.
2. n2 takes over. Its committed offset is still 0 (it never received
   REPLCONF COMMIT for the write), even though its log holds the write.
3. n2 promotes empty replica n3. The catch-up check passes because ack 0 is at
   or past committed 0. n3 is committed as eligible.
4. n3 takes over with an empty log. The acknowledged write is gone.

**Why the section 2 sentence does not close it:** "only then serves
clients" does not cover promotion or full resync. Also, when no sync replica
remains, the section 5 rule freezes the committed offset, so
"reconciliation" either never completes or does nothing.

**Proposed doc change:** after a takeover, promotion catch-up (step 1)
and full resync are measured against the log the new primary inherited,
not against its own committed offset. Following PacificA, that log holds
every committed write. The new primary accepts client writes only once it
has committed that log. The commit itself still follows the normal rule
(it needs min-sync-replicas acks). It must not bypass that rule, as
reviewers pointed out in step 3. Otherwise a new primary left with no
eligible replica could never reach the minimum again.

**Model:** `CatchUpPoint` / switch `ReconcileFirst` in `spec/Shard.tla`.
The trace needs 6 configuration changes: the loss becomes client-visible
only once the empty new primary commits and acknowledges a conflicting
write. Safe runs (iteration 2, merged model): `Shard_m_safe` 24.2M distinct
states, `Shard_m_safeMin0` 46.1M (3 nodes, 2 writes, 5 config changes,
1 crash, no restarts); `Shard_f_safe` 1.04M (1 write, with restarts). The
counts are as reported at the time; reproduce them with `spec/regress.sh`
(the first two take several hours each).

**Proof status (CoreRecon):** the fix as proposed, with promotion catch-up
and full resync measured against the inherited log while unreconciled, is
proven safe in Lean for every min-sync value (`SyncReplication.safety`,
`ackSafety`, `ackedHeld`; `spec/CoreRecon.tla`). Core's stricter rule (no
promotion or resync until reconciled) is safe but deadlocks at min-sync ≥ 1
after a takeover that leaves no sync replica: `CoreRecon_strictReachLoneReconMin1`
explores the full state space without ever reconciling such a primary,
while `CoreRecon_ReachLoneReconMin1` (the fix) reconciles it in 12 states.
Lean counterexample without the fix: `SyncReplication.noReconcile_unsafe`
(11 steps).

## F2. Held replies must be fenced by primaryship, not only by offset

**Status:** confirmed by TLC, and all 3 reviewers agree.

**Proof status:** with the F1 and F2 fixes, no acknowledged write is lost,
for any number of nodes and any log length. `SyncReplication.ackSafety` and
`ackedHeld` prove it for every min-sync value, with restarts with and without
data, given the F5 fix and the survival condition (see below). Neither covers
forced failover. Writes are identified by offset and primaryship term, and the
fence uses the node's local, possibly stale view of its primaryship. Without
the reply fence, `CoreAck_noReplyFence` (TLC) and `SyncReplication.noReplyFence_unsafe`
(Lean, 14 steps) acknowledge a write that is not in the history. Reviewed in
round 4: sound within that scope.

Section 1 releases a held reply when the committed offset passes a bare
offset boundary in the output buffer. Offsets are reused after a full
resync.

**Counterexample** (`Shard_m_noStepDown`, min-sync = 0, 18 states): n1
holds the reply for write 2 at offset 1. n3 takes over, and n1 is resynced
to an empty log. n1 is later re-elected and puts a different write at
offset 1, which then commits. The old reply for write 2 is released as OK.
The client is told a write succeeded that is not in the history.

Section 5 says a primary that steps down "returns UNCOMMITTED" for held
replies. It does not say this must happen before any other primary action.
It also does not say the boundary carries the primaryship.

**Proposed doc change:** every reply boundary carries the configuration
epoch (or term) of the primaryship that set it. A reply is released as OK
only while that primaryship is current. Once it ends, the reply is
UNCOMMITTED. This supports the existing review comment about putting the
shard epoch in REPLCONF COMMIT/ACK.

## F3. The doc's reason for "no split brain" is wrong; the conclusion holds

Section 5: "A deposed primary can't commit, because ... it can no longer
collect acknowledgements from its whole sync replica set." In the model, a
deposed primary that has not yet learned the new configuration *does* advance
its committed offset, using acks from replicas that also have not learned it.
Safety still holds because of the two ordering rules in section 4: a replica
counts toward commits before it becomes eligible, and becomes ineligible
before anything commits without it. The doc should give the ordering rules as
the reason.

## F4 (minor). Gaps the model had to fill in

- **Expiry below min-sync-replicas.** "New writes are rejected" applies to
  client writes. Expiry and eviction deletes keep piling up uncommitted.
- **Held replica reads below min-sync-replicas.** A replica can't tell the
  primary is below the minimum, so the UNCOMMITTED release in the fault table
  only applies on the primary.
- **UNCOMMITTED then commit.** A write answered UNCOMMITTED may still commit
  later, which takes effect after its response. That is not linearizable for
  that write. The doc means this ("treat it like a timeout"), but it should
  say so.

## F5. A restarted primary must rebuild its sync set from the config

**Status:** confirmed: without the fix a committed write can be lost. The
reviewers split 2/3 on calling it a doc gap when only the invariant was known
to break (see "History" below); the loss found since settles it.

The sync set the primary counts acks from lives in memory, while the doc
records eligibility in Cluster V2. Section 5, "Restarts", says only that
lease state is in memory. A primary that restarts with its data comes back
with an empty sync set and can commit without an eligible replica.

**Counterexample** (Lean `SyncReplication.noRebuild_unsafe`, 9 steps,
min-sync = 1; TLC `CoreRestart_noRebuildMin1`, 10 states, breaks the same
invariant):
1. n0 is primary. It counts n1, makes it eligible, and writes.
2. n0 restarts with its data. Its sync set is empty.
3. n2 replicates and acknowledges the write; n0 counts n2 and makes it
   eligible.
4. n0 commits with n2's ack only. n1 is eligible and authoritative but does
   not have the committed write.

**Loss** (`CoreRestart_noRebuildMin1Loss`, 22 states, nodes n1-n3): after the
restart n1 commits with only n3's ack; n2, still eligible and without the
write, takes over, resyncs n1 and commits a different write at offset 1. The
lost write was committed but not acknowledged (its held reply was dropped at
the restart). `CoreRestart_noRebuildMin1Ack` shows an acknowledged write
missing from an authoritative node.

**Proposed doc change:** a primary that restarts with its data rebuilds its
sync set from the eligible replicas in the current configuration (whose
incarnations match), discards cached acks, and commits nothing until fresh
acks arrive.

**Proof status:** with the fix, `SyncReplication.safety`, `ackSafety` and
`ackedHeld` (Lean, every min-sync, any number of nodes, unbounded restarts)
prove that every authoritative node holds the committed history and no
acknowledged write is lost, given the survival condition at every restart
without data. `commit_two_copies` shows min-sync >= 1 puts each committed
write on two authoritative nodes.

**History:** the first counterexample (`Shard_f_noRestoreMin1`, 12 states)
broke only the invariant. Within Shard's bounds (one client write) no loss was
found: `Shard_f_noRestoreMin1Loss` is clean at 5 and 6 configuration changes
(4.04M distinct states). One reviewer traced an earlier version of that
counterexample to a flaw in my model (reconciliation bypassed
min-sync-replicas); that flaw was fixed and the invariant still broke.
CoreRestart (commit 370ca9d) then found the loss above.

## Incarnation check on primaryship

**Status:** found while modelling restarts (CoreRestart). Not yet reviewed by
the panel as a separate finding; it is in the Lean write-up, which was
reviewed adversarially.

Section 6 says the takeover compare-and-set checks the incarnation, so a node
that came back empty cannot be promoted. That is not enough: the node may
already be the primary.

**Counterexample** (Lean `SyncReplication.noIncCheck_unsafe`, 9 steps,
min-sync = 1, every other fix on):
1. A write commits on n0 (primary) and n1 (eligible).
2. n0 restarts empty, with a new incarnation. n1 keeps the write.
3. n0 keeps acting as primary on its stale configuration. It counts n2, whose
   log is empty, and makes it eligible.
4. n2 is authoritative without the committed write.

TLC `CoreRestart_noIncMin1` finds the same violation with all three
incarnation checks below removed at once.

**Proposed doc change:** a node acts as primary (counts replicas, changes
eligibility, commits, releases replies) only while its own configuration
records its current incarnation.

**Scope:** the model also checked incarnations in two other places, and
each has now been settled on its own. Counting a replica into the sync set
(`Count`) needs no incarnation check: the proofs never used it, and the guard
has been removed from the Lean model. Counting toward min-sync-replicas
(`Writable`) does need it, for the two-copies property rather than for safety:
`SyncReplication.noIncWritable_oneCopy` (14 steps, min-sync = 1) has a replica
restart empty, stay listed as eligible, catch up and be counted again; the
primary then commits with it as its only sync member, and after the commit
the primary is the only authoritative node. The data is on the replica, but
the replica cannot take over. **Proposed doc change:** a sync replica counts
toward min-sync-replicas only while it is eligible with the incarnation the
configuration records for it.

## Survival condition (an assumption, not a defect)

The design accepts that committed writes are lost if every member of the sync
replica set loses its data at once (section 6, "Correlated data loss is
detected"). The proofs therefore assume that at every restart without data,
some other authoritative node keeps its data. This entry records that the
guarantee depends on it.

**Counterexample** (Lean `SyncReplication.noSurvivor_loses`, 9 steps; TLC
`CoreRestart_noSurvivorMin0`, `CoreRestart_noSurvivorMin1`): a write commits
on n0 and n1, n1 restarts empty, then n0 restarts empty. No node holds the
write, and no node is authoritative. Because no node is authoritative,
"every authoritative node holds the committed history" holds only vacuously,
so the Lean theorem states the loss directly.

**Proposed doc change:** state the durability guarantee with this condition.
The design's detection of the case (no eligible replica with a matching
incarnation, so the shard stays unavailable) is not proven.

## F6. Re-promotion after a restart: not a doc gap if demotion is atomic

**Status:** withdrawn as a doc gap. The reviewers split 2/3 the other way. The
counterexample needed the demotion CAS and "stop counting" to be two
separate steps, so that a replica could be made eligible again in between.
Section 4 demotion step 3 says the primary removes the replica "once the
change commits". With that modelled as one step, `Shard_f_noCatchUp` and
`Shard_f_noCatchUpLoss` are clean (2.09M states).
I kept a catch-up re-check at step 4 as defence in depth. Worth one line in
the doc: a replica that reconnects with a new incarnation starts again at
promotion step 1.

## F7. Forced failover to an ineligible node does not fence the old primary

**Status:** confirmed. All 3 reviewers agree, and one rated it critical.
After the review I strengthened the check: the model's committed history
only grows when an authoritative node holds the write. Now the
acknowledged-write check fails directly on a run with no lossy action
(`Shard_f_force`, 13 states, `lossy = FALSE`):
1. n1 is primary and n2 is eligible. n1 executes a write and n2 receives it.
2. The operator forces n3 (ineligible, empty) to primary.
3. n2 has not learned the change and acks n1.
4. n1 commits and replies OK.

The write is in no authoritative copy, and the loss is not operator-visible.
The doc says only that the old primary "may serve stale reads", and that
committed writes the target lacks are lost.

**Proposed doc change (revised, review round 5):** replica fencing alone
can't stop the old primary, which already holds the ack it needs, and a
fixed lease wait isn't enough because replicas that haven't learned of the
change keep renewing its lease. Both are needed: a lease gate on commits
and replies, and a two-step forced failover (first remove the old
primaryship so replicas stop acking, then install the target once the old
primary confirms or every former sync replica has learned step one and a
lease plus margin has passed). Otherwise, state that acknowledgements issued
until the old primary learns of the change may also be lost. Not
model-checked.

## F8. Leases must also stop the old primary from acknowledging writes

**Status:** 2 of 3 step 4 reviewers call it a doc gap. All agree the doc
does not imply the fix.

The lease rules in section 5 stop **reads** when a primary's lease expires.
Nothing stops the primary from advancing its committed offset or releasing
write replies. In `Leases_docAckF8two` (real timing, 2 nodes), n1 commits
after its lease expired and releases OK after n2's takeover. One reviewer
points out that this particular write is still held by n2, so nothing is
lost in that trace. The data-loss case is the step 3 trace
`Shard_f_noFence`, where a deposed primary releases OK for a write no
authoritative node holds. That trace uses the lease abstraction, not real
timing. Given the Core and CoreRestart results below, real lease timing
alone can't produce the loss without forced failover.

**Proposed doc change:** a valid primary lease is required to advance the
committed offset and to release held write replies, not only to serve
reads.

**Core result:** in Core's model (no restarts, no data loss, no forced
failover), the fix is not needed for no-loss. CoreRestart extends this to
restarts with and without data, given the F5 fix. This does not show the
fence is unneeded in the full protocol: with forced failover it matters
(F7).
In `spec/CoreAck.tla` there is no lease and no "currently primary" guard. A
deposed primary can still commit and release OK
(`CoreAck_ReachDeposedCommit`, `CoreAck_ReachDeposedAck`), yet
`SyncReplication.ackSafety` proves that no acknowledged write is lost. The F8 loss
depends on forced failover (`Shard_f_noFence`). Without forced failover,
the fix still matters for stale reads and for clients being told OK by a
node that is no longer primary.

## F9 (minor). Forced failover can bring lost writes back

`Shard_f_forceResurrect`: after a forced failover drops a committed write,
a second forced failover back to the old primary commits that write again.
The abstract contract says lost writes never reappear. The doc should say
which of these it intends. Both are operator actions.

## F10. REPLCONF COMMIT must renew the read lease only of sync replicas

**Status:** all 3 step 4 reviewers agree it is a doc gap.

Section 5 renews a replica's read lease when the primary's REPLCONF COMMIT
echoes the replica's ack. It never says the echo stops when the replica is
demoted. Counterexample `Leases_noEchoSync` (PrimDur=5, ReadDur=2,
Margin=2, Drift=1): the primary demotes n2 after waiting out its read lease,
as the doc requires (state 3). n2, still connected, sends a new ACK
(states 5-6); the primary's next COMMIT echoes it (state 7); the primary
commits a write n2 lacks (state 9); the COMMIT arrives and renews n2's read
lease (state 10).
(Earlier text said the COMMIT was already in flight; the trace shows it is
sent after the demotion.) The primary commits a write n2 lacks, and n2 serves a linearizable
read of the old value.

**Proposed doc change:** REPLCONF COMMIT renews a read lease only for
replicas in the sync set when it is sent. A COMMIT in flight after the
demotion is harmless, because the lease runs from the echoed ACK's send
time, which the demotion wait covers. (Round 4 review: the earlier text
"clear the lease in the same step" can't be done remotely and isn't
needed.)

**Not modelled (round 4):** Leases.tla makes the read-lease wait and the
demotion CAS one step. In the design the CAS takes time, the replica stays
in the sync set until it commits, and a slow but live replica's acks keep
renewing its lease. Proposed: stop echoing a replica's acks when its
demotion starts, keep counting them, and wait out the lease from the last
echoed ack before proposing the CAS. Not yet model-checked.

## F11. The doc's drift-margin wording is unsafe if read literally

**Status:** raised independently by all 3 step 4 reviewers.

Section 5, "Timing", says both sides "use monotonic clocks and subtract a
clock-drift margin". If the holder and the grantor subtract the same
margin, the margins cancel. With opposite clock errors, the holder can still
believe its lease is valid after the grantor considers its promise over: an
overlap of up to 2 × drift. The model uses the safe reading: the holder
expires at `Dur - Margin`, the grantor waits the full `Dur`, and
`Margin >= 2 * Drift`.

**Proposed doc change:** state this asymmetry explicitly.

**Proven in Lean** (`lean/Lease/`, for every duration, drift and message
delay, in both the additive and the rate-bounded clock model):
- `asym_safe`: with the asymmetric rule, `Margin >= 2 * Drift` rules out
  any overlap.
- `asym_tight`: below that bound an overlap exists.
- `asym_safe_iff`: the two together: safe exactly when `Margin >= 2 * Drift`,
  apart from the degenerate case where the margin is the whole lease.
- `literal_unsafe`: the literal reading (both sides subtract the margin) is
  unsafe for every margin shorter than the lease once drift is positive.

## F12. The "Lease durations" rule leaves out the round trip and needs 2 × drift

**Status:** proven in Lean (`lean/Lease/Durations.lean`). Reviewed with the
Lean write-up, which corrected an earlier claim: `demotion_in_time` gives a
sufficient condition, not an exact one.

Section 5, "Lease durations", says: read lease + time to commit a demotion
to the cluster bus + drift margin < primary lease. The aim is that a failed
sync replica is demoted before the primary's own lease from that replica
expires, so the primary keeps serving reads. Two terms are missing:
- the round trip between the last acknowledgement and the primary's view of
  it;
- a second drift term. Round 4 review corrected the explanation: the
  primary times two intervals on its own clock (the demotion wait from the
  ACK's arrival, and its lease from the data's send), and in the additive
  model each can be off by the drift. The margin already covers the
  cross-node difference.

`doc_condition_insufficient_rtt` and `doc_condition_insufficient_drift`
give counterexamples. With bus delay ≤ B and round trip ≤ Δ,
`demotion_in_time` proves that
ReadDur + B + Δ + Margin + 2·Drift < PrimDur is enough, with Δ the time
from sending data to receiving its ACK and B everything from the end of the
wait to the demotion committing (timers, scheduling, Raft). This is the
additive clock model only; a rate-bounded version is not derived. A
condition with one drift term also fails, so both are needed (witness from
review round 5: D=2, M=4, ReadDur=2, B=1, Δ=0, PrimDur=10; not yet a Lean
example).

This is an availability issue, not a safety one: if the condition fails,
the primary stops serving reads until the demotion commits, as the doc
already describes.



## Step 4: which lease rules are shown to be needed (corrected)

My first report said removing any of six lease rules gives a stale read.
The review showed that is only half supported:
- **Shown:** takeover waits for the primary lease (`noWaitPrim`). Demotion
  waits for the read lease (`noWaitRead`). The drift margin covers both
  clocks (`smallMargin`); this is a condition of the clock model, see F11.
- **Not shown:** `noWaitOld`, `noStopGrant` and `noReset`. Their first
  traces never took the disabled action (they were the F10 echo bug). Rerun
  with F10 fixed: no stale read found in one hour for `noWaitOld` and
  `noStopGrant`, and in 10 minutes for `noReset` (its one-hour run was
  interrupted). Either these rules
  are redundant given the others, or the bounds are too small to need them.
- **Config error:** I later shrank the safe configs to PrimDur=4, ReadDur=1.
  With Margin=2 and Drift=1, a read lease is then never valid, so those runs
  could not see a stale replica read. The generator is back at PrimDur=5,
  ReadDur=2.
- Capping timestamp ages in the model (`VIEW`) is sound (2 reviewers
  checked it).

## Model limits so far

- Step 4: no safe lease run has finished, and the ones offered as evidence
  used configs where replica read leases were never valid (see above).
  They show nothing about replica reads. Not modelled: Cluster V2 commit
  delay during demotion (the doc's "read lease + bus commit + drift <
  primary lease"), restarts waiting one lease, and epoch/incarnation on
  lease traffic. The safe runs `Leases_safe`, `Leases_safe2` and
  `Leases_safe2T7` (PrimDur=5, ReadDur=2) were stopped unfinished on
  4 November when the host disk filled (`Leases_safe2` at 185M distinct
  states) and have not been rerun.
- Step 3: MaxOps = 1 (complete). The MaxOps = 2 run never ran (its config
  was deleted when the configs were regenerated). Config
  learning after a restart is instant, and ACKs carry no epoch or
  incarnation.
- No REPLCONF COMMIT in step 2. Replica committed views are always 0, which is
  what produces F1.
- Bounds are small: 1 key, 2 writes, 3 nodes. Step 2 with 7 config changes
  is clean (251.9M distinct states).
