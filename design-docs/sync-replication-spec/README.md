# Valkey sync replication: formal spec

Formal models of the proposed design in
[Valkey Durability: Synchronous Replication Architecture](https://docs.google.com/document/d/15-VWM9KR2dfG4Y05RVF3tOnaVoYgKhmiFQ8jJZtxirg/edit?tab=t.0#heading=h.2sacx7to1xu)
(also proposed as `design-docs/sync-replication.md` in
[valkey#5286](https://github.com/valkey-io/valkey/pull/5286)).

**Findings on the doc: see [FINDINGS.md](FINDINGS.md).**


## Method

For each step:
1. Write the model.
2. Run TLC on the safe configuration, on bug variants (each must fail), on
   reachability checks (each must fail, which proves the clean result is
   not vacuous), and on refinement to the step 0 contract.
3. Independent adversarial review of the model and its claims.
4. Fix the BLOCKER and MAJOR findings, rerun, then move on.

Steps 0-4 are bounded model checking. Step 6 adds unbounded Lean proofs of
the core protocol, cross-checked against TLC. The Lean proof now lives on the
[`sync-repl-lean`](https://github.com/jjuleslasarte/valkey/tree/sync-repl-lean/design-docs/sync-replication-spec) branch; the older Lean snapshot that was here has been removed.

## Results at a glance

With the proposed fixes for F1 (reconcile against the inherited log), F2
(fence held replies by primaryship) and F5 (a restarted primary rebuilds its
sync set), Lean proves, for any number of nodes, log length, configuration
changes and restarts, and every min-sync-replicas value:
- no acknowledged write is lost;
- every authoritative node (the primary and each eligible replica, with its
  recorded incarnation) holds every committed and acknowledged write;
- with min-sync-replicas >= 1, every committed write is on at least two
  authoritative nodes.

The one assumption is the design's survival condition: whenever a node
restarts without its data, another authoritative node keeps its data.
Removing any of the fixes, or the incarnation check, gives a TLC
counterexample. The lease timing rules (F11, F12) are proven separately.

Not covered: forced failover (F7), the delay while a demotion's
compare-and-set commits (F10 follow-up), and a rate-bounded version of the
F12 formula. Details in [FINDINGS.md](FINDINGS.md).

## Steps

| Step | Model | Status |
|---|---|---|
| 0 | `spec/DurableShard.tla`: client contract | rev 3 after review 1; clean |
| 1 | `spec/SyncCommit.tla`: commit rule, reply blocking, dirty keys, SETNX, DBSIZE, AOF (Milestone II) | rev 2 after review 1; clean |
| 2–3 | `spec/Shard.tla`: sync set via Cluster V2 CAS, takeover, reconciliation; crash/restart, incarnations, REPLCONF COMMIT, forced failover, correlated loss | merged in iteration 2; clean; F1, F2, F3, F5, F7, F8, F9 |
| 4 | `spec/Leases.tla`: real time, drift, delay/loss, both leases, demotion, takeover | reviewed; refines the contract since iteration 2; F10, F11; F8 2/3; safe not exhaustive |
| 5 | Compose and refine | not started |
| 6 | `spec/Core.tla` + Apalache (`spec/CoreInd.tla`) + Lean: unbounded proofs of the core invariant and of the lease timing conditions; TLC-Lean cross-checks (Core and CoreAck) | done, see [COMPARISON.md](COMPARISON.md); F11 proven, F12 new |
| 6a | `spec/CoreAck.tla` + Lean: client replies; no acknowledged write is lost with the F1 and F2 fixes (min-sync = 0, strict reconciliation) | proven; F8 fence not needed outside forced failover |
| 6b | `spec/CoreRecon.tla` + Lean: the F1 fix as proposed (inherited-log catch-up), every min-sync value | proven; strict rule deadlocks at min-sync >= 1 (TLC) |
| 6c | `spec/CoreRestart.tla` + Lean: restarts with and without data, incarnations, the F5 fix, every min-sync value | proven; without F5 a committed write is lost (TLC, 22 states) |

Cluster V2 (Raft) is a linearizable CAS register over a configuration log.
Raft itself is out of scope.

## Step 0: DurableShard (rev 3)

- One committed history, `log`, that only grows except through an
  explicit lossy action.
- **Writes:** W (SET; DEL is a write of Nil) and C (SETNX, whose reply
  depends on state).
- **Reads:** R and K (GET and DBSIZE, linearizable), plus S and KS
  (serializable). A read observes a committed prefix between `lo` and now.
  For linearizable reads, `lo` = the log length at invocation. For
  serializable reads, `lo` = the reader's cursor, so one endpoint never goes
  backwards.
- **Outcomes:** OK only for writes that have committed. CLUSTERDOWN means the
  write never takes effect. UNCOMMITTED means the outcome is unknown.
- **Data loss:** only through `LossyTruncate`.

| Config | Expected | Result |
|---|---|---|
| `safe` (2 keys, 2 values, MaxOps=3) | holds | 8.14M distinct |
| `lossy` | durability violated | violated |
| 8 reachability checks | each violated | all violated |

## Step 1: SyncCommit (rev 2)

The abstract log is `plog[1..commit]`. Each feature group gets its own
safe config (`EnabledKinds`).

Distinct-state counts are after iteration 1 (replica symmetry). The
pre-symmetry count is in brackets.

| Config | Expected | Result |
|---|---|---|
| `safe` (W, R, S) | refinement holds | 49.7M (98.2M) |
| `safeSetNX` | refinement holds | 117.2M (230.6M) |
| `safeDbSize` | refinement holds | 49.7M. With one key DBSIZE is isomorphic to GET, so this adds nothing; see `safeDbSize2` |
| `safeDbSize2` (2 keys) | refinement holds | large tier, new |
| `min0` | refinement holds | 30.8M (60.8M) |
| `aof` | refinement holds | did not finish (87.5M, 2 h limit) |
| `live` (`HealthySpec`) | every op answered; accepted writes get OK | holds |
| `liveNeg` | "no write ever OK" fails | fails |
| `nodirty`, `nodirtySetNX`, `nodirtyDbSize`, `nodirtyDbSize2` | refinement fails | all fail |
| `nonatomic` | `SyncHoldsCommitted` fails | fails |
| 11 reachability checks | each violated | all violated |

## Steps 2 and 3: Shard

Since iteration 2, steps 2 and 3 are one parameterised module,
`spec/Shard.tla`. Before that, Membership and Failover were copies that had
drifted apart: the step 3 review fixes never reached step 2.

- `Shard_m_*` is the step 2 scope: 3 nodes, 2 writes, 5 config changes,
  1 crash, no restarts, no forced failover. It also runs without the
  step 3 defences (catch-up re-check, lease fence).
- `Shard_f_*` is the step 3 scope: 1 write, restarts, incarnations, forced
  failover, correlated loss.

The abstract log is the ghost committed history `clog`. It grows only when
an authoritative node (named by the current config, with a matching
incarnation) holds the new entry. A consequence: a lost write becomes
client-visible only when a later conflicting write is acknowledged, so the
`*Loss` configs need enough config changes for that to happen.

Bug switches and ghost variables are listed in `spec/SWITCHES.md`.

| Config | Expected | Result |
|---|---|---|
| `Shard_m_safe` | refinement, `AckedDurable`, `EligibleHoldsCommitted`, `CommittedAgree` | 24.2M distinct (reported; log not kept) |
| `Shard_m_safeMin0` | same | 46.1M distinct (reported; log not kept) |
| `Shard_m_safeCfg7` (7 config changes) | same | no violation; interrupted at 326.6M distinct |
| `Shard_f_safe` | plus `UnavailableWithoutAuthority` | 1.04M distinct |
| `Shard_f_safeMin0` | same | 1.34M distinct |
| `Shard_m_docAsWrittenLossFenced` | acknowledged write lost (F1), 6 config changes | lost, 25 states |
| `Shard_m_noStepDown` | false OK (F2) | 18 states |
| `Shard_m_nonatomicLoss`, `earlydropLoss`, `eligfirstLoss` | acknowledged write lost | all lose one (`nonatomicLoss` needs 6 config changes) |
| `Shard_f_force` | lost acknowledged write, no lossy action (F7) | 13 steps |
| `Shard_f_noFence` | lost acknowledged write without lease fence (F8) | 21 steps |
| `Shard_f_noRestore`, `noRestoreMin1` | core invariant breaks (F5) | breaks |
| `Shard_f_noRestoreMin1Loss` | client-visible loss? | none, at 5 and at 6 config changes |
| `Shard_f_noCatchUp`, `noCatchUpLoss` | F6 | clean (F6 withdrawn) |
| `Shard_f_noIncHolds` | core invariant breaks without incarnation check | breaks |
| `Shard_f_forceResurrect` | refinement (no resurrection) | fails (F9) |
| 13 reachability checks | each violated | all violated |

## Step 4: Leases

Since iteration 2, Leases has client read operations and refines the client
contract, like every other step, in addition to `NoStaleLinRead`.

| Config | Expected | Result |
|---|---|---|
| `noWaitPrim`, `noWaitRead`, `noEchoSync` (F10), `smallMargin` (F11) | stale read; each also violates refinement (`*Ref`) | all violated |
| `docAckF8two` | OK after takeover (F8) | violated |
| `noWaitOld`, `noStopGrant`, `noReset` | ? | no violation (with F10 fixed): 1 h, 1 h, 10 min |
| `safe2` (2 nodes, 2 ops) | refinement + `NoStaleLinRead` | no violation; did not finish (113.4M distinct, depth 20, 40 min) |
| `ReachReplReadOp` | reachable | violated (large tier) |

## Running

- `spec/regress.sh [ci|large|all]` runs every config of a tier and compares
  each outcome with `spec/expected.tsv`.
  - `COVERAGE=1` also fails a passing config if the set of actions that never
    fire differs from its row in `spec/coverage.tsv`, which records the
    reason each listed action is off.
  - The run stops if free disk drops below `MINFREE_GB`, and TLC state
    directories are always deleted.
- Each module has its own generator: `spec/gen_ds_cfgs.sh`,
  `gen_sc_cfgs.sh`, `gen_shard_cfgs.sh` and `gen_ls_cfgs.sh`. Every
  committed config can be regenerated.
- TLA+ tools 1.8.0 are not committed. Download the jar into `tools/`:
  `curl -L -o tools/tla2tools.jar https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar`.
  `tools/apalache.sh` runs Apalache 0.62.4 in a container (unpack it into
  `tools/apalache-0.62.4/` first).
