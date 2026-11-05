# Bug switches and ghost variables

## Bug switches

Each switch is a boolean `CONSTANT`. The **safe** value is the protocol as
we believe it must be (the design doc plus the fixes in `../FINDINGS.md`).
The **bug** value removes one rule. Every bug value has at least one config
in `expected.tsv` whose expected outcome is a violation. That config is the
regression test showing the rule is needed. "Doc" in the third column means
the rule is in the design doc. "Fix" means the doc does not have it yet.

### SyncCommit.tla (step 1)

| Switch | Safe | Rule | Doc / fix | Must-fail configs |
|---|---|---|---|---|
| `TrackDirty` | TRUE | Reads and SETNX-0 wait for dirty keys; DBSIZE waits for the applied offset | Doc §1 | `nodirty`, `nodirtySetNX`, `nodirtyDbSize`, `nodirtyDbSize2` |
| `AtomicPromote` | TRUE | Catch-up check and "count its acks" in one step | Doc §4 step 1–2 | `nonatomic` (invariant only; client-invisible without failover) |
| `AOF` | – | AOF fsync offset as a commit source (feature, not a bug switch) | Doc §2 | – |

### Shard.tla (steps 2–3)

| Switch | Safe | Rule | Doc / fix | Must-fail configs |
|---|---|---|---|---|
| `AtomicPromote` | TRUE | as above | Doc §4 | `Shard_m_nonatomic`, `Shard_m_nonatomicLoss` |
| `EarlyDrop` | FALSE | Do not stop counting a replica before the ineligible CAS commits (ordering rule O2) | Doc §4 | `Shard_m_earlydrop`, `Shard_m_earlydropLoss` |
| `EligibleFirst` | FALSE | Count a replica before it becomes eligible (ordering rule O1) | Doc §4 | `Shard_m_eligfirst`, `Shard_m_eligfirstLoss` |
| `ReconcileFirst` | TRUE | After takeover, catch-up and resync are measured against the inherited log | **Fix F1** | `Shard_m_docAsWritten`, `Shard_m_docAsWrittenLoss`, `Shard_m_docAsWrittenLossFenced` |
| `StepDownRelease` | TRUE | Held replies are fenced by the primaryship term | **Fix F2** | `Shard_m_noStepDown` |
| `IncCheck` | TRUE | Config and takeover check incarnations | Doc §6 | `Shard_f_noIncHolds` |
| `RestoreSync` | TRUE | A restarted primary rebuilds its sync set from the config | **Fix F5** | `Shard_f_noRestore`, `Shard_f_noRestoreMin1` (invariant only; no client-visible loss found up to MaxCfg = 6) |
| `CatchUpAtEligible` | TRUE | Promotion step 4 re-checks catch-up (defence in depth) | F6, withdrawn | none; `Shard_f_noCatchUp*` pass |
| `LeaseFence` | TRUE | Only the current primary commits and releases replies (abstraction of step 4) | **Fix F8** | `Shard_f_noFence` |
| `AllowForce` | – | Enables operator forced failover (feature) | Doc §5 | `Shard_f_force`, `Shard_f_forceLoss` (F7), `Shard_f_forceResurrect` (F9) |

`Shard_m_*` configs run with `MaxRestarts = 0`, `AllowForce = FALSE`,
`CatchUpAtEligible = FALSE` and `LeaseFence = FALSE`. That is the step 2
scope, without the step 3 defences, so their safe runs are the stronger
check.

### Leases.tla (step 4)

| Switch | Safe | Rule | Doc / fix | Must-fail configs |
|---|---|---|---|---|
| `WaitPrimLease` | TRUE | Takeover waits until the old primary's lease expired | Doc §5 | `noWaitPrim`, `noWaitPrimRef` |
| `WaitReadLease` | TRUE | Demotion waits until the replica's read lease expired | Doc §5 | `noWaitRead`, `noWaitReadRef` |
| `EchoOnlySync` | TRUE | REPLCONF COMMIT renews read leases only for sync replicas | **Fix F10** | `noEchoSync`, `noEchoSyncRef` |
| `Margin` vs `Drift` | Margin ≥ 2·Drift | Holder expires at Dur − Margin, grantor waits full Dur | **Fix F11** | `smallMargin`, `smallMarginRef` |
| `WaitOldLeases` | TRUE | A new primary waits out old read leases | Doc §5 | **not shown**: `noWaitOld` has no violation in 1 h |
| `StopGrant` | TRUE | A deposed primary stops granting read leases | Doc §5 | **not shown**: `noStopGrant` has no violation in 1 h |
| `ResetOnLearn` | TRUE | Takeover timers restart on a config change | Doc §5 | **not shown**: `noReset` has no violation in 10 min (liveness only?) |
| `StopAckOnExpiry` | TRUE | Commits and write replies stop at lease expiry | **Fix F8** | `docAckF8two` (an OK after takeover; no lost write with real timing) |

"Not shown" means TLC found no stale read with that rule removed, within
the bounds and time limit. Either the rule is redundant given the others,
or the bounds are too small to need it. That is still open.

## Ghost variables

Ghost variables exist only to state properties or the refinement mapping.
A ghost is safe if no real action's guard reads it. Then removing it
changes no reachable behaviour of the real protocol. The table records
where each ghost is read.

| Module | Ghost | Meaning | Read by real guards? |
|---|---|---|---|
| SyncCommit | `meta[id].held` | The reply was held when it executed | No; reachability only |
| Shard | `clog` | Committed history: grows only when an authoritative node holds the new entry | No; refinement and invariants |
| Shard | `everC` | Ids ever committed | No; refinement (`everIn`) |
| Shard | `lossy` | An explicit lossy event (forced failover, correlated loss) happened | No; `AckedDurable` is conditional on it |
| Shard | `unfenced` | Primaries deposed by a forced failover, so not lease-fenced | **Yes**: `Fenced(p)` reads it. This is deliberate: it is the abstraction of "forced failover does not wait for the old lease". It is not a pure ghost. |
| Shard | `clog` in `ForceTakeover` | Common prefix of the history and the target's log | Was **yes** until iteration 2: the forced target's commit offset was set from it, which a real node cannot know. Now the target starts from its own `rcommit` (capped by that prefix); `clog` only drives the ghost bookkeeping. F7/F9 configs unchanged. |
| Shard | `commitG` (old Membership) | removed in the merge; replaced by `clog` | – |
| Leases | `clog` | Committed history | No; refinement and invariants |
| Leases | `olo`, `rat`, `rseen`, `rnode` | Read-operation bookkeeping for the refinement mapping | `rnode` is read by `ReadEffect` (which node serves the read); the rest is ghost |
