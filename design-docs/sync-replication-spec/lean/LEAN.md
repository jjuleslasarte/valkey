# The Lean proofs: reference

The companion to [`../README.md`](../README.md), which states the guarantee, the
model and the method in design terms. This file is the reference for the code: the
theorem statements as Lean prints them, the encoding of the design, how the proof is
laid out, the conventions it follows, and how to rebuild and check it. The
counterexamples are in the appendix.

## Layout

```
lean/
  SyncReplication.lean          root import
  SyncReplication/
    Model.lean                  state, actions, Step, lts, Reachable, the safety properties
    Replies.lean                held client replies: AState, AStep, AckedDurable, AckedHeld
    Leases.lean                 the lease layer: LeaseState, LeaseStep, the read rule, NoStaleRead
    Invariant.lean              the inductive invariant in five layers; the fence; frame lemmas
    Contracts.lean              each action's effect in design terms, proved without the invariant
    Preserve.lean               dispatch: every Step preserves Invariant
    Preserve/                   Replication, Commit, Config, Failover, Restart
    Safety.lean                 safety, commit_two_copies
    Durability.lean             ReplyInvariant; ackSafety, ackedHeld
    LeaseInvariant.lean         LeaseInvariant and its preservation; noStaleRead, lease_safety
    Counterexamples/            Basic, Reconcile, ReplyFence, Rebuild, Uncount, Incarnation,
                                MinSyncIncarnation, Survival, StaleRestore, Leases
    Lists.lean                  list-prefix lemmas
  Lease/                        Additive, Rate, Durations
  Check.lean                    #print axioms for every theorem
  LeaseCheck.lean               the same for Lease/
```

Dependency order: `Lists` → `Model` → `Replies`, `Invariant` → `Contracts` →
`Preserve/*` → `Preserve` → `Safety` → `Durability`, `Leases` → `LeaseInvariant` →
`Counterexamples/*`.

## Theorems

### Log safety (`Safety.lean`)

```lean
theorem safety {m : Nat} {i : Node} {s : State Node} (h : Reachable m i s) : Safety s

theorem commit_two_copies {m : Nat} (hm : 1 ≤ m) {i : Node} {s : State Node}
    (h : Reachable m i s) {p : Node} (hp : ThinksPrimary s p) (hpp : p = s.cfg.primary)
    (hw : Writable m s p) (hlen : s.commit p < (s.log p).length)
    (hcap : ∀ r, s.sync p r = true → s.commit p < s.acked p r) :
    ∃ e, e ≠ p ∧ IsAuthoritative (commitNext s p) e ∧ IsAuthoritative (commitNext s p) p ∧
      (commitNext s p).hist <+: (commitNext s p).log e ∧ (commitNext s p).hist <+: (commitNext s p).log p
```

`m` is `min-sync-replicas`, universally quantified. `Node` is any type with decidable
equality, so any number of nodes; logs, configuration versions, incarnations and
restarts are unbounded. `Safety` is `EligibleHoldsCommitted ∧ CommittedAgree`:

```lean
IsAuthoritative s n       :=  (s.cfg.eligible n = true ∨ n = s.cfg.primary) ∧ s.cfg.incarnation n = s.incarnation n
EligibleHoldsCommitted s  :=  ∀ n, IsAuthoritative s n → s.hist <+: s.log n
CommittedAgree s          :=  ∀ p, s.commit p ≤ (s.log p).length ∧
                                   (s.log p).take (s.commit p) = s.hist.take (s.commit p)
```

`commit_two_copies` says what `min-sync-replicas ≥ 1` adds: a commit by the current
primary needs an eligible sync member whose recorded incarnation matches (`Writable`
counts only those), so right after the commit the history is on at least two distinct
authoritative nodes, the primary and that replica. With `m = 0` the primary may
commit on an empty sync replica set and the history may rest on the primary alone;
the survival guard then forbids the primary restarting empty, since no other node is
authoritative (README §2).

### No acknowledged write is lost (`Durability.lean`)

```lean
theorem ackSafety {i : Node} {a : AState Node} {m : Nat} (h : AReachable m i a) :
    AckedDurable a ∧ Safety a.core

theorem ackedHeld {i : Node} {a : AState Node} {m : Nat} (h : AReachable m i a) : AckedHeld a
```

```lean
AckedDurable a  :=  ∀ x ∈ a.okd, 1 ≤ x.1 ∧ x.1 ≤ a.core.hist.length ∧ a.core.hist.getD (x.1 - 1) 0 = x.2
AckedHeld a     :=  ∀ x ∈ a.okd, ∀ n, IsAuthoritative a.core n →
                      x.1 ≤ (a.core.log n).length ∧ (a.core.log n).getD (x.1 - 1) 0 = x.2
```

`okd` is the list of `(offset, value)` pairs released to clients as OK. `hist` only
grows, so an acknowledged write stays in the committed history.

### No stale linearizable read (`LeaseInvariant.lean`)

```lean
theorem noStaleRead {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {m : Nat} {i : Node}
    {a : LeaseState Node} (h : LeaseReachable m P i a) : NoStaleRead P a

theorem lease_safety {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {m : Nat} {i : Node}
    {a : LeaseState Node} (h : LeaseReachable m P i a) : Safety a.core
```

```lean
HolderValid P now start dur  :=  start = some t0 ∧ now + P.margin < t0 + dur + P.drift   (false for none)
GrantorOver P now recv dur   :=  recv = some t0 → t0 + dur ≤ now + P.drift
PrimLeaseValid P a p  :=  ∀ r, (a.core.known p).eligible r = true → r ≠ p →
                            HolderValid P a.now (a.primaryLease p r) P.primDur
ReadLeaseValid P a r  :=  HolderValid P a.now (a.readLease r) P.readDur
PrimCanRead P a p     :=  ThinksPrimary a.core p ∧ PrimLeaseValid P a p ∧ a.core.commit p = (a.core.log p).length
ReplCanRead P a r     :=  ¬ ThinksPrimary a.core r ∧ ReadLeaseValid P a r ∧ a.committedView r = (a.core.log r).length
NoStaleRead P a       :=  (∀ p, PrimCanRead P a p → a.core.log p = a.core.hist) ∧
                          (∀ r, ReplCanRead P a r → a.core.log r = a.core.hist)
```

`P` holds the two durations, the drift bound and the margin. The hypothesis
`2 * drift ≤ margin` is the design's "the doc's argument needs Margin ≥ 2 · Drift";
`smallMargin_stale` shows it cannot be dropped.

### Counterexamples (`Counterexamples/`)

Each states a reachable state of a *weakened* protocol (the model's `Step` plus one
action with a rule removed) that violates the guarantee; see the appendix.

```lean
theorem noReconcile_unsafe        : ∃ s, (ltsNoReconcile 1).CanReach (init 0) s ∧ ¬ Safety s
theorem noReplyFence_unsafe       : ∃ a, (altsNoFence 0).CanReach (ainit 0) a ∧ ¬ AckedDurable a
theorem noRebuild_unsafe          : ∃ s, (ltsNoRebuild 1).CanReach (init 0) s ∧ ¬ Safety s
theorem noIncCheck_unsafe         : ∃ s, (ltsNoInc 1).CanReach (init 0) s ∧ ¬ Safety s
theorem staleRestoreKeepsInc_unsafe : ∃ s, (ltsStaleKeep 1).CanReach (init 0) s ∧ ¬ Safety s
theorem staleRestoreKeepsInc_loses  : ∃ s, (ltsStaleKeep 1).CanReach (init 0) s ∧
    s.hist ≠ [] ∧ ∀ n, ¬ s.hist <+: s.log n
theorem noSurvivor_loses          : ∃ s, (ltsNoSurv 1).CanReach (init 0) s ∧
    s.hist ≠ [] ∧ (∀ n, ¬ s.hist <+: s.log n) ∧ (∀ n, ¬ IsAuthoritative s n)
theorem uncountElig_unsafe        : ∃ s, (ltsUncountElig 1).CanReach (init 0) s ∧ ¬ Safety s
theorem noWaitPrim_stale  : ∃ a, (leaseLTSNoWaitPrim 0 P0).CanReach (leaseInit 0) a ∧ PrimCanRead P0 a 0 ∧ a.core.log 0 ≠ a.core.hist
theorem noWaitRead_stale  : ∃ a, (leaseLTSNoWaitRead 0 P0).CanReach (leaseInit 0) a ∧ ReplCanRead P0 a 1 ∧ a.core.log 1 ≠ a.core.hist
theorem grantAny_stale    : ∃ a, (leaseLTSGrantAny 0 P0).CanReach (leaseInit 0) a ∧ ReplCanRead P0 a 2 ∧ a.core.log 2 ≠ a.core.hist
theorem grantSync_stale   : ∃ a, (leaseLTSGrantSync 0 P0).CanReach (leaseInit 0) a ∧ ReplCanRead P0 a 2 ∧ a.core.log 2 ≠ a.core.hist
theorem grantNoInc_stale  : ∃ a, (leaseLTSGrantNoInc 0 P3).CanReach (leaseInit 0) a ∧ ReplCanRead P3 a 1 ∧ a.core.log 1 ≠ a.core.hist
theorem smallMargin_stale : ∃ a, LeaseReachable 0 P1 0 a ∧ PrimCanRead P1 a 0 ∧ a.core.log 0 ≠ a.core.hist
theorem noIncWritable_oneCopy     : ∃ s, (ltsNoIncWritable 1).CanReach (init 0) s ∧
    ThinksPrimary s 0 ∧ 0 = s.cfg.primary ∧ WritableNoInc 1 s 0 ∧ s.commit 0 < (s.log 0).length ∧
    (∀ r, s.sync 0 r = true → s.commit 0 < s.acked 0 r) ∧
    ∀ e, e ≠ 0 → ¬ IsAuthoritative (commitNext s 0) e
```

The last one mirrors `commit_two_copies` with `Writable` replaced by `WritableNoInc`
(no incarnation condition): its hypotheses hold and its conclusion fails.

### Lease timing (`Lease/`)

See "Lease timing" below.

## Encoding

### State (`Model.lean`)

| Field | Type | Meaning |
|---|---|---|
| `log` | `Node → List Nat` | Each node's replication log. An entry is the term of the primary that wrote it, so a write is identified by its offset and term. 0-indexed; the design's offset `o` is index `o - 1`. |
| `incarnation` | `Node → Nat` | Each node's incarnation. A restart without data increments it. |
| `cfg` | `Cfg Node` | The latest Cluster V2 configuration: `version`, `primary`, `eligible : Node → Bool`, `incarnation : Node → Nat` (the incarnation recorded for each node). |
| `known` | `Node → Cfg Node` | The configuration each node last learned; possibly stale. |
| `sync` | `Node → Node → Bool` | `sync p r`: `r` is in `p`'s sync replica set. |
| `acked` | `Node → Node → Nat` | `acked p r`: how far `p` believes `r` has acknowledged. |
| `commit` | `Node → Nat` | Each node's committed offset. |
| `recon` | `Node → Nat` | Each node's catch-up point: a new primary must commit up to here before it serves. |
| `term` | `Node → Nat` | The term each node writes new entries with. |
| `ackHigh` | `Node → Nat` | Each node's acknowledgement high-water mark: the highest offset it has acknowledged as a replica (Ack) or as a primary (Commit). Survives a restart with data. |
| `hist` | `List Nat` | Ghost: the committed history, extended the first time any node commits an offset. |

Sets of nodes are `Node → Bool`. `update f a b` is `f` with the value at `a` replaced by
`b`. Messages are not modelled: a delayed message is the same step taken later and a
lost one is the step never taken, so acknowledgements carry the replica's offset at
delivery (README §1 and §5). Restarts with data, without data and from a stale
persistence file are actions; correlated loss of every copy is excluded by the
survival guard on the restarts that take a new incarnation (README §2). `init i` has `i` primary at version 1, no eligible replica, every incarnation 1,
empty logs.

Derived predicates: `ThinksPrimary s p` (`known[p]` names `p` primary with its current
incarnation), `KnowsLatest s n` (`known[n].version = cfg.version`), `primaryOf s n`
(`known[n].primary`), `Reconciled s p` (`recon p ≤ commit p`), `IsAuthoritative`,
`PrimaryAuthoritative s` (the current primary's incarnation matches),
`catchUpPoint s p` (`commit p` once reconciled, else `min (recon p) (log p).length`),
`Writable m s p` (`m ≤` the number of sync members of `p` that are eligible with a
matching incarnation in `known[p]`, as `Set.encard`).

### Actions

Each action is a function `State → State` using structure update, so fields it does
not mention are unchanged. Its guard is the corresponding `Step` constructor, which
also carries the action's label (`Action`). `Step m s μ s'` reads: with
`min-sync-replicas = m`, action `μ` takes `s` to `s'`.

| Action | Guard | Effect |
|---|---|---|
| `append p` | `p` thinks it is primary, is writable and reconciled | appends `term p` to `log p` |
| `replicate r` | `r` does not consider itself primary; its log is a strict prefix of its primary's | copies the next entry |
| `ack r` | `r` does not consider itself primary; its log is a prefix of its primary's and longer than its recorded ack | primary records `acked p r := (log r).length`; `ackHigh r` raised to it |
| `commit p` | `p` thinks it is primary, is writable, has an uncommitted entry, and every sync member has acknowledged past `commit p` | `commit p + 1`; `hist` extended if this offset is new; `ackHigh p` raised to the new commit point |
| `count p r` | `p` thinks it is primary; `r ≠ p` follows `p`, is not counted, and has acknowledged `catchUpPoint s p` | `sync p r := true` |
| `uncount p r` | `p` thinks it is primary and knows the latest configuration; `r` is counted and not eligible in `cfg` | `sync p r := false` |
| `makeEligible p r` | `p` thinks it is primary, knows the latest configuration, counts `r`; `r` not eligible | new version with `r` eligible and `inc r` recorded; `known p` updated |
| `makeIneligible p r` | `p` thinks it is primary, knows the latest configuration; `r` eligible | new version with `r` ineligible; `known p` updated; `sync p r := false` |
| `learn n` | `n` does not know the latest configuration | `known n := cfg`; `sync n` emptied unless `n` is primary there |
| `takeover n` | `n` knows the latest configuration, is eligible, is not the primary, and `cfg.incarnation n = inc n` | new version with `n` primary and the old primary dropped from the eligible set; `sync n` := the matching eligible replicas; `acked n`, `commit n` reset; `recon n := (log n).length`; `term n := cfg.version + 1` |
| `resync r` | `r` does not consider itself primary; its log is not a prefix of its primary's; `r` is neither counted nor eligible in its primary's configuration | `log r := (log p).take (catchUpPoint s p)`; `acked p r := 0`; `commit r` capped |
| `restartEmpty n` | `n` knows the latest configuration; some other node is authoritative | `log n := []`, `incarnation n + 1`, volatile state and `ackHigh n` reset; the current primary drops `n` from its sync set and acks |
| `restartKeep n` | `n` knows the latest configuration | `commit n := 0`, `acked n` reset, `recon n := (log n).length`; if `n` thinks it is primary, `sync n := rebuiltSync s n` (the matching eligible replicas in `known n`), else emptied |
| `restartPartial n k`, keeping the incarnation | as `restartKeep`, with `k < (log n).length` and `ackHigh n ≤ k` | `restartKeep` on `(log n).take k`, with `recon n := k` |
| `restartPartial n k`, new incarnation | `n` knows the latest configuration, `k < (log n).length`, `k < ackHigh n`, some other node authoritative | `restartEmpty`, except `log n := (log n).take k` |

The protocol is a CSLib labelled transition system, `lts m : LTS (State Node)
(Action Node)` with `Tr := Step m`, and `Reachable m i s := (lts m).CanReach (init i) s`.

### Leases (`Leases.lean`)

`LeaseState` is a `State` plus real time `now`, each replica's committed view `committedView`, and
the lease timestamps (`Option Nat`; `none` is no lease): `primaryLease p r` (start of the primary
lease `p` holds from `r`: send time of the data `r` last acknowledged), `ackReceived p r`
(when `p` last received an acknowledgement from `r`), `ackEcho p r` (send time of the
acknowledgement `p` will echo), `readLease r` (start of `r`'s read lease), `primaryTraffic r` (when
`r` last received traffic from its primary, learned a configuration, or restarted),
`dataSent r` (send time of the latest data `r` received), `primarySince p` (when `p`'s primaryship
began on this node, by takeover or restart), `oldEligible p r` (`r` was eligible in the
configuration `p`'s takeover replaced; every `r` after a restart). `LeaseStep m P` has:

| Action | Guard | Effect |
|---|---|---|
| `tick` | | `now + 1` |
| `core μ` | `Step m` for AppendWrite, Commit, Count, Uncount, MakeEligible | the replication step; no lease state moves |
| `replicate r` | as `Step.replicate` | the replication step; `committedView r := max (committedView r) (min (commit p) \|log r\|)`, `primaryTraffic r := now`, `dataSent r := now` |
| `heartbeat r` | `r` does not consider itself primary; its log is a prefix of its primary's | the `committedView`, `primaryTraffic`, `dataSent` updates; log unchanged |
| `heartbeat r` with echo | as above; the primary thinks it is primary; `MayGrant`: it holds its lease from every eligible replica it knows, and `r` is a sync member eligible with a matching incarnation | as above, and `readLease r := max (readLease r) (ackEcho p r)` |
| `ack r` | as `Step.ack` | the replication step; `primaryLease p r := max (primaryLease p r) (dataSent r)`, `ackReceived p r := now`, `ackEcho p r := now` |
| `ack r` renewal | `r` does not consider itself primary; its log is a prefix of its primary's | the three lease updates; replication state unchanged |
| `learn n` | as `Step.learn` | the replication step; `primaryTraffic n := now` |
| `demote p r` | as `Step.makeIneligible`; `GrantorOver (ackReceived p r) readDur`; `primarySince p = some T → oldEligible p r = true → T + readDur + margin ≤ now + drift` | the replication step |
| `takeover n` | as `Step.takeover`; `primaryTraffic n + primDur ≤ now + drift` | the replication step; `primarySince n := now`; `oldEligible n := cfg.eligible` (before the takeover); `primaryLease n`, `ackReceived n`, `ackEcho n` cleared; `readLease n := none` |
| `resync r` | as `Step.resync` | the replication step; `committedView r := 0` |
| the restarts | as the replication restarts | the replication step; `committedView n := 0`; `n`'s leases cleared; `primaryTraffic n := now`, `dataSent n := now`, `primarySince n := now`, `oldEligible n := fun _ => true` |

`leaseLTS m P` and `LeaseReachable m P i a` as for the replication model.

### Held client replies (`Replies.lean`)

`AState` is a `State` plus `held : List (Held Node)` and `okd : List (Nat × Nat)`. A
held reply is `(p, o, t)`: primary `p`, 1-based offset `o`, tag `t = term p` at the
append; since a log entry is the term, `t` is also the value written. `AStep m` has:

| Action | Guard | Effect |
|---|---|---|
| `core μ` | `Step m` for a non-restart action `μ` | the replication step; `held`, `okd` unchanged |
| `write p` | as `append p` | `appendWrite` plus `(p, (log p).length + 1, term p)` held |
| `release h` | `h` held, `h.o ≤ commit h.p`, and `fenced`: `h.p` thinks it is primary with `term h.p = h.t` | `h` removed; `(h.o, h.t)` added to `okd` |
| `abort h` | `h` held and not `fenced` | `h` removed (UNCOMMITTED) |
| `restartE n`, `restartK n`, `restartP n k` | as the replication restarts | the replication restart; `n`'s held replies dropped |

`alts m`, `AReachable m i a` as above.

## The proof

### Invariant (`Invariant.lean`)

`Invariant s` extends five structures, `ConfigInvariant`, `ReplInvariant`,
`MembershipInvariant`, `CommitInvariant`, `FailoverInvariant`, and adds the goal
`ehc`. README §3.1 lists all 23 fields with their meaning; each has a docstring here
citing the design. `invariant_init` proves it of `init i`, and `invariant_safety`
that it implies `Safety`.

The fence of a deposed primary `p` is `fence s p := sInf (s.acked p '' leftSync s p)`,
the smallest acknowledgement `p` recorded from a sync member that now follows another
primary. `Fenced s p` packages the five facts the proof needs about it (`left`,
`reconLe`, `primHolds`, `primAck`, `eligHolds`). The preservation proofs use four
lemmas rather than the definition: `Fenced.of_left` (to show `p` is fenced, name one
departed replica and check the properties at its acknowledgement), `Fenced.attained`
(the fence is some departed replica's acknowledgement), `Fenced.mono` (for steps that
only extend logs or add sync members) and `Fenced.transfer` (for steps that leave the
fenced primary's row alone). `Learn` and `Takeover` are the two actions where the fence
can drop, and they build a fresh witness.

`commit_holds` is the central lemma: if any primary, current or deposed, may commit
offset `c` by the commit rule, every authoritative node holds the first `c + 1`
entries of its log. `commit_ackHigh` is its acknowledgement-side counterpart.

### Contracts (`Contracts.lean`)

For each action, what it changes and what it leaves alone, in design terms: who
thinks it is primary, who is authoritative, whose log, sync replica set,
acknowledgements and commit point move (`takeover_thinksPrimary`,
`restartEmpty_isAuthoritative`, `takeover_log`, ...). These follow from the action's
definition alone. Each preservation lemma takes the facts it needs from the contract;
the action is not unfolded in a preservation proof.

### Preservation (`Preserve/`, `Preserve.lean`)

One file per subsystem of the design: `Replication.lean` (AppendWrite, Replicate, Ack,
Resync), `Commit.lean` (Commit, Count, Uncount), `Config.lean` (Learn, MakeEligible,
MakeIneligible), `Failover.lean` (Takeover), `Restart.lean` (RestartEmpty,
RestartKeep, RestartPartial). Every action with a non-trivial proof is proved one
layer at a time, `config_X`, `repl_X`, `membership_X`, `commit_X`, `failover_X`,
`ehc_X`, each with a docstring saying in design terms why that layer survives the
action, and `invariant_X` assembles them as a term. Steps that leave a layer's
variables alone use that layer's frame lemma (`ConfigInvariant.frame`, ...).

`Preserve.lean` is the dispatch: `invariant_step` does a `cases` on `Step` and calls
the `invariant_X` for each constructor; `invariant_trInv` states this as a CSLib
one-step invariant, and `invariant_reachable` gets the run invariant from CSLib's
`mtrInv_of_trInv`.

### Lease invariant (`LeaseInvariant.lean`)

`LeaseInvariant P a` is `Invariant a.core` plus fourteen conjuncts. Eight bookkeeping
facts: `primaryTrafficLe`, `ackReceivedLe`, `readLeaseLe`, `primarySinceLe` (every recorded time is in the past),
`dataSentLe` (`dataSent r ≤ primaryTraffic r`), `primaryLeaseLe` (a primary lease starts no later than the
grantor's last traffic), `echoLe` (an echo was sent no later than it arrived), `primarySinceAck`
(every acknowledgement a primary holds arrived during its current primaryship; this
lets a read lease dated by a takeover be renewed into one dated by an acknowledgement).
The two that carry the argument: `deposed` (a deposed primary has a witness, the replica
that deposed it, eligible in its configuration and following someone else, whose
lease to it is over for good) and `leaseAuth` (a valid read lease implies the holder is
authoritative), with `leaseBound` (a read lease started no later than the current
primary's last acknowledgement from its holder, or no later than its takeover, and in
the latter case the holder was eligible in the replaced configuration or the lease has
already expired) feeding the latter. The last clause is what lets the post-takeover
demotion wait apply only to replicas of the replaced configuration: a lease held by any
other replica at takeover time was already invalid, since a valid one would have made
its holder authoritative, and invalid leases stay invalid until renewed by the current
primary, which puts them under the first bound.
Then `selfPrimNoLease` (a node whose configuration names it primary holds no read
lease; keeps a deposed primary out of the read-lease holders across Takeover and
Learn), `committedViewLen` and `committedViewHist` (the committed view is within the log and a committed
prefix). `leaseValid_current` is the lemma that a primary holding its lease is the
current primary; `lease_over_of_guards` turns the two demotion waits into "the read
lease is not valid"; `margin ≥ 2 · drift` is consumed in exactly those two lemmas.
`primCanRead_reachable` and `replCanRead_reachable` (`Counterexamples/Leases.lean`)
show the read rule's premises are reachable, so `noStaleRead` is not vacuous.
Preservation is one theorem per action in the same file. Frame lemmas carry the
conjuncts an action does not touch: `leaseInvariant_frame` (a replication step that
moves no lease state: data messages, resync, the plain actions), `deposed_frame` and
`deposed_cfgBump` (the deposed primary's witness survives a replication step, or a
configuration change by the current primary), `cleared_rows` (a node's lease rows are
cleared: takeover, restart), `committedView_reset` (a node's view starts over: resync,
restart), `primaryTraffic_bump` (a node's traffic timer restarts). The per-action
proofs are then the conjuncts the action moves: the read-lease renewal in
`leaseInvariant_heartbeatGrant`, the new witness and the bound on existing read leases
in `_takeover`, the two demotion waits in `_demote`.

### Durability (`Durability.lean`)

`ReplyInvariant a` is `Invariant a.core` plus `TermLe` (every term is at most
`cfg.version`), `HeldInvariant` (a held reply's tag is at most `cfg.version`, and a fenced
reply points at its own entry in its primary's log) and `AckedDurable`. `step_facts`
shows that every non-restart replication step extends `hist`, does not lower
`cfg.version`, keeps `TermLe`, and keeps fenced replies fenced with their log only grown;
the cases that matter are Takeover (the new term `cfg.version + 1` exceeds every tag),
Learn (can never make a node primary) and Resync (changes only a node that does not
think it is primary). `release` reads its entry from `HeldInvariant`, and
`CommittedAgree` turns that into `hist[o] = t`.

## Proof style

Conventions, following *Theorem Proving in Lean 4* ch. 5 (Structuring Tactic Proofs)
and the robustness notes there:

- Every sub-goal is a bullet (`·`) closed in place; `show` states the goal where it is
  not obvious from the field name.
- Hypotheses introduced by a case split are named at the split (`split_ifs with e`,
  `cases hs with | append p …`, `obtain ⟨…⟩`), never recovered afterwards with
  `rename_i`. The tree has no `rename_i`.
- `simp` with the default simp set is used only to close a goal. When a tactic
  follows, the call is `simp only [...]` with the lemmas named, so a change in the simp
  set cannot change the shape of the goal the next tactic sees.
- Layer assemblies (`invariant_takeover : Invariant … where …`) are term-style; the
  field names carry the structure.
- Names follow the design where it has one (`ThinksPrimary`, `KnowsLatest`,
  `IsAuthoritative`, `Writable`, `catchUpPoint`); otherwise Mathlib's: UpperCamelCase
  for types and propositions, lowerCamelCase for functions, snake_case for theorems.
- No `sorry`, and no theorem statement is weakened to make a proof go through; a
  property that does not hold gets a counterexample instead.

## Libraries

- **Mathlib** `v4.35.0`: list-prefix lemmas (`List.IsPrefix`, `take`), `Set.encard`
  for `Writable`, `sInf` on `Nat` for the fence, and the `@[refl]` lemmas that let
  `rw` close reflexive goals.
- **CSLib** at `0b1e3680` (its last commit on Lean 4.35.0, built against the same
  Mathlib revision): `Cslib.Foundations.Semantics.LTS.Basic`, supplying `LTS`, `MTr`
  (runs; `refl`, `stepL`, `comp`), `CanReach`, `TrInv`, `MTrInv` and
  `mtrInv_of_trInv`. Nothing about the protocol comes from CSLib.

## Axioms

`Check.lean`:

```
'SyncReplication.safety' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.commit_two_copies' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.ackSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.ackedHeld' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.noReconcile_unsafe' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.noReplyFence_unsafe' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.noRebuild_unsafe' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.noIncCheck_unsafe' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.noSurvivor_loses' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.staleRestoreKeepsInc_unsafe' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.staleRestoreKeepsInc_loses' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.noIncWritable_oneCopy' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.uncountElig_unsafe' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.noStaleRead' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.lease_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.noWaitPrim_stale' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.noWaitRead_stale' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.smallMargin_stale' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.grantAny_stale' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.primCanRead_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.replCanRead_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.grantSync_stale' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.grantNoInc_stale' depends on axioms: [propext, Classical.choice, Quot.sound]
'SyncReplication.demoteNew_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard axioms. There is no `sorryAx`. `Classical.choice` enters
through `sInf`, `Set.encard` and `by_cases` on propositions over an abstract node
type; `Quot.sound` through function extensionality.

## Size

| File | Lines |
|---|---|
| `SyncReplication/Model.lean` | 451 |
| `SyncReplication/Leases.lean` | 314 |
| `SyncReplication/LeaseInvariant.lean` | 1,055 |
| `SyncReplication/Replies.lean` | 113 |
| `SyncReplication/Invariant.lean` | 444 |
| `SyncReplication/Contracts.lean` | 616 |
| `SyncReplication/Preserve/Replication.lean` | 343 |
| `SyncReplication/Preserve/Commit.lean` | 421 |
| `SyncReplication/Preserve/Config.lean` | 592 |
| `SyncReplication/Preserve/Failover.lean` | 295 |
| `SyncReplication/Preserve/Restart.lean` | 859 |
| `SyncReplication/Preserve.lean` | 56 |
| `SyncReplication/Safety.lean` | 43 |
| `SyncReplication/Durability.lean` | 248 |
| `SyncReplication/Counterexamples/` (10 files) | 1,048 |
| `SyncReplication/Lists.lean` | 68 |
| `Lease/` (3 files) | 377 |
| total | 7,343 (plus the two root imports, 15 lines) |

`lake build` of the whole tree takes about 20 seconds warm on a laptop-class
machine (1,030 jobs including Mathlib's and CSLib's prebuilt modules).

## Reproduce

```
cd lean
docker build -t valkey-lean:24.04 -f ../tools/Dockerfile.lean ../tools   # once
../tools/lean.sh lake exe cache get         # once: Mathlib's prebuilt oleans (~7 GB)
../tools/lean.sh lake build                 # about 30 s from clean
../tools/lean.sh lake env lean Check.lean   # prints the axioms
../tools/lean.sh lake env lean LeaseCheck.lean
```

Lean 4.35.0, Mathlib `v4.35.0` and CSLib `0b1e3680`, all pinned in `lakefile.lean`
and `lake-manifest.json`. `tools/lean.sh` runs the toolchain in an Ubuntu image that
adds git and curl, which Lake and `cache get` need. If the container has no `git`,
clone Mathlib and the packages listed in its `lake-manifest.json` into
`.lake/packages/` on the host at the pinned revisions; Lake then uses those checkouts.

# Lease timing

Files: `Lease/Additive.lean`, `Lease/Rate.lean`, `Lease/Durations.lean`, root
`Lease.lean`, axioms in `LeaseCheck.lean`. Lean core only (`omega` plus a few
`Int.mul_*` lemmas), about 380 lines, no `sorry`. Independent of the replication model.

## Setting

One lease instance. The holder H sends at real time `s`. The grantor G receives at
`r ≥ s`. The delay `r - s` is **unbounded** in every safety theorem. A clock is any
`c : Int → Int` from real time to local reading.

* `Valid cH s W t`: `s ≤ t` and `cH t - cH s < W`, so H believes its lease valid.
* `Over cG r G t`: `r ≤ t` and `cG t - cG r ≥ G`, so G's promise is over.
* The asymmetric rule (the holder subtracts the margin) is `W = Dur - M`, `G = Dur`.
* The literal reading ("both sides subtract a margin") is `W = G = Dur - M`.

Two clock models:

* **Additive** (`AddDrift c a D`). For every `t ≥ a`, local elapsed since `a` is
  within `D` of real elapsed. Every type is `Int`.
* **Rate** (`RateClock a b c`, drift rate `ρ = a/b`, `0 ≤ a < b`). Lean core has no
  ordered-field lemmas for `Rat`, so the model is **scaled to integers**. Clocks read
  in units of `1/b` real tick, and for all `t1 ≤ t2`:
  `(b-a)(t2-t1) ≤ c t2 - c t1 ≤ (b+a)(t2-t1)`. A duration `X` corresponds to `b*X`
  local units. Such clocks are monotone.

## Theorems

| Theorem | Statement |
|---|---|
| `asym_safe` | `M ≥ 2D` ⇒ no real time where H is valid and G is over. Holds for all `s ≤ r`, all additive clocks (monotone or not), and all `Dur, D, M`. |
| `asym_tight` | `0 ≤ D`, `M < 2D`, `M < Dur` ⇒ overlap with zero delay. H's clock is `D` slow and G's clock is `D` fast, both monotone, at real time `max D (Dur - D)`. |
| `asym_safe_iff` | For `D ≥ 0`: every instance is safe ⇔ `2D ≤ M ∨ Dur ≤ M`. The second disjunct says H's lease is never valid. |
| `literal_unsafe` | `D > 0`, `M < Dur` ⇒ overlap, **for every margin M**. |
| `literal_safe_iff` | For `D ≥ 0`: the literal reading is safe ⇔ `D = 0 ∨ Dur ≤ M`. The margin size never matters. |
| `rate_asym_safe` | `2a·Dur ≤ (b+a)·M`, that is `M ≥ 2ρ·Dur/(1+ρ)`, ⇒ no overlap, for all `s ≤ r` and all rate clocks. |
| `rate_asym_tight` | `(b+a)M < 2a·Dur` ⇒ overlap. H runs at `1-ρ` and G at `1+ρ`, with zero delay. |
| `rate_literal_unsafe` / `rate_literal_safe_nodrift` | The literal reading is unsafe for every `a > 0` when `M < Dur`, and safe when `a = 0`. |
| `demotion_in_time` | A sufficient condition for the "Lease durations" rule, with bus commit delay `≤ B` and round trip `≤ Δ`. See below. |
| `doc_condition_insufficient_drift` / `_rtt` | Concrete runs where the design's own condition holds and P's lease has already expired at commit. |

**The rate tightness theorems are tight up to a tick refinement.** With integer real
time, the overlap window `bW/(b-a) - bG/(b+a)` can be shorter than one tick. The
witness therefore scales every duration by `k = (b-a)(b+a)`. This is the same physical
scenario measured with a finer tick.

The rate-form condition depends on `Dur`. The additive `D` is the worst drift over one
lease, and `D ≈ ρ·Dur` recovers `M ≥ 2D` to first order.

`demotion_in_time` (additive model) uses this timeline:

1. P sends offset X at `sp`. This starts P's primary lease from R.
2. R ACKs at `sa`. This starts R's read lease.
3. P receives the ACK at `ra ≤ sp + Δ`.
4. P's wait ends at `w`, the earliest time with local elapsed since `ra` `≥ ReadDur`.
5. The demotion commits at `d ≤ w + B`.

If `ReadDur + B + Δ + M + 2D < PrimDur` and `M ≥ 2D`, then at `d` P's primary lease
from R is still valid and R's read lease is invalid. The design's condition, read
lease + commit + margin < primary lease, omits the round trip `Δ` (with no drift,
`ReadDur=2, B=1, PrimDur=4, Δ=2` already fails) and a second drift term (P's clock can
run `D` slow while P waits and then `D` fast; with `D=1, M=2, ReadDur=2, B=1,
PrimDur=6` the lease expires at commit). This is an availability property only: P
then stops serving reads, which is safe.

`#print axioms`: every theorem depends only on `[propext, Quot.sound]`, plus
`Classical.choice` for the `_iff` theorems, `rate_asym_tight`, `rate_literal_*`, and
`doc_condition_*` (from `by_cases` and `decide`/`simp` on `Int` propositions). There is
no `sorryAx`.

# Appendix: Counterexamples

Every counterexample is a concrete run on three nodes (`N := Fin 3`, node 0 the initial
primary) in a weakened protocol: the model's `Step` plus one action with a rule
removed, as its own inductive relation with a `step` constructor that admits every
model step. Each run is a CSLib `MTr` whose label list is the trace, so the sequence of
actions is in the theorem statement; every guard is discharged by `decide`, so each run
is a genuine execution. `Counterexamples/Basic.lean` has the decidability instances,
`writable_one` (a `Writable 1` witness from one counted replica), `mtr_of_step` (a run
of the model is a run of any weakening), and the prefix three runs share: n0 promotes
n1, writes, n1 replicates and acknowledges, n0 commits (`committed_run`, 6 steps; the
history is `[1]`, on n0 and n1).

| File | Weakened relation | Rule removed | Trace | Violates |
|---|---|---|---|---|
| `Reconcile.lean` | `StepNoReconcile` | Count measures catch-up against the primary's own commit point | count 0 1, makeEligible 0 1, append 0, learn 1, replicate 1, ack 1, commit 0, takeover 1, learn 2, **count 1 2**, makeEligible 1 2 | EligibleHoldsCommitted: n2 authoritative with an empty log |
| `ReplyFence.lean` | `AStepNoFence` | Release on the committed offset alone, no primaryship check (`min-sync-replicas = 0`) | count 0 1, makeEligible 0 1, write 0, learn 1, takeover 1, learn 0, resync 0, count 1 0, makeEligible 1 0, learn 0, takeover 0, write 0, commit 0, **release (0, 1, 1)** | AckedDurable: `(1, 1)` acknowledged, history `[5]` |
| `Rebuild.lean` | `StepNoRebuild` | RestartKeep empties the sync replica set instead of rebuilding it | count 0 1, makeEligible 0 1, append 0, **restartKeep 0**, replicate 2, ack 2, count 0 2, makeEligible 0 2, commit 0 | EligibleHoldsCommitted: n1 authoritative without the write |
| `Incarnation.lean` | `StepNoInc` | Count and MakeEligible check `known[p].primary = p` only, not the incarnation | *prefix*, restartEmpty 0, **count 0 2**, **makeEligible 0 2** | EligibleHoldsCommitted: n2 authoritative with an empty log |
| `Survival.lean` | `StepNoSurv` | RestartEmpty without the survival guard | *prefix*, learn 1, restartEmpty 1, **restartEmpty 0** | the history is non-empty, no log holds it, no node is authoritative |
| `Leases.lean` | `LeaseStepNoWaitPrim`, `LeaseStepNoWaitRead`, `LeaseStepGrantAny`, `LeaseStepGrantSync`, `LeaseStepGrantNoInc` (with `P3`: primary lease 6, read lease 3, within the duration rule), and `leaseLTS` itself with `P1` | takeover without the primary-lease wait; demotion without the read-lease wait; echo to a follower outside the sync set; echo to a counted but ineligible member, then early removal; echo to a restarted-empty eligible member, then a takeover that never counts it; margin 1 with drift 1 | shared prefix count 0 1, makeEligible 0 1, learn 1, heartbeat 1, ack 1; then **takeover 1**, append 1, commit 1 / heartbeat 1 (grant), **demote 0 1**, append 0, commit 0 / (from `leaseInit`) heartbeat 2, ack 2, **heartbeat 2 (grant)**, append 0, commit 0 / tick ×4, takeover 1, append 1, commit 1 | `PrimCanRead` or `ReplCanRead` holds and the log is not the history |
| `Uncount.lean` | `StepUncountElig` | Uncount of an eligible counted replica | count 0 1, makeEligible 0 1, count 0 2, makeEligible 0 2, append 0, replicate 2, ack 2, **uncount 0 1**, commit 0 | EligibleHoldsCommitted: n1 authoritative without the write |
| `MinSyncIncarnation.lean` | `StepNoIncWritable` | AppendWrite and Commit use `Writable` without the incarnation condition | *prefix*, learn 1, restartEmpty 1, replicate 1, ack 1, count 0 1, **append 0**, replicate 1, ack 1 (then the **commit 0** whose guard the theorem states) | `commit_two_copies`' conclusion: after the commit, no node but the primary is authoritative |
| `StaleRestore.lean` | `StepStaleKeep` | RestartPartial keeps the incarnation whatever the file covers | *prefix*, learn 1, **restartPartial 1 0** (then restartEmpty 0 for `_loses`) | EligibleHoldsCommitted: n1 authoritative without the write; after n0 restarts empty, no log holds the history (`staleRestoreKeepsInc_loses`) |

The weakened action in each trace is in bold; *prefix* is `committed_run`. In
`Survival.lean` no node is authoritative in the final state, so EligibleHoldsCommitted
holds vacuously there and the theorem states the loss itself.
