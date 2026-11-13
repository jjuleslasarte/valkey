import SyncReplication.Lists
import Cslib.Foundations.Semantics.LTS.Basic

open Cslib

/-!
# The replication model

Transition-system encoding of the synchronous replication design
(`design-docs/sync-replication.md`): the commit protocol, the Cluster V2 shard
configuration, failover and node restarts.

A shard has one primary and any number of replicas. The primary appends client
writes to its log, replicas apply the log through the replication stream and acknowledge
how far they have copied, and the primary commits an entry once every replica in its
sync set has acknowledged it. Cluster V2 (Raft-based) holds a versioned configuration
(the primary, the set of replicas eligible to take over, and the incarnation recorded
for each node; an incarnation identifies one lifetime of a node's data and changes
when the node restarts without it);
every node keeps its own possibly stale copy. A node can restart and keep its data,
or restart empty with a new incarnation.

The theorem proved about this model (`SyncReplication.safety` in `Safety.lean`):

> In every reachable state, for every min-sync-replicas value, every authoritative
> node (the primary or an eligible replica, with the incarnation the configuration
> records for it) holds the whole committed history, and no node has committed an
> entry that differs from that history.

Where to find the design's reconciliation and restart rules: catch-up against the
inherited log (`catchUpPoint`), the restarted primary's sync replica set
(`rebuiltSync`), the stale-restore rule (`ackHigh`) and the survival assumption
(`Step.restartEmpty`). `Counterexamples/` shows what each one prevents.

## Incarnations

- `inc n` is the node's incarnation; `cfg.incarnation r` is the incarnation the configuration
  records for it. A node that restarts without its data takes a new incarnation.
- A node thinks it is primary only if its configuration names it primary with its
  current incarnation: `ThinksPrimary s p` is `localCfg[p].primary = p ∧ localCfg[p].incarnation p = inc p`.
- A node is authoritative if the latest configuration lists it as primary or eligible
  with its current incarnation: `IsAuthoritative s n` is
  `(cfg.eligible n ∨ n = cfg.primary) ∧ cfg.incarnation n = inc n`.
- Writable counts eligible sync members with a matching incarnation; Takeover checks the new
  primary's incarnation and counts every eligible replica (a stale one costs availability,
  not safety); MakeEligible records the replica's incarnation.
- Every restart requires KnowsLatest: a node syncs the Cluster V2 log before it
  rejoins (design §6). RestartEmpty is guarded by the survival assumption
  `∃ m, m ≠ n ∧ IsAuthoritative s m`, so it leaves the committed history on some
  authoritative node and `hist` unchanged.

## Encoding conventions

- Sets of nodes are `Node → Bool`.
- A log entry is the replication ID of the primaryship that wrote it, so a write is
  identified by its offset and that ID. IDs are compared only for equality.
- Each action is a function `State → State` returning the post-state; fields it
  does not mention keep their value. Its guard lives in the
  matching `Step` constructor.
- No `MaxLen` / `MaxVer` / `MaxRestarts` bounds.
- Names follow Lean's convention: a definition that is a proposition is
  UpperCamelCase (`ThinksPrimary`, `IsAuthoritative`), and one that computes a value
  is lowerCamelCase (`primaryOf`, `catchUpPoint`, the actions' `appendWrite` …).
-/

namespace SyncReplication

/-- Functional update: the function `f` with its value at `a` replaced by `b`, and
unchanged everywhere else. Per-node state is a function from `Node`, so "node `a`'s
log becomes `l`" is `update s.log a l`. -/
def update {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-- `update f a b a = b`: after node `a`'s value is set to `b`, reading it at `a`
gives `b`.

`@[simp]` registers this as a rewrite rule for the `simp` tactic, so a proof can
write `simp` and have `update f a b a` replaced by `b` automatically wherever it
appears. -/
@[simp] theorem update_self {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    update f a b a = b := by simp [update]

/-- `update f a b x = f x` for `x ≠ a`: after node `a`'s value is set to `b`, reading
it at any other node `x` gives the old value. The suffix `_of_ne` is Lean's naming for
"given not equal": the lemma takes the hypothesis `h : x ≠ a`. It is not a `simp` rule,
because a proof must supply that hypothesis. -/
theorem update_of_ne {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β) (h : x ≠ a) :
    update f a b x = f x := by simp [update, h]

/-- A Cluster V2 configuration. -/
structure Cfg (Node : Type) where
  /-- Epoch; every configuration change increments it. -/
  epoch  : Nat
  /-- The primary. -/
  primary : Node
  /-- The replicas eligible to take over. -/
  eligible : Node → Bool
  /-- The incarnation the configuration records for each node. -/
  incarnation  : Node → Nat

/-- The state of the whole shard. -/
structure State (Node : Type) [DecidableEq Node] where
  /-- Each node's replication log; an entry is the replication ID it was written with. -/
  log    : Node → List Nat
  /-- Each node's actual incarnation; restarting empty increments it. -/
  incarnation    : Node → Nat
  /-- The latest configuration in Cluster V2. -/
  cfg    : Cfg Node
  /-- The configuration each node has seen, possibly stale. -/
  localCfg  : Node → Cfg Node
  /-- `sync p r`: `r` is in `p`'s sync set, so `p` waits for `r`'s ack to commit. -/
  sync   : Node → Node → Bool
  /-- `acked p r`: how far `p` believes `r` has acknowledged. -/
  acked  : Node → Node → Nat
  /-- Each node's committed offset: how many entries at the start of its log it has
  committed. -/
  commit : Node → Nat
  /-- End of the inherited log: a new primary commits up to here before anything it
  appends after it (design §5, reconciliation). `catchUpPoint` is derived from it. -/
  inheritedEnd : Node → Nat
  /-- The replication ID each node writes new entries with: an opaque value, compared
  only for equality, fresh at each takeover (Valkey's replication ID). -/
  replId   : Node → Nat
  /-- Ghost variable: every replication ID used so far. A takeover or `newId` picks one
  outside it. Used only in the proof of the reply fence: a fresh ID cannot match any
  held reply, because every held reply's ID is in this set (`ReplyInvariant`). -/
  usedIds : Finset Nat
  /-- `ackHigh n`: the highest offset `n` has ever acknowledged, as a replica to a
  primary (Ack) or as a primary to its clients (Commit). Node-local, and it must
  survive a restart with data: a node that restarts from a persistence file covering
  less than this has acknowledged writes it no longer holds. Used as the guard that
  decides whether RestartPartial keeps the node's incarnation. -/
  ackHigh : Node → Nat
  /-- Ghost variable: the committed history. No node stores it; it is extended the
  first time any node commits a given offset. Used as the reference the properties
  compare against: `Safety` and `AckedDurable` compare each node's log, and each
  acknowledged write, with it. -/
  hist   : List Nat

variable {Node : Type} [DecidableEq Node]

/-- The initial configuration: `i` is primary at epoch 1, no replica is eligible,
every incarnation is 1. -/
def initCfg (i : Node) : Cfg Node := ⟨1, i, fun _ => false, fun _ => 1⟩

/-- The initial state: empty logs and history, every node knows `initCfg i`, and `i`
writes with replication ID 1; IDs 0 and 1 are in use. -/
def init (i : Node) : State Node where
  log    := fun _ => []
  incarnation    := fun _ => 1
  cfg    := initCfg i
  localCfg  := fun _ => initCfg i
  sync   := fun _ _ => false
  acked  := fun _ _ => 0
  commit := fun _ => 0
  inheritedEnd  := fun _ => 0
  replId   := fun n => if n = i then 1 else 0
  usedIds := {0, 1}
  ackHigh := fun _ => 0
  hist   := []

/-- `p` thinks it is primary: the configuration `p` knows (which may be stale) names
`p` as primary, and the incarnation it records for `p` is `p`'s current one. A
primary that restarted empty has a new incarnation and so fails the second half:
it no longer acts as primary. -/
def ThinksPrimary (s : State Node) (p : Node) : Prop :=
  (s.localCfg p).primary = p ∧ (s.localCfg p).incarnation p = s.incarnation p
/-- `n` knows the latest configuration: its copy has the current epoch. -/
def KnowsLatest (s : State Node) (n : Node) : Prop := (s.localCfg n).epoch = s.cfg.epoch
/-- The node `n` believes is primary, according to the configuration `n` knows; the
one it replicates from. -/
def primaryOf (s : State Node) (n : Node) : Node := (s.localCfg n).primary
/-- `n` is authoritative: in the latest configuration, `n` is the primary or an eligible
replica, and the incarnation recorded for it is its actual one. These are the nodes
that must hold the committed history. -/
def IsAuthoritative (s : State Node) (n : Node) : Prop :=
  (s.cfg.eligible n = true ∨ n = s.cfg.primary) ∧ s.cfg.incarnation n = s.incarnation n
/-- The current primary is authoritative (it has not come back empty). -/
def PrimaryAuthoritative (s : State Node) : Prop := s.cfg.incarnation s.cfg.primary = s.incarnation s.cfg.primary

/-! ### Post-states of the actions. Fields an action does not mention keep their value. -/

/-- `appendWrite s p`: `p` appends one client write to its own log, tagged with its
current replication ID. Nothing else changes. -/
def appendWrite (s : State Node) (p : Node) : State Node :=
  { s with log := update s.log p (s.log p ++ [s.replId p]) }

/-- `replicate s r`: `r` copies the next entry of its primary's log onto its own and adopts
its primary's replication ID, as a Valkey replica does on sync. -/
def replicate (s : State Node) (r : Node) : State Node :=
  { s with log := update s.log r (s.log r ++ [(s.log (primaryOf s r)).getD (s.log r).length 0]),
           replId := update s.replId r (s.replId (primaryOf s r)) }

/-- `ack s r`: `r`'s primary records that `r` holds its whole log, and `r` records that it
has acknowledged up to there. -/
def ack (s : State Node) (r : Node) : State Node :=
  { s with acked := update s.acked (primaryOf s r) (update (s.acked (primaryOf s r)) r (s.log r).length),
           ackHigh := update s.ackHigh r (max (s.ackHigh r) (s.log r).length) }

/-- `commitNext s p`: `p` commits its next entry. If no node has committed this offset yet,
the entry is appended to the ghost history. A commit is `p`'s acknowledgement to its
clients, so `p`'s high-water mark covers it. -/
def commitNext (s : State Node) (p : Node) : State Node :=
  { s with commit := update s.commit p (s.commit p + 1),
           hist := if s.commit p = s.hist.length
                   then s.hist ++ [(s.log p).getD (s.commit p) 0] else s.hist,
           ackHigh := update s.ackHigh p (max (s.ackHigh p) (s.commit p + 1)) }

/-- `addToSyncSet s p r`: `p` adds `r` to its sync set (design §4, promotion step 2, "start
counting its acks"). -/
def addToSyncSet (s : State Node) (p r : Node) : State Node :=
  { s with sync := update s.sync p (update (s.sync p) r true) }

/-- `removeFromSyncSet s p r`: `p` removes `r` from its sync set again, before `r` has become
eligible ("if the replica falls behind or fails before step 4, the primary simply
removes it from the commit calculation", design §4). -/
def removeFromSyncSet (s : State Node) (p r : Node) : State Node :=
  { s with sync := update s.sync p (update (s.sync p) r false) }

/-- MakeEligible's configuration: next epoch, `r` eligible, `r`'s current
incarnation recorded. -/
def makeEligibleCfg (s : State Node) (r : Node) : Cfg Node :=
  { s.cfg with epoch := s.cfg.epoch + 1, eligible := update s.cfg.eligible r true,
               incarnation := update s.cfg.incarnation r (s.incarnation r) }

/-- MakeIneligible's configuration: next epoch, `r` no longer eligible. -/
def makeIneligibleCfg (s : State Node) (r : Node) : Cfg Node :=
  { s.cfg with epoch := s.cfg.epoch + 1, eligible := update s.cfg.eligible r false }

/-- `makeEligible s p r`: primary `p` publishes a configuration in which `r` is eligible
(design §4, promotion step 4, the compare-and-set on the cluster bus). After it, `r`
counts toward `Writable` and may take over. `p`'s own copy of the configuration changes
in the same step, so `p` always knows the outcome of its own compare-and-set. -/
def makeEligible (s : State Node) (p r : Node) : State Node :=
  { s with cfg := makeEligibleCfg s r, localCfg := update s.localCfg p (makeEligibleCfg s r) }

/-- `makeIneligible s p r`: primary `p` publishes a configuration in which `r` is not
eligible, and drops `r` from its sync set. -/
def makeIneligible (s : State Node) (p r : Node) : State Node :=
  { s with cfg := makeIneligibleCfg s r, localCfg := update s.localCfg p (makeIneligibleCfg s r),
           sync := update s.sync p (update (s.sync p) r false) }

/-- `learn s n`: `n` adopts the latest configuration; unless it is the primary there,
it empties its sync set. -/
def learn (s : State Node) (n : Node) : State Node :=
  { s with localCfg := update s.localCfg n s.cfg,
           sync := update s.sync n (if s.cfg.primary = n then s.sync n else fun _ => false) }

/-- `cfg.eligible \ {cfg.primary, n}`: the eligible set after `n` takes over from the
current primary. -/
def eligibleAfterTakeover (s : State Node) (n : Node) : Node → Bool :=
  fun x => s.cfg.eligible x && decide (x ≠ s.cfg.primary) && decide (x ≠ n)

/-- Takeover's configuration: next epoch, `n` primary, `eligibleAfterTakeover` eligible, the
recorded incarnations unchanged. -/
def takeoverCfg (s : State Node) (n : Node) : Cfg Node := ⟨s.cfg.epoch + 1, n, eligibleAfterTakeover s n, s.cfg.incarnation⟩

/-- The new primary's sync replica set: every eligible replica of the new configuration.
A replica whose recorded incarnation is stale is counted too; the new primary then waits
for it, which costs availability but not safety (it cannot count toward `Writable`). -/
def syncAfterTakeover (s : State Node) (n : Node) : Node → Bool :=
  fun x => eligibleAfterTakeover s n x

/-- A replication ID not used before. Any choice outside `s.usedIds` would do; the proofs
use only `freshId_not_mem`. This one takes the largest used value plus one, the only
place an ordering on IDs appears. -/
def freshId (s : State Node) : Nat := s.usedIds.sup id + 1

/-- The fresh ID is not among the used ones. -/
theorem freshId_not_mem (s : State Node) : freshId s ∉ s.usedIds := fun h => by
  have := Finset.le_sup (f := id) h
  simp only [freshId, id] at this; omega

/-- `takeover s n`: eligible replica `n` becomes primary in a new configuration. Its
sync set is the eligible replicas of the new configuration, its acks and commit point are reset, its
catch-up point is the end of its log (so it commits what it inherited before anything
it writes afterwards), and it writes with a fresh replication ID. -/
def takeover (s : State Node) (n : Node) : State Node :=
  { s with cfg := takeoverCfg s n, localCfg := update s.localCfg n (takeoverCfg s n),
           sync := update s.sync n (syncAfterTakeover s n),
           acked := update s.acked n (fun _ => 0),
           commit := update s.commit n 0,
           inheritedEnd := update s.inheritedEnd n (s.log n).length,
           replId := update s.replId n (freshId s), usedIds := insert (freshId s) s.usedIds }

/-- The point a replica must have acknowledged before `p` counts it: `p`'s catch-up
point while it is still reconciling, otherwise its commit point. -/
def catchUpPoint (s : State Node) (p : Node) : Nat :=
  if s.commit p < s.inheritedEnd p then min (s.inheritedEnd p) (s.log p).length else s.commit p

/-- The sync members of `p` that are eligible in `p`'s configuration with the
incarnation it records for them. These are the replicas
that count toward `min-sync-replicas`. -/
def syncEligible (s : State Node) (p : Node) : Set Node :=
  {r | s.sync p r = true ∧ (s.localCfg p).eligible r = true ∧ (s.localCfg p).incarnation r = s.incarnation r}

/-- `p` is writable: at least `m` distinct sync members of `p` are eligible in `p`'s configuration with the
incarnation it records for them. `Set.encard` is the cardinality in `ℕ∞`, so this
needs no finiteness assumption on `Node`. -/
def Writable (m : Nat) (s : State Node) (p : Node) : Prop :=
  (m : ℕ∞) ≤ (syncEligible s p).encard

/-- `Writable` is the earlier list form: some duplicate-free list of at least `m`
nodes, all counted. -/
theorem writable_iff_list (m : Nat) (s : State Node) (p : Node) :
    Writable m s p ↔ ∃ l : List Node, l.Nodup ∧ m ≤ l.length ∧
      ∀ r ∈ l, s.sync p r = true ∧ (s.localCfg p).eligible r = true ∧ (s.localCfg p).incarnation r = s.incarnation r :=
  le_encard_iff_list m _

/-- `resync s r`: a replica whose log has diverged from its primary's replaces it with
the primary's log up to the primary's catch-up point, and starts acking from 0. -/
def resync (s : State Node) (r : Node) : State Node :=
  { s with log := update s.log r ((s.log (primaryOf s r)).take (catchUpPoint s (primaryOf s r))),
           acked := update s.acked (primaryOf s r) (update (s.acked (primaryOf s r)) r 0),
           commit := update s.commit r (min (s.commit r) (s.commit (primaryOf s r))) }

/-- `restartEmpty s n`: empty log, new incarnation, no volatile state; the current
primary forgets `n`'s ack and stops counting it. -/
def restartEmpty (s : State Node) (n : Node) : State Node :=
  { s with log := update s.log n [],
           incarnation := update s.incarnation n (s.incarnation n + 1),
           ackHigh := update s.ackHigh n 0,
           commit := update s.commit n 0,
           inheritedEnd := update s.inheritedEnd n 0,
           sync := fun p => if p = n then (fun _ => false)
                            else if p = s.cfg.primary then update (s.sync p) n false else s.sync p,
           acked := fun p => if p = n then (fun _ => 0)
                             else if p = s.cfg.primary then update (s.acked p) n 0 else s.acked p }

/-- The sync replica set a restarted primary starts from: the replicas that are
eligible, with a matching recorded incarnation, in the configuration it knows, minus
itself. Recomputed from the configuration, not from any data transfer. -/
def rebuiltSync (s : State Node) (n : Node) : Node → Bool :=
  fun r => (s.localCfg n).eligible r && decide ((s.localCfg n).incarnation r = s.incarnation r) && decide (r ≠ n)

/-- `restartKeep s n`: data and incarnation kept, volatile state lost. `n` must commit
its whole log again before it serves reads. If `n` is primary, its sync set is rebuilt from
the configuration it knows (`rebuiltSync`); otherwise it is empty. -/
def restartKeep (s : State Node) (n : Node) : State Node :=
  { s with commit := update s.commit n 0,
           inheritedEnd := update s.inheritedEnd n (s.log n).length,
           acked := update s.acked n (fun _ => 0),
           sync := update s.sync n
             (if (s.localCfg n).primary = n ∧ (s.localCfg n).incarnation n = s.incarnation n
              then rebuiltSync s n else fun _ => false) }

/-- `restartPartialKeep s n k`, keeping the incarnation: `n` restarts from a persistence
file holding only the first `k` entries of its log. Everything else is RestartKeep on
the truncated log: volatile state lost, catch-up point at the end of what it holds,
sync replica set rebuilt if it is primary. -/
def restartPartialKeep (s : State Node) (n : Node) (k : Nat) : State Node :=
  { restartKeep s n with log := update s.log n ((s.log n).take k), inheritedEnd := update s.inheritedEnd n k }

/-- `restartPartialFresh s n k`, taking a new incarnation: RestartEmpty, except that `n` keeps
the first `k` entries of its log as a starting point for resynchronisation. -/
def restartPartialFresh (s : State Node) (n : Node) (k : Nat) : State Node :=
  { restartEmpty s n with log := update s.log n ((s.log n).take k) }

/-- The actions of the protocol, as labels on steps. Labels make a run readable: a
counterexample's statement lists its actions in order. They also let the reply and
lease layers wrap a replication step (`ReplyAction.core`). A restore from a stale file
has one label, `restartPartial n k`, although `Step` has two constructors for it: the
outcome (keep or replace the incarnation) is decided by the node's `ackHigh`, not
chosen by whoever restarts it. -/
inductive Action (Node : Type)
  | append (p : Node) | replicate (r : Node) | ack (r : Node) | commit (p : Node)
  | addToSyncSet (p r : Node) | removeFromSyncSet (p r : Node) | makeEligible (p r : Node) | makeIneligible (p r : Node)
  | learn (n : Node)
  | takeover (n : Node) | resync (r : Node) | restartEmpty (n : Node) | restartKeep (n : Node)
  | restartPartial (n : Node) (k : Nat)

/-- The restart actions. The acknowledgement layer treats them apart from the other
actions: a node's held replies die with its client connections when it restarts. -/
def Action.isRestart : Action Node → Bool
  | .restartEmpty _ | .restartKeep _ | .restartPartial _ _ => true
  | .append _ | .replicate _ | .ack _ | .commit _ | .addToSyncSet _ _ | .removeFromSyncSet _ _
  | .makeEligible _ _ | .makeIneligible _ _ | .learn _ | .takeover _ | .resync _ => false

/-- The step relation. `m` is `min-sync-replicas`. Each constructor is one
action: its arguments after the state are the guard, and its result is the action's
label and the post-state. -/
inductive Step (m : Nat) : State Node → Action Node → State Node → Prop
  /-- A node that thinks it is primary and has enough sync replicas may append a write.
  It need not have committed its inherited log first: AddToSyncSet and Commit already order
  the inherited entries before any new one (`committed_inherited_first`). -/
  | append (s p) : ThinksPrimary s p → Writable m s p → Step m s (.append p) (appendWrite s p)
  /-- A replica whose log is a strict prefix of its primary's may copy the next entry. -/
  | replicate (s r) : primaryOf s r ≠ r → s.log r <+: s.log (primaryOf s r) →
      (s.log r).length < (s.log (primaryOf s r)).length → Step m s (.replicate r) (replicate s r)
  /-- A replica whose log is a prefix of its primary's may acknowledge new entries. -/
  | ack (s r) : primaryOf s r ≠ r → s.log r <+: s.log (primaryOf s r) →
      s.acked (primaryOf s r) r < (s.log r).length → Step m s (.ack r) (ack s r)
  /-- A writable primary may commit its next entry once every sync member has
  acknowledged it. -/
  | commit (s p) : (hThinksPrimary : ThinksPrimary s p) → (hWritable : Writable m s p) → (hHasNext : s.commit p < (s.log p).length) →
      (hAllAcked : ∀ r, s.sync p r = true → s.commit p < s.acked p r) → Step m s (.commit p) (commitNext s p)
  /-- A primary may count one of its replicas once that replica has acknowledged up
  to the catch-up point. -/
  | addToSyncSet (s p r) : (hThinksPrimary : ThinksPrimary s p) → (hNotSelf : r ≠ p) → (hFollows : primaryOf s r = p) →
      (hNotInSync : s.sync p r = false) → (hCaughtUp : catchUpPoint s p ≤ s.acked p r) →
      Step m s (.addToSyncSet p r) (addToSyncSet s p r)
  /-- A primary may drop a counted replica that is not eligible in its own configuration
  (design §4: "if the replica falls behind or fails before step 4, the primary simply
  removes it from the commit calculation"). It need not know the latest configuration:
  a deposed primary is fenced only by departed members it lists as eligible, and it
  cannot drop those. -/
  | removeFromSyncSet (s p r) : (hThinksPrimary : ThinksPrimary s p) → (hInSync : s.sync p r = true) →
      (hNotLocallyEligible : (s.localCfg p).eligible r = false) → Step m s (.removeFromSyncSet p r) (removeFromSyncSet s p r)
  /-- A primary that knows the latest configuration may make a sync member eligible. -/
  | makeEligible (s p r) : (hThinksPrimary : ThinksPrimary s p) → (hKnowsLatest : KnowsLatest s p) → (hInSync : s.sync p r = true) →
      (hNotEligible : s.cfg.eligible r = false) → Step m s (.makeEligible p r) (makeEligible s p r)
  /-- A primary that knows the latest configuration may make a replica ineligible. -/
  | makeIneligible (s p r) : (hThinksPrimary : ThinksPrimary s p) → (hKnowsLatest : KnowsLatest s p) → (hEligible : s.cfg.eligible r = true) →
      Step m s (.makeIneligible p r) (makeIneligible s p r)
  /-- A node with a stale configuration may learn the latest one. -/
  | learn (s n) : (hStale : ¬ KnowsLatest s n) → Step m s (.learn n) (learn s n)
  /-- An eligible replica that knows the latest configuration, with a matching
  recorded incarnation, may take over from the current primary. -/
  | takeover (s n) : (hKnowsLatest : KnowsLatest s n) → (hEligible : s.cfg.eligible n = true) → (hNotPrimary : n ≠ s.cfg.primary) →
      (hIncMatches : s.cfg.incarnation n = s.incarnation n) → Step m s (.takeover n) (takeover s n)
  /-- A diverged replica may resync once its primary has neither counted it nor made
  it eligible. -/
  | resync (s r) : (hFollowsOther : primaryOf s r ≠ r) → (hDiverged : ¬ (s.log r <+: s.log (primaryOf s r))) →
      (hNotInSync : s.sync (primaryOf s r) r = false) → (hNotLocallyEligible : (s.localCfg (primaryOf s r)).eligible r = false) →
      Step m s (.resync r) (resync s r)
  /-- A node that knows the latest configuration may restart empty while some other
  authoritative node keeps its data (the survival assumption). -/
  | restartEmpty (s n) : (hKnowsLatest : KnowsLatest s n) → (hSurvivor : ∃ m, m ≠ n ∧ IsAuthoritative s m) →
      Step m s (.restartEmpty n) (restartEmpty s n)
  /-- A node that knows the latest configuration may restart and keep its data. -/
  | restartKeep (s n) : (hKnowsLatest : KnowsLatest s n) → Step m s (.restartKeep n) (restartKeep s n)
  /-- A node may restart from a persistence file holding only the first `k` entries of
  its log. It keeps its incarnation only if the file covers every offset it has
  acknowledged (`ackHigh n ≤ k`). -/
  | restartPartialKeep (s n k) : (hKnowsLatest : KnowsLatest s n) → (hFileShorter : k < (s.log n).length) → (hCoversAcks : s.ackHigh n ≤ k) →
      Step m s (.restartPartial n k) (restartPartialKeep s n k)
  /-- Otherwise it takes a new incarnation and rejoins as after RestartEmpty, under the
  same survival assumption, keeping the `k` entries it has. -/
  | restartPartialFresh (s n k) : (hKnowsLatest : KnowsLatest s n) → (hFileShorter : k < (s.log n).length) → (hMissesAcks : k < s.ackHigh n) →
      (hSurvivor : ∃ m, m ≠ n ∧ IsAuthoritative s m) →
      Step m s (.restartPartial n k) (restartPartialFresh s n k)

/-- The protocol as a labelled transition system (CSLib's `LTS`): `Step` is its
transition relation, so CSLib's runs (`MTr`), reachability (`CanReach`), invariants
(`TrInv`, `MTrInv`) apply to it. -/
def transitionSystem (m : Nat) : LTS (State Node) (Action Node) where
  Tr := Step m

@[simp] theorem transitionSystem_tr {m : Nat} {s s' : State Node} {μ : Action Node} :
    (transitionSystem m).Tr s μ s' ↔ Step m s μ s' := Iff.rfl

/-- The states reachable from `init i` by any finite run. -/
def Reachable (m : Nat) (i : Node) (s : State Node) : Prop :=
  (transitionSystem m).CanReach (init i) s

theorem Reachable.init {m : Nat} (i : Node) : Reachable m i (init i) :=
  LTS.CanReach.refl (transitionSystem m) _

/-- One more step keeps a state reachable. -/
theorem Reachable.stepR {m : Nat} {i : Node} {s s' : State Node} {μ : Action Node}
    (h : Reachable m i s) (hs : Step m s μ s') : Reachable m i s' :=
  let ⟨_, run⟩ := h; ⟨_, LTS.MTr.stepR (transitionSystem m) run hs⟩

/-! ### Properties -/

/-- EligibleHoldsCommitted, restated for authoritative nodes: every authoritative
node holds the whole committed history, so losing any other node loses nothing
committed. -/
def EligibleHoldsCommitted (s : State Node) : Prop := ∀ n, IsAuthoritative s n → s.hist <+: s.log n

/-- CommittedAgree: every node's commit point is within its log, and what it has
committed is exactly the start of the committed history. In particular no two nodes
have committed different entries at the same offset. -/
def CommittedAgree (s : State Node) : Prop :=
  ∀ p, s.commit p ≤ (s.log p).length ∧ (s.log p).take (s.commit p) = s.hist.take (s.commit p)

/-- The property `SyncReplication.safety` proves for every reachable state:
EligibleHoldsCommitted and CommittedAgree. -/
def Safety (s : State Node) : Prop := EligibleHoldsCommitted s ∧ CommittedAgree s

end SyncReplication
