import SyncReplication.Lists
import Cslib.Foundations.Semantics.LTS.Basic

open Cslib

/-!
# The replication model

Transition-system encoding of the synchronous replication design
(`design-docs/sync-replication.md`): the commit protocol, the Cluster V2 shard
configuration, failover and node restarts.

## In prose

A shard has one primary and any number of replicas. The primary appends client
writes to its log, replicas copy the log and acknowledge how far they have copied,
and the primary commits an entry once every replica in its sync set has
acknowledged it. Cluster V2 holds a versioned configuration (the primary, the set
of replicas eligible to take over, and the incarnation recorded for each node);
every node keeps its own possibly stale copy. A node can restart and keep its data,
or restart empty with a new incarnation.

The theorem proved about this model (`SyncReplication.safety` in `Safety.lean`):

> In every reachable state, for every min-sync-replicas value, every authoritative
> node (the primary or an eligible replica, with the incarnation the configuration
> records for it) holds the whole committed history, and no node has committed an
> entry that differs from that history.

The model is the design with its reconciliation and restart rules in place: a new
primary commits its inherited log before it writes (`Reconciled`), a primary that
restarts with its data rebuilds its sync set from its configuration (`rebuiltSync`),
a node keeps its incarnation across a restart only if the data it restores covers
what it has acknowledged (`ackHigh`), and a node restarts empty only while some other
authoritative node keeps its data (the survival assumption). `Counterexamples/`
shows what each of these rules prevents.

## Incarnations

- `inc n` is the node's incarnation; `cfg.inc r` is the incarnation the configuration
  records for it. A node that restarts without its data takes a new incarnation.
- A node thinks it is primary only if its configuration names it primary with its
  current incarnation: `ThinksPrimary s p` is `known[p].prim = p ∧ known[p].inc p = inc p`.
- A node is authoritative if the latest configuration lists it as primary or eligible
  with its current incarnation: `IsAuthoritative s n` is
  `(cfg.elig n ∨ n = cfg.prim) ∧ cfg.inc n = inc n`.
- Writable counts eligible sync members with a matching incarnation; Takeover checks the new
  primary's incarnation and counts only the matching eligible replicas; MakeEligible
  records the replica's incarnation.
- Every restart requires KnowsLatest: a node syncs the Cluster V2 log before it
  rejoins (design §6). RestartEmpty is guarded by the survival assumption
  `∃ m, m ≠ n ∧ IsAuthoritative s m`, so it leaves the committed history on some
  authoritative node and `hist` unchanged.

## Encoding conventions

- Sets of nodes are `Node → Bool`.
- A log entry is the term it was written in, so a write is identified by its
  offset and term.
- Each action is a function `State → State` returning the post-state; fields it
  does not mention keep their value. Its guard lives in the
  matching `Step` constructor.
- No `MaxLen` / `MaxVer` / `MaxRestarts` bounds.
-/

namespace SyncReplication

/-- Functional update: `f` with the value at `a` replaced by `b`
-/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

@[simp] theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

theorem upd_ne {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β) (h : x ≠ a) :
    upd f a b x = f x := by simp [upd, h]

/-- A Cluster V2 configuration. -/
structure Cfg (Node : Type) where
  /-- Version; every configuration change increments it. -/
  ver  : Nat
  /-- The primary. -/
  prim : Node
  /-- The replicas eligible to take over. -/
  elig : Node → Bool
  /-- The incarnation the configuration records for each node. -/
  inc  : Node → Nat

/-- The state of the whole shard, plus the ghost history. -/
structure State (Node : Type) [DecidableEq Node] where
  /-- Each node's replication log; an entry is the term it was written in. -/
  log    : Node → List Nat
  /-- Each node's actual incarnation; restarting empty increments it. -/
  inc    : Node → Nat
  /-- The latest configuration in Cluster V2. -/
  cfg    : Cfg Node
  /-- The configuration each node has seen, possibly stale. -/
  known  : Node → Cfg Node
  /-- `sync p r`: `r` is in `p`'s sync set, so `p` waits for `r`'s ack to commit. -/
  sync   : Node → Node → Bool
  /-- `acked p r`: how far `p` believes `r` has acknowledged. -/
  acked  : Node → Node → Nat
  /-- Each node's commit point. -/
  commit : Node → Nat
  /-- Catch-up point: a new primary must commit up to here before taking writes. -/
  recon  : Node → Nat
  /-- The term each node writes new entries with. -/
  term   : Node → Nat
  /-- `ackHigh n`: the highest offset `n` has ever acknowledged, as a replica to a
  primary (Ack) or as a primary to its clients (Commit). Node-local, and it must
  survive a restart with data: a node that restarts from a persistence file covering
  less than this has acknowledged writes it no longer holds (RestartPartial). -/
  ackHigh : Node → Nat
  /-- Ghost variable: the committed history. No node stores it; it is extended the
  first time any node commits a given offset. -/
  hist   : List Nat

variable {Node : Type} [DecidableEq Node]

/-- The initial configuration: `i` is primary at version 1, no replica is eligible,
every incarnation is 1. -/
def initCfg (i : Node) : Cfg Node := ⟨1, i, fun _ => false, fun _ => 1⟩

/-- The initial state: empty logs and history, every node knows `initCfg i`, and `i`
writes with term 1. -/
def init (i : Node) : State Node where
  log    := fun _ => []
  inc    := fun _ => 1
  cfg    := initCfg i
  known  := fun _ => initCfg i
  sync   := fun _ _ => false
  acked  := fun _ _ => 0
  commit := fun _ => 0
  recon  := fun _ => 0
  term   := fun n => if n = i then 1 else 0
  ackHigh := fun _ => 0
  hist   := []

/-- ThinksPrim(p): `p`'s own configuration names it primary and records its current
incarnation. A primary that restarted empty fails the second half. -/
def ThinksPrimary (s : State Node) (p : Node) : Prop :=
  (s.known p).prim = p ∧ (s.known p).inc p = s.inc p
/-- KnowsLatest(n): `n` has seen the latest configuration. -/
def KnowsLatest (s : State Node) (n : Node) : Prop := (s.known n).ver = s.cfg.ver
/-- PrimOf(n): the node `n` believes is primary, the one it replicates from. -/
def primaryOf (s : State Node) (n : Node) : Node := (s.known n).prim
/-- Reconciled(p): `p` has committed up to its catch-up point, so it holds and has
committed everything it inherited. -/
def Reconciled (s : State Node) (p : Node) : Prop := s.recon p ≤ s.commit p
/-- `n \in Auth`: in the latest configuration, `n` is the primary or an eligible
replica, and the incarnation recorded for it is its actual one. These are the nodes
that must hold the committed history. -/
def IsAuthoritative (s : State Node) (n : Node) : Prop :=
  (s.cfg.elig n = true ∨ n = s.cfg.prim) ∧ s.cfg.inc n = s.inc n
/-- The current primary is authoritative (it has not come back empty). -/
def PrimaryAuthoritative (s : State Node) : Prop := s.cfg.inc s.cfg.prim = s.inc s.cfg.prim

/-! ### Post-states of the actions (the UNCHANGED parts are implicit). -/

/-- AppendWrite(p): `p` appends one client write to its own log, tagged with its
current term. Nothing else changes. -/
def appendWrite (s : State Node) (p : Node) : State Node :=
  { s with log := upd s.log p (s.log p ++ [s.term p]) }

/-- Replicate(r): `r` copies the next entry of its primary's log onto its own. -/
def replicate (s : State Node) (r : Node) : State Node :=
  { s with log := upd s.log r (s.log r ++ [(s.log (primaryOf s r)).getD (s.log r).length 0]) }

/-- Ack(r): `r`'s primary records that `r` holds its whole log, and `r` records that it
has acknowledged up to there. -/
def ack (s : State Node) (r : Node) : State Node :=
  { s with acked := upd s.acked (primaryOf s r) (upd (s.acked (primaryOf s r)) r (s.log r).length),
           ackHigh := upd s.ackHigh r (max (s.ackHigh r) (s.log r).length) }

/-- Commit(p): `p` commits its next entry. If no node has committed this offset yet,
the entry is appended to the ghost history. A commit is `p`'s acknowledgement to its
clients, so `p`'s high-water mark covers it. -/
def commitNext (s : State Node) (p : Node) : State Node :=
  { s with commit := upd s.commit p (s.commit p + 1),
           hist := if s.commit p = s.hist.length
                   then s.hist ++ [(s.log p).getD (s.commit p) 0] else s.hist,
           ackHigh := upd s.ackHigh p (max (s.ackHigh p) (s.commit p + 1)) }

/-- Count(p, r): `p` adds `r` to its sync set. -/
def count (s : State Node) (p r : Node) : State Node :=
  { s with sync := upd s.sync p (upd (s.sync p) r true) }

/-- MakeEligible's configuration: next version, `r` eligible, `r`'s current
incarnation recorded. -/
def makeEligCfg (s : State Node) (r : Node) : Cfg Node :=
  { s.cfg with ver := s.cfg.ver + 1, elig := upd s.cfg.elig r true,
               inc := upd s.cfg.inc r (s.inc r) }

/-- MakeIneligible's configuration: next version, `r` no longer eligible. -/
def makeIneligCfg (s : State Node) (r : Node) : Cfg Node :=
  { s.cfg with ver := s.cfg.ver + 1, elig := upd s.cfg.elig r false }

/-- MakeEligible(p, r): primary `p` publishes a configuration in which `r` is eligible. -/
def makeElig (s : State Node) (p r : Node) : State Node :=
  { s with cfg := makeEligCfg s r, known := upd s.known p (makeEligCfg s r) }

/-- MakeIneligible(p, r): primary `p` publishes a configuration in which `r` is not
eligible, and drops `r` from its sync set. -/
def makeInelig (s : State Node) (p r : Node) : State Node :=
  { s with cfg := makeIneligCfg s r, known := upd s.known p (makeIneligCfg s r),
           sync := upd s.sync p (upd (s.sync p) r false) }

/-- Learn(n): `n` adopts the latest configuration; unless it is the primary there,
it empties its sync set. -/
def learn (s : State Node) (n : Node) : State Node :=
  { s with known := upd s.known n s.cfg,
           sync := upd s.sync n (if s.cfg.prim = n then s.sync n else fun _ => false) }

/-- `cfg.elig \ {cfg.prim, n}`: the eligible set after `n` takes over from the
current primary. -/
def takeoverElig (s : State Node) (n : Node) : Node → Bool :=
  fun x => s.cfg.elig x && decide (x ≠ s.cfg.prim) && decide (x ≠ n)

/-- Takeover's configuration: next version, `n` primary, `takeoverElig` eligible, the
recorded incarnations unchanged. -/
def takeoverCfg (s : State Node) (n : Node) : Cfg Node := ⟨s.cfg.ver + 1, n, takeoverElig s n, s.cfg.inc⟩

/-- MatchElig of the new config: the matching eligible replicas. -/
def takeoverSync (s : State Node) (n : Node) : Node → Bool :=
  fun x => takeoverElig s n x && decide (s.cfg.inc x = s.inc x)

/-- Takeover(n): eligible replica `n` becomes primary in a new configuration. Its
sync set is the matching eligible replicas, its acks and commit point are reset, its
catch-up point is the end of its log (so it commits what it inherited before it
writes), and it writes with a new term. -/
def takeover (s : State Node) (n : Node) : State Node :=
  { s with cfg := takeoverCfg s n, known := upd s.known n (takeoverCfg s n),
           sync := upd s.sync n (takeoverSync s n),
           acked := upd s.acked n (fun _ => 0),
           commit := upd s.commit n 0,
           recon := upd s.recon n (s.log n).length,
           term := upd s.term n (s.cfg.ver + 1) }

/-- The point a replica must have acknowledged before `p` counts it: `p`'s catch-up
point while it is still reconciling, otherwise its commit point. -/
def catchUpPoint (s : State Node) (p : Node) : Nat :=
  if s.commit p < s.recon p then min (s.recon p) (s.log p).length else s.commit p

/-- `sync[p] \cap MatchElig(known[p])`: the sync members of `p` that are eligible in
`p`'s configuration with the incarnation it records for them. These are the replicas
that count toward `min-sync-replicas`. -/
def syncEligible (s : State Node) (p : Node) : Set Node :=
  {r | s.sync p r = true ∧ (s.known p).elig r = true ∧ (s.known p).inc r = s.inc r}

/-- Writable(p): `Cardinality(sync[p] \cap MatchElig(known[p])) >= m`, that is, at
least `m` distinct sync members of `p` are eligible in `p`'s configuration with the
incarnation it records for them. `Set.encard` is the cardinality in `ℕ∞`, so this
needs no finiteness assumption on `Node`. -/
def Writable (m : Nat) (s : State Node) (p : Node) : Prop :=
  (m : ℕ∞) ≤ (syncEligible s p).encard

/-- `Writable` is the earlier list form: some duplicate-free list of at least `m`
nodes, all counted. -/
theorem writable_iff_list (m : Nat) (s : State Node) (p : Node) :
    Writable m s p ↔ ∃ l : List Node, l.Nodup ∧ m ≤ l.length ∧
      ∀ r ∈ l, s.sync p r = true ∧ (s.known p).elig r = true ∧ (s.known p).inc r = s.inc r :=
  le_encard_iff_list m _

/-- Resync(r): a replica whose log has diverged from its primary's replaces it with
the primary's log up to the primary's catch-up point, and starts acking from 0. -/
def resync (s : State Node) (r : Node) : State Node :=
  { s with log := upd s.log r ((s.log (primaryOf s r)).take (catchUpPoint s (primaryOf s r))),
           acked := upd s.acked (primaryOf s r) (upd (s.acked (primaryOf s r)) r 0),
           commit := upd s.commit r (min (s.commit r) (s.commit (primaryOf s r))) }

/-- RestartEmpty(n): empty log, new incarnation, no volatile state; the current
primary forgets `n`'s ack and stops counting it. -/
def restartEmpty (s : State Node) (n : Node) : State Node :=
  { s with log := upd s.log n [],
           inc := upd s.inc n (s.inc n + 1),
           ackHigh := upd s.ackHigh n 0,
           commit := upd s.commit n 0,
           recon := upd s.recon n 0,
           sync := fun p => if p = n then (fun _ => false)
                            else if p = s.cfg.prim then upd (s.sync p) n false else s.sync p,
           acked := fun p => if p = n then (fun _ => 0)
                             else if p = s.cfg.prim then upd (s.acked p) n 0 else s.acked p }

/-- The rebuilt sync set of a restarted primary: `MatchElig(known[n]) \ {n}`, the
eligible replicas whose recorded incarnation matches. -/
def rebuiltSync (s : State Node) (n : Node) : Node → Bool :=
  fun r => (s.known n).elig r && decide ((s.known n).inc r = s.inc r) && decide (r ≠ n)

/-- RestartKeep(n): data and incarnation kept, volatile state lost. `n` must commit
its whole log again before it serves. If `n` is primary, its sync set is rebuilt from
the configuration it knows (`rebuiltSync`); otherwise it is empty. -/
def restartKeep (s : State Node) (n : Node) : State Node :=
  { s with commit := upd s.commit n 0,
           recon := upd s.recon n (s.log n).length,
           acked := upd s.acked n (fun _ => 0),
           sync := upd s.sync n
             (if (s.known n).prim = n ∧ (s.known n).inc n = s.inc n
              then rebuiltSync s n else fun _ => false) }

/-- RestartPartial(n, k), keeping the incarnation: `n` restarts from a persistence
file holding only the first `k` entries of its log. Everything else is RestartKeep on
the truncated log: volatile state lost, catch-up point at the end of what it holds,
sync replica set rebuilt if it is primary. -/
def restartPartialKeep (s : State Node) (n : Node) (k : Nat) : State Node :=
  { restartKeep s n with log := upd s.log n ((s.log n).take k), recon := upd s.recon n k }

/-- RestartPartial(n, k), taking a new incarnation: RestartEmpty, except that `n` keeps
the first `k` entries of its log as a starting point for resynchronisation. -/
def restartPartialFresh (s : State Node) (n : Node) (k : Nat) : State Node :=
  { restartEmpty s n with log := upd s.log n ((s.log n).take k) }

/-- The actions of the protocol, one per `Step` constructor. A run of
the protocol is a list of actions, so a counterexample's trace can be read off its
statement. `restartPartial n k` labels both outcomes of a stale restore. -/
inductive Action (Node : Type)
  | append (p : Node) | replicate (r : Node) | ack (r : Node) | commit (p : Node)
  | count (p r : Node) | makeElig (p r : Node) | makeInelig (p r : Node) | learn (n : Node)
  | takeover (n : Node) | resync (r : Node) | restartEmpty (n : Node) | restartKeep (n : Node)
  | restartPartial (n : Node) (k : Nat)

/-- The restart actions. The acknowledgement layer treats them apart from the other
actions: a node's held replies die with its client connections when it restarts. -/
def Action.isRestart : Action Node → Bool
  | .restartEmpty _ | .restartKeep _ | .restartPartial _ _ => true
  | _ => false

/-- The step relation. `m` is `min-sync-replicas`. Each constructor is one
action: its arguments after the state are the guard, and its result is the action's
label and the post-state. -/
inductive Step (m : Nat) : State Node → Action Node → State Node → Prop
  /-- A node that thinks it is primary, has enough sync replicas and has reconciled
  may append a write. -/
  | append (s p) : ThinksPrimary s p → Writable m s p → Reconciled s p → Step m s (.append p) (appendWrite s p)
  /-- A replica whose log is a strict prefix of its primary's may copy the next entry. -/
  | replicate (s r) : primaryOf s r ≠ r → s.log r <+: s.log (primaryOf s r) →
      (s.log r).length < (s.log (primaryOf s r)).length → Step m s (.replicate r) (replicate s r)
  /-- A replica whose log is a prefix of its primary's may acknowledge new entries. -/
  | ack (s r) : primaryOf s r ≠ r → s.log r <+: s.log (primaryOf s r) →
      s.acked (primaryOf s r) r < (s.log r).length → Step m s (.ack r) (ack s r)
  /-- A writable primary may commit its next entry once every sync member has
  acknowledged it. -/
  | commit (s p) : ThinksPrimary s p → Writable m s p → s.commit p < (s.log p).length →
      (∀ r, s.sync p r = true → s.commit p < s.acked p r) → Step m s (.commit p) (commitNext s p)
  /-- A primary may count one of its replicas once that replica has acknowledged up
  to the catch-up point. -/
  | count (s p r) : ThinksPrimary s p → r ≠ p → primaryOf s r = p → s.sync p r = false →
      catchUpPoint s p ≤ s.acked p r → Step m s (.count p r) (count s p r)
  /-- A primary that knows the latest configuration may make a sync member eligible. -/
  | makeElig (s p r) : ThinksPrimary s p → KnowsLatest s p → s.sync p r = true → s.cfg.elig r = false →
      Step m s (.makeElig p r) (makeElig s p r)
  /-- A primary that knows the latest configuration may make a replica ineligible. -/
  | makeInelig (s p r) : ThinksPrimary s p → KnowsLatest s p → s.cfg.elig r = true →
      Step m s (.makeInelig p r) (makeInelig s p r)
  /-- A node with a stale configuration may learn the latest one. -/
  | learn (s n) : ¬ KnowsLatest s n → Step m s (.learn n) (learn s n)
  /-- An eligible replica that knows the latest configuration, with a matching
  recorded incarnation, may take over from the current primary. -/
  | takeover (s n) : KnowsLatest s n → s.cfg.elig n = true → n ≠ s.cfg.prim →
      s.cfg.inc n = s.inc n → Step m s (.takeover n) (takeover s n)
  /-- A diverged replica may resync once its primary has neither counted it nor made
  it eligible. -/
  | resync (s r) : primaryOf s r ≠ r → ¬ (s.log r <+: s.log (primaryOf s r)) →
      s.sync (primaryOf s r) r = false → (s.known (primaryOf s r)).elig r = false →
      Step m s (.resync r) (resync s r)
  /-- A node that knows the latest configuration may restart empty while some other
  authoritative node keeps its data (the survival assumption). -/
  | restartEmpty (s n) : KnowsLatest s n → (∃ m, m ≠ n ∧ IsAuthoritative s m) → Step m s (.restartEmpty n) (restartEmpty s n)
  /-- A node that knows the latest configuration may restart and keep its data. -/
  | restartKeep (s n) : KnowsLatest s n → Step m s (.restartKeep n) (restartKeep s n)
  /-- A node may restart from a persistence file holding only the first `k` entries of
  its log. It keeps its incarnation only if the file covers every offset it has
  acknowledged (`ackHigh n ≤ k`). -/
  | restartPartialKeep (s n k) : KnowsLatest s n → k < (s.log n).length → s.ackHigh n ≤ k →
      Step m s (.restartPartial n k) (restartPartialKeep s n k)
  /-- Otherwise it takes a new incarnation and rejoins as after RestartEmpty, under the
  same survival assumption, keeping the `k` entries it has. -/
  | restartPartialFresh (s n k) : KnowsLatest s n → k < (s.log n).length → k < s.ackHigh n →
      (∃ m, m ≠ n ∧ IsAuthoritative s m) →
      Step m s (.restartPartial n k) (restartPartialFresh s n k)

/-- The protocol as a labelled transition system (CSLib's `LTS`): `Step` is its
transition relation, so CSLib's runs (`MTr`), reachability (`CanReach`), invariants
(`TrInv`, `MTrInv`) apply to it. -/
def lts (m : Nat) : LTS (State Node) (Action Node) where
  Tr := Step m

@[simp] theorem lts_tr {m : Nat} {s s' : State Node} {μ : Action Node} :
    (lts m).Tr s μ s' ↔ Step m s μ s' := Iff.rfl

/-- The states reachable from `init i` by any finite run. -/
def Reachable (m : Nat) (i : Node) (s : State Node) : Prop :=
  (lts m).CanReach (init i) s

theorem Reachable.init {m : Nat} (i : Node) : Reachable m i (init i) :=
  LTS.CanReach.refl (lts m) _

/-- One more step keeps a state reachable. -/
theorem Reachable.stepR {m : Nat} {i : Node} {s s' : State Node} {μ : Action Node}
    (h : Reachable m i s) (hs : Step m s μ s') : Reachable m i s' :=
  let ⟨_, run⟩ := h; ⟨_, LTS.MTr.stepR (lts m) run hs⟩

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
