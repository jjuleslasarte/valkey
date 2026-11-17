import Mathlib.Data.List.Nodup

/-!
# Linearizability: the definition (no proof yet)

Herlihy and Wing, "Linearizability: A Correctness Condition for Concurrent Objects",
TOPLAS 12(3), 1990, §2. The first part is generic: histories of invocation and
response events on one object, and `Linearizable spec h`. The second part is the
sequential specification of a log object. The third part says how a client history
of the synchronous-replication design maps onto these events, and checks the
definition on five small histories.

No theorem here says that the model's client histories are linearizable.
-/

open scoped List

namespace SyncReplication.Lin

/-! ## Histories (H&W §2) -/

variable {P Op Res : Type}

/-- H&W §2: an *event* is an invocation `⟨x op A⟩` or a response `⟨x res A⟩` by process
`A`. There is one object, so `x` is left out. Each event carries an operation id that
pairs an invocation with its response; H&W pair them by process instead. -/
inductive Event (P Op Res : Type) where
  | inv (id : Nat) (proc : P) (op : Op)
  | res (id : Nat) (proc : P) (result : Res)
  deriving DecidableEq, Repr

/-- H&W §2: a *history* is a finite sequence of events, oldest first. -/
abbrev History (P Op Res : Type) := List (Event P Op Res)

namespace Event

/-- The operation id of an event. -/
def id : Event P Op Res → Nat
  | .inv i _ _ => i
  | .res i _ _ => i

/-- The process of an event. -/
def proc : Event P Op Res → P
  | .inv _ p _ => p
  | .res _ p _ => p

/-- Whether an event is an invocation. -/
def isInv : Event P Op Res → Bool
  | .inv .. => true
  | .res .. => false

/-- Whether an event is a response. -/
def isRes : Event P Op Res → Bool
  | .inv .. => false
  | .res .. => true

end Event

/-- H&W §2: an *operation* is an invocation with its matching response. -/
structure Operation (P Op Res : Type) where
  id : Nat
  proc : P
  op : Op
  result : Res
  deriving DecidableEq, Repr

/-- The invocation event of an operation. -/
def Operation.inv (x : Operation P Op Res) : Event P Op Res := .inv x.id x.proc x.op

/-- The response event of an operation. -/
def Operation.res (x : Operation P Op Res) : Event P Op Res := .res x.id x.proc x.result

/-- The operation and result of an operation, the part a sequential specification sees. -/
def Operation.call (x : Operation P Op Res) : Op × Res := (x.op, x.result)

/-- H&W §2, *well-formed*, stated with operation ids: no two invocations share an id, no
two responses share an id, and each response follows an invocation with its id and
process. H&W ask instead that each process's subhistory be sequential; with ids, one
process may have several operations open. -/
def WellFormed (h : History P Op Res) : Prop :=
  ((h.filter Event.isInv).map Event.id).Nodup ∧
  ((h.filter Event.isRes).map Event.id).Nodup ∧
  ∀ e ∈ h, e.isRes → ∃ e' ∈ h, e'.isInv ∧ e'.id = e.id ∧ e'.proc = e.proc ∧ [e', e] <+ h

instance [DecidableEq P] [DecidableEq Op] [DecidableEq Res] (h : History P Op Res) :
    Decidable (WellFormed h) := by
  unfold WellFormed; infer_instance

/-- The result of the first response with id `i` in `h`, if any. -/
def resultOf (h : History P Op Res) (i : Nat) : Option Res :=
  h.findSome? fun
    | .res j _ r => if j = i then some r else none
    | .inv .. => none

/-- The operation an invocation starts, given a lookup of results; none for a response
or an invocation without a result. -/
def opOf (g : Nat → Option Res) : Event P Op Res → Option (Operation P Op Res)
  | .inv i p o => (g i).map fun r => ⟨i, p, o, r⟩
  | .res .. => none

/-- H&W §2, `complete(H)`: the operations of `h` whose invocation has a matching
response, in the order of their invocations. -/
def complete (h : History P Op Res) : List (Operation P Op Res) :=
  h.filterMap (opOf (resultOf h))

/-- H&W §2: the *pending* invocations of `h`, those with no matching response, as
(id, process, operation). -/
def pending (h : History P Op Res) : List (Nat × P × Op) :=
  h.filterMap fun
    | .inv i p o => if resultOf h i = none then some (i, p, o) else none
    | .res .. => none

/-- H&W §2, the real-time order `<_H`: `x <_H y` iff the response of `x` precedes the
invocation of `y` in `h`. -/
def Precedes (h : History P Op Res) (x y : Operation P Op Res) : Prop :=
  [x.res, y.inv] <+ h

instance [DecidableEq P] [DecidableEq Op] [DecidableEq Res] (h : History P Op Res)
    (x y : Operation P Op Res) : Decidable (Precedes h x y) := by
  unfold Precedes; infer_instance

/-- H&W §2, *extension*: `h'` is `h` followed by responses, and is well-formed. So each
added response answers a distinct pending invocation of `h`, with its process. -/
def IsExtension (h h' : History P Op Res) : Prop :=
  ∃ rs, h' = h ++ rs ∧ (∀ e ∈ rs, e.isRes) ∧ WellFormed h'

/-- H&W §2, `<_H ⊆ <_S`: every pair of operations of `S` ordered in real time by `h`
comes in that order in `S`. -/
def RespectsRealTime (h : History P Op Res) (S : List (Operation P Op Res)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, Precedes h x y → [x, y] <+ S

instance [DecidableEq P] [DecidableEq Op] [DecidableEq Res] (h : History P Op Res)
    (S : List (Operation P Op Res)) : Decidable (RespectsRealTime h S) := by
  unfold RespectsRealTime Precedes; infer_instance

/-- H&W §2, *linearizable*: `h` has an extension `h'` and a sequential history `S` such
that `S` holds exactly the operations of `complete(h')` (L1, H&W's "equivalent"), `S`
is legal for `spec`, and `S` respects `<_H` (L2). Extending `h` gives some pending
invocations a response; `complete` drops the rest. A sequential history is a list of
operations, each an invocation followed at once by its response. `spec` is the set of
legal sequential histories of the object, as lists of (operation, result). -/
def Linearizable (spec : List (Op × Res) → Prop) (h : History P Op Res) : Prop :=
  ∃ h', IsExtension h h' ∧ ∃ S : List (Operation P Op Res),
    S.Perm (complete h') ∧ spec (S.map Operation.call) ∧ RespectsRealTime h S

/-! ## The log object: a sequential specification -/

variable {V : Type}

/-- Operations on the log: append a value, or read the whole log. -/
inductive LogOp (V : Type) where
  | write (v : V)
  | read
  deriving DecidableEq, Repr

/-- Results: a write returns OK, a read returns a log. -/
inductive LogRes (V : Type) where
  | ok
  | log (l : List V)
  deriving DecidableEq, Repr

/-- The values written in a sequential history, in order. -/
def writes (S : List (LogOp V × LogRes V)) : List V :=
  S.filterMap fun
    | (.write v, _) => some v
    | (.read, _) => none

/-- The result the log gives an operation after the sequential history `pre`. -/
def answer (pre : List (LogOp V × LogRes V)) : LogOp V → LogRes V
  | .write _ => .ok
  | .read => .log (writes pre)

/-- A sequential history is legal for the log iff each write returns OK and each read
returns exactly the values written before it, in order. -/
def LogLegal (S : List (LogOp V × LogRes V)) : Prop :=
  ∀ k (hk : k < S.length), S[k].2 = answer (S.take k) S[k].1

instance [DecidableEq V] (S : List (LogOp V × LogRes V)) : Decidable (LogLegal S) := by
  unfold LogLegal; infer_instance

/-! ## Client histories

A client history of the design maps onto events as follows. A client is a process.
Sending a write is an invocation `write v`; an OK reply is the response `ok`. A write
answered UNCOMMITTED gets no response event: it stays pending forever, because it may
still commit. `Linearizable` then either drops it or gives it a response and places it
after its invocation, so later reads may or may not include it, and no read that
responded before it was invoked does. A read sent to node n is an invocation `read`,
answered by n's log once n may serve the read. Values stay abstract.

The five histories below check the definition against these expectations. In each,
client 0 writes the value 1 (operation 0) and client 1 reads (operation 1).
-/

/-- Client 0 writes 1. -/
def w : Operation Nat (LogOp Nat) (LogRes Nat) := ⟨0, 0, .write 1, .ok⟩

/-- Client 1 reads, getting `m`. -/
def rd (m : List Nat) : Operation Nat (LogOp Nat) (LogRes Nat) := ⟨1, 1, .read, .log m⟩

/-- A sequential history, the write then a read that sees it, is linearizable. -/
theorem sequential_linearizable :
    Linearizable LogLegal [w.inv, w.res, (rd [1]).inv, (rd [1]).res] :=
  ⟨_, ⟨[], rfl, by decide, by decide⟩, [w, rd [1]], by decide, by decide, by decide⟩

/-- An UNCOMMITTED write that a later read sees is linearizable: the write is completed. -/
theorem uncommitted_seen_linearizable :
    Linearizable LogLegal [w.inv, (rd [1]).inv, (rd [1]).res] :=
  ⟨_, ⟨[w.res], rfl, by decide, by decide⟩, [w, rd [1]], by decide, by decide, by decide⟩

/-- An UNCOMMITTED write that a later read misses is linearizable: the write is dropped. -/
theorem uncommitted_unseen_linearizable :
    Linearizable LogLegal [w.inv, (rd []).inv, (rd []).res] :=
  ⟨_, ⟨[], rfl, by decide, by decide⟩, [rd []], by decide, by decide, by decide⟩

/-! ### Lemmas for the two negative checks -/

theorem mem_complete_append {h rs : History P Op Res} {x : Operation P Op Res}
    (hx : x ∈ complete h) : x ∈ complete (h ++ rs) := by
  unfold complete at *
  obtain ⟨e, he, hex⟩ := List.mem_filterMap.1 hx
  refine List.mem_filterMap.2 ⟨e, List.mem_append_left _ he, ?_⟩
  cases e with
  | inv i p o =>
    cases hr : resultOf h i with
    | none => simp [opOf, hr] at hex
    | some r =>
      have : resultOf (h ++ rs) i = some r := by
        simp only [resultOf, List.findSome?_append] at hr ⊢; simp [hr]
      simpa [opOf, hr, this] using hex
  | res => simp [opOf] at hex

theorem inv_mem_of_mem_complete {h : History P Op Res} {x : Operation P Op Res}
    (hx : x ∈ complete h) : x.inv ∈ h := by
  obtain ⟨e, he, hex⟩ := List.mem_filterMap.1 hx
  cases e with
  | inv i p o =>
    cases hr : resultOf h i <;> simp [opOf, hr] at hex
    subst hex; exact he
  | res => simp [opOf] at hex

theorem filterMap_opOf_ids (g : Nat → Option Res) (l : History P Op Res) :
    ((l.filterMap (opOf g)).map Operation.id).Sublist ((l.filter Event.isInv).map Event.id) := by
  induction l with
  | nil => simp
  | cons e l ih =>
    cases e with
    | inv i p o =>
      cases hg : g i with
      | none =>
        simp only [List.filterMap_cons, opOf, hg, Option.map_none, List.filter_cons,
          Event.isInv, ite_true, List.map_cons, Event.id]
        exact ih.cons i
      | some r =>
        simp only [List.filterMap_cons, opOf, hg, Option.map_some, List.filter_cons,
          Event.isInv, ite_true, List.map_cons, Event.id]
        exact ih.cons_cons i
    | res =>
      simp only [List.filterMap_cons, opOf, List.filter_cons, Event.isInv]
      simpa using ih

theorem nodup_complete {h : History P Op Res} (hw : WellFormed h) : (complete h).Nodup :=
  List.Nodup.of_map _ ((hw.1).sublist (filterMap_opOf_ids _ h))

/-- In a list without duplicates, two elements are not in both orders. -/
theorem not_both_orders {α : Type} {a b : α} :
    ∀ {S : List α}, S.Nodup → [a, b] <+ S → [b, a] <+ S → False
  | [], _, h, _ => by simp at h
  | x :: s, hn, h1, h2 => by
    have hx := (List.nodup_cons.1 hn).1
    rcases List.sublist_cons_iff.1 h1 with h1 | ⟨t, ht, h1⟩ <;>
      rcases List.sublist_cons_iff.1 h2 with h2 | ⟨u, hu, h2⟩
    · exact not_both_orders (List.nodup_cons.1 hn).2 h1 h2
    · simp only [List.cons.injEq] at hu; rw [← hu.1] at hx
      exact hx (h1.subset (by simp))
    · simp only [List.cons.injEq] at ht; rw [← ht.1] at hx
      exact hx (h2.subset (by simp))
    · simp only [List.cons.injEq] at ht hu; rw [← ht.2] at h1; rw [← hu.1] at hx
      exact hx (h1.subset (by simp))

/-- `[a, b] <+ S` splits `S` at `b` with `a` before it. -/
theorem split_of_pair {α : Type} {a b : α} {S : List α} (h : [a, b] <+ S) :
    ∃ s₁ s₂, S = s₁ ++ b :: s₂ ∧ a ∈ s₁ := by
  obtain ⟨r₁, r₂, rfl, ha, hb⟩ := List.cons_sublist_iff.1 h
  obtain ⟨t₁, t₂, rfl⟩ := List.append_of_mem (hb.subset (List.mem_singleton_self b))
  exact ⟨r₁ ++ t₁, t₂, by simp, List.mem_append_left _ ha⟩

/-- A legal log history gives the operation after `s₁` the answer for `s₁`. -/
theorem LogLegal.split {S s₁ s₂ : List (LogOp V × LogRes V)} {c : LogOp V × LogRes V}
    (hl : LogLegal S) (hS : S = s₁ ++ c :: s₂) : c.2 = answer s₁ c.1 := by
  subst hS
  have := hl s₁.length (by simp)
  simpa using this

theorem mem_writes {s : List (Operation P (LogOp V) (LogRes V))} {x : Operation P (LogOp V) (LogRes V)}
    {v : V} (hx : x ∈ s) (hv : x.op = .write v) : v ∈ writes (s.map Operation.call) :=
  List.mem_filterMap.2 ⟨x.call, List.mem_map_of_mem hx, by simp [Operation.call, hv]⟩

/-- A read that misses a write which responded before the read was invoked is not
linearizable. -/
theorem staleRead_not_linearizable :
    ¬ Linearizable LogLegal [w.inv, w.res, (rd []).inv, (rd []).res] := by
  rintro ⟨_, ⟨rs, rfl, -, -⟩, S, hp, hl, hrt⟩
  have hw : w ∈ S := hp.mem_iff.2 (mem_complete_append (by decide))
  have hr : rd [] ∈ S := hp.mem_iff.2 (mem_complete_append (by decide))
  obtain ⟨s₁, s₂, hS, hw₁⟩ := split_of_pair (hrt _ hw _ hr (by decide))
  have := hl.split (s₁ := s₁.map Operation.call) (s₂ := s₂.map Operation.call) (c := (rd []).call) (by simp [hS])
  have h1 := mem_writes hw₁ (v := 1) rfl
  simp only [rd, Operation.call, answer, LogRes.log.injEq] at this
  simp [← this] at h1

/-- An UNCOMMITTED write does not appear in a read that responded before the write was
invoked. -/
theorem uncommitted_notBefore :
    ¬ Linearizable LogLegal [(rd [1]).inv, (rd [1]).res, w.inv] := by
  rintro ⟨_, ⟨rs, rfl, hrs, hwf⟩, S, hp, hl, hrt⟩
  have hn : S.Nodup := hp.nodup_iff.2 (nodup_complete hwf)
  have hr : rd [1] ∈ S := hp.mem_iff.2 (mem_complete_append (by decide))
  obtain ⟨s₁, s₂, hS⟩ := List.append_of_mem hr
  have := hl.split (s₁ := s₁.map Operation.call) (s₂ := s₂.map Operation.call) (c := (rd [1]).call) (by simp [hS])
  simp only [rd, Operation.call, answer, LogRes.log.injEq] at this
  have h1 : (1 : Nat) ∈ writes (s₁.map Operation.call) := by simp [← this]
  obtain ⟨c, hc, hc1⟩ := List.mem_filterMap.1 h1
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hc
  have hzS : z ∈ S := by simp [hS, hz]
  -- `z` is a write of 1, so its invocation is operation 0's, invoked after the read responded.
  have hzop : z.op = .write 1 := by
    rcases z with ⟨_, _, _ | _, _⟩ <;> simp_all [Operation.call]
  have hzinv : z.inv ∈ [(rd [1]).inv, (rd [1]).res, w.inv] := by
    rcases List.mem_append.1 (inv_mem_of_mem_complete (hp.mem_iff.1 hzS)) with h | h
    · exact h
    · simpa [Operation.inv, Event.isRes] using hrs _ h
  have hzw : z.inv = w.inv := by
    simp [Operation.inv, Operation.res, rd, w, hzop] at hzinv ⊢; exact hzinv
  have hpre : Precedes [(rd [1]).inv, (rd [1]).res, w.inv] (rd [1]) z := by
    unfold Precedes; rw [hzw]; decide
  exact not_both_orders hn (hrt _ hr _ hzS hpre)
    (by rw [hS]; exact (List.singleton_sublist.2 hz).append (List.singleton_sublist.2 (by simp)))

end SyncReplication.Lin
