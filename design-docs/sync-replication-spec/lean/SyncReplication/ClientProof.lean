import SyncReplication.Client

/-!
# Client histories are linearizable

`linearizable`: with `margin ≥ 2 · drift`, every reachable client history is
linearizable for the log specification (`Lin.Linearizable Lin.LogLegal`).

The proof gives each operation a linearization point: a write when its entry joins the
committed history, a read when it responds. The ghost `lin` lists the operations
linearized so far with the history length at their point. `Lin.linearizable_of_points`
shows that such a list is enough: if each point lies between the operation's
invocation and its response, the points are in order, every response belongs to a
linearized operation, and the list is legal, then the history is linearizable. The
client invariant (`ClientInvariant`) supplies these facts, using `AckedDurable` for
writes released as OK and `NoStaleRead` for reads.
-/

open scoped List

namespace SyncReplication.Lin

variable {P Op Res : Type} [DecidableEq P] [DecidableEq Op] [DecidableEq Res]

/-! ## From linearization points to linearizability -/

theorem inv_unique {h : History P Op Res} (hw : WellFormed h) {e₁ e₂ : Event P Op Res}
    (h₁ : e₁ ∈ h) (h₂ : e₂ ∈ h) (i₁ : e₁.isInv) (i₂ : e₂.isInv) (he : e₁.id = e₂.id) : e₁ = e₂ :=
  List.inj_on_of_nodup_map hw.1 (List.mem_filter.2 ⟨h₁, i₁⟩) (List.mem_filter.2 ⟨h₂, i₂⟩) he

theorem res_unique {h : History P Op Res} (hw : WellFormed h) {e₁ e₂ : Event P Op Res}
    (h₁ : e₁ ∈ h) (h₂ : e₂ ∈ h) (i₁ : e₁.isRes) (i₂ : e₂.isRes) (he : e₁.id = e₂.id) : e₁ = e₂ :=
  List.inj_on_of_nodup_map hw.2.1 (List.mem_filter.2 ⟨h₁, i₁⟩) (List.mem_filter.2 ⟨h₂, i₂⟩) he

theorem resultOf_some {h : History P Op Res} {i : Nat} {r : Res} (hr : resultOf h i = some r) :
    ∃ q, Event.res i q r ∈ h := by
  obtain ⟨e, he, hf⟩ := List.exists_of_findSome?_eq_some hr
  cases e with
  | inv => simp at hf
  | res j q r' =>
    simp only at hf; split at hf
    · subst_vars; simp only [Option.some.injEq] at hf; subst hf; exact ⟨q, he⟩
    · simp at hf

/-- In a well-formed history, an operation is complete iff its invocation and its
response are both there. -/
theorem mem_complete_iff {h : History P Op Res} (hw : WellFormed h) {x : Operation P Op Res} :
    x ∈ complete h ↔ x.inv ∈ h ∧ x.res ∈ h := by
  constructor
  · intro hx
    refine ⟨inv_mem_of_mem_complete hx, ?_⟩
    obtain ⟨e, he, hex⟩ := List.mem_filterMap.1 hx
    cases e with
    | res => simp [opOf] at hex
    | inv i p o =>
      cases hr : resultOf h i with
      | none => simp [opOf, hr] at hex
      | some r =>
        simp only [opOf, hr, Option.map_some, Option.some.injEq] at hex; subst hex
        obtain ⟨q, hq⟩ := resultOf_some hr
        obtain ⟨e', he', hi', hid', hp', -⟩ := hw.2.2 _ hq rfl
        have := inv_unique hw he' he hi' rfl hid'
        subst this
        simp only [Event.proc] at hp'
        subst hp'; exact hq
  · rintro ⟨hi, hr⟩
    refine List.mem_filterMap.2 ⟨x.inv, hi, ?_⟩
    have hsome : (resultOf h x.id).isSome := by
      rw [resultOf, List.findSome?_isSome_iff]
      exact ⟨x.res, hr, by simp [Operation.res]⟩
    obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.1 hsome
    obtain ⟨q, hq⟩ := resultOf_some hr'
    have := res_unique hw hq hr rfl rfl rfl
    simp only [Operation.res, Event.res.injEq] at this
    obtain ⟨-, -, rfl⟩ := this
    simp [opOf, Operation.inv, hr']

/-- Two elements at increasing positions form a sublist. -/
theorem pair_sublist_of_getElem? {α : Type} {l : List α} {i j : Nat} {a b : α} (hij : i < j)
    (ha : l[i]? = some a) (hb : l[j]? = some b) : [a, b] <+ l := by
  have hj : j < l.length := (List.getElem?_eq_some_iff.1 hb).1
  rw [← List.take_append_drop j l, List.drop_eq_getElem_cons hj]
  have hb' : l[j] = b := (List.getElem?_eq_some_iff.1 hb).2
  rw [hb']
  have hat : a ∈ l.take j := by
    rw [List.mem_iff_getElem?]; exact ⟨i, by rw [List.getElem?_take, if_pos hij]; exact ha⟩
  exact (List.singleton_sublist.2 hat).append (List.singleton_sublist.2 (List.mem_cons_self))

/-- A sublist of two elements gives their positions. -/
theorem getElem?_of_pair_sublist {α : Type} {l : List α} {a b : α} (h : [a, b] <+ l) :
    ∃ i j : Nat, i < j ∧ l[i]? = some a ∧ l[j]? = some b := by
  obtain ⟨s₁, s₂, rfl, ha⟩ := split_of_pair h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ha
  have hil : i < s₁.length := (List.getElem?_eq_some_iff.1 hi).1
  exact ⟨i, s₁.length, hil, by rw [List.getElem?_append_left hil]; exact hi, by simp⟩

/-- **Linearization points suffice.** Let `lin` list operations, each with a point (a
position in `h`). If every operation of `lin` is invoked before its point and responds,
if at all, at or after it; the points are in order; every response in `h` belongs to an
operation of `lin`; and `lin` is legal, then `h` is linearizable. The extension adds the
missing responses of the operations of `lin`; every other pending invocation is
dropped. -/
theorem linearizable_of_points {spec : List (Op × Res) → Prop} {h : History P Op Res}
    (lin : List (Operation P Op Res × Nat)) (hw : WellFormed h)
    (hids : (lin.map fun u => u.1.id).Nodup)
    (hinv : ∀ u ∈ lin, u.1.inv ∈ h)
    (hinvLt : ∀ u ∈ lin, ∀ i, h[i]? = some u.1.inv → i < u.2)
    (hresGe : ∀ u ∈ lin, ∀ i, h[i]? = some u.1.res → u.2 ≤ i)
    (hresEq : ∀ u ∈ lin, ∀ e ∈ h, e.isRes → e.id = u.1.id → e = u.1.res)
    (hsorted : lin.Pairwise fun u v => u.2 ≤ v.2)
    (hresp : ∀ e ∈ h, e.isRes → ∃ u ∈ lin, u.1.res = e)
    (hspec : spec ((lin.map Prod.fst).map Operation.call)) :
    Linearizable spec h := by
  classical
  set S := lin.map Prod.fst with hSdef
  have hSids : (S.map Operation.id).Nodup := by rw [hSdef, List.map_map]; exact hids
  have hSnd : S.Nodup := List.Nodup.of_map _ hSids
  have hSinv : ∀ x ∈ S, x.inv ∈ h := by
    intro x hx; obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx; exact hinv u hu
  set rs := (S.filter fun x => x.res ∉ h).map Operation.res with hrs
  have hrsRes : ∀ e ∈ rs, e.isRes := by
    intro e he; obtain ⟨x, -, rfl⟩ := List.mem_map.1 he; rfl
  -- The extension is well-formed.
  have hw' : WellFormed (h ++ rs) := by
    refine ⟨?_, ?_, ?_⟩
    · have : rs.filter Event.isInv = [] :=
        List.filter_eq_nil_iff.2 fun e he => by have := hrsRes e he; cases e <;> simp_all [Event.isInv, Event.isRes]
      rw [List.filter_append, this, List.append_nil]; exact hw.1
    · have hf : rs.filter Event.isRes = rs := List.filter_eq_self.2 hrsRes
      rw [List.filter_append, hf, List.map_append, List.nodup_append]
      refine ⟨hw.2.1, ?_, ?_⟩
      · rw [hrs, List.map_map]
        have : ((S.filter fun x => x.res ∉ h).map (Event.id ∘ Operation.res)) =
            (S.filter fun x => x.res ∉ h).map Operation.id := by
          apply List.map_congr_left; intro x _; rfl
        rw [this]; exact hSids.sublist ((List.filter_sublist).map _)
      · intro a ha b hb hab; subst hab
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
        obtain ⟨e', he', heq⟩ := List.mem_map.1 hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he'
        obtain ⟨hxS, hxn⟩ := List.mem_filter.1 hx
        obtain ⟨heh, hres⟩ := List.mem_filter.1 he
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hxS
        have := hresEq u hu e heh hres heq.symm
        simp only [decide_eq_true_eq] at hxn; exact hxn (this ▸ heh)
    · intro e he hres
      rcases List.mem_append.1 he with he | he
      · obtain ⟨e', h1, h2, h3, h4, h5⟩ := hw.2.2 e he hres
        exact ⟨e', List.mem_append_left _ h1, h2, h3, h4, h5.trans (List.sublist_append_left _ _)⟩
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
        have hxS := (List.mem_filter.1 hx).1
        exact ⟨x.inv, List.mem_append_left _ (hSinv x hxS), rfl, rfl, rfl,
          (List.singleton_sublist.2 (hSinv x hxS)).append (List.singleton_sublist.2 he)⟩
  refine ⟨h ++ rs, ⟨rs, rfl, hrsRes, hw'⟩, S, ?_, hspec, ?_⟩
  · -- `S` holds exactly the complete operations of the extension.
    refine (List.perm_ext_iff_of_nodup hSnd (nodup_complete hw')).2 fun x => ?_
    rw [mem_complete_iff hw']
    constructor
    · intro hx
      refine ⟨List.mem_append_left _ (hSinv x hx), ?_⟩
      by_cases hr : x.res ∈ h
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, by simpa using hr⟩, rfl⟩)
    · rintro ⟨hi, hr⟩
      have hi' : x.inv ∈ h := by
        rcases List.mem_append.1 hi with hi | hi
        · exact hi
        · exact absurd (hrsRes _ hi) (by simp [Operation.inv, Event.isRes])
      obtain ⟨y, hyS, hyr⟩ : ∃ y ∈ S, y.res = x.res := by
        rcases List.mem_append.1 hr with hr | hr
        · obtain ⟨u, hu, hur⟩ := hresp _ hr rfl
          exact ⟨u.1, List.mem_map_of_mem hu, hur⟩
        · obtain ⟨y, hy, hyr⟩ := List.mem_map.1 hr
          exact ⟨y, (List.mem_filter.1 hy).1, hyr⟩
      have hyx : y.inv = x.inv := by
        have hid : y.id = x.id := by
          have := congrArg Event.id hyr; simpa [Operation.res, Event.id] using this
        exact inv_unique hw (hSinv y hyS) hi' rfl rfl (by simpa [Operation.inv, Event.id] using hid)
      have : y = x := by
        rcases x with ⟨xi, xp, xo, xr⟩; rcases y with ⟨yi, yp, yo, yr⟩
        simp only [Operation.res, Operation.inv, Event.res.injEq, Event.inv.injEq] at hyr hyx
        obtain ⟨rfl, rfl, rfl⟩ := hyr; obtain ⟨-, -, rfl⟩ := hyx; rfl
      exact this ▸ hyS
  · -- `S` respects the real-time order.
    intro x hx y hy hpre
    obtain ⟨i, j, hij, hi, hj⟩ := getElem?_of_pair_sublist hpre
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hy
    have h1 := hresGe u hu i hi
    have h2 := hinvLt v hv j hj
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hu
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hv
    rcases Nat.lt_or_ge p q with hpq | hpq
    · have := pair_sublist_of_getElem? hpq hp hq
      exact this.map Prod.fst
    · exfalso
      rcases Nat.lt_or_eq_of_le hpq with hqp | rfl
      · have hpl := (List.getElem?_eq_some_iff.1 hp)
        have hql := (List.getElem?_eq_some_iff.1 hq)
        have := List.pairwise_iff_getElem.1 hsorted q p hql.1 hpl.1 hqp
        rw [hpl.2, hql.2] at this; omega
      · rw [hp] at hq; cases hq; omega

end SyncReplication.Lin

namespace SyncReplication

open Lin

variable {Node : Type} [DecidableEq Node]

/-! ## The client invariant -/

/-- Every entry of `L` was appended: some append has its offset and value. -/
def Keyed (w : List Written) (L : List Nat) : Prop :=
  ∀ j v, L[j]? = some v → ∃ x ∈ w, x.offset = j + 1 ∧ x.replId = v

/-- Operation `i` has a response in `H`. -/
def Responded (H : ClientHistory) (i : Nat) : Prop := ∃ e ∈ H, e.isRes ∧ e.id = i

/-- The client layer's invariant: the lease and reply invariants, plus facts about the
history, the appends, the held replies, the operations in progress and the
linearization so far. -/
structure ClientInvariant (P : LeaseParams) (a : ClientState Node) : Prop where
  lease : LeaseInvariant P a.lease
  reply : ReplyInvariant a.reply
  /-- The history is well-formed, and its ids are below the counter. -/
  wf : WellFormed a.history
  idsLt : ∀ e ∈ a.history, e.id < a.nextOp
  /-- No two appends share an offset and ID, or an operation. -/
  keysNodup : (a.written.map fun x => (x.offset, x.replId)).Nodup
  opsNodup : (a.written.map Written.op).Nodup
  /-- Every append is of an invoked write, with an ID handed out. -/
  writtenInv : ∀ x ∈ a.written, Event.inv x.op x.client (.write x.op) ∈ a.history
  writtenIds : ∀ x ∈ a.written, x.replId ∈ a.lease.core.usedIds
  /-- An append with a node's current ID, of a node that thinks it is primary, is within
  that node's log; so its next append has a new offset-and-ID pair. -/
  owned : ∀ x ∈ a.written, ∀ p, ThinksPrimary a.lease.core p → a.lease.core.replId p = x.replId →
    x.offset ≤ (a.lease.core.log p).length
  /-- No two nodes that think they are primary share an ID. -/
  uniqPrim : ∀ p q, ThinksPrimary a.lease.core p → ThinksPrimary a.lease.core q →
    a.lease.core.replId p = a.lease.core.replId q → p = q
  /-- Every entry of every log, and of the committed history, was appended. -/
  logKeyed : ∀ n, Keyed a.written (a.lease.core.log n)
  histKeyed : Keyed a.written a.lease.core.hist
  /-- A write that has responded is in the committed history. -/
  respondedCommitted : ∀ x ∈ a.written, Responded a.history x.op →
    1 ≤ x.offset ∧ a.lease.core.hist[x.offset - 1]? = some x.replId
  /-- Each held reply is of one append, whose write has not responded. -/
  heldKeyed : ∀ h ∈ a.held, ∃ x ∈ a.written, x.offset = h.offset ∧ x.replId = h.replId
  heldKeysNodup : (a.held.map fun h => (h.offset, h.replId)).Nodup
  heldPending : ∀ h ∈ a.held, ∀ x ∈ a.written, x.offset = h.offset → x.replId = h.replId →
    ¬ Responded a.history x.op
  /-- Writes waiting to be appended, and reads waiting for an answer, are invoked and
  have not responded. -/
  waitingInv : ∀ u ∈ a.waiting, Event.inv u.1 u.2 (.write u.1) ∈ a.history ∧
    ¬ Responded a.history u.1 ∧ u.1 ∉ a.written.map Written.op
  waitingNodup : (a.waiting.map Prod.fst).Nodup
  readingInv : ∀ u ∈ a.reading, Event.inv u.1 u.2.1 .read ∈ a.history ∧ ¬ Responded a.history u.1
  readingNodup : (a.reading.map Prod.fst).Nodup
  /-- The linearization so far: committed writes, in the history's order, and reads
  that have responded. -/
  linShape : ∀ u ∈ a.lin, (∃ x ∈ a.written, u.1 = x.toOp) ∨ (u.1.op = .read ∧ u.1.res ∈ a.history)
  linWrites : writes ((a.lin.map Prod.fst).map Operation.call) = logOps a.written a.lease.core.hist
  /-- A linearized write is in the committed history. -/
  linCommitted : ∀ u ∈ a.lin, ∀ x ∈ a.written, u.1 = x.toOp →
    1 ≤ x.offset ∧ a.lease.core.hist[x.offset - 1]? = some x.replId
  linIds : (a.lin.map fun u => u.1.id).Nodup
  linInv : ∀ u ∈ a.lin, u.1.inv ∈ a.history
  /-- Each point is after the invocation and no later than the response. -/
  linInvLt : ∀ u ∈ a.lin, ∀ i, a.history[i]? = some u.1.inv → i < u.2
  linResGe : ∀ u ∈ a.lin, ∀ i, a.history[i]? = some u.1.res → u.2 ≤ i
  linResEq : ∀ u ∈ a.lin, ∀ e ∈ a.history, e.isRes → e.id = u.1.id → e = u.1.res
  linMarkLe : ∀ u ∈ a.lin, u.2 ≤ a.history.length
  linSorted : a.lin.Pairwise fun u v => u.2 ≤ v.2
  /-- Every response is of a linearized operation. -/
  linResp : ∀ e ∈ a.history, e.isRes → ∃ u ∈ a.lin, u.1.res = e
  /-- The linearization is legal for the log. -/
  linLegal : LogLegal ((a.lin.map Prod.fst).map Operation.call)

/-- The invariant's conclusion: the history is linearizable. -/
theorem ClientInvariant.linearizable {P : LeaseParams} {a : ClientState Node}
    (h : ClientInvariant P a) : Linearizable LogLegal a.history :=
  linearizable_of_points a.lin h.wf h.linIds h.linInv h.linInvLt h.linResGe h.linResEq
    h.linSorted h.linResp h.linLegal

theorem uniqPrim_init (i : Node) {p : Node} (hp : ThinksPrimary (init i) p) : p = i := by
  have := hp.1; simpa [init, initCfg] using this.symm

theorem clientInvariant_init (P : LeaseParams) (i : Node) : ClientInvariant P (clientInit i) where
  lease := leaseInvariant_init P i
  reply := replyInvariant_init i
  wf := by refine ⟨?_, ?_, ?_⟩ <;> simp [clientInit]
  idsLt := by simp [clientInit]
  keysNodup := by simp [clientInit]
  opsNodup := by simp [clientInit]
  writtenInv := by simp [clientInit]
  writtenIds := by simp [clientInit]
  owned := by simp [clientInit]
  uniqPrim := fun p q hp hq _ => (uniqPrim_init i hp).trans (uniqPrim_init i hq).symm
  logKeyed := by intro n j v h; simp [clientInit, leaseInit, init] at h
  histKeyed := by intro j v h; simp [clientInit, leaseInit, init] at h
  respondedCommitted := by simp [clientInit]
  heldKeyed := by simp [clientInit]
  heldKeysNodup := by simp [clientInit]
  heldPending := by simp [clientInit]
  waitingInv := by simp [clientInit]
  waitingNodup := by simp [clientInit]
  readingInv := by simp [clientInit]
  readingNodup := by simp [clientInit]
  linShape := by simp [clientInit]
  linWrites := by simp [clientInit, leaseInit, init, writes, logOps]
  linCommitted := by simp [clientInit]
  linIds := by simp [clientInit]
  linInv := by simp [clientInit]
  linInvLt := by simp [clientInit]
  linResGe := by simp [clientInit]
  linResEq := by simp [clientInit]
  linMarkLe := by simp [clientInit]
  linSorted := by simp [clientInit]
  linResp := by simp [clientInit]
  linLegal := by intro k hk; simp [clientInit] at hk

end SyncReplication

namespace SyncReplication

open Lin

variable {Node : Type} [DecidableEq Node]

/-! ## What a move of the replication state keeps

`CoreMove c c'` collects what the client invariant needs of a change of replication
state other than an append: IDs in use are kept, a node that thinks it is primary with
an old ID did so before with a log that has only grown, a new ID is held by at most one
such node, every log entry was at the same index of some log before, and the committed
history only grows, from log entries. -/
structure CoreMove (c c' : State Node) : Prop where
  ids : c.usedIds ⊆ c'.usedIds
  prim : ∀ p, ThinksPrimary c' p → c'.replId p ∈ c.usedIds →
    ThinksPrimary c p ∧ c.replId p = c'.replId p ∧ c.log p <+: c'.log p
  newId : ∀ p q, ThinksPrimary c' p → ThinksPrimary c' q → c'.replId p = c'.replId q →
    c'.replId p ∉ c.usedIds → p = q
  entries : ∀ (n : Node) (j v : Nat), (c'.log n)[j]? = some v → ∃ n', (c.log n')[j]? = some v
  hist : c.hist <+: c'.hist
  histNew : ∀ (j v : Nat), c'.hist[j]? = some v → c.hist.length ≤ j → ∃ n', (c.log n')[j]? = some v

theorem prefix_getElem? {l l' : List Nat} (h : l <+: l') {j : Nat} (hj : j < l.length) :
    l'[j]? = l[j]? := by
  obtain ⟨t, rfl⟩ := h; exact List.getElem?_append_left hj

theorem CoreMove.refl {c : State Node} (ht : ReplIdsIssued c) : CoreMove c c where
  ids := Finset.Subset.refl _
  prim := fun _ hp _ => ⟨hp, rfl, List.prefix_refl _⟩
  newId := fun p _ _ _ _ h => absurd (ht p) h
  entries := fun n _ _ h => ⟨n, h⟩
  hist := List.prefix_refl _
  histNew := fun j v h hj => absurd (List.getElem?_eq_some_iff.1 h).1 (by omega)

theorem CoreMove.trans {c₁ c₂ c₃ : State Node} (h₁ : CoreMove c₁ c₂) (h₂ : CoreMove c₂ c₃) :
    CoreMove c₁ c₃ where
  ids := h₁.ids.trans h₂.ids
  prim := by
    intro p hp hu
    obtain ⟨hp₂, e₂, l₂⟩ := h₂.prim p hp (h₁.ids hu)
    obtain ⟨hp₁, e₁, l₁⟩ := h₁.prim p hp₂ (by rw [e₂]; exact hu)
    exact ⟨hp₁, e₁.trans e₂, l₁.trans l₂⟩
  newId := by
    intro p q hp hq he hn
    by_cases hu : c₃.replId p ∈ c₂.usedIds
    · obtain ⟨hp₂, e₂, -⟩ := h₂.prim p hp hu
      obtain ⟨hq₂, e₂', -⟩ := h₂.prim q hq (he ▸ hu)
      exact h₁.newId p q hp₂ hq₂ (by rw [e₂, e₂', he]) (by rw [e₂]; exact hn)
    · exact h₂.newId p q hp hq he hu
  entries := by
    intro n j v h
    obtain ⟨n', h'⟩ := h₂.entries n j v h
    exact h₁.entries n' j v h'
  hist := h₁.hist.trans h₂.hist
  histNew := by
    intro j v h hj
    by_cases hj₂ : c₂.hist.length ≤ j
    · obtain ⟨n', h'⟩ := h₂.histNew j v h hj₂
      exact h₁.entries n' j v h'
    · have : c₂.hist[j]? = some v := by
        rw [← h]; exact (prefix_getElem? h₂.hist (by omega)).symm
      exact h₁.histNew j v this hj

/-- An entry of `update L r X` at index `j` is one of `L`'s or one of `X`'s. -/
theorem entry_update {L : Node → List Nat} {r : Node} {X : List Nat} {n : Node} {j v : Nat}
    (h : (update L r X n)[j]? = some v) : L n = update L r X n ∨ X[j]? = some v := by
  by_cases hn : n = r
  · subst hn; right; simpa using h
  · left; rw [update_of_ne _ _ hn]

/-- A replication step other than an append or a restart. -/
theorem coreMove_step {s s' : State Node} (h : Invariant s) (ht : ReplIdsIssued s) {m : Nat}
    {μ : Action Node} (hs : Step m s μ s') (hμ : μ.isRestart = false) (hna : ∀ p, μ ≠ .append p) :
    CoreMove s s' := by
  obtain ⟨hh, hv, ht', hx⟩ := step_facts h ht hs hμ
  have hids : ∀ x, s'.replId x ∈ s.usedIds ∨ (∀ y, s'.replId y = s'.replId x → y = x) := by
    cases hs with
    | takeover n _ _ _ _ =>
      intro x
      by_cases hxn : x = n
      · subst hxn; right; intro y hy
        by_contra hyx
        have : s.replId y = freshId s := by
          simpa [takeover, update, hyx] using hy
        exact freshId_not_mem s (this ▸ ht y)
      · left; simpa [takeover, update, hxn] using ht x
    | replicate r _ _ _ =>
      intro x; left
      show update s.replId r (s.replId (primaryOf s r)) x ∈ _
      by_cases hxr : x = r
      · subst hxr; rw [update_self]; exact ht _
      · rw [update_of_ne _ _ hxr]; exact ht x
    | _ => intro x; left; exact ht x
  have hentries : ∀ (n : Node) (j v : Nat), (s'.log n)[j]? = some v → ∃ n', (s.log n')[j]? = some v := by
    cases hs with
    | append p _ _ => exact absurd rfl (hna p)
    | replicate r hne hpre hlt =>
      intro n j v hj
      change (update s.log r _ n)[j]? = some v at hj
      by_cases hn : n = r
      · subst hn; rw [update_self] at hj
        rcases Nat.lt_or_ge j (s.log n).length with hl | hl
        · exact ⟨n, by rw [List.getElem?_append_left hl] at hj; exact hj⟩
        · refine ⟨primaryOf s n, ?_⟩
          rw [List.getElem?_append_right hl] at hj
          have hj0 : j - (s.log n).length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hj).1; simp at this; omega
          rw [hj0] at hj; simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          have hjn : j = (s.log n).length := by omega
          rw [hjn, ← hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
      · rw [update_of_ne _ _ hn] at hj; exact ⟨n, hj⟩
    | resync r _ _ _ _ =>
      intro n j v hj
      change (update s.log r _ n)[j]? = some v at hj
      by_cases hn : n = r
      · subst hn; rw [update_self, List.getElem?_take] at hj
        split at hj
        · exact ⟨_, hj⟩
        · simp at hj
      · rw [update_of_ne _ _ hn] at hj; exact ⟨n, hj⟩
    | restartEmpty => exact absurd hμ (by simp [Action.isRestart])
    | restartKeep => exact absurd hμ (by simp [Action.isRestart])
    | restartPartialKeep => exact absurd hμ (by simp [Action.isRestart])
    | restartPartialFresh => exact absurd hμ (by simp [Action.isRestart])
    | _ => exact fun n j v hj => ⟨n, hj⟩
  have hhistNew : ∀ (j v : Nat), s'.hist[j]? = some v → s.hist.length ≤ j → ∃ n', (s.log n')[j]? = some v := by
    cases hs with
    | commit p _ _ hnext _ =>
      intro j v hj hl
      change (if s.commit p = s.hist.length then s.hist ++ [(s.log p).getD (s.commit p) 0] else s.hist)[j]? = some v at hj
      split at hj
      · rename_i hc
        rw [List.getElem?_append_right hl] at hj
        have hj0 : j - s.hist.length = 0 := by
          have := (List.getElem?_eq_some_iff.1 hj).1; simp at this; omega
        rw [hj0] at hj; simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        refine ⟨p, ?_⟩
        have hjn : j = s.commit p := by omega
        rw [hjn, ← hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnext]; rfl
      · exact absurd (List.getElem?_eq_some_iff.1 hj).1 (by omega)
    | _ => intro j v hj hl; exact absurd (List.getElem?_eq_some_iff.1 hj).1 (by
        change ¬ j < s.hist.length; omega)
  exact {
    ids := hv
    prim := fun p hp hu => by
      obtain ⟨h1, h2, h3⟩ := hx p _ hu hp rfl
      exact ⟨h1, h2, h3⟩
    newId := fun p q hp hq he hn => by
      rcases hids p with hu | hu
      · exact absurd hu hn
      · exact (hu q he.symm).symm
    entries := hentries
    hist := hh
    histNew := hhistNew }

end SyncReplication

namespace SyncReplication

open Lin

variable {Node : Type} [DecidableEq Node]

/-! ## Lookups and lists -/

theorem entryOp_mem {w : List Written} {o v : Nat} {x : Written} (h : entryOp w o v = some x) :
    x ∈ w ∧ x.offset = o ∧ x.replId = v := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h; simpa using this

theorem entryOp_of_mem {w : List Written} (hk : (w.map fun x => (x.offset, x.replId)).Nodup)
    {x : Written} (hx : x ∈ w) : entryOp w x.offset x.replId = some x := by
  cases hy : entryOp w x.offset x.replId with
  | none => exfalso; have := List.find?_eq_none.1 hy x hx; simp at this
  | some y =>
    obtain ⟨hy', h1, h2⟩ := entryOp_mem hy
    have := List.inj_on_of_nodup_map hk hy' hx (by simp [h1, h2])
    rw [this]

theorem entryOf_eq {w : List Written} (hk : (w.map fun x => (x.offset, x.replId)).Nodup)
    {x : Written} (hx : x ∈ w) {o v : Nat} (ho : x.offset = o) (hv : x.replId = v) :
    entryOf w o v = x := by
  subst ho hv; simp [entryOf, entryOp_of_mem hk hx]

theorem entryOf_keyed {w : List Written} (hk : (w.map fun x => (x.offset, x.replId)).Nodup)
    {L : List Nat} (hL : Keyed w L) {j v : Nat} (hj : L[j]? = some v) :
    entryOf w (j + 1) v ∈ w ∧ (entryOf w (j + 1) v).offset = j + 1 ∧ (entryOf w (j + 1) v).replId = v := by
  obtain ⟨x, hx, h1, h2⟩ := hL j v hj
  rw [entryOf_eq hk hx h1 h2]; exact ⟨hx, h1, h2⟩

theorem logOps_append (w : List Written) (L M : List Nat) :
    logOps w (L ++ M) = logOps w L ++ (M.zipIdx (L.length + 1)).map fun e => (entryOf w e.2 e.1).op := by
  simp only [logOps, List.zipIdx_append, List.map_append]; rw [Nat.add_comm]

theorem writes_append {V : Type} (L M : List (LogOp V × LogRes V)) :
    writes (L ++ M) = writes L ++ writes M := List.filterMap_append

theorem writes_commitsOf (w : List Written) (old new : List Nat) (mark : Nat) :
    writes (((commitsOf w old new mark).map Prod.fst).map Operation.call) =
      ((new.drop old.length).zipIdx (old.length + 1)).map fun e => (entryOf w e.2 e.1).op := by
  simp only [commitsOf, writes, List.map_map]
  rw [List.filterMap_map]
  exact (List.filterMap_eq_map).symm ▸ rfl

theorem logLegal_append_writes {V : Type} [DecidableEq V] {L M : List (LogOp V × LogRes V)}
    (hL : LogLegal L) (hM : ∀ c ∈ M, ∃ v, c = (.write v, .ok)) : LogLegal (L ++ M) := by
  intro k hk
  by_cases hkL : k < L.length
  · rw [List.getElem_append_left hkL, List.take_append_of_le_length (by omega)]
    exact hL k hkL
  · have hk' : k - L.length < M.length := by simp at hk; omega
    rw [List.getElem_append_right (by omega)]
    obtain ⟨v, hv⟩ := hM _ (List.getElem_mem hk')
    rw [hv]; rfl

theorem logLegal_append_read {V : Type} [DecidableEq V] {L : List (LogOp V × LogRes V)}
    (hL : LogLegal L) : LogLegal (L ++ [(.read, .log (writes L))]) := by
  intro k hk
  by_cases hkL : k < L.length
  · rw [List.getElem_append_left hkL, List.take_append_of_le_length (by omega)]
    exact hL k hkL
  · have hkeq : k = L.length := by simp at hk; omega
    subst hkeq
    simp [answer]

theorem zipIdx_nodup {α : Type} (l : List α) (k : Nat) : (l.zipIdx k).Nodup := by
  apply List.Nodup.of_map Prod.snd
  rw [List.zipIdx_map_snd]; exact List.nodup_range'

/-- The elements of `commitsOf`: the newly committed writes, each an append in the
committed history beyond its old length, at point `mark`. -/
theorem mem_commitsOf {w : List Written} (hk : (w.map fun x => (x.offset, x.replId)).Nodup)
    {old new : List Nat} (hn : Keyed w new) {mark : Nat} {u : ClientOp × Nat}
    (hu : u ∈ commitsOf w old new mark) :
    u.2 = mark ∧ ∃ x ∈ w, u.1 = x.toOp ∧ old.length < x.offset ∧ new[x.offset - 1]? = some x.replId := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hu
  obtain ⟨h1, h2⟩ := List.mem_zipIdx_iff_le_and_getElem?_sub.1 he
  rw [List.getElem?_drop] at h2
  have hj : old.length + (e.2 - (old.length + 1)) = e.2 - 1 := by omega
  rw [hj] at h2
  have := entryOf_keyed hk hn h2
  have he2 : e.2 - 1 + 1 = e.2 := by omega
  rw [he2] at this
  obtain ⟨hx, ho, hv⟩ := this
  refine ⟨rfl, _, hx, rfl, by omega, ?_⟩
  rw [ho, hv]; exact h2

end SyncReplication

namespace SyncReplication

open Lin

variable {Node : Type} [DecidableEq Node]

theorem mem_zip_drop {old new : List Nat} {e : Nat × Nat}
    (he : e ∈ (new.drop old.length).zipIdx (old.length + 1)) :
    old.length + 1 ≤ e.2 ∧ new[e.2 - 1]? = some e.1 := by
  obtain ⟨h1, h2⟩ := List.mem_zipIdx_iff_le_and_getElem?_sub.1 he
  rw [List.getElem?_drop, show old.length + (e.2 - (old.length + 1)) = e.2 - 1 by omega] at h2
  exact ⟨h1, h2⟩

theorem entryOf_zip {w : List Written} (hk : (w.map fun x => (x.offset, x.replId)).Nodup)
    {old new : List Nat} (hn : Keyed w new) {e : Nat × Nat}
    (he : e ∈ (new.drop old.length).zipIdx (old.length + 1)) :
    entryOf w e.2 e.1 ∈ w ∧ (entryOf w e.2 e.1).offset = e.2 := by
  obtain ⟨h1, h2⟩ := mem_zip_drop he
  have := entryOf_keyed hk hn h2
  rw [show e.2 - 1 + 1 = e.2 by omega] at this
  exact ⟨this.1, this.2.1⟩

theorem commitsOf_ids_nodup {w : List Written} (hk : (w.map fun x => (x.offset, x.replId)).Nodup)
    (ho : (w.map Written.op).Nodup) {old new : List Nat} (hn : Keyed w new) {mark : Nat} :
    ((commitsOf w old new mark).map fun u => u.1.id).Nodup := by
  rw [commitsOf, List.map_map]
  refine List.Nodup.map_on ?_ (zipIdx_nodup _ _)
  intro e he e' he' hee
  simp only [Function.comp, Written.toOp] at hee
  obtain ⟨m1, o1⟩ := entryOf_zip hk hn he
  obtain ⟨m2, o2⟩ := entryOf_zip hk hn he'
  have hxy := List.inj_on_of_nodup_map ho m1 m2 hee
  have hidx : e.2 = e'.2 := by rw [← o1, ← o2, hxy]
  have v1 := (mem_zip_drop he).2
  have v2 := (mem_zip_drop he').2
  rw [hidx, v2] at v1
  exact Prod.ext (Option.some.inj v1).symm hidx

/-- A linearized operation with the id of an append's write is that write. -/
theorem ClientInvariant.lin_of_id {P : LeaseParams} {a : ClientState Node} (h : ClientInvariant P a)
    {u : ClientOp × Nat} (hu : u ∈ a.lin) {x : Written} (hx : x ∈ a.written) (he : u.1.id = x.op) :
    u.1 = x.toOp := by
  rcases h.linShape u hu with ⟨y, hy, hyu⟩ | ⟨hr, -⟩
  · have : y = x := List.inj_on_of_nodup_map h.opsNodup hy hx (by rw [← he, hyu]; rfl)
    rw [hyu, this]
  · exfalso
    have := inv_unique h.wf (h.linInv u hu) (h.writtenInv x hx) rfl rfl (by rw [← he]; rfl)
    simp only [Operation.inv, Event.inv.injEq] at this
    rw [hr] at this; exact absurd this.2.2 (by simp)

/-- The client invariant survives a move of the replication state that is not an append,
with the held replies cut down to a sublist and the newly committed writes linearized
now. -/
theorem ClientInvariant.move {P : LeaseParams} {a : ClientState Node} (h : ClientInvariant P a)
    (l : LeaseState Node) (hd : List (Held Node))
    (hl : LeaseInvariant P l) (hr : ReplyInvariant ⟨l.core, hd, a.acknowledged⟩)
    (hsub : hd.Sublist a.held) (hm : CoreMove a.lease.core l.core) :
    ClientInvariant P { a with
      lease := l
      held := hd
      lin := a.lin ++ commitsOf a.written a.lease.core.hist l.core.hist a.history.length } := by
  have hsplit : a.lease.core.hist ++ l.core.hist.drop a.lease.core.hist.length = l.core.hist :=
    List.prefix_iff_eq_append.1 hm.hist
  have hlift : ∀ j v, a.lease.core.hist[j]? = some v → l.core.hist[j]? = some v := fun j v hj => by
    rw [prefix_getElem? hm.hist (List.getElem?_eq_some_iff.1 hj).1]; exact hj
  have hlogKeyed : ∀ n, Keyed a.written (l.core.log n) := by
    intro n j v hj; obtain ⟨n', h'⟩ := hm.entries n j v hj; exact h.logKeyed n' j v h'
  have hhistKeyed : Keyed a.written l.core.hist := by
    intro j v hj
    by_cases hjl : j < a.lease.core.hist.length
    · exact h.histKeyed j v (by rw [← prefix_getElem? hm.hist hjl]; exact hj)
    · obtain ⟨n', h'⟩ := hm.histNew j v hj (by omega); exact h.logKeyed n' j v h'
  have hnew := fun u (hu : u ∈ commitsOf a.written a.lease.core.hist l.core.hist a.history.length) =>
    mem_commitsOf h.keysNodup hhistKeyed hu
  -- A newly committed write has not responded.
  have hnotResp : ∀ x ∈ a.written, a.lease.core.hist.length < x.offset → ¬ Responded a.history x.op := by
    intro x hx hlt hresp
    have := (List.getElem?_eq_some_iff.1 (h.respondedCommitted x hx hresp).2).1; omega
  exact {
  lease := hl
  reply := hr
  wf := h.wf
  idsLt := h.idsLt
  keysNodup := h.keysNodup
  opsNodup := h.opsNodup
  writtenInv := h.writtenInv
  writtenIds := fun x hx => hm.ids (h.writtenIds x hx)
  owned := by
    intro x hx p hp he
    obtain ⟨hp0, e0, lp⟩ := hm.prim p hp (by rw [he]; exact h.writtenIds x hx)
    exact (h.owned x hx p hp0 (e0.trans he)).trans lp.length_le
  uniqPrim := by
    intro p q hp hq he
    by_cases hu : l.core.replId p ∈ a.lease.core.usedIds
    · obtain ⟨hp0, ep, -⟩ := hm.prim p hp hu
      obtain ⟨hq0, eq, -⟩ := hm.prim q hq (he ▸ hu)
      exact h.uniqPrim p q hp0 hq0 (ep.trans (he.trans eq.symm))
    · exact hm.newId p q hp hq he hu
  logKeyed := hlogKeyed
  histKeyed := hhistKeyed
  respondedCommitted := fun x hx hresp => by
    obtain ⟨h1, h2⟩ := h.respondedCommitted x hx hresp; exact ⟨h1, hlift _ _ h2⟩
  heldKeyed := fun x hx => h.heldKeyed x (hsub.subset hx)
  heldKeysNodup := h.heldKeysNodup.sublist (hsub.map _)
  heldPending := fun x hx => h.heldPending x (hsub.subset hx)
  waitingInv := h.waitingInv
  waitingNodup := h.waitingNodup
  readingInv := h.readingInv
  readingNodup := h.readingNodup
  linShape := by
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact h.linShape u hu
    · obtain ⟨-, x, hx, hux, -⟩ := hnew u hu; exact Or.inl ⟨x, hx, hux⟩
  linWrites := by
    show writes (((a.lin ++ _).map Prod.fst).map Operation.call) = logOps a.written l.core.hist
    rw [List.map_append, List.map_append, writes_append, h.linWrites, writes_commitsOf,
      ← logOps_append, hsplit]
  linCommitted := by
    intro u hu x hx hux
    rcases List.mem_append.1 hu with hu | hu
    · obtain ⟨h1, h2⟩ := h.linCommitted u hu x hx hux; exact ⟨h1, hlift _ _ h2⟩
    · obtain ⟨-, y, hy, huy, hlt, hh⟩ := hnew u hu
      have : y = x := List.inj_on_of_nodup_map h.opsNodup hy hx
        (by have := congrArg Operation.id (huy.symm.trans hux); exact this)
      subst this; exact ⟨by omega, hh⟩
  linIds := by
    show ((a.lin ++ _).map fun u => u.1.id).Nodup
    rw [List.map_append, List.nodup_append]
    refine ⟨h.linIds, ?_, ?_⟩
    · exact commitsOf_ids_nodup h.keysNodup h.opsNodup hhistKeyed
    · intro i hi j hj hij; subst hij
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hi
      obtain ⟨v, hv, hvi⟩ := List.mem_map.1 hj
      obtain ⟨-, x, hx, hvx, hlt, -⟩ := hnew v hv
      have hux := h.lin_of_id hu hx (by rw [← hvi, hvx]; rfl)
      obtain ⟨-, hh⟩ := h.linCommitted u hu x hx hux
      have := (List.getElem?_eq_some_iff.1 hh).1; omega
  linInv := by
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact h.linInv u hu
    · obtain ⟨-, x, hx, hux, -⟩ := hnew u hu; rw [hux]; exact h.writtenInv x hx
  linInvLt := by
    intro u hu i hi
    rcases List.mem_append.1 hu with hu | hu
    · exact h.linInvLt u hu i hi
    · obtain ⟨hm, -⟩ := hnew u hu; rw [hm]; exact (List.getElem?_eq_some_iff.1 hi).1
  linResGe := by
    intro u hu i hi
    rcases List.mem_append.1 hu with hu | hu
    · exact h.linResGe u hu i hi
    · obtain ⟨-, x, hx, hux, hlt, -⟩ := hnew u hu
      exact absurd ⟨_, List.mem_of_getElem? hi, rfl, by rw [hux]; rfl⟩ (hnotResp x hx hlt)
  linResEq := by
    intro u hu e he hres hid
    rcases List.mem_append.1 hu with hu | hu
    · exact h.linResEq u hu e he hres hid
    · obtain ⟨-, x, hx, hux, hlt, -⟩ := hnew u hu
      exact absurd ⟨e, he, hres, by rw [hid, hux]; rfl⟩ (hnotResp x hx hlt)
  linMarkLe := by
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact h.linMarkLe u hu
    · obtain ⟨hm, -⟩ := hnew u hu; exact hm.le
  linSorted := by
    refine List.pairwise_append.2 ⟨h.linSorted, List.pairwise_of_forall_mem_list fun u hu v hv => ?_,
      fun u hu v hv => ?_⟩
    · rw [(hnew u hu).1, (hnew v hv).1]
    · rw [(hnew v hv).1]; exact h.linMarkLe u hu
  linResp := fun e he hres => by
    obtain ⟨u, hu, hue⟩ := h.linResp e he hres; exact ⟨u, List.mem_append_left _ hu, hue⟩
  linLegal := by
    show LogLegal (((a.lin ++ _).map Prod.fst).map Operation.call)
    rw [List.map_append, List.map_append]
    refine logLegal_append_writes h.linLegal fun c hc => ?_
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
    obtain ⟨-, x, -, hvx, -⟩ := hnew v hv
    exact ⟨x.op, by rw [hvx]; rfl⟩ }

end SyncReplication

namespace SyncReplication

open Lin

variable {Node : Type} [DecidableEq Node]

/-! ## Lease steps, restarts and fresh IDs -/

/-- A fresh replication ID does not touch anything the lease invariant reads. -/
theorem leaseInvariant_freshen {P : LeaseParams} {l : LeaseState Node} (h : LeaseInvariant P l)
    (n : Node) : LeaseInvariant P (freshen l n) :=
  { h with core := h.core.replId_frame _ _,
           drop := ⟨h.drop.1, h.drop.2, h.drop.3, h.drop.4⟩ }

/-- A lease step of the client layer either leaves the replication state alone or is a
replication step other than an append or a restart. -/
theorem leaseStep_core {m : Nat} {P : LeaseParams} {a l : LeaseState Node} {μ : LeaseAction Node}
    (hs : LeaseStep m P a μ l) (hμ : μ.isClientLease = true) :
    l.core = a.core ∨ ∃ μ', Step m a.core μ' l.core ∧ μ'.isRestart = false ∧ ∀ p, μ' ≠ .append p := by
  cases hs with
  | core μ c hc hcore =>
    right; refine ⟨μ, hc, ?_, ?_⟩
    · cases μ <;> simp_all [Action.isCore, Action.isRestart]
    · intro p e; subst e; simp [LeaseAction.isClientLease] at hμ
  | learn n hn => right; exact ⟨_, Step.learn _ n hn, rfl, by simp⟩
  | demote p r hp hkl hel _ => right; exact ⟨_, Step.makeIneligible _ p r hp hkl hel, rfl, by simp⟩
  | takeover n hkl hel hnp hin _ => right; exact ⟨_, Step.takeover _ n hkl hel hnp hin, rfl, by simp⟩
  | resync r h1 h2 h3 h4 => right; exact ⟨_, Step.resync _ r h1 h2 h3 h4, rfl, by simp⟩
  | restartEmpty => simp [LeaseAction.isClientLease] at hμ
  | restartKeep => simp [LeaseAction.isClientLease] at hμ
  | restartPartialKeep => simp [LeaseAction.isClientLease] at hμ
  | restartPartialFresh => simp [LeaseAction.isClientLease] at hμ
  | _ => left; rfl

/-- The replication state after `freshen`. -/
theorem freshen_core (l : LeaseState Node) (n : Node) :
    (freshen l n).core = { l.core with replId := update l.core.replId n (freshId l.core),
                                       usedIds := insert (freshId l.core) l.core.usedIds } := rfl

/-- A restart of `n` (or nothing), then a fresh ID for `n`. -/
theorem coreMove_fresh {c : State Node} (ht : ReplIdsIssued c) {n : Node} (l : LeaseState Node)
    (hids : l.core.usedIds = c.usedIds) (hrep : l.core.replId = c.replId) (hhist : l.core.hist = c.hist)
    (hlog : ∀ x, x ≠ n → l.core.log x = c.log x)
    (hlogn : ∀ (j v : Nat), (l.core.log n)[j]? = some v → (c.log n)[j]? = some v)
    (htp : ∀ x, x ≠ n → ThinksPrimary l.core x → ThinksPrimary c x) :
    CoreMove c (freshen l n).core := by
  have hfresh : freshId l.core ∉ c.usedIds := hids ▸ freshId_not_mem l.core
  have hrid : ∀ x, x ≠ n → (freshen l n).core.replId x = c.replId x := fun x hx => by
    rw [freshen_core]; show update l.core.replId n _ x = _; rw [update_of_ne _ _ hx, hrep]
  have hridn : (freshen l n).core.replId n = freshId l.core := by
    rw [freshen_core]; show update l.core.replId n _ n = _; rw [update_self]
  exact {
  ids := by rw [freshen_core, ← hids]; exact Finset.subset_insert _ _
  prim := by
    intro p hp hu
    by_cases hpn : p = n
    · subst hpn; rw [hridn] at hu; exact absurd hu hfresh
    · rw [hrid p hpn] at hu ⊢
      exact ⟨htp p hpn hp, rfl, by rw [freshen_core]; show c.log p <+: l.core.log p; rw [hlog p hpn]⟩
  newId := by
    intro p q _ _ he hn
    have hp : p = n := by_contra fun hpn => hn (by rw [hrid p hpn]; exact ht p)
    have hq : q = n := by_contra fun hqn => hn (by rw [he, hrid q hqn]; exact ht q)
    rw [hp, hq]
  entries := by
    intro x j v hj
    change (l.core.log x)[j]? = some v at hj
    by_cases hxn : x = n
    · subst hxn; exact ⟨x, hlogn j v hj⟩
    · rw [hlog x hxn] at hj; exact ⟨x, hj⟩
  hist := by rw [freshen_core]; show c.hist <+: l.core.hist; rw [hhist]
  histNew := by
    intro j v hj hl
    change l.core.hist[j]? = some v at hj
    rw [hhist] at hj; exact absurd (List.getElem?_eq_some_iff.1 hj).1 (by omega) }

theorem commitsOf_self (w : List Written) (L : List Nat) (k : Nat) : commitsOf w L L k = [] := by
  simp [commitsOf]

theorem take_entries {L : List Nat} {k j v : Nat} (h : (L.take k)[j]? = some v) : L[j]? = some v := by
  rw [List.getElem?_take] at h; split at h
  · exact h
  · simp at h

end SyncReplication

namespace SyncReplication

open Lin

variable {Node : Type} [DecidableEq Node]

/-! ## Appending events -/

theorem getElem?_append_one {α : Type} {H : List α} {e x : α} {i : Nat} (h : (H ++ [e])[i]? = some x) :
    H[i]? = some x ∨ (i = H.length ∧ x = e) := by
  rcases Nat.lt_or_ge i H.length with hi | hi
  · left; rwa [List.getElem?_append_left hi] at h
  · right; rw [List.getElem?_append_right hi] at h
    have : i - H.length = 0 := by
      have := (List.getElem?_eq_some_iff.1 h).1; simp at this; omega
    rw [this] at h; simp at h; exact ⟨by omega, h.symm⟩

theorem responded_append_inv {H : ClientHistory} {e : Event Nat (LogOp Nat) (LogRes Nat)} (he : e.isInv)
    {i : Nat} : Responded (H ++ [e]) i ↔ Responded H i := by
  constructor
  · rintro ⟨e', he', hr, hid⟩
    rcases List.mem_append.1 he' with h | h
    · exact ⟨e', h, hr, hid⟩
    · rw [List.mem_singleton] at h; subst h; cases e' <;> simp_all [Event.isInv, Event.isRes]
  · rintro ⟨e', he', hr, hid⟩; exact ⟨e', List.mem_append_left _ he', hr, hid⟩

theorem responded_append_res {H : ClientHistory} {e : Event Nat (LogOp Nat) (LogRes Nat)}
    {i : Nat} (h : Responded (H ++ [e]) i) : Responded H i ∨ e.id = i := by
  obtain ⟨e', he', hr, hid⟩ := h
  rcases List.mem_append.1 he' with h | h
  · exact Or.inl ⟨e', h, hr, hid⟩
  · rw [List.mem_singleton] at h; subst h; exact Or.inr hid

theorem wf_append_inv {H : ClientHistory} (hw : WellFormed H) {e : Event Nat (LogOp Nat) (LogRes Nat)}
    (he : e.isInv) (hlt : ∀ e' ∈ H, e'.id < e.id) : WellFormed (H ++ [e]) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.filter_append, List.map_append, List.nodup_append]
    refine ⟨hw.1, by simp [List.filter_singleton, he], ?_⟩
    intro a ha b hb hab; subst hab
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 ha
    simp [List.filter_singleton, he] at hb
    have := hlt e' (List.mem_filter.1 he').1; omega
  · rw [List.filter_append]
    have : [e].filter Event.isRes = [] := by cases e <;> simp_all [Event.isInv, Event.isRes]
    rw [this, List.append_nil]; exact hw.2.1
  · intro e' he' hres
    rcases List.mem_append.1 he' with h | h
    · obtain ⟨e'', h1, h2, h3, h4, h5⟩ := hw.2.2 e' h hres
      exact ⟨e'', List.mem_append_left _ h1, h2, h3, h4, h5.trans (List.sublist_append_left _ _)⟩
    · rw [List.mem_singleton] at h; subst h; cases e' <;> simp_all [Event.isInv, Event.isRes]

theorem wf_append_res {H : ClientHistory} (hw : WellFormed H) {e : Event Nat (LogOp Nat) (LogRes Nat)}
    (he : e.isRes) (hnr : ¬ Responded H e.id)
    {e' : Event Nat (LogOp Nat) (LogRes Nat)} (hi : e' ∈ H) (hii : e'.isInv) (hid : e'.id = e.id)
    (hp : e'.proc = e.proc) : WellFormed (H ++ [e]) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.filter_append]
    have : [e].filter Event.isInv = [] := by cases e <;> simp_all [Event.isInv, Event.isRes]
    rw [this, List.append_nil]; exact hw.1
  · rw [List.filter_append, List.map_append, List.nodup_append]
    refine ⟨hw.2.1, by simp [List.filter_singleton, he], ?_⟩
    intro a ha b hb hab; subst hab
    obtain ⟨e'', he'', rfl⟩ := List.mem_map.1 ha
    simp [List.filter_singleton, he] at hb
    exact hnr ⟨e'', (List.mem_filter.1 he'').1, (List.mem_filter.1 he'').2, hb⟩
  · intro x hx hres
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨e'', h1, h2, h3, h4, h5⟩ := hw.2.2 x h hres
      exact ⟨e'', List.mem_append_left _ h1, h2, h3, h4, h5.trans (List.sublist_append_left _ _)⟩
    · rw [List.mem_singleton] at h; subst h
      exact ⟨e', List.mem_append_left _ hi, hii, hid, hp,
        (List.singleton_sublist.2 hi).append (List.Sublist.refl _)⟩

theorem mem_writes {V : Type} {L : List (LogOp V × LogRes V)} {v : V} (h : v ∈ writes L) :
    ∃ c ∈ L, c.1 = .write v := by
  obtain ⟨c, hc, hcv⟩ := List.mem_filterMap.1 h
  rcases c with ⟨_ | _, r⟩ <;> simp at hcv
  subst hcv; exact ⟨_, hc, rfl⟩

theorem mem_logOps {w : List Written} {L : List Nat} {j v : Nat} (h : L[j]? = some v) :
    (entryOf w (j + 1) v).op ∈ logOps w L := by
  apply List.mem_map.2
  refine ⟨(v, j + 1), List.mem_zipIdx_iff_le_and_getElem?_sub.2 ⟨by omega, by simpa using h⟩, rfl⟩

theorem entryOp_cons_ne {y : Written} {w : List Written} {o v : Nat}
    (h : ¬ (y.offset = o ∧ y.replId = v)) : entryOp (y :: w) o v = entryOp w o v := by
  simp only [entryOp, List.find?_cons]
  have : (y.offset == o && y.replId == v) = false := by
    simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; tauto
  rw [this]

/-- Adding an append whose key is not that of any entry of `L` keeps `L`'s operations. -/
theorem logOps_cons {y : Written} {w : List Written} {L : List Nat}
    (h : ∀ j v, L[j]? = some v → ¬ (y.offset = j + 1 ∧ y.replId = v)) :
    logOps (y :: w) L = logOps w L := by
  apply List.map_congr_left
  intro e he
  obtain ⟨h1, h2⟩ := List.mem_zipIdx_iff_le_and_getElem?_sub.1 he
  have h3 := h (e.2 - 1) e.1 h2
  rw [show e.2 - 1 + 1 = e.2 by omega] at h3
  simp only [entryOf, entryOp_cons_ne h3]

end SyncReplication

namespace SyncReplication

open Lin

variable {Node : Type} [DecidableEq Node]

/-! ## The client steps -/

section steps

variable {P : LeaseParams} {a : ClientState Node} (h : ClientInvariant P a)
include h

theorem ClientInvariant.moveSameHist (l : LeaseState Node) (hd : List (Held Node))
    (hl : LeaseInvariant P l) (hr : ReplyInvariant ⟨l.core, hd, a.acknowledged⟩)
    (hsub : hd.Sublist a.held) (hm : CoreMove a.lease.core l.core)
    (hh : l.core.hist = a.lease.core.hist) : ClientInvariant P { a with lease := l, held := hd } := by
  have := h.move l hd hl hr hsub hm
  rw [hh, commitsOf_self, List.append_nil] at this
  exact this

theorem ClientInvariant.ids_lt_of_inv {e : Event Nat (LogOp Nat) (LogRes Nat)} (he : e ∈ a.history) :
    e.id < a.nextOp := h.idsLt e he

/-- An invocation with a fresh id keeps every history fact. -/
theorem ClientInvariant.invoke_common {e : Event Nat (LogOp Nat) (LogRes Nat)} (he : e.isInv)
    (hid : e.id = a.nextOp) :
    WellFormed (a.history ++ [e]) ∧ (∀ e' ∈ a.history ++ [e], e'.id < a.nextOp + 1) ∧
    (∀ u ∈ a.lin, ∀ i, (a.history ++ [e])[i]? = some u.1.inv → i < u.2) ∧
    (∀ u ∈ a.lin, ∀ i, (a.history ++ [e])[i]? = some u.1.res → u.2 ≤ i) ∧
    (∀ u ∈ a.lin, ∀ e' ∈ a.history ++ [e], e'.isRes → e'.id = u.1.id → e' = u.1.res) ∧
    (∀ e' ∈ a.history ++ [e], e'.isRes → ∃ u ∈ a.lin, u.1.res = e') := by
  have hlt : ∀ e' ∈ a.history, e'.id < e.id := fun e' h' => hid ▸ h.idsLt e' h'
  refine ⟨wf_append_inv h.wf he hlt, ?_, ?_, ?_, ?_, ?_⟩
  · intro e' h'
    rcases List.mem_append.1 h' with h' | h'
    · have := h.idsLt e' h'; omega
    · rw [List.mem_singleton] at h'; subst h'; omega
  · intro u hu i hi
    rcases getElem?_append_one hi with hi | ⟨rfl, hie⟩
    · exact h.linInvLt u hu i hi
    · exfalso
      have := hlt _ (h.linInv u hu); rw [← hie] at this; exact absurd this (by simp [Operation.inv, Event.id])
  · intro u hu i hi
    rcases getElem?_append_one hi with hi | ⟨rfl, hie⟩
    · exact h.linResGe u hu i hi
    · exfalso; rw [← hie] at he; simp [Operation.res, Event.isInv] at he
  · intro u hu e' h' hres hid'
    rcases List.mem_append.1 h' with h' | h'
    · exact h.linResEq u hu e' h' hres hid'
    · rw [List.mem_singleton] at h'; subst h'; cases e' <;> simp_all [Event.isInv, Event.isRes]
  · intro e' h' hres
    rcases List.mem_append.1 h' with h' | h'
    · exact h.linResp e' h' hres
    · rw [List.mem_singleton] at h'; subst h'; cases e' <;> simp_all [Event.isInv, Event.isRes]

theorem ClientInvariant.invokeWrite (c : Nat) : ClientInvariant P
    { a with history := a.history ++ [.inv a.nextOp c (.write a.nextOp)],
             nextOp := a.nextOp + 1, waiting := (a.nextOp, c) :: a.waiting } := by
  obtain ⟨hwf, hids, hiv, hrg, hre, hrp⟩ := h.invoke_common (e := .inv a.nextOp c (.write a.nextOp)) rfl rfl
  have hresp : ∀ i, Responded (a.history ++ [.inv a.nextOp c (.write a.nextOp)]) i ↔ Responded a.history i :=
    fun _ => responded_append_inv rfl
  have hfresh : ¬ Responded a.history a.nextOp := by
    rintro ⟨e, he, -, hid⟩; have := h.idsLt e he; omega
  exact {
  lease := h.lease, reply := h.reply, wf := hwf, idsLt := hids
  keysNodup := h.keysNodup, opsNodup := h.opsNodup
  writtenInv := fun x hx => List.mem_append_left _ (h.writtenInv x hx)
  writtenIds := h.writtenIds, owned := h.owned, uniqPrim := h.uniqPrim
  logKeyed := h.logKeyed, histKeyed := h.histKeyed
  respondedCommitted := fun x hx hr => h.respondedCommitted x hx ((hresp _).1 hr)
  heldKeyed := h.heldKeyed, heldKeysNodup := h.heldKeysNodup
  heldPending := fun hh hm x hx h1 h2 hr => h.heldPending hh hm x hx h1 h2 ((hresp _).1 hr)
  waitingInv := by
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · refine ⟨List.mem_append_right _ (List.mem_singleton_self _), fun hr => hfresh ((hresp _).1 hr), ?_⟩
      intro hm; obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hm
      have := h.idsLt _ (h.writtenInv x hx); simp [Event.id] at this; omega
    · obtain ⟨h1, h2, h3⟩ := h.waitingInv u hu
      exact ⟨List.mem_append_left _ h1, fun hr => h2 ((hresp _).1 hr), h3⟩
  waitingNodup := by
    refine List.nodup_cons.2 ⟨fun hm => ?_, h.waitingNodup⟩
    obtain ⟨u, hu, hue⟩ := List.mem_map.1 hm
    have := h.idsLt _ (h.waitingInv u hu).1; simp [Event.id] at this; omega
  readingInv := fun u hu => ⟨List.mem_append_left _ (h.readingInv u hu).1,
    fun hr => (h.readingInv u hu).2 ((hresp _).1 hr)⟩
  readingNodup := h.readingNodup
  linShape := fun u hu => (h.linShape u hu).imp id fun ⟨h1, h2⟩ => ⟨h1, List.mem_append_left _ h2⟩
  linWrites := h.linWrites, linCommitted := h.linCommitted, linIds := h.linIds
  linInv := fun u hu => List.mem_append_left _ (h.linInv u hu)
  linInvLt := hiv, linResGe := hrg, linResEq := hre
  linMarkLe := fun u hu => (h.linMarkLe u hu).trans (by simp)
  linSorted := h.linSorted, linResp := hrp, linLegal := h.linLegal }

theorem ClientInvariant.invokeRead (c : Nat) (n : Node) : ClientInvariant P
    { a with history := a.history ++ [.inv a.nextOp c .read],
             nextOp := a.nextOp + 1, reading := (a.nextOp, c, n) :: a.reading } := by
  obtain ⟨hwf, hids, hiv, hrg, hre, hrp⟩ := h.invoke_common (e := .inv a.nextOp c .read) rfl rfl
  have hresp : ∀ i, Responded (a.history ++ [.inv a.nextOp c .read]) i ↔ Responded a.history i :=
    fun _ => responded_append_inv rfl
  have hfresh : ¬ Responded a.history a.nextOp := by
    rintro ⟨e, he, -, hid⟩; have := h.idsLt e he; omega
  exact {
  lease := h.lease, reply := h.reply, wf := hwf, idsLt := hids
  keysNodup := h.keysNodup, opsNodup := h.opsNodup
  writtenInv := fun x hx => List.mem_append_left _ (h.writtenInv x hx)
  writtenIds := h.writtenIds, owned := h.owned, uniqPrim := h.uniqPrim
  logKeyed := h.logKeyed, histKeyed := h.histKeyed
  respondedCommitted := fun x hx hr => h.respondedCommitted x hx ((hresp _).1 hr)
  heldKeyed := h.heldKeyed, heldKeysNodup := h.heldKeysNodup
  heldPending := fun hh hm x hx h1 h2 hr => h.heldPending hh hm x hx h1 h2 ((hresp _).1 hr)
  waitingInv := fun u hu => by
    obtain ⟨h1, h2, h3⟩ := h.waitingInv u hu
    exact ⟨List.mem_append_left _ h1, fun hr => h2 ((hresp _).1 hr), h3⟩
  waitingNodup := h.waitingNodup
  readingInv := by
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ⟨List.mem_append_right _ (List.mem_singleton_self _), fun hr => hfresh ((hresp _).1 hr)⟩
    · exact ⟨List.mem_append_left _ (h.readingInv u hu).1, fun hr => (h.readingInv u hu).2 ((hresp _).1 hr)⟩
  readingNodup := by
    refine List.nodup_cons.2 ⟨fun hm => ?_, h.readingNodup⟩
    obtain ⟨u, hu, hue⟩ := List.mem_map.1 hm
    have := h.idsLt _ (h.readingInv u hu).1; simp [Event.id] at this; omega
  linShape := fun u hu => (h.linShape u hu).imp id fun ⟨h1, h2⟩ => ⟨h1, List.mem_append_left _ h2⟩
  linWrites := h.linWrites, linCommitted := h.linCommitted, linIds := h.linIds
  linInv := fun u hu => List.mem_append_left _ (h.linInv u hu)
  linInvLt := hiv, linResGe := hrg, linResEq := hre
  linMarkLe := fun u hu => (h.linMarkLe u hu).trans (by simp)
  linSorted := h.linSorted, linResp := hrp, linLegal := h.linLegal }

end steps

end SyncReplication

namespace SyncReplication

open Lin

variable {Node : Type} [DecidableEq Node]

section steps2

variable {P : LeaseParams} {a : ClientState Node} (h : ClientInvariant P a)
include h

/-- A primary appends a waiting write. -/
theorem ClientInvariant.append (hM : 2 * P.drift ≤ P.margin) {m : Nat} {p : Node} {op c : Nat}
    (hw : (op, c) ∈ a.waiting) (hp : ThinksPrimary a.lease.core p) (hW : Writable m a.lease.core p) :
    ClientInvariant P
      { a with lease := withCore a.lease (appendWrite a.lease.core p),
               held := ⟨p, (a.lease.core.log p).length + 1, a.lease.core.replId p⟩ :: a.held,
               written := ⟨(a.lease.core.log p).length + 1, a.lease.core.replId p, op, c⟩ :: a.written,
               waiting := a.waiting.erase (op, c) } := by
  set y : Written := ⟨(a.lease.core.log p).length + 1, a.lease.core.replId p, op, c⟩ with hy
  obtain ⟨hwi, hwr, hwo⟩ := h.waitingInv _ hw
  -- No earlier append, entry or held reply has the new key.
  have hnew : ∀ x ∈ a.written, ¬ (x.offset = y.offset ∧ x.replId = y.replId) := by
    rintro x hx ⟨h1, h2⟩
    have := h.owned x hx p hp (by rw [h2])
    rw [hy] at h1; simp only at h1; omega
  have hnotHist : ∀ j v, a.lease.core.hist[j]? = some v → ¬ (y.offset = j + 1 ∧ y.replId = v) := by
    rintro j v hj ⟨h1, h2⟩
    obtain ⟨x, hx, h3, h4⟩ := h.histKeyed j v hj
    exact hnew x hx ⟨h3.trans h1.symm, h4.trans h2.symm⟩
  have hlogp : (appendWrite a.lease.core p).log p = a.lease.core.log p ++ [a.lease.core.replId p] := by simp [appendWrite]
  have hlog : ∀ x, a.lease.core.log x <+: (appendWrite a.lease.core p).log x := grow_upd a.lease.core.log p _
  have hwnd : a.waiting.Nodup := List.Nodup.of_map _ h.waitingNodup
  exact {
  lease := leaseInvariant_step hM h.lease (LeaseStep.core _ (.append p) _ (Step.append _ p hp hW) rfl)
  reply := replyInvariant_step h.reply (ReplyStep.write a.reply p hp hW)
  wf := h.wf, idsLt := h.idsLt
  keysNodup := List.nodup_cons.2 ⟨fun hm => by
      obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hm
      exact hnew x hx (by simpa using hxe), h.keysNodup⟩
  opsNodup := List.nodup_cons.2 ⟨hwo, h.opsNodup⟩
  writtenInv := fun x hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hwi
    · exact h.writtenInv x hx
  writtenIds := fun x hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.reply.replIdsIssued p
    · exact h.writtenIds x hx
  owned := by
    intro x hx q hq he
    rcases List.mem_cons.1 hx with rfl | hx
    · have : q = p := h.uniqPrim q p hq hp he
      subst this; show y.offset ≤ ((appendWrite a.lease.core q).log q).length
      rw [hlogp, hy]; simp
    · exact (h.owned x hx q hq he).trans (hlog q).length_le
  uniqPrim := h.uniqPrim
  logKeyed := by
    intro n j v hj
    change ((appendWrite a.lease.core p).log n)[j]? = some v at hj
    by_cases hn : n = p
    · subst hn; rw [hlogp] at hj
      rcases getElem?_append_one hj with hj | ⟨rfl, rfl⟩
      · obtain ⟨x, hx, h1, h2⟩ := h.logKeyed n j v hj; exact ⟨x, List.mem_cons_of_mem _ hx, h1, h2⟩
      · exact ⟨y, List.mem_cons_self, rfl, rfl⟩
    · have : (appendWrite a.lease.core p).log n = a.lease.core.log n := by simp [appendWrite, update, hn]
      rw [this] at hj
      obtain ⟨x, hx, h1, h2⟩ := h.logKeyed n j v hj; exact ⟨x, List.mem_cons_of_mem _ hx, h1, h2⟩
  histKeyed := fun j v hj => by
    obtain ⟨x, hx, h1, h2⟩ := h.histKeyed j v hj; exact ⟨x, List.mem_cons_of_mem _ hx, h1, h2⟩
  respondedCommitted := by
    intro x hx hr
    rcases List.mem_cons.1 hx with rfl | hx
    · exact absurd hr hwr
    · exact h.respondedCommitted x hx hr
  heldKeyed := by
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ⟨y, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨x, hx, h1, h2⟩ := h.heldKeyed g hg; exact ⟨x, List.mem_cons_of_mem _ hx, h1, h2⟩
  heldKeysNodup := List.nodup_cons.2 ⟨fun hm => by
      obtain ⟨g, hg, hge⟩ := List.mem_map.1 hm
      obtain ⟨x, hx, h1, h2⟩ := h.heldKeyed g hg
      simp only [Prod.mk.injEq] at hge
      exact hnew x hx ⟨h1.trans hge.1, h2.trans hge.2⟩, h.heldKeysNodup⟩
  heldPending := by
    intro g hg x hx h1 h2
    rcases List.mem_cons.1 hg with rfl | hg
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact hwr
      · exact absurd ⟨h1, h2⟩ (hnew x hx)
    · rcases List.mem_cons.1 hx with rfl | hx
      · obtain ⟨x', hx', h1', h2'⟩ := h.heldKeyed g hg
        exact absurd ⟨h1'.trans h1.symm, h2'.trans h2.symm⟩ (hnew x' hx')
      · exact h.heldPending g hg x hx h1 h2
  waitingInv := by
    intro u hu
    have hu' := (List.Nodup.mem_erase_iff hwnd).1 hu
    obtain ⟨h1, h2, h3⟩ := h.waitingInv u hu'.2
    refine ⟨h1, h2, fun hm => ?_⟩
    rcases List.mem_cons.1 hm with he | hm
    · exact hu'.1 (List.inj_on_of_nodup_map h.waitingNodup hu'.2 hw he)
    · exact h3 hm
  waitingNodup := h.waitingNodup.sublist (List.erase_sublist.map _)
  readingInv := h.readingInv, readingNodup := h.readingNodup
  linShape := fun u hu => (h.linShape u hu).imp
    (fun ⟨x, hx, hux⟩ => ⟨x, List.mem_cons_of_mem _ hx, hux⟩) id
  linWrites := by rw [h.linWrites]; exact (logOps_cons hnotHist).symm
  linCommitted := by
    intro u hu x hx hux
    rcases List.mem_cons.1 hx with rfl | hx
    · exfalso
      rcases h.linShape u hu with ⟨x', hx', hux'⟩ | ⟨hr, -⟩
      · apply hwo; rw [hux'] at hux; exact List.mem_map.2 ⟨x', hx', congrArg Operation.id hux⟩
      · rw [hux] at hr; simp [Written.toOp] at hr
    · exact h.linCommitted u hu x hx hux
  linIds := h.linIds, linInv := h.linInv, linInvLt := h.linInvLt, linResGe := h.linResGe
  linResEq := h.linResEq, linMarkLe := h.linMarkLe, linSorted := h.linSorted
  linResp := h.linResp, linLegal := h.linLegal }

/-- A write that has committed is linearized. -/
theorem ClientInvariant.committed_lin {x : Written} (hx : x ∈ a.written) (h1 : 1 ≤ x.offset)
    (hc : a.lease.core.hist[x.offset - 1]? = some x.replId) : ∃ u ∈ a.lin, u.1 = x.toOp := by
  have hm := mem_logOps (w := a.written) hc
  rw [show x.offset - 1 + 1 = x.offset by omega, entryOf_eq h.keysNodup hx rfl rfl, ← h.linWrites] at hm
  obtain ⟨cl, hcl, hce⟩ := mem_writes hm
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hcl
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ho
  refine ⟨u, hu, ?_⟩
  rcases h.linShape u hu with ⟨x', hx', hux'⟩ | ⟨hr, -⟩
  · rw [hux'] at hce ⊢
    have : x'.op = x.op := by simpa [Written.toOp, Operation.call] using hce
    rw [List.inj_on_of_nodup_map h.opsNodup hx' hx this]
  · simp [Operation.call, hr] at hce

/-- A held reply is released as OK. -/
theorem ClientInvariant.release {m : Nat} {g : Held Node} {x : Written} (hm : g ∈ a.held)
    (hc : g.offset ≤ a.lease.core.commit g.primary) (hf : ReplyFenced a.lease.core g)
    (hx : entryOp a.written g.offset g.replId = some x) :
    ClientInvariant P
      { a with held := a.held.erase g, acknowledged := (g.offset, g.replId) :: a.acknowledged,
               history := a.history ++ [.res x.op x.client .ok] } := by
  obtain ⟨hxw, hxo, hxr⟩ := entryOp_mem hx
  have hr := replyInvariant_step (m := m) h.reply (ReplyStep.release a.reply g hm hc hf)
  obtain ⟨hd1, hd2, hd3⟩ := hr.acked _ List.mem_cons_self
  have hd1 : 1 ≤ g.offset := hd1
  have hd2 : g.offset ≤ a.lease.core.hist.length := hd2
  have hd3 : a.lease.core.hist.getD (g.offset - 1) 0 = g.replId := hd3
  have hcom : a.lease.core.hist[x.offset - 1]? = some x.replId := by
    rw [hxo, hxr, List.getElem?_eq_getElem (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at hd3
    simpa using hd3
  have hpend := h.heldPending g hm x hxw hxo hxr
  have hinv := h.writtenInv x hxw
  have hheldNd : a.held.Nodup := List.Nodup.of_map _ h.heldKeysNodup
  obtain ⟨u0, hu0, hu0x⟩ := h.committed_lin hxw (by rw [hxo]; exact hd1) hcom
  -- Responded after the release: before, or this write.
  have hresp : ∀ i, Responded (a.history ++ [.res x.op x.client .ok]) i → Responded a.history i ∨ i = x.op :=
    fun i hr' => (responded_append_res hr').imp id fun e => e.symm
  exact {
  lease := h.lease, reply := hr
  wf := wf_append_res h.wf rfl hpend hinv rfl rfl rfl
  idsLt := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact h.idsLt e he
    · rw [List.mem_singleton] at he; subst he; have := h.idsLt _ hinv; exact this
  keysNodup := h.keysNodup, opsNodup := h.opsNodup
  writtenInv := fun y hy => List.mem_append_left _ (h.writtenInv y hy)
  writtenIds := h.writtenIds, owned := h.owned, uniqPrim := h.uniqPrim
  logKeyed := h.logKeyed, histKeyed := h.histKeyed
  respondedCommitted := by
    intro y hy hry
    rcases hresp _ hry with hry | hry
    · exact h.respondedCommitted y hy hry
    · rw [List.inj_on_of_nodup_map h.opsNodup hy hxw hry]; exact ⟨by rw [hxo]; exact hd1, hcom⟩
  heldKeyed := fun g' hg' => h.heldKeyed g' (List.mem_of_mem_erase hg')
  heldKeysNodup := h.heldKeysNodup.sublist (List.erase_sublist.map _)
  heldPending := by
    intro g' hg' y hy h1 h2 hry
    have hg'' := (List.Nodup.mem_erase_iff hheldNd).1 hg'
    rcases hresp _ hry with hry | hry
    · exact h.heldPending g' hg''.2 y hy h1 h2 hry
    · have hyx : y = x := List.inj_on_of_nodup_map h.opsNodup hy hxw hry
      subst hyx
      exact hg''.1 (List.inj_on_of_nodup_map h.heldKeysNodup hg''.2 hm
        (by simp only [Prod.mk.injEq]; exact ⟨h1.symm.trans hxo, h2.symm.trans hxr⟩))
  waitingInv := by
    intro u hu
    obtain ⟨h1, h2, h3⟩ := h.waitingInv u hu
    refine ⟨List.mem_append_left _ h1, fun hr' => ?_, h3⟩
    rcases hresp _ hr' with hr' | hr'
    · exact h2 hr'
    · exact h3 (hr' ▸ List.mem_map_of_mem hxw)
  waitingNodup := h.waitingNodup
  readingInv := by
    intro u hu
    obtain ⟨h1, h2⟩ := h.readingInv u hu
    refine ⟨List.mem_append_left _ h1, fun hr' => ?_⟩
    rcases hresp _ hr' with hr' | hr'
    · exact h2 hr'
    · have := inv_unique h.wf h1 hinv rfl rfl (by simp [Event.id, hr'])
      simp at this
  readingNodup := h.readingNodup
  linShape := fun u hu => (h.linShape u hu).imp id fun ⟨h1, h2⟩ => ⟨h1, List.mem_append_left _ h2⟩
  linWrites := h.linWrites, linCommitted := h.linCommitted, linIds := h.linIds
  linInv := fun u hu => List.mem_append_left _ (h.linInv u hu)
  linInvLt := by
    intro u hu i hi
    rcases getElem?_append_one hi with hi | ⟨-, hie⟩
    · exact h.linInvLt u hu i hi
    · simp [Operation.inv] at hie
  linResGe := by
    intro u hu i hi
    rcases getElem?_append_one hi with hi | ⟨rfl, -⟩
    · exact h.linResGe u hu i hi
    · exact h.linMarkLe u hu
  linResEq := by
    intro u hu e he hres hid
    rcases List.mem_append.1 he with he | he
    · exact h.linResEq u hu e he hres hid
    · rw [List.mem_singleton] at he; subst he
      have := h.lin_of_id hu hxw (by simpa [Event.id] using hid.symm)
      rw [this]; rfl
  linMarkLe := fun u hu => (h.linMarkLe u hu).trans (by simp)
  linSorted := h.linSorted
  linResp := by
    intro e he hres
    rcases List.mem_append.1 he with he | he
    · exact h.linResp e he hres
    · rw [List.mem_singleton] at he; subst he; exact ⟨u0, hu0, by rw [hu0x]; rfl⟩
  linLegal := h.linLegal }

/-- A node answers a read. -/
theorem ClientInvariant.respondRead (hM : 2 * P.drift ≤ P.margin) {op c : Nat} {n : Node}
    (hrd : (op, c, n) ∈ a.reading) (hcan : PrimCanRead P a.lease n ∨ ReplCanRead P a.lease n) :
    ClientInvariant P
      { a with history := a.history ++ [.res op c (.log (logOps a.written (a.lease.core.log n)))],
               reading := a.reading.erase (op, c, n),
               lin := a.lin ++ [(⟨op, c, .read, .log (logOps a.written (a.lease.core.log n))⟩,
                                 a.history.length)] } := by
  obtain ⟨hri, hrr⟩ := h.readingInv _ hrd
  have hlog : a.lease.core.log n = a.lease.core.hist := by
    have hs := leaseInvariant_noStaleRead hM h.lease
    rcases hcan with hc | hc
    · exact hs.1 n hc
    · exact hs.2 n hc
  set R : ClientOp := ⟨op, c, .read, .log (logOps a.written (a.lease.core.log n))⟩ with hR
  have hRres : R.res = .res op c (.log (logOps a.written (a.lease.core.log n))) := rfl
  have hrnd : a.reading.Nodup := List.Nodup.of_map _ h.readingNodup
  -- No append and no linearized operation has this read's id.
  have hnotW : ∀ x ∈ a.written, x.op ≠ op := by
    intro x hx he
    have := inv_unique h.wf (h.writtenInv x hx) hri rfl rfl (by simp [Event.id, he])
    simp at this
  have hnotLin : ∀ u ∈ a.lin, u.1.id ≠ op := by
    intro u hu he
    rcases h.linShape u hu with ⟨x, hx, hux⟩ | ⟨-, hres⟩
    · exact hnotW x hx (by rw [← he, hux]; rfl)
    · exact hrr ⟨_, hres, rfl, he⟩
  have hresp : ∀ i, Responded (a.history ++ [R.res]) i → Responded a.history i ∨ i = op :=
    fun i hr' => (responded_append_res hr').imp id fun e => e.symm
  exact {
  lease := h.lease, reply := h.reply
  wf := wf_append_res h.wf rfl hrr hri rfl rfl rfl
  idsLt := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact h.idsLt e he
    · rw [List.mem_singleton] at he; subst he; have := h.idsLt _ hri; exact this
  keysNodup := h.keysNodup, opsNodup := h.opsNodup
  writtenInv := fun y hy => List.mem_append_left _ (h.writtenInv y hy)
  writtenIds := h.writtenIds, owned := h.owned, uniqPrim := h.uniqPrim
  logKeyed := h.logKeyed, histKeyed := h.histKeyed
  respondedCommitted := by
    intro y hy hry
    rcases hresp _ hry with hry | hry
    · exact h.respondedCommitted y hy hry
    · exact absurd hry (hnotW y hy)
  heldKeyed := h.heldKeyed, heldKeysNodup := h.heldKeysNodup
  heldPending := by
    intro g hg y hy h1 h2 hry
    rcases hresp _ hry with hry | hry
    · exact h.heldPending g hg y hy h1 h2 hry
    · exact hnotW y hy hry
  waitingInv := by
    intro u hu
    obtain ⟨h1, h2, h3⟩ := h.waitingInv u hu
    refine ⟨List.mem_append_left _ h1, fun hr' => ?_, h3⟩
    rcases hresp _ hr' with hr' | hr'
    · exact h2 hr'
    · have := inv_unique h.wf h1 hri rfl rfl (by simp [Event.id, hr'])
      simp at this
  waitingNodup := h.waitingNodup
  readingInv := by
    intro u hu
    have hu' := (List.Nodup.mem_erase_iff hrnd).1 hu
    obtain ⟨h1, h2⟩ := h.readingInv u hu'.2
    refine ⟨List.mem_append_left _ h1, fun hr' => ?_⟩
    rcases hresp _ hr' with hr' | hr'
    · exact h2 hr'
    · exact hu'.1 (List.inj_on_of_nodup_map h.readingNodup hu'.2 hrd hr')
  readingNodup := h.readingNodup.sublist (List.erase_sublist.map _)
  linShape := by
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact (h.linShape u hu).imp id fun ⟨h1, h2⟩ => ⟨h1, List.mem_append_left _ h2⟩
    · rw [List.mem_singleton] at hu; subst hu
      exact Or.inr ⟨rfl, List.mem_append_right _ (List.mem_singleton_self _)⟩
  linWrites := by
    rw [List.map_append, List.map_append, writes_append, h.linWrites]
    simp only [writes, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil]
    rw [hR]; simp [Operation.call]
  linCommitted := by
    intro u hu x hx hux
    rcases List.mem_append.1 hu with hu | hu
    · exact h.linCommitted u hu x hx hux
    · rw [List.mem_singleton] at hu; subst hu
      exact absurd (congrArg Operation.op hux) (by simp [hR, Written.toOp])
  linIds := by
    rw [List.map_append, List.nodup_append]
    refine ⟨h.linIds, List.nodup_singleton _, ?_⟩
    intro i hi j hj hij; subst hij
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hi
    simp at hj
    exact hnotLin u hu hj
  linInv := by
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact List.mem_append_left _ (h.linInv u hu)
    · rw [List.mem_singleton] at hu; subst hu; exact List.mem_append_left _ hri
  linInvLt := by
    intro u hu i hi
    rcases getElem?_append_one hi with hi' | ⟨-, hie⟩
    · rcases List.mem_append.1 hu with hu | hu
      · exact h.linInvLt u hu i hi'
      · rw [List.mem_singleton] at hu; subst hu; exact (List.getElem?_eq_some_iff.1 hi').1
    · simp [Operation.inv, Operation.res] at hie
  linResGe := by
    intro u hu i hi
    rcases List.mem_append.1 hu with hu | hu
    · rcases getElem?_append_one hi with hi | ⟨rfl, -⟩
      · exact h.linResGe u hu i hi
      · exact h.linMarkLe u hu
    · rw [List.mem_singleton] at hu; subst hu
      rcases getElem?_append_one hi with hi | ⟨rfl, -⟩
      · exact absurd ⟨_, List.mem_of_getElem? hi, rfl, rfl⟩ hrr
      · exact le_refl _
  linResEq := by
    intro u hu e he hres hid
    rcases List.mem_append.1 hu with hu | hu
    · rcases List.mem_append.1 he with he | he
      · exact h.linResEq u hu e he hres hid
      · rw [List.mem_singleton] at he; subst he
        exact absurd (by simpa [Event.id] using hid.symm) (hnotLin u hu)
    · rw [List.mem_singleton] at hu; subst hu
      rcases List.mem_append.1 he with he | he
      · exact absurd ⟨e, he, hres, hid⟩ hrr
      · rw [List.mem_singleton] at he; exact he
  linMarkLe := by
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact (h.linMarkLe u hu).trans (by simp)
    · rw [List.mem_singleton] at hu; subst hu; simp
  linSorted := List.pairwise_append.2 ⟨h.linSorted, List.pairwise_singleton _ _,
    fun u hu v hv => by rw [List.mem_singleton] at hv; subst hv; exact h.linMarkLe u hu⟩
  linResp := by
    intro e he hres
    rcases List.mem_append.1 he with he | he
    · obtain ⟨u, hu, hue⟩ := h.linResp e he hres; exact ⟨u, List.mem_append_left _ hu, hue⟩
    · rw [List.mem_singleton] at he; subst he
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
  linLegal := by
    rw [List.map_append, List.map_append]
    have := logLegal_append_read h.linLegal
    rw [h.linWrites, ← hlog] at this
    exact this }

end steps2

end SyncReplication

namespace SyncReplication

open Lin

variable {Node : Type} [DecidableEq Node]

/-! ## Every step preserves the invariant; the theorem -/

/-- Every client step preserves the client invariant, given `margin ≥ 2 · drift`. -/
theorem clientInvariant_step {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {m : Nat}
    {a a' : ClientState Node} {μ : ClientAction Node} (h : ClientInvariant P a)
    (hs : ClientStep m P a μ a') : ClientInvariant P a' := by
  cases hs with
  | lease μ l hs hμ =>
    have hl := leaseInvariant_step hM h.lease hs
    rcases leaseStep_core hs hμ with he | ⟨μ', hst, hr, hna⟩
    · have hr' : ReplyInvariant ⟨l.core, a.held, a.acknowledged⟩ := by rw [he]; exact h.reply
      have hm : CoreMove a.lease.core l.core := by rw [he]; exact CoreMove.refl h.reply.replIdsIssued
      exact h.move l a.held hl hr' (List.Sublist.refl _) hm
    · exact h.move l a.held hl (replyInvariant_core h.reply hst hr) (List.Sublist.refl _)
        (coreMove_step h.reply.core h.reply.replIdsIssued hst hr hna)
  | restart μ l n hs hμ =>
    have hl := leaseInvariant_freshen (leaseInvariant_step hM h.lease hs) n
    cases hs with
    | restartEmpty n' hkl hsurv =>
      simp only [LeaseAction.restarted, Option.some.injEq] at hμ; subst hμ
      have hr := replyInvariant_step (replyInvariant_step h.reply
        (ReplyStep.restartEmpty (m := m) a.reply n' hkl hsurv)) (ReplyStep.newId (m := m) _ n')
      exact h.moveSameHist _ _ hl hr List.filter_sublist
        (coreMove_fresh h.reply.replIdsIssued _ rfl rfl rfl (fun x hx => restartEmpty_log_other hx)
          (fun j v hj => by simp [leaseRestart, restartEmpty] at hj)
          (fun x _ hx => (restartEmpty_thinksPrimary (h.lease.core.localCfgEq n' hkl)
            (h.lease.core.incLe n') hx).2)) rfl
    | restartKeep n' hkl =>
      simp only [LeaseAction.restarted, Option.some.injEq] at hμ; subst hμ
      have hr := replyInvariant_step (replyInvariant_step h.reply
        (ReplyStep.restartKeep (m := m) a.reply n' hkl)) (ReplyStep.newId (m := m) _ n')
      exact h.moveSameHist _ _ hl hr List.filter_sublist
        (coreMove_fresh h.reply.replIdsIssued _ rfl rfl rfl (fun _ _ => rfl) (fun _ _ hj => hj)
          (fun _ _ hx => hx)) rfl
    | restartPartialKeep n' k hkl hk hkeep =>
      simp only [LeaseAction.restarted, Option.some.injEq] at hμ; subst hμ
      have hr := replyInvariant_step (replyInvariant_step h.reply
        (ReplyStep.restartPartialKeep (m := m) a.reply n' k hkl hk hkeep)) (ReplyStep.newId (m := m) _ n')
      exact h.moveSameHist _ _ hl hr List.filter_sublist
        (coreMove_fresh h.reply.replIdsIssued _ rfl rfl rfl (fun x hx => restartPartialKeep_log_other hx)
          (fun j v hj => by
            change ((restartPartialKeep a.lease.core n' k).log n')[j]? = some v at hj
            rw [restartPartialKeep_log_self] at hj; exact take_entries hj)
          (fun _ _ hx => hx)) rfl
    | restartPartialFresh n' k hkl hk hfresh hsurv =>
      simp only [LeaseAction.restarted, Option.some.injEq] at hμ; subst hμ
      have hr := replyInvariant_step (replyInvariant_step h.reply
        (ReplyStep.restartPartialFresh (m := m) a.reply n' k hkl hk hfresh hsurv))
        (ReplyStep.newId (m := m) _ n')
      exact h.moveSameHist _ _ hl hr List.filter_sublist
        (coreMove_fresh h.reply.replIdsIssued _ rfl rfl rfl (fun x hx => restartPartialFresh_log_other hx)
          (fun j v hj => by
            change ((restartPartialFresh a.lease.core n' k).log n')[j]? = some v at hj
            rw [restartPartialFresh_log, if_pos rfl] at hj; exact take_entries hj)
          (fun x _ hx => (restartPartialFresh_thinksPrimary (h.lease.core.localCfgEq n' hkl)
            (h.lease.core.incLe n') hx).2)) rfl
    | _ => simp [LeaseAction.restarted] at hμ
  | newId p =>
    have hr := replyInvariant_step (m := m) h.reply (ReplyStep.newId _ p)
    exact h.moveSameHist _ _ (leaseInvariant_freshen h.lease p) hr (List.Sublist.refl _)
      (coreMove_fresh h.reply.replIdsIssued a.lease rfl rfl rfl (fun _ _ => rfl) (fun _ _ hj => hj)
        (fun _ _ hx => hx)) rfl
  | invokeWrite c => exact h.invokeWrite c
  | append p op c hw hp hW => exact h.append hM hw hp hW
  | release g x hm hc hf hx => exact h.release (m := m) hm hc hf hx
  | abort g hm hf =>
    have hr := replyInvariant_step (m := m) h.reply (ReplyStep.abort a.reply g hm hf)
    exact h.moveSameHist a.lease _ h.lease hr List.erase_sublist (CoreMove.refl h.reply.replIdsIssued) rfl
  | invokeRead c n => exact h.invokeRead c n
  | respondRead op c n hr hcan => exact h.respondRead hM hr hcan

/-- The client invariant holds in every reachable state. -/
theorem clientInvariant_reachable {P : LeaseParams} (hM : 2 * P.drift ≤ P.margin) {m : Nat}
    {i : Node} {a : ClientState Node} (h : ClientReachable m P i a) : ClientInvariant P a :=
  let ⟨_, run⟩ := h
  Cslib.LTS.mtrInv_of_trInv (p := ClientInvariant P) (fun _ _ _ hs h => clientInvariant_step hM h hs) _ _ _ run
    (clientInvariant_init P i)

/-- **Client histories are linearizable.** If the clock-drift margin is at least twice
the drift bound, then for every `min-sync-replicas` value, every reachable client
history is linearizable for the log: some way to complete or drop the pending writes
and some order of the operations, legal for the log, keeps every operation that
responded before another was invoked ahead of it. -/
theorem linearizable {P : LeaseParams} (hMargin : 2 * P.drift ≤ P.margin) {m : Nat} {i : Node}
    {a : ClientState Node} (hReachable : ClientReachable m P i a) :
    Lin.Linearizable Lin.LogLegal a.history :=
  (clientInvariant_reachable hMargin hReachable).linearizable

end SyncReplication
