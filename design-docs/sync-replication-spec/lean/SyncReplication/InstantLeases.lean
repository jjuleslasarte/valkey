import SyncReplication.LeaseInvariant

/-!
# Instant messages are a special case

`InstantLeaseStep` is the lease layer in which every message is delivered in the step
that sends it. Each of its steps is a run of `LeaseStep`: a data message, a heartbeat or
an acknowledgement is a send followed at once by its delivery (with, for Replicate and
Ack, the replication step first), and every other step is the same step. So everything
reachable with instant messages is reachable with delayed ones
(`instantReachable_leaseReachable`), and the lease counterexamples, which are runs with
instant messages, are runs of the delayed model too.
-/

open Cslib

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

theorem Action.isCore_of_isPlain {μ : Action Node} (h : μ.isPlain = true) : μ.isCore = true := by
  cases μ <;> simp_all [Action.isPlain, Action.isCore]

/-- After copying one entry, the replica's log is still a prefix of its primary's. -/
theorem replicate_log_prefix {s : State Node} {r : Node} (hpre : s.log r <+: s.log (primaryOf s r))
    (hlt : (s.log r).length < (s.log (primaryOf s r)).length) :
    (replicate s r).log r <+: s.log (primaryOf s r) := by
  show update s.log r (s.log r ++ [(s.log (primaryOf s r)).getD (s.log r).length 0]) r <+: _
  rw [update_self]
  obtain ⟨t, ht⟩ := hpre
  have hne : t ≠ [] := by
    intro e; subst e; simp at ht; rw [← ht] at hlt; exact absurd hlt (Nat.lt_irrefl _)
  obtain ⟨x, t', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hx : (s.log (primaryOf s r)).getD (s.log r).length 0 = x := by
    rw [← ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
  rw [hx, ← ht]
  exact ⟨t', by simp⟩

/-- A data message sent and at once delivered is `recvData`. -/
theorem deliverData_send_eq (a : LeaseState Node) (c : State Node) (p r : Node) (e : Option Nat)
    (hcommit : c.commit p = a.core.commit (primaryOf a.core r)) (hp : p = primaryOf a.core r) :
    deliverData (send (withCore a c) (.data p r (a.gen p) (a.gen r) a.now (c.commit p) e))
        (.data p r (a.gen p) (a.gen r) a.now (c.commit p) e) r a.now (c.commit p) e =
      recvData a r c e := by
  subst hp
  simp only [deliverData, send, withCore, recvData, List.erase_cons_head, hcommit]

/-- An acknowledgement sent and at once delivered is `recvAck`. -/
theorem deliverAck_send_eq (a : LeaseState Node) (c : State Node) (r : Node) :
    deliverAck (send (withCore a c) (.ack r (primaryOf a.core r) (a.gen r) (a.gen (primaryOf a.core r))
        a.now (a.dataSent r)))
        (.ack r (primaryOf a.core r) (a.gen r) (a.gen (primaryOf a.core r)) a.now (a.dataSent r))
        r (primaryOf a.core r) a.now (a.dataSent r) =
      recvAck a r c := by
  simp only [deliverAck, send, withCore, recvAck, List.erase_cons_head]

/-- **Every instant step is a run of the delayed lease layer.** -/
theorem instant_simulates {m : Nat} {P : LeaseParams} {a a' : LeaseState Node} {μ : LeaseAction Node}
    (hs : InstantLeaseStep m P a μ a') : ∃ μs, (leaseTransitionSystem m P).MTr a μs a' := by
  cases hs with
  | tick => exact ⟨_, .single _ (LeaseStep.tick a)⟩
  | core μ c hc hpl => exact ⟨_, .single _ (LeaseStep.core a μ c hc (Action.isCore_of_isPlain hpl))⟩
  | replicate r hne hpre hlt =>
    -- the entry, then a `REPLCONF COMMIT` without an echo, delivered at once.
    set p := primaryOf a.core r
    set c := replicate a.core r
    set a1 := withCore a c
    set msg : Msg Node := .data p r (a.gen p) (a.gen r) a.now (c.commit p) none
    have h1 : LeaseStep m P a (.core (.replicate r)) a1 :=
      LeaseStep.core a _ c (Step.replicate a.core r hne hpre hlt) rfl
    have h2 : LeaseStep m P a1 (.sendData p r) (send a1 msg) := LeaseStep.sendData a1 p r hne rfl
    have hpre' : c.log r <+: c.log p := by
      have := replicate_log_prefix hpre hlt
      show c.log r <+: update a.core.log r _ p
      rw [update_of_ne _ _ hne]; exact this
    have h3 : LeaseStep m P (send a1 msg) (.deliver msg) (deliverData (send a1 msg) msg r a.now (c.commit p) none) :=
      LeaseStep.deliverData (send a1 msg) p r _ _ _ _ _ (List.mem_cons_self ..) ⟨rfl, rfl⟩ rfl hpre'
    rw [deliverData_send_eq a c p r none rfl rfl] at h3
    exact ⟨_, .stepL h1 (.stepL h2 (.single _ h3))⟩
  | heartbeat r hne hpre =>
    set p := primaryOf a.core r
    set msg : Msg Node := .data p r (a.gen p) (a.gen r) a.now (a.core.commit p) none
    have h2 : LeaseStep m P a (.sendData p r) (send a msg) := LeaseStep.sendData a p r hne rfl
    have h3 : LeaseStep m P (send a msg) (.deliver msg) (deliverData (send a msg) msg r a.now (a.core.commit p) none) :=
      LeaseStep.deliverData (send a msg) p r _ _ _ _ _ (List.mem_cons_self ..) ⟨rfl, rfl⟩ rfl hpre
    have e := deliverData_send_eq a a.core p r none rfl rfl
    simp only [withCore] at e
    rw [e] at h3
    exact ⟨_, .stepL h2 (.single _ h3)⟩
  | heartbeatGrant r hne hp hpre hg =>
    set p := primaryOf a.core r
    set msg : Msg Node := .data p r (a.gen p) (a.gen r) a.now (a.core.commit p) (a.ackEcho p r)
    have h2 : LeaseStep m P a (.sendData p r) (send a msg) := LeaseStep.sendGrant a p r hne rfl hp hg
    have h3 : LeaseStep m P (send a msg) (.deliver msg)
        (deliverData (send a msg) msg r a.now (a.core.commit p) (a.ackEcho p r)) :=
      LeaseStep.deliverData (send a msg) p r _ _ _ _ _ (List.mem_cons_self ..) ⟨rfl, rfl⟩ rfl hpre
    have e := deliverData_send_eq a a.core p r (a.ackEcho p r) rfl rfl
    simp only [withCore] at e
    rw [e] at h3
    exact ⟨_, .stepL h2 (.single _ h3)⟩
  | ack r hne hpre hlt =>
    set c := ack a.core r
    set a1 := withCore a c
    set p := primaryOf a.core r
    set msg : Msg Node := .ack r p (a.gen r) (a.gen p) a.now (a.dataSent r)
    have h1 : LeaseStep m P a (.core (.ack r)) a1 := LeaseStep.core a _ c (Step.ack a.core r hne hpre hlt) rfl
    have h2 : LeaseStep m P a1 (.sendAck r) (send a1 msg) := LeaseStep.sendAck a1 r hne
    have h3 : LeaseStep m P (send a1 msg) (.deliver msg) (deliverAck (send a1 msg) msg r p a.now (a.dataSent r)) :=
      LeaseStep.deliverAck (send a1 msg) r p _ _ _ _ (List.mem_cons_self ..) ⟨rfl, rfl⟩
    rw [deliverAck_send_eq a c r] at h3
    exact ⟨_, .stepL h1 (.stepL h2 (.single _ h3))⟩
  | ackRenew r hne hpre =>
    set p := primaryOf a.core r
    set msg : Msg Node := .ack r p (a.gen r) (a.gen p) a.now (a.dataSent r)
    have h2 : LeaseStep m P a (.sendAck r) (send a msg) := LeaseStep.sendAck a r hne
    have h3 : LeaseStep m P (send a msg) (.deliver msg) (deliverAck (send a msg) msg r p a.now (a.dataSent r)) :=
      LeaseStep.deliverAck (send a msg) r p _ _ _ _ (List.mem_cons_self ..) ⟨rfl, rfl⟩
    have e := deliverAck_send_eq a a.core r
    simp only [withCore] at e
    rw [e] at h3
    exact ⟨_, .stepL h2 (.single _ h3)⟩
  | learn n hnkl => exact ⟨_, .single _ (LeaseStep.learn a n hnkl)⟩
  | demote p r hp hkl hel hgo hwo => exact ⟨_, .single _ (LeaseStep.demote a p r hp hkl hel hgo hwo)⟩
  | takeover n hkl hel hnp hin hwait => exact ⟨_, .single _ (LeaseStep.takeover a n hkl hel hnp hin hwait)⟩
  | resync r hne hnpre hsy hke => exact ⟨_, .single _ (LeaseStep.resync a r hne hnpre hsy hke)⟩
  | restartEmpty n hkl hsurv => exact ⟨_, .single _ (LeaseStep.restartEmpty a n hkl hsurv)⟩
  | restartKeep n hkl => exact ⟨_, .single _ (LeaseStep.restartKeep a n hkl)⟩
  | restartPartialKeep n k hkl hk hkeep => exact ⟨_, .single _ (LeaseStep.restartPartialKeep a n k hkl hk hkeep)⟩
  | restartPartialFresh n k hkl hk hfresh hsurv =>
    exact ⟨_, .single _ (LeaseStep.restartPartialFresh a n k hkl hk hfresh hsurv)⟩

/-- A run with instant messages is a run with delayed ones. -/
theorem instant_mtr {m : Nat} {P : LeaseParams} {a b : LeaseState Node} {μs : List (LeaseAction Node)}
    (h : (instantTransitionSystem m P).MTr a μs b) : ∃ νs, (leaseTransitionSystem m P).MTr a νs b := by
  induction h with
  | refl => exact ⟨_, .refl⟩
  | stepL hs _ ih =>
    obtain ⟨ν1, r1⟩ := instant_simulates hs
    obtain ⟨ν2, r2⟩ := ih
    exact ⟨_, LTS.MTr.comp _ r1 r2⟩

/-- Everything reachable with instant messages is reachable with delayed ones. -/
theorem instantReachable_leaseReachable {m : Nat} {P : LeaseParams} {i : Node} {a : LeaseState Node}
    (h : (instantTransitionSystem m P).CanReach (leaseInit i) a) : LeaseReachable m P i a :=
  let ⟨_, run⟩ := h
  instant_mtr run

end SyncReplication
