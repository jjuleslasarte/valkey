import SyncReplication.LeaseInvariant

/-!
# Instant messages are a special case

`InstantLeaseStep` is the lease layer in which every lease message is delivered in the
step that sends it. Each of its steps is a run of `LeaseStep`: a heartbeat or an
acknowledgement is a send followed at once by its delivery, and every other step is the
same step. Replication is `Step`'s, delayed, in both layers. So everything reachable
with instant lease messages is reachable with delayed ones
(`instantReachable_leaseReachable`), and the lease counterexamples, which are runs with
instant lease messages, are runs of the delayed model too.
-/

open Cslib

namespace SyncReplication

variable {Node : Type} [DecidableEq Node]

/-- A data message sent and at once delivered is `recvData`. -/
theorem deliverData_send_eq (a : LeaseState Node) (c : State Node) (p r : Node) (e : Option Nat)
    (hcommit : c.commit p = a.core.commit (primaryOf a.core r)) (hp : p = primaryOf a.core r) :
    deliverData (send (withCore a c) (.data p r (a.gen p r) a.now (c.commit p) e))
        (.data p r (a.gen p r) a.now (c.commit p) e) r a.now (c.commit p) e =
      recvData a r c e := by
  subst hp
  simp only [deliverData, send, withCore, recvData, List.erase_cons_head, hcommit]

/-- An acknowledgement sent and at once delivered is `recvAck`. -/
theorem deliverAck_send_eq (a : LeaseState Node) (c : State Node) (r : Node) :
    deliverAck (send (withCore a c) (.ack r (primaryOf a.core r) (a.gen (primaryOf a.core r) r)
        a.now (a.dataSent r)))
        (.ack r (primaryOf a.core r) (a.gen (primaryOf a.core r) r) a.now (a.dataSent r))
        r (primaryOf a.core r) a.now (a.dataSent r) =
      recvAck a r c := by
  simp only [deliverAck, send, withCore, recvAck, List.erase_cons_head]

/-- **Every instant step is a run of the delayed lease layer.** -/
theorem instant_simulates {m : Nat} {P : LeaseParams} {a a' : LeaseState Node} {μ : LeaseAction Node}
    (hs : InstantLeaseStep m P a μ a') : ∃ μs, (leaseTransitionSystem m P).MTr a μs a' := by
  cases hs with
  | tick => exact ⟨_, .single _ (LeaseStep.tick a)⟩
  | core μ c hc hpl => exact ⟨_, .single _ (LeaseStep.core a μ c hc hpl)⟩
  | heartbeat r hne hpre =>
    set p := primaryOf a.core r
    set msg : Msg Node := .data p r (a.gen p r) a.now (a.core.commit p) none
    have h2 : LeaseStep m P a (.sendData p r) (send a msg) := LeaseStep.sendData a p r hne rfl
    have h3 : LeaseStep m P (send a msg) (.deliver msg) (deliverData (send a msg) msg r a.now (a.core.commit p) none) :=
      LeaseStep.deliverData (send a msg) p r _ _ _ _ (List.mem_cons_self ..) rfl rfl hpre
    have e := deliverData_send_eq a a.core p r none rfl rfl
    simp only [withCore] at e
    rw [e] at h3
    exact ⟨_, .stepL h2 (.single _ h3)⟩
  | heartbeatGrant r hne hp hpre hg =>
    set p := primaryOf a.core r
    set msg : Msg Node := .data p r (a.gen p r) a.now (a.core.commit p) (a.ackEcho p r)
    have h2 : LeaseStep m P a (.sendData p r) (send a msg) := LeaseStep.sendGrant a p r hne rfl hp hg
    have h3 : LeaseStep m P (send a msg) (.deliver msg)
        (deliverData (send a msg) msg r a.now (a.core.commit p) (a.ackEcho p r)) :=
      LeaseStep.deliverData (send a msg) p r _ _ _ _ (List.mem_cons_self ..) rfl rfl hpre
    have e := deliverData_send_eq a a.core p r (a.ackEcho p r) rfl rfl
    simp only [withCore] at e
    rw [e] at h3
    exact ⟨_, .stepL h2 (.single _ h3)⟩
  | ackRenew r hne =>
    set p := primaryOf a.core r
    set msg : Msg Node := .ack r p (a.gen p r) a.now (a.dataSent r)
    have h2 : LeaseStep m P a (.sendAck r) (send a msg) := LeaseStep.sendAck a r hne
    have h3 : LeaseStep m P (send a msg) (.deliver msg) (deliverAck (send a msg) msg r p a.now (a.dataSent r)) :=
      LeaseStep.deliverAck (send a msg) r p _ _ _ (List.mem_cons_self ..) rfl
    have e := deliverAck_send_eq a a.core r
    simp only [withCore] at e
    rw [e] at h3
    exact ⟨_, .stepL h2 (.single _ h3)⟩
  | learn n hnkl => exact ⟨_, .single _ (LeaseStep.learn a n hnkl)⟩
  | demote p r hp hkl hel hgo hwo => exact ⟨_, .single _ (LeaseStep.demote a p r hp hkl hel (Or.inl ⟨hgo, hwo⟩))⟩
  | takeover n hkl hel hnp hin hwait => exact ⟨_, .single _ (LeaseStep.takeover a n hkl hel hnp hin hwait)⟩
  | resync r hne hsy hke => exact ⟨_, .single _ (LeaseStep.resync a r hne hsy hke)⟩
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
