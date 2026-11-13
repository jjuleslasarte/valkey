import SyncReplication.Counterexamples.Leases

/-!
# Planned demotion

For a planned demotion of a healthy replica, the primary asks it to drop its read lease
and demotes it once the replica confirms, instead of waiting the lease out (design §4).
Messages are delayed, so three rules keep this safe:

- **The request closes the connection.** Every message to or from the replica still in
  flight is discarded, so an echo sent before the request cannot arrive after the
  replica dropped its lease (`noCloseOnRequest_stale`).
- **An acknowledgement resets a confirmed drop.** Once the primary hears from the
  replica again it may echo again, so the confirmation no longer stands
  (`noResetOnAck_stale`).
- **A confirmation counts only if no acknowledgement arrived since the request.** An
  acknowledgement in between lets the primary echo on the new connection, and that echo
  may reach the replica after it dropped its lease (`noConfirmGuard_stale`).

Each run is in the lease layer with that one rule removed, at `P0` and
`min-sync-replicas = 0`, from the shared prefix (n0 holds its lease from the eligible
n1 and has n1's acknowledgement to echo). Each ends with n0 demoting n1 on its
confirmation, committing a write alone, while n1 holds a valid read lease and may serve
a read that misses the write. `plannedDemotion_reachable` shows the path is used in the
model itself: a demotion before the read-lease wait has passed.
-/

open Cslib

namespace SyncReplication

/-- A run of the lease layer is a run of any weakening of it. -/
theorem delayedMtr_lift {L : LTS (LeaseState N) (LeaseAction N)} {m : Nat} {P : LeaseParams}
    (hL : ∀ {a μ a'}, LeaseStep m P a μ a' → L.Tr a μ a') {a b : LeaseState N} {μs : List (LeaseAction N)}
    (h : (leaseTransitionSystem m P).MTr a μs b) : L.MTr a μs b := by
  induction h with
  | refl => exact .refl
  | stepL hs _ ih => exact .stepL (hL hs) ih

/-- The shared prefix as a run with delayed messages. -/
theorem leases_prefix_delayed : ∃ μs, (leaseTransitionSystem 0 P0).MTr l0 μs l5 :=
  instant_mtr (leases_prefix P0)

/-! ## The planned demotion is reachable -/

def pd1 := send l5 (.data 0 1 (l5.gen 0) (l5.gen 1) l5.now (l5.core.commit 0) (l5.ackEcho 0 1))
def pd2 := deliverData pd1 (.data 0 1 0 0 0 0 (some 0)) 1 0 0 (some 0)  -- n1 holds a read lease
def pd3 := sendDropRequest pd2 0 1                                      -- n0 asks n1 to drop it
def pd4 := deliverDropRequest pd3 (.dropReq 0 1 0 1 0) 1 0              -- n1 drops it and confirms
def pd5 := deliverDropConfirm pd4 (.dropAck 1 0 1 0 0) 0 1              -- n0 has the confirmation
def pd6 := withCore pd5 (makeIneligible pd5.core 0 1)                   -- n0 demotes n1

/-- A planned demotion is reachable: n0 demotes n1, which held a read lease from it, at
the same instant, before the read-lease wait has passed. -/
theorem plannedDemotion_reachable : ∃ a, LeaseReachable 0 P0 (0 : N) a ∧
    a.core.cfg.eligible 1 = false ∧ ¬ GrantorOver P0 a.now (a.ackReceived 0 1) P0.readDur := by
  obtain ⟨_, hp⟩ := leases_prefix_delayed
  exact ⟨pd6, ⟨_, LTS.MTr.comp _ hp <|
    .stepL (LeaseStep.sendGrant l5 0 1 (by decide) (by decide) (by decide) (by decide)) <|
    .stepL (LeaseStep.deliverData pd1 0 1 0 0 0 0 (some 0) (by decide) (by decide) (by decide) (by decide)) <|
    .stepL (LeaseStep.sendDropRequest pd2 0 1 (by decide) (by decide) (by decide)) <|
    .stepL (LeaseStep.deliverDropRequest pd3 0 1 0 1 0 (by decide) (by decide)) <|
    .stepL (LeaseStep.deliverDropConfirm pd4 1 0 1 0 0 (by decide) (by decide) (by decide)) <|
    .stepL (LeaseStep.demote pd5 0 1 (by decide) (by decide) (by decide) (Or.inr (by decide))) <|
    .refl⟩, by decide, by decide⟩

/-! ## The request must close the connection -/

/-- A drop request that does not close the connection to the replica. -/
def sendDropRequestNoClose (a : LeaseState N) (p r : N) : LeaseState N :=
  send { a with ackEcho := update2 a.ackEcho p r none } (.dropReq p r (a.gen p) (a.gen r) a.now)

/-- `LeaseStep`, plus a drop request that leaves the connection open. -/
inductive LeaseStepNoCloseOnRequest (m : Nat) (P : LeaseParams) :
    LeaseState N → LeaseAction N → LeaseState N → Prop
  | step {a μ a'} : LeaseStep m P a μ a' → LeaseStepNoCloseOnRequest m P a μ a'
  | sendDropRequest (a : LeaseState N) (p r : N) : p ≠ r → primaryOf a.core r = p → ThinksPrimary a.core p →
      LeaseStepNoCloseOnRequest m P a (.sendDropRequest p r) (sendDropRequestNoClose a p r)

def leaseTransitionSystemNoCloseOnRequest (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepNoCloseOnRequest m P

def nc1 := send l5 (.data 0 1 (l5.gen 0) (l5.gen 1) l5.now (l5.core.commit 0) (l5.ackEcho 0 1)) -- echo in flight
def nc2 := sendDropRequestNoClose nc1 0 1                                 -- request, connection kept
def nc3 := deliverDropRequest nc2 (.dropReq 0 1 0 0 0) 1 0                -- n1 drops and confirms
def nc4 := deliverData nc3 (.data 0 1 0 0 0 0 (some 0)) 1 0 0 (some 0)    -- the old echo arrives
def nc5 := deliverDropConfirm nc4 (.dropAck 1 0 0 0 0) 0 1                -- n0 has the confirmation
def nc6 := withCore nc5 (makeIneligible nc5.core 0 1)                     -- n0 demotes n1
def nc7 := withCore nc6 (appendWrite nc6.core 0)                          -- n0 writes
def nc8 := withCore nc7 (commitNext nc7.core 0)                           -- and commits alone

/-- The drop request must close the connection: otherwise an echo sent before it
arrives after the replica dropped its lease, and the replica may serve a stale read
after the planned demotion. -/
theorem noCloseOnRequest_stale :
    ∃ a, (leaseTransitionSystemNoCloseOnRequest 0 P0).CanReach (leaseInit 0) a ∧
      ReplCanRead P0 a 1 ∧ a.core.log 1 ≠ a.core.hist := by
  obtain ⟨_, hp⟩ := leases_prefix_delayed
  exact ⟨nc8, ⟨_, LTS.MTr.comp _ (delayedMtr_lift LeaseStepNoCloseOnRequest.step hp) <|
    .stepL (.step (LeaseStep.sendGrant l5 0 1 (by decide) (by decide) (by decide) (by decide))) <|
    .stepL (LeaseStepNoCloseOnRequest.sendDropRequest nc1 0 1 (by decide) (by decide) (by decide)) <|
    .stepL (.step (LeaseStep.deliverDropRequest nc2 0 1 0 0 0 (by decide) (by decide))) <|
    .stepL (.step (LeaseStep.deliverData nc3 0 1 0 0 0 0 (some 0) (by decide) (by decide) (by decide)
      (by decide))) <|
    .stepL (.step (LeaseStep.deliverDropConfirm nc4 1 0 0 0 0 (by decide) (by decide) (by decide))) <|
    .stepL (.step (LeaseStep.demote nc5 0 1 (by decide) (by decide) (by decide) (Or.inr (by decide)))) <|
    .stepL (.step (LeaseStep.core nc6 _ _ (Step.append nc6.core 0 (by decide) (writable_zero _ _)) rfl)) <|
    .stepL (.step (LeaseStep.core nc7 _ _ (Step.commit nc7.core 0 (by decide) (writable_zero _ _)
      (by decide) (by decide)) rfl)) <|
    .refl⟩, by decide, by decide⟩

/-! ## An acknowledgement must reset a confirmed drop -/

/-- An acknowledgement that leaves a confirmed drop in place. -/
def deliverAckNoReset (a : LeaseState N) (msg : Msg N) (r p : N) (t d : Nat) : LeaseState N :=
  { deliverAck a msg r p t d with dropConfirmed := a.dropConfirmed }

/-- `LeaseStep`, plus an acknowledgement that does not reset a confirmed drop. -/
inductive LeaseStepNoResetOnAck (m : Nat) (P : LeaseParams) :
    LeaseState N → LeaseAction N → LeaseState N → Prop
  | step {a μ a'} : LeaseStep m P a μ a' → LeaseStepNoResetOnAck m P a μ a'
  | deliverAck (a : LeaseState N) (r p : N) (gs gd t d : Nat) : Msg.ack r p gs gd t d ∈ a.net →
      (Msg.ack r p gs gd t d).Current a →
      LeaseStepNoResetOnAck m P a (.deliver (.ack r p gs gd t d)) (deliverAckNoReset a (.ack r p gs gd t d) r p t d)

def leaseTransitionSystemNoResetOnAck (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepNoResetOnAck m P

def nr1 := sendDropRequest l5 0 1                                         -- n0 asks n1
def nr2 := deliverDropRequest nr1 (.dropReq 0 1 0 1 0) 1 0                -- n1 drops and confirms
def nr3 := deliverDropConfirm nr2 (.dropAck 1 0 1 0 0) 0 1                -- n0 has the confirmation
def nr4 := send nr3 (.ack 1 (primaryOf nr3.core 1) (nr3.gen 1) (nr3.gen (primaryOf nr3.core 1)) nr3.now
  (nr3.dataSent 1))                                                       -- n1 acknowledges again
def nr5 := deliverAckNoReset nr4 (.ack 1 0 1 0 0 0) 1 0 0 0               -- n0 receives it, no reset
def nr6 := send nr5 (.data 0 1 (nr5.gen 0) (nr5.gen 1) nr5.now (nr5.core.commit 0) (nr5.ackEcho 0 1))
def nr7 := deliverData nr6 (.data 0 1 0 1 0 0 (some 0)) 1 0 0 (some 0)    -- n1 holds a read lease again
def nr8 := withCore nr7 (makeIneligible nr7.core 0 1)                     -- n0 demotes n1 on the stale confirmation
def nr9 := withCore nr8 (appendWrite nr8.core 0)
def nr10 := withCore nr9 (commitNext nr9.core 0)

/-- An acknowledgement must reset a confirmed drop: otherwise the primary echoes it,
renewing the replica's read lease, and still demotes the replica on the old
confirmation. -/
theorem noResetOnAck_stale :
    ∃ a, (leaseTransitionSystemNoResetOnAck 0 P0).CanReach (leaseInit 0) a ∧
      ReplCanRead P0 a 1 ∧ a.core.log 1 ≠ a.core.hist := by
  obtain ⟨_, hp⟩ := leases_prefix_delayed
  exact ⟨nr10, ⟨_, LTS.MTr.comp _ (delayedMtr_lift LeaseStepNoResetOnAck.step hp) <|
    .stepL (.step (LeaseStep.sendDropRequest l5 0 1 (by decide) (by decide) (by decide))) <|
    .stepL (.step (LeaseStep.deliverDropRequest nr1 0 1 0 1 0 (by decide) (by decide))) <|
    .stepL (.step (LeaseStep.deliverDropConfirm nr2 1 0 1 0 0 (by decide) (by decide) (by decide))) <|
    .stepL (.step (LeaseStep.sendAck nr3 1 (by decide))) <|
    .stepL (LeaseStepNoResetOnAck.deliverAck nr4 1 0 1 0 0 0 (by decide) (by decide)) <|
    .stepL (.step (LeaseStep.sendGrant nr5 0 1 (by decide) (by decide) (by decide) (by decide))) <|
    .stepL (.step (LeaseStep.deliverData nr6 0 1 0 1 0 0 (some 0) (by decide) (by decide) (by decide)
      (by decide))) <|
    .stepL (.step (LeaseStep.demote nr7 0 1 (by decide) (by decide) (by decide) (Or.inr (by decide)))) <|
    .stepL (.step (LeaseStep.core nr8 _ _ (Step.append nr8.core 0 (by decide) (writable_zero _ _)) rfl)) <|
    .stepL (.step (LeaseStep.core nr9 _ _ (Step.commit nr9.core 0 (by decide) (writable_zero _ _)
      (by decide) (by decide)) rfl)) <|
    .refl⟩, by decide, by decide⟩

/-! ## A confirmation counts only with no acknowledgement since the request -/

/-- `LeaseStep`, plus a confirmation accepted whatever arrived since the request. -/
inductive LeaseStepNoConfirmGuard (m : Nat) (P : LeaseParams) :
    LeaseState N → LeaseAction N → LeaseState N → Prop
  | step {a μ a'} : LeaseStep m P a μ a' → LeaseStepNoConfirmGuard m P a μ a'
  | deliverDropConfirm (a : LeaseState N) (r p : N) (gs gd t : Nat) : Msg.dropAck r p gs gd t ∈ a.net →
      (Msg.dropAck r p gs gd t).Current a →
      LeaseStepNoConfirmGuard m P a (.deliver (.dropAck r p gs gd t)) (deliverDropConfirm a (.dropAck r p gs gd t) p r)

def leaseTransitionSystemNoConfirmGuard (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepNoConfirmGuard m P

def ng1 := sendDropRequest l5 0 1                                         -- n0 asks n1
def ng2 := send ng1 (.ack 1 (primaryOf ng1.core 1) (ng1.gen 1) (ng1.gen (primaryOf ng1.core 1)) ng1.now
  (ng1.dataSent 1))                                                       -- n1 acknowledges first
def ng3 := deliverAck ng2 (.ack 1 0 1 0 0 0) 1 0 0 0                      -- n0 receives it
def ng4 := send ng3 (.data 0 1 (ng3.gen 0) (ng3.gen 1) ng3.now (ng3.core.commit 0) (ng3.ackEcho 0 1))
def ng5 := deliverDropRequest ng4 (.dropReq 0 1 0 1 0) 1 0                -- n1 drops and confirms
def ng6 := deliverData ng5 (.data 0 1 0 1 0 0 (some 0)) 1 0 0 (some 0)    -- the echo arrives after the drop
def ng7 := deliverDropConfirm ng6 (.dropAck 1 0 1 0 0) 0 1                -- accepted without the guard
def ng8 := withCore ng7 (makeIneligible ng7.core 0 1)
def ng9 := withCore ng8 (appendWrite ng8.core 0)
def ng10 := withCore ng9 (commitNext ng9.core 0)

/-- A confirmation must count only if no acknowledgement arrived since the request:
otherwise an echo of that acknowledgement may reach the replica after it dropped its
lease, and the replica may serve a stale read after the planned demotion. -/
theorem noConfirmGuard_stale :
    ∃ a, (leaseTransitionSystemNoConfirmGuard 0 P0).CanReach (leaseInit 0) a ∧
      ReplCanRead P0 a 1 ∧ a.core.log 1 ≠ a.core.hist := by
  obtain ⟨_, hp⟩ := leases_prefix_delayed
  exact ⟨ng10, ⟨_, LTS.MTr.comp _ (delayedMtr_lift LeaseStepNoConfirmGuard.step hp) <|
    .stepL (.step (LeaseStep.sendDropRequest l5 0 1 (by decide) (by decide) (by decide))) <|
    .stepL (.step (LeaseStep.sendAck ng1 1 (by decide))) <|
    .stepL (.step (LeaseStep.deliverAck ng2 1 0 1 0 0 0 (by decide) (by decide))) <|
    .stepL (.step (LeaseStep.sendGrant ng3 0 1 (by decide) (by decide) (by decide) (by decide))) <|
    .stepL (.step (LeaseStep.deliverDropRequest ng4 0 1 0 1 0 (by decide) (by decide))) <|
    .stepL (.step (LeaseStep.deliverData ng5 0 1 0 1 0 0 (some 0) (by decide) (by decide) (by decide)
      (by decide))) <|
    .stepL (LeaseStepNoConfirmGuard.deliverDropConfirm ng6 1 0 1 0 0 (by decide) (by decide)) <|
    .stepL (.step (LeaseStep.demote ng7 0 1 (by decide) (by decide) (by decide) (Or.inr (by decide)))) <|
    .stepL (.step (LeaseStep.core ng8 _ _ (Step.append ng8.core 0 (by decide) (writable_zero _ _)) rfl)) <|
    .stepL (.step (LeaseStep.core ng9 _ _ (Step.commit ng9.core 0 (by decide) (writable_zero _ _)
      (by decide) (by decide)) rfl)) <|
    .refl⟩, by decide, by decide⟩

end SyncReplication
