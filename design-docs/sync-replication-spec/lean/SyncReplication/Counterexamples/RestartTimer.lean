import SyncReplication.Counterexamples.Leases

/-!
# A restarted node must not treat its primary as long silent

A replica takes over only once the old primary's lease from it must have expired,
measured from the last traffic it received from that primary (`primaryTraffic`). The
design's restart rule says a restarted node "waits one full lease duration before it
attempts a takeover"; the model implements that by restarting the timer at the restart
time. A restarted node that has forgotten the timer and treats the primary as never
heard from breaks the rule, and this file shows that loses property 6.

`LeaseStepRestartForgetsTimer` is `LeaseStep` plus RestartKeep that sets the restarted
node's timer to 0, the oldest possible time. The run, at `P0` and
`min-sync-replicas = 0`: n0 promotes n1; at time 4 a heartbeat reaches n1 and n1
acknowledges, so n0 holds its lease from n1 from time 4; n1 restarts with its data and
takes over at once (`0 + 5 ≤ 4 + 1`), writes and commits alone. n0 has not learned of
it, still holds its lease from n1 (`4 + 2 < 4 + 5 + 1`) and may serve a read that misses
n1's write.
-/

open Cslib

namespace SyncReplication

/-- `leaseRestart`, except that the restarted node's takeover timer is set to 0: it
behaves as if it had never heard from its primary. -/
def leaseRestartForgettingTimer (a : LeaseState N) (n : N) (c : State N) : LeaseState N :=
  { leaseRestart a n c with primaryTraffic := update a.primaryTraffic n 0 }

/-- `LeaseStep`, plus RestartKeep that forgets the takeover timer. -/
inductive LeaseStepRestartForgetsTimer (m : Nat) (P : LeaseParams) :
    LeaseState N → LeaseAction N → LeaseState N → Prop
  /-- Every step of the lease layer. -/
  | step {a μ a'} : LeaseStep m P a μ a' → LeaseStepRestartForgetsTimer m P a μ a'
  /-- RestartKeep, with its guard, setting the takeover timer to 0. -/
  | restartKeep (a : LeaseState N) (n : N) : KnowsLatest a.core n →
      LeaseStepRestartForgetsTimer m P a (.restartKeep n)
        (leaseRestartForgettingTimer a n (restartKeep a.core n))

/-- The weakened lease layer as a transition system. -/
def leaseLTSRestartForgetsTimer (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepRestartForgetsTimer m P

/-- n0 counts n1. -/
def forgetTimer1 := withCore l0 (count l0.core 0 1)
/-- n0 makes n1 eligible. -/
def forgetTimer2 := withCore forgetTimer1 (makeEligible forgetTimer1.core 0 1)
/-- n1 learns the configuration. -/
def forgetTimer3 := leaseLearn forgetTimer2 1
/-- Time 1. -/
def forgetTimer4 := tick forgetTimer3
/-- Time 2. -/
def forgetTimer5 := tick forgetTimer4
/-- Time 3. -/
def forgetTimer6 := tick forgetTimer5
/-- Time 4. -/
def forgetTimer7 := tick forgetTimer6
/-- A heartbeat from n0 reaches n1 at time 4. -/
def forgetTimer8 := recvData forgetTimer7 1 forgetTimer7.core none
/-- n1 acknowledges: n0's lease from n1 starts at 4. -/
def forgetTimer9 := recvAck forgetTimer8 1 forgetTimer8.core
/-- n1 restarts with its data and forgets its takeover timer. -/
def forgetTimer10 := leaseRestartForgettingTimer forgetTimer9 1 (restartKeep forgetTimer9.core 1)
/-- n1 takes over at once. -/
def forgetTimer11 := leaseTakeover forgetTimer10 1
/-- n1 writes. -/
def forgetTimer12 := withCore forgetTimer11 (appendWrite forgetTimer11.core 1)
/-- n1 commits alone: the history is `[3]`. -/
def forgetTimer13 := withCore forgetTimer12 (commitNext forgetTimer12.core 1)

/-- The run; the label list is its trace. Only `restartKeep 1` is the weakened action;
the takeover that follows is a step of the lease layer. -/
theorem restartForgetsTimer_run : (leaseLTSRestartForgetsTimer 0 P0).MTr l0
    [.core (.count 0 1), .core (.makeEligible 0 1), .learn 1, .tick, .tick, .tick, .tick,
     .heartbeat 1, .ack 1, .restartKeep 1, .takeover 1, .core (.append 1), .core (.commit 1)]
    forgetTimer13 :=
  .stepL (.step (LeaseStep.core l0 _ _ (Step.count l0.core 0 1 (by decide) (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core forgetTimer1 _ _ (Step.makeEligible forgetTimer1.core 0 1 (by decide)
    (by decide) (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.learn forgetTimer2 1 (by decide))) <|
  .stepL (.step (LeaseStep.tick forgetTimer3)) <| .stepL (.step (LeaseStep.tick forgetTimer4)) <|
  .stepL (.step (LeaseStep.tick forgetTimer5)) <| .stepL (.step (LeaseStep.tick forgetTimer6)) <|
  .stepL (.step (LeaseStep.heartbeat forgetTimer7 1 (by decide) (by decide))) <|
  .stepL (.step (LeaseStep.ackRenew forgetTimer8 1 (by decide) (by decide))) <|
  .stepL (LeaseStepRestartForgetsTimer.restartKeep forgetTimer9 1 (by decide)) <|
  .stepL (.step (LeaseStep.takeover forgetTimer10 1 (by decide) (by decide) (by decide) (by decide)
    (by decide))) <|
  .stepL (.step (LeaseStep.core forgetTimer11 _ _ (Step.append forgetTimer11.core 1 (by decide)
    (writable_zero _ _)) rfl)) <|
  .stepL (.step (LeaseStep.core forgetTimer12 _ _ (Step.commit forgetTimer12.core 1 (by decide)
    (writable_zero _ _) (by decide) (by decide)) rfl)) <|
  .refl

/-- A restarted node must not treat its primary as long silent: a replica that restarts,
forgets its takeover timer and takes over at once commits while the deposed primary
still holds its lease from it, and the deposed primary may serve a linearizable read
that misses the write. -/
theorem restartForgetsTimer_stale :
    ∃ a, (leaseLTSRestartForgetsTimer 0 P0).CanReach (leaseInit 0) a ∧
      PrimCanRead P0 a 0 ∧ a.core.log 0 ≠ a.core.hist :=
  ⟨forgetTimer13, ⟨_, restartForgetsTimer_run⟩, by decide, by decide⟩

end SyncReplication
