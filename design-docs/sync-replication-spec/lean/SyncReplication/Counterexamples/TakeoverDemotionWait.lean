import SyncReplication.Counterexamples.Leases

/-!
# A new primary must wait before demoting a replica of the old configuration

After a takeover the new primary has received no acknowledgement from anyone, so the
demotion guard's read-lease wait (`GrantorOver`) is vacuous. A replica of the replaced
configuration may still hold a read lease granted by the old primary. The model's
takeover therefore records which replicas were eligible before (`oldEligible`) and
the demotion guard waits one read lease plus the margin after the takeover for those.

`LeaseStepTakeoverNoDemotionWait` is `InstantLeaseStep` plus a takeover that marks no replica
as old, so no wait follows it. The run uses `P3` (primary lease 6, read lease 3, drift
1, margin 2), within the design's duration rule: with a read lease of 2 (`P0`) a lease
granted at the last moment the old primary may grant has expired by the earliest
takeover. n0 promotes n1 and n2, both acknowledge at time 0; at time 4, the last tick at
which n0 holds its lease from n1, n2 acknowledges again and n0 echoes it, so n2's read
lease starts at 4; at time 5 n1 takes over, demotes n2 at once, writes and commits alone.
n2's read lease is still valid.
-/

open Cslib

namespace SyncReplication

/-- `leaseTakeover`, except that the new primary marks no replica as one of the
replaced configuration, so no demotion wait follows the takeover. -/
def leaseTakeoverWithoutDemotionWait (a : LeaseState N) (n : N) : LeaseState N :=
  { leaseTakeover a n with oldEligible := update a.oldEligible n (fun _ => false) }

/-- `InstantLeaseStep`, plus a takeover without the demotion wait. -/
inductive LeaseStepTakeoverNoDemotionWait (m : Nat) (P : LeaseParams) :
    LeaseState N → LeaseAction N → LeaseState N → Prop
  /-- Every step of the lease layer. -/
  | step {a μ a'} : InstantLeaseStep m P a μ a' → LeaseStepTakeoverNoDemotionWait m P a μ a'
  /-- Takeover, with every guard of `InstantLeaseStep.takeover`, arming no demotion wait. -/
  | takeover (a : LeaseState N) (n : N) : KnowsLatest a.core n → a.core.cfg.eligible n = true →
      n ≠ a.core.cfg.primary → a.core.cfg.incarnation n = a.core.incarnation n →
      a.primaryTraffic n + P.primDur ≤ a.now + P.drift →
      LeaseStepTakeoverNoDemotionWait m P a (.takeover n) (leaseTakeoverWithoutDemotionWait a n)

/-- The weakened lease layer as a transition system. -/
def leaseTransitionSystemTakeoverNoDemotionWait (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepTakeoverNoDemotionWait m P

def lt5 := leaseLearn li4 1                           -- n1 learns epoch 3
def lt6 := leaseLearn lt5 2                           -- n2 learns epoch 3
def lt6a := withCore lt6 (reconnect lt6.core 1)       -- n1 reconnects with PSYNC
def lt6b := withCore lt6a (reconnect lt6a.core 2)     -- n2 reconnects with PSYNC
def lt7 := recvData lt6b 1 lt6b.core none             -- a heartbeat reaches n1 at time 0
def lt8 := recvAck lt7 1 lt7.core                     -- n1 acknowledges: n0's lease from n1 starts at 0
def lt9 := recvData lt8 2 lt8.core none               -- a heartbeat reaches n2 at time 0
def lt10 := recvAck lt9 2 lt9.core                    -- n2 acknowledges
def lt11 := tick lt10
def lt12 := tick lt11
def lt13 := tick lt12
def lt14 := tick lt13                                 -- now = 4
def lt15 := recvData lt14 2 lt14.core none            -- a heartbeat reaches n2
def lt16 := recvAck lt15 2 lt15.core                  -- n2 acknowledges at 4
def lt17 := recvData lt16 2 lt16.core (lt16.ackEcho 0 2) -- n0 echoes it: n2's read lease starts at 4
def lt18 := tick lt17                                 -- now = 5
def lt19 := leaseTakeoverWithoutDemotionWait lt18 1   -- n1's wait is over: 0 + 6 ≤ 5 + 1
def lt20 := withCore lt19 (makeIneligible lt19.core 1 2) -- n1 demotes n2 at once
def lt21 := withCore lt20 (appendWrite lt20.core 1)   -- n1 writes
def lt22 := withCore lt21 (commitNext lt21.core 1)    -- n1 commits alone: the history is [4]

/-- The run; the label list is its trace. Only `takeover 1` is the weakened action;
the demotion that follows is a step of the lease layer. -/
theorem takeoverNoDemotionWait_run : (leaseTransitionSystemTakeoverNoDemotionWait 0 P3).MTr l0
    [.core (.addToSyncSet 0 1), .core (.makeEligible 0 1), .core (.addToSyncSet 0 2), .core (.makeEligible 0 2),
     .learn 1, .learn 2, .core (.psync 1), .core (.psync 2), .heartbeat 1, .ack 1, .heartbeat 2, .ack 2,
     .tick, .tick, .tick, .tick, .heartbeat 2, .ack 2, .heartbeat 2, .tick,
     .takeover 1, .demote 1 2, .core (.append 1), .core (.commit 1)] lt22 :=
  .stepL (.step (InstantLeaseStep.core l0 _ _ (Step.addToSyncSet l0.core 0 1 (by decide) (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core li1 _ _ (Step.makeEligible li1.core 0 1 (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core li2 _ _ (Step.addToSyncSet li2.core 0 2 (by decide) (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core li3 _ _ (Step.makeEligible li3.core 0 2 (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.learn li4 1 (by decide))) <|
  .stepL (.step (InstantLeaseStep.learn lt5 2 (by decide))) <|
  .stepL (.step (InstantLeaseStep.core lt6 _ _ (Step.psync lt6.core 1 (by decide) (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core lt6a _ _ (Step.psync lt6a.core 2 (by decide) (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.heartbeat lt6b 1 (by decide) (by decide))) <|
  .stepL (.step (InstantLeaseStep.ackRenew lt7 1 (by decide))) <|
  .stepL (.step (InstantLeaseStep.heartbeat lt8 2 (by decide) (by decide))) <|
  .stepL (.step (InstantLeaseStep.ackRenew lt9 2 (by decide))) <|
  .stepL (.step (InstantLeaseStep.tick lt10)) <| .stepL (.step (InstantLeaseStep.tick lt11)) <|
  .stepL (.step (InstantLeaseStep.tick lt12)) <| .stepL (.step (InstantLeaseStep.tick lt13)) <|
  .stepL (.step (InstantLeaseStep.heartbeat lt14 2 (by decide) (by decide))) <|
  .stepL (.step (InstantLeaseStep.ackRenew lt15 2 (by decide))) <|
  .stepL (.step (InstantLeaseStep.heartbeatGrant lt16 2 (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (InstantLeaseStep.tick lt17)) <|
  .stepL (LeaseStepTakeoverNoDemotionWait.takeover lt18 1 (by decide) (by decide) (by decide)
    (by decide) (by decide)) <|
  .stepL (.step (InstantLeaseStep.demote lt19 1 2 (by decide) (by decide) (by decide) (by decide)
    (by decide))) <|
  .stepL (.step (InstantLeaseStep.core lt20 _ _ (Step.append lt20.core 1 (by decide) (writable_zero _ _)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core lt21 _ _ (Step.commit lt21.core 1 (by decide) (writable_zero _ _)
    (by decide) (by decide)) rfl)) <|
  .refl

/-- The post-takeover demotion wait is needed, within the design's duration rule: a new
primary that demotes a replica of the replaced configuration at once commits without
it while the read lease the old primary granted it is still valid, and the replica may
serve a linearizable read that misses the write. -/
theorem takeoverNoDemotionWait_stale :
    ∃ a, (leaseTransitionSystemTakeoverNoDemotionWait 0 P3).CanReach (leaseInit 0) a ∧
      ReplCanRead P3 a 2 ∧ a.core.log 2 ≠ a.core.hist :=
  ⟨lt22, ⟨_, takeoverNoDemotionWait_run⟩, by decide, by decide⟩

end SyncReplication
