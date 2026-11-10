import SyncReplication.Counterexamples.Leases

/-!
# Only a primary holding its primary lease may grant read leases

`MayGrant` requires the granting node to hold a valid primary lease from every eligible
replica it knows of (`PrimLeaseValid`): a deposed primary stops granting (design §5,
"Leases across a failover"). A deposed primary that has not learned of the takeover
still thinks it is primary, and a replica that has not learned of it still follows it.

`LeaseStepGrantWithoutPrimaryLease` is `LeaseStep` plus an echo that checks every part
of `MayGrant` except `PrimLeaseValid`. The run, at `P0` and `min-sync-replicas = 0`:
n0 promotes n1 and n2; n1 learns the configuration, waits out n0's lease and takes over;
after its post-takeover wait it demotes n2, writes and commits alone. n0 and n2 have
not learned of it: n2 acknowledges to n0, and n0, holding no valid lease (none from n1, an expired one from n2), echoes the
acknowledgement. n2 holds a fresh read lease and an empty log.
-/

open Cslib

namespace SyncReplication

/-- `LeaseStep`, plus an echo from a node that need not hold its primary lease. -/
inductive LeaseStepGrantWithoutPrimaryLease (m : Nat) (P : LeaseParams) :
    LeaseState N → LeaseAction N → LeaseState N → Prop
  /-- Every step of the lease layer. -/
  | step {a μ a'} : LeaseStep m P a μ a' → LeaseStepGrantWithoutPrimaryLease m P a μ a'
  /-- The echo with every guard of `LeaseStep.heartbeatGrant` except `PrimLeaseValid`:
  `r` is a sync member, eligible with a matching incarnation, in its primary's
  configuration. -/
  | heartbeatGrant (a : LeaseState N) (r : N) : primaryOf a.core r ≠ r →
      ThinksPrimary a.core (primaryOf a.core r) → a.core.log r <+: a.core.log (primaryOf a.core r) →
      a.core.sync (primaryOf a.core r) r = true → (a.core.localCfg (primaryOf a.core r)).eligible r = true →
      (a.core.localCfg (primaryOf a.core r)).incarnation r = a.core.incarnation r →
      LeaseStepGrantWithoutPrimaryLease m P a (.heartbeat r)
        (recvData a r a.core (a.ackEcho (primaryOf a.core r) r))

/-- The weakened lease layer as a transition system. -/
def leaseTransitionSystemGrantWithoutPrimaryLease (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepGrantWithoutPrimaryLease m P

def lq5 := leaseLearn li4 1                           -- n1 learns epoch 3; n0 and n2 never learn more
def lq6 := tick lq5
def lq7 := tick lq6
def lq8 := tick lq7
def lq9 := tick lq8                                   -- now = 4
def lq10 := leaseTakeover lq9 1                       -- n1's wait is over: 0 + 5 ≤ 4 + 1
def lq11 := tick lq10
def lq12 := tick lq11
def lq13 := tick lq12                                 -- now = 7: post-takeover wait over, 4 + 2 + 2 ≤ 7 + 1
def lq14 := withCore lq13 (makeIneligible lq13.core 1 2) -- n1 demotes n2
def lq15 := withCore lq14 (appendWrite lq14.core 1)   -- n1 writes
def lq16 := withCore lq15 (commitNext lq15.core 1)    -- n1 commits alone: the history is [4]
def lq17 := recvAck lq16 2 lq16.core                  -- n2, still following n0, acknowledges to it
def lq18 := recvData lq17 2 lq17.core (lq17.ackEcho 0 2) -- n0, deposed and leaseless, echoes it

/-- The run; the label list is its trace. Only the last `heartbeat 2` is the weakened
action. -/
theorem grantWithoutPrimaryLease_run : (leaseTransitionSystemGrantWithoutPrimaryLease 0 P0).MTr l0
    [.core (.addToSyncSet 0 1), .core (.makeEligible 0 1), .core (.addToSyncSet 0 2), .core (.makeEligible 0 2),
     .learn 1, .tick, .tick, .tick, .tick, .takeover 1, .tick, .tick, .tick, .demote 1 2,
     .core (.append 1), .core (.commit 1), .ack 2, .heartbeat 2] lq18 :=
  .stepL (.step (LeaseStep.core l0 _ _ (Step.addToSyncSet l0.core 0 1 (by decide) (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core li1 _ _ (Step.makeEligible li1.core 0 1 (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core li2 _ _ (Step.addToSyncSet li2.core 0 2 (by decide) (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.core li3 _ _ (Step.makeEligible li3.core 0 2 (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.learn li4 1 (by decide))) <|
  .stepL (.step (LeaseStep.tick lq5)) <| .stepL (.step (LeaseStep.tick lq6)) <|
  .stepL (.step (LeaseStep.tick lq7)) <| .stepL (.step (LeaseStep.tick lq8)) <|
  .stepL (.step (LeaseStep.takeover lq9 1 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (LeaseStep.tick lq10)) <| .stepL (.step (LeaseStep.tick lq11)) <|
  .stepL (.step (LeaseStep.tick lq12)) <|
  .stepL (.step (LeaseStep.demote lq13 1 2 (by decide) (by decide) (by decide) (by decide)
    (by decide))) <|
  .stepL (.step (LeaseStep.core lq14 _ _ (Step.append lq14.core 1 (by decide) (writable_zero _ _)) rfl)) <|
  .stepL (.step (LeaseStep.core lq15 _ _ (Step.commit lq15.core 1 (by decide) (writable_zero _ _)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (LeaseStep.ackRenew lq16 2 (by decide) (by decide))) <|
  .stepL (LeaseStepGrantWithoutPrimaryLease.heartbeatGrant lq17 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) <|
  .refl

/-- `PrimLeaseValid` in `MayGrant` is needed: a deposed primary that has not learned of
the takeover grants a read lease to a replica that still follows it, and the replica
may serve a linearizable read that misses the new primary's committed write. -/
theorem grantWithoutPrimaryLease_stale :
    ∃ a, (leaseTransitionSystemGrantWithoutPrimaryLease 0 P0).CanReach (leaseInit 0) a ∧
      ReplCanRead P0 a 2 ∧ a.core.log 2 ≠ a.core.hist :=
  ⟨lq18, ⟨_, grantWithoutPrimaryLease_run⟩, by decide, by decide⟩

end SyncReplication
