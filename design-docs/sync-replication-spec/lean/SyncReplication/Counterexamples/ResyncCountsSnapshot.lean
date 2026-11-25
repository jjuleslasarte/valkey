import SyncReplication.Counterexamples.Leases

/-!
# A replica must hold reads after a full sync until the snapshot's offset commits

A full sync from a primary that is still reconciling carries the whole log the primary
inherited, not only its committed prefix (`resync` copies up to `catchUpPoint`, which is
the inherited end during reconciliation). The tail past the committed offset has not
committed and can still be lost. The model's Resync therefore starts the replica's
committed view at 0 (`leaseResync`). With whole-keyspace dirty tracking, every entry past
the committed view is dirty, so the replica holds every read until a `REPLCONF COMMIT`
covers its log. In the design's per-key terms, after a full sync a node treats its whole
keyspace as dirty until its committed offset passes the snapshot's offset.

`LeaseStepResyncCountsSnapshot` is `InstantLeaseStep` plus a Resync that counts the
snapshot as committed: the replica's committed view is set to the length of the log it
loaded. This is the per-key gap in the model's terms: loading a snapshot modifies no
key, so no key it brought is marked dirty.

The run, at `P0` and `min-sync-replicas = 0`: the shared prefix; n0 writes and n1 copies
the entry; n2 learns the configuration; time passes until n0's lease from n1 is over and
n1 takes over, inheriting `[1]`, which has not committed. n2 learns that n1 is primary
and full-syncs from it, loading `[1]`. n2 reconnects with PSYNC and acknowledges offset
1, the catch-up point, so n1 counts it and makes it eligible. n2 acknowledges a heartbeat,
which gives n1 its primary lease from n2, and n1 echoes the acknowledgement. n2 holds a
read lease and serves a linearizable read of the uncommitted write. In the protocol its
committed view would be 0 and the read would be held.

Keeping the committed view from before the full sync is argued safe, not proven:
README Appendix B.
-/

open Cslib

namespace SyncReplication

/-- `leaseResync`, except that the replica counts the loaded snapshot as committed. -/
def leaseResyncCountingSnapshot (a : LeaseState N) (r : N) : LeaseState N :=
  { leaseResync a r with committedView := update a.committedView r ((resync a.core r).log r).length }

/-- `InstantLeaseStep`, plus a Resync that counts the snapshot as committed. -/
inductive LeaseStepResyncCountsSnapshot (m : Nat) (P : LeaseParams) :
    LeaseState N → LeaseAction N → LeaseState N → Prop
  /-- Every step of the lease layer. -/
  | step {a μ a'} : InstantLeaseStep m P a μ a' → LeaseStepResyncCountsSnapshot m P a μ a'
  /-- Resync, with its guards, counting the snapshot as committed. -/
  | resync (a : LeaseState N) (r : N) : primaryOf a.core r ≠ r →
      a.core.sync (primaryOf a.core r) r = false → (a.core.localCfg (primaryOf a.core r)).eligible r = false →
      LeaseStepResyncCountsSnapshot m P a (.resync r) (leaseResyncCountingSnapshot a r)

/-- The weakened lease layer as a transition system. -/
def leaseTransitionSystemResyncCountsSnapshot (m : Nat) (P : LeaseParams) : LTS (LeaseState N) (LeaseAction N) where
  Tr := LeaseStepResyncCountsSnapshot m P

def rs6 := withCore l5 (appendWrite l5.core 0)           -- n0 writes at offset 1
def rs7b := withCore rs6 (streamNext rs6.core 0 1 0)     -- n0 streams the entry
def rs7 := withCore rs7b (applyData rs7b.core (.data 0 1 1 1 1) 1 1 1) -- n1 copies it
def rs8 := leaseLearn rs7 2                              -- n2 learns the configuration
def rs9 := tick rs8
def rs10 := tick rs9
def rs11 := tick rs10
def rs12 := tick rs11                                    -- now = 4
def rs13 := leaseTakeover rs12 1                         -- n1 takes over (0 + 5 ≤ 4 + 1), inheriting [1]
def rs14 := leaseLearn rs13 2                            -- n2 learns it and follows n1
def rs15 := leaseResyncCountingSnapshot rs14 2           -- n2 full-syncs: [1], counted committed
def rs16 := withCore rs15 (reconnect rs15.core 2)        -- n2 reconnects with PSYNC
def rs17a := withCore rs16 (sendAckMsg rs16.core 2)      -- n2 acknowledges offset 1
def rs17 := withCore rs17a (recordAck rs17a.core (.ack 2 1 4 1) 1 2 1) -- n1 records it
def rs18 := withCore rs17 (addToSyncSet rs17.core 1 2)   -- n1 counts n2: it reached the catch-up point
def rs19p := withCore rs18 (proposeEligible rs18.core 1 2)
def rs19 := leaseLearn rs19p 1                           -- n1 makes n2 eligible
def rs20 := recvData rs19 2 rs19.core none               -- a heartbeat reaches n2
def rs21 := recvAck rs20 2 rs20.core                     -- n2 acknowledges: n1's lease from n2
def rs22 := recvData rs21 2 rs21.core (rs21.ackEcho 1 2) -- n1 echoes it: n2's read lease

/-- The run; the label list is its trace. Only `resync 2` is the weakened action. -/
theorem resyncCountsSnapshot_run : (leaseTransitionSystemResyncCountsSnapshot 0 P0).MTr l0
    [.core (.addToSyncSet 0 1), .core (.makeEligible 0 1), .learn 0, .learn 1, .core (.psync 1), .heartbeat 1, .ack 1,
     .core (.append 0), .core (.sendData 0 1), .core (.deliver (.data 0 1 1 1 1)), .learn 2,
     .tick, .tick, .tick, .tick, .takeover 1, .learn 2, .resync 2, .core (.psync 2),
     .core (.sendAck 2), .core (.deliver (.ack 2 1 4 1)), .core (.addToSyncSet 1 2),
     .core (.makeEligible 1 2), .learn 1, .heartbeat 2, .ack 2, .heartbeat 2] rs22 :=
  LTS.MTr.comp (leaseTransitionSystemResyncCountsSnapshot 0 P0)
    (leaseMtr_of_step LeaseStepResyncCountsSnapshot.step (leases_prefix P0)) <|
  .stepL (.step (InstantLeaseStep.core l5 _ _ (Step.append l5.core 0 (by decide) (writable_zero _ _)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core rs6 _ _ (Step.sendData rs6.core 0 1 0 (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core rs7b _ _
    (Step.deliverData rs7b.core 0 1 1 1 1 (by decide) (by decide) (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.learn rs7 2 (by decide))) <|
  .stepL (.step (InstantLeaseStep.tick rs8)) <| .stepL (.step (InstantLeaseStep.tick rs9)) <|
  .stepL (.step (InstantLeaseStep.tick rs10)) <| .stepL (.step (InstantLeaseStep.tick rs11)) <|
  .stepL (.step (InstantLeaseStep.takeover rs12 1 (by decide) (by decide) (by decide) (by decide) (by decide))) <|
  .stepL (.step (InstantLeaseStep.learn rs13 2 (by decide))) <|
  .stepL (LeaseStepResyncCountsSnapshot.resync rs14 2 (by decide) (by decide) (by decide)) <|
  .stepL (.step (InstantLeaseStep.core rs15 _ _ (Step.psync rs15.core 2 (by decide) (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core rs16 _ _ (Step.sendAck rs16.core 2 (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core rs17a _ _
    (Step.deliverAck rs17a.core 2 1 4 1 1 (by decide) (by decide) (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core rs17 _ _ (Step.addToSyncSet rs17.core 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.core rs18 _ _ (Step.makeEligible rs18.core 1 2 (by decide) (by decide) (by decide)
    (by decide)) rfl)) <|
  .stepL (.step (InstantLeaseStep.learn rs19p 1 (by unfold KnowsLatest; decide))) <|
  .stepL (.step (InstantLeaseStep.heartbeat rs19 2 (by decide) (by decide))) <|
  .stepL (.step (InstantLeaseStep.ackRenew rs20 2 (by decide))) <|
  .stepL (.step (InstantLeaseStep.heartbeatGrant rs21 2 (by decide) (by decide) (by decide) (by decide))) <|
  .refl

/-- A replica must hold reads after a full sync until the snapshot's offset commits: a
write-behind replica that counts a snapshot from a reconciling primary as committed is
promoted, granted a read lease, and serves a linearizable read of a write nobody has
committed. -/
theorem resyncCountsSnapshot_stale :
    ∃ a, (leaseTransitionSystemResyncCountsSnapshot 0 P0).CanReach (leaseInit 0) a ∧
      ReplCanRead P0 a 2 ∧ a.core.log 2 ≠ a.core.hist ∧ a.core.hist = [] :=
  ⟨rs22, ⟨_, resyncCountsSnapshot_run⟩, by decide, by decide, by decide⟩

end SyncReplication
