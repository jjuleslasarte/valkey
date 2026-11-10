import SyncReplication.Counterexamples.Basic

/-!
# Resync only a replica its primary has not counted: the state the guard excludes is reachable

Resync is allowed only for a replica its primary does not count. The preservation
proof uses the guard (`resync_acked_sync`): Resync resets the primary's record of the
replica's acknowledgement to 0, and the invariant bounds a primary's commit point and
its catch-up obligations by its counted members' acknowledgements.

No run shows the guard is needed. This file shows it is not vacuous either: a counted
replica whose log has diverged from its primary's is reachable. The run, at
`min-sync-replicas = 0`: n0 counts n1 (so n1 is a sync replica and may receive
uncommitted writes, as the design allows only sync replicas), n0 writes, n1 copies the
write, n0 restarts from a persistence file holding none of its log (it has
acknowledged nothing, the write being uncommitted while n1 has not acknowledged it, so
it keeps its incarnation; n1 is not eligible, so the rebuilt sync replica set is
empty), and n0 counts n1 again, whose recorded acknowledgement is 0, at catch-up point
0. n1's log `[1]` is not a prefix of n0's empty log.

In this state n0's record of n1's acknowledgement is 0, so the Resync the guard forbids
would leave every acknowledgement unchanged. Whether that holds in every reachable
state (a counted follower that has diverged has acknowledgement 0) is not proven here.
-/

open Cslib

namespace SyncReplication

/-- n0 counts n1: n1 is a sync replica. -/
def counted0 := addToSyncSet c0 0 1
/-- n0 writes at offset 1. -/
def counted1 := appendWrite counted0 0
/-- n1 copies the uncommitted write. -/
def counted2 := replicate counted1 1
/-- n0 restarts from an empty file with the same incarnation; its rebuilt sync
replica set is empty. -/
def counted3 := restartPartialKeep counted2 0 0
/-- n0 counts n1 again, at catch-up point 0. -/
def counted4 := addToSyncSet counted3 0 1

/-- The run; the label list is its trace. Every step is a step of the model. -/
theorem countedDiverged_run : (transitionSystem 0).MTr c0
    [.addToSyncSet 0 1, .append 0, .replicate 1, .restartPartial 0 0, .addToSyncSet 0 1] counted4 :=
  .stepL (Step.addToSyncSet c0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)) <|
  .stepL (Step.append counted0 0 (by decide) (writable_zero counted0 0)) <|
  .stepL (Step.replicate counted1 1 (by decide) (by decide) (by decide)) <|
  .stepL (Step.restartPartialKeep counted2 0 0 (by decide) (by decide) (by decide)) <|
  .stepL (Step.addToSyncSet counted3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)) <|
  .refl

/-- A replica its primary counts can have a log that has diverged from the primary's:
Resync's guard that the replica is not counted excludes a reachable state. In the
witness the primary's record of the replica's acknowledgement is 0. -/
theorem countedDiverged_reachable : ∃ s, Reachable 0 (0 : N) s ∧ s.sync 0 1 = true ∧
    primaryOf s 1 = 0 ∧ ¬ (s.log 1 <+: s.log 0) ∧ s.acked 0 1 = 0 :=
  ⟨counted4, ⟨_, countedDiverged_run⟩, by decide, by decide, by decide, by decide⟩

end SyncReplication
