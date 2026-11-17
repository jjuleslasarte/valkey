import Lake
open Lake DSL

package SyncReplication

-- Mathlib, pinned to the release matching `lean-toolchain`. Fetch its prebuilt
-- oleans with `lake exe cache get` before the first build.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

-- CSLib (https://www.cslib.io), pinned to its last commit on Lean v4.35.0 and the same
-- Mathlib revision. Supplies labelled transition systems, runs, reachability and
-- invariants.
require cslib from git
  "https://github.com/leanprover/cslib" @ "0b1e3680b43ad9cd482a66f183764f33fc8a4e8f"

-- The synchronous replication design: model, invariant, safety and durability
-- theorems, counterexamples (see the README, section 6).
@[default_target]
lean_lib SyncReplication

-- Lease timing (see the README, section 3.2).
@[default_target]
lean_lib Lease
