import Lake
open Lake DSL

package CoreProof

-- Mathlib, pinned to the release matching `lean-toolchain`. Fetch its prebuilt
-- oleans with `lake exe cache get` before the first build.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

-- CSLib (https://www.cslib.io), pinned to its last commit on Lean v4.35.0 and the same
-- Mathlib revision. Supplies LTS, multi-step transitions, invariants and simulations.
require cslib from git
  "https://github.com/leanprover/cslib" @ "0b1e3680b43ad9cd482a66f183764f33fc8a4e8f"

@[default_target]
lean_lib CoreProof

@[default_target]
lean_lib Lease

-- CoreAck: acknowledged writes are never lost (see LEAN.md, "Acknowledged writes").
@[default_target]
lean_lib AckProof

-- CoreRecon: safety for every min-sync-replicas value with the inherited-log
-- reconciliation rule (see LEAN.md, "Reconciliation against the inherited log").
@[default_target]
lean_lib ReconProof

-- CoreRestart: restarts with and without data, incarnations, F5 fix; acknowledged
-- writes survive while an authoritative node keeps its data (see LEAN.md, "Restarts").
@[default_target]
lean_lib RestartProof
