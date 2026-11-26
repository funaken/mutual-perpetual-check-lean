import Lake
open Lake DSL

package mutualPerpetualCheck where
  leanOptions := #[⟨`autoImplicit, false⟩]
  -- Mathlib is designed for the module system; this project's files are not modules.
  allowNonModules := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.36.0"

@[default_target]
lean_lib MPC where
  roots := #[`MPC, `MPC.Verification, `MPC.Axioms, `MPC.PaperVerification]
