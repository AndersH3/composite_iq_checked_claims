import Lake
open Lake DSL

/-!
Project: composite IQ Gaussian formal probability bridge.
Researcher/requester: Anders Hellström.
Pinned mathlib release SHA: 6d97e8ad9c32c778e7000ffda543a29488155467.
Purpose: Compile a genuinely measure-theoretic Gaussian conditional
expectation using standard mathlib Gaussian independence and conditional
expectation, rather than defining a new probability measure or assuming
the independence of zero-covariance Gaussian blocks.
AI disclosure: The Lean source and project configuration were AI-assisted.
No theorem is regarded as verified unless the Lean kernel build succeeds.
-/

package composite_iq_gaussian where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "6d97e8ad9c32c778e7000ffda543a29488155467"

@[default_target]
lean_lib GaussianRegression where
  srcDir := "analyses/sequential-conditional-means/lean"
