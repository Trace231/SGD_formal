import Lake
open Lake DSL

package sgd_apollo_ablation

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"stable"

lean_lib StochOptLib where
  roots := #[`Lib]

@[default_target]
lean_lib Main where
  leanOptions := #[⟨`autoImplicit, false⟩]
  roots := #[`Main]
  extraDepTargets := #[`StochOptLib]

lean_lib AblationAlgorithms where
  roots := #[`Algorithms.SubgradientMethod_scaffold]
  extraDepTargets := #[`Main]
