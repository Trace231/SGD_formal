import Lake
open Lake DSL

package sgd

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"stable"

-- Core library: all modules under Lib/ (Layer0, Layer1)
lean_lib StochOptLib where
  roots := #[`Lib]

-- Main entry: will be replaced by Algorithms/SGD.lean after full migration
@[default_target]
lean_lib Main where
  leanOptions := #[⟨`autoImplicit, false⟩]
  roots := #[`Main]
  extraDepTargets := #[`StochOptLib]

-- Algorithm layer: concrete SGD convergence proofs built on Layer1 meta-theorems
-- Depends on Main (for SGDSetup, sgdProcess, etc.) which itself depends on StochOptLib
lean_lib SGDAlgorithms where
  roots := #[`Algorithms.SGD, `Algorithms.WeightDecaySGD,
             `Algorithms.ProjectedGD,  `Algorithms.SVRG]
  extraDepTargets := #[`Main]
