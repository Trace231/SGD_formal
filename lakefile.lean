import Lake
open Lake DSL

package sgd

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"stable"

-- Core library: all modules under Lib/ (Layer0, Layer1)
lean_lib StochOptLib where
  roots := #[`Lib]

-- Root-level files still being migrated to Lib/
-- These entries are removed one by one as each file moves into Lib/
lean_lib ConvexGradient

lean_lib IndepExpect

-- Main entry: will be replaced by Algorithms/SGD.lean after full migration
@[default_target]
lean_lib Main where
  leanOptions := #[⟨`autoImplicit, false⟩]
  roots := #[`Main]
  extraDepTargets := #[`StochOptLib, `ConvexGradient, `IndepExpect]
