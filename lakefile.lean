import Lake
open Lake DSL

package sgd

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"stable"

lean_lib SmoothDescent

lean_lib ConvexGradient

lean_lib IndepExpect

@[default_target]
lean_lib Main where
  leanOptions := #[⟨`autoImplicit, false⟩]
  roots := #[`Main]
  extraDepTargets := #[`SmoothDescent, `ConvexGradient, `IndepExpect]
