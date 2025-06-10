import Lake
open Lake DSL

package «RiemannHypothesis» where
  -- add package configuration options here

lean_lib «RiemannHypothesis» where
  -- All modules
  roots := #[
    `Infrastructure.WeightedHilbertSpace,
    `Infrastructure.WeightedInnerProduct,
    `RiemannHypothesis_Complete_Reconstructed,
    `RiemannHypothesis_Complete,
    `Main
  ]

@[default_target]
lean_exe «riemann» where
  root := `Main
  supportInterpreter := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"
