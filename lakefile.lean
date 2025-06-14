import Lake
open Lake DSL

package «RiemannHypothesis» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.10.0"

@[default_target]
lean_lib «RiemannHypothesis» where
  -- add library configuration options here
  roots := #[`RiemannHypothesis_Axiomatized_Final]

lean_exe «riemann» where
  root := `Main
