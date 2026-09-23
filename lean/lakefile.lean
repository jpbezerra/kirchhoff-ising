import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"

package kirchhoff_ising where
  srcDir := "."

@[default_target]
lean_lib Kirchhoff where
  roots := #[`Circuit, `Ising, `Laws, `Tests]
