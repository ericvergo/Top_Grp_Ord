import Lake
open Lake DSL

package «TopGrpOrd» where
  -- add package configuration options here
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,  -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «OrdinalHomeo» where
  -- add library configuration options here

@[default_target]
lean_lib «TopGrpOrd» where
  -- add library configuration options here
