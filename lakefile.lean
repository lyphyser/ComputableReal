import Lake
open Lake DSL

package «computableReal» {
    leanOptions := #[⟨`experimental.module, true⟩]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «ComputableReal» {
  -- add any library configuration options here
}
