import Lake
open Lake DSL

package «PCF» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs, true⟩ -- shows full proofs in infoview
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

@[default_target]
lean_lib «PCF» where
  globs := #[.submodules `PCF]
