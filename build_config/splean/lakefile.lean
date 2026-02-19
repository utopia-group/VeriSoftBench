import Lake
open Lake DSL

package splean where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require batteries from
    git "https://github.com/leanprover-community/batteries" @ "v4.11.0"
require mathlib from
    git "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"
-- require loogle from git "https://github.com/nomeata/loogle.git" @ "master"
require ssreflect from
    git "https://github.com/verse-lab/lean-ssr.git" @ "v4.11.0"

@[default_target]
lean_lib SPLean where
  -- add any library configuration options here
