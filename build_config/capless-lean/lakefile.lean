import Lake
open Lake DSL

package «capless» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`linter.unusedVariables, false⟩
  ]
  -- add any additional package configuration options here

-- Batteries
require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.21.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.21.0"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.21.0"

require «importGraph» from git -- requires graphviz
  "https://github.com/leanprover-community/import-graph" @ "v4.21.0"

@[default_target]
lean_lib «Capless» where
  -- add any library configuration options here
