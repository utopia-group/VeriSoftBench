import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.23.0"
require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "2c088e7617d6e2018386de23b5df3b127fae4634"

package Loom where
  leanOptions :=  #[⟨`pp.unicode.fun , true⟩] -- pretty-prints `fun a ↦ b`

def CaseStudiesRoot : Array Glob :=
  #[`CaseStudies.Extension,
    `CaseStudies.Macro,
    `CaseStudies.Tactic,
    `CaseStudies.TestingUtil,
    `CaseStudies.Theory]

@[default_target]
lean_lib Loom {
  globs := #[Glob.submodules `Loom]
}

@[default_target]
lean_lib CaseStudiesBase {
  globs := CaseStudiesRoot
}

lean_lib Cashmere {
  globs := #[Glob.submodules `CaseStudies.Cashmere]
}

lean_lib Velvet {
  globs := #[Glob.submodules `CaseStudies.Velvet]
}

lean_lib CaseStudies {
  globs := #[Glob.submodules `Loom, Glob.submodules `CaseStudies]
}
