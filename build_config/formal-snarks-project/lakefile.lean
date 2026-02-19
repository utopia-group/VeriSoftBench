import Lake
open Lake DSL

package «formalSnarksProject» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib «FormalSnarksProject» {
  globs := #[
    .one `FormalSnarksProject,
    .submodules `FormalSnarksProject.Models,
    .one `FormalSnarksProject.SoundnessTactic.SoundnessProver,
    .one `FormalSnarksProject.SoundnessTactic.CasesOr,
    .one `FormalSnarksProject.SoundnessTactic.ProofMode,
    .submodules `FormalSnarksProject.Transformations,
    .one `FormalSnarksProject.ToMathlib.OptionEquivRight,
    .submodules `FormalSnarksProject.SNARKs.Lipmaa,
    .one `FormalSnarksProject.SNARKs.ToySnark
  ]
}
