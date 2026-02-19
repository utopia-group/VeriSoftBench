import Lake
open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "36d85bf6372f1a35fb5487325d1ef965b33c6296"
require smt from git "https://github.com/ufmg-smite/lean-smt.git" @ "3c6b049eb0ccf7c331f3686e12e5f5b666bdd30a"

package veil

@[default_target]
lean_lib «Veil» {
  globs := #[`Veil, .submodules `Veil]
}

@[default_target, test_driver]
lean_lib Test {
  globs := #[Glob.submodules `Test]
}

lean_lib Examples {
  globs := #[.submodules `Examples]
}
