import Lake
open Lake DSL

abbrev vcvLinters : Array LeanOption := #[
  -- ⟨`linter.docPrime, true⟩,
  ⟨`linter.hashCommand, true⟩,
  ⟨`linter.oldObtain, true,⟩,
  ⟨`linter.refine, true⟩,
  ⟨`linter.style.cdot, true⟩,
  ⟨`linter.style.dollarSyntax, true⟩,
  -- ⟨`linter.style.lambdaSyntax, true⟩,
  ⟨`linter.style.longLine, true⟩,
  ⟨`linter.style.longFile, .ofNat 1500⟩,
  ⟨`linter.style.missingEnd, true⟩,
  ⟨`linter.style.setOption, true⟩
]

package VCVio where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]
    ++ vcvLinters.map fun s ↦
      { s with name := `weak ++ s.name }

require "leanprover-community" / "mathlib" @ git "v4.24.0-rc1"

/-- Main library. -/
@[default_target] lean_lib VCVio
/-- Example constructions of cryptographic primitives. -/
@[default_target] lean_lib Examples

/-- Seperate section of the project for things that should be ported. -/
lean_lib ToMathlib
/-- Access to external C++ implementations of crypto primitives. -/
lean_lib LibSodium

/-- Main function for testing -/
lean_exe test where root := `Test

-- /-- Runnable implementations of specific cryptographic algorithms.
-- Set `precompileModules` in order to allow execution of external code. -/
-- lean_lib Implementations where
--    precompileModules := true

-- C++ extern_lib removed for Docker build (not needed for proof verification)
