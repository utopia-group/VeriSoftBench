import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"334be41cd6a4737ac24813c926c6f61fcedd1998"

package «FVIntmax» where

@[default_target]
lean_lib «FVIntmax» where
  
