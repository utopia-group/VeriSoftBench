import Lake
open Lake DSL

package «WadrayVerification» {
  -- add package configuration options here
}

require corelib_verification from git
  "https://github.com/lindy-labs/corelib_verification.git" @ "main"

@[default_target]
lean_lib «WadrayVerification» {
  -- add library configuration options here
}

