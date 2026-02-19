import Lake
open Lake DSL

package Hoare

@[default_target]
lean_lib HoareWhile where
  roots := #[`Hoare.While]
