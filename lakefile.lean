import Lake
open Lake DSL

package «lean-playground» where
  -- add package configuration options here

lean_lib «LeanPlayground» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-playground» where
  root := `Main
