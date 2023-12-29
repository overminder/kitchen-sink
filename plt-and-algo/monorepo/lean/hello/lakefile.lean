import Lake
open Lake DSL

package «hello» where
  -- add package configuration options here

lean_lib «Hello» where
  -- add library configuration options here

@[default_target]
lean_exe «hello» where
  root := `Main
