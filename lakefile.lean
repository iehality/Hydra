import Lake
open Lake DSL

package «Hydra» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "FormalizedFormalLogic" / "foundation" @ git "master"

@[default_target]
lean_lib «Hydra» where
  -- add any library configuration options here
