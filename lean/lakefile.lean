import Lake
open Lake DSL

package "synth_lean" where
  version := v!"0.1.0"
  -- mathlib's stack uses these for performance.
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib «SynthLean» where
  -- add library configuration options here
