import Lake
open Lake DSL

package «PauliContextuality» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

/-- Computational data and Boolean checkers (imports only Lean core).
Compiled to native code so that `native_decide` in `Qminus.lean` runs in ~1 minute
instead of hours in the interpreter. -/
lean_lib «PauliData» where
  precompileModules := true

@[default_target]
lean_lib «PauliContextuality» where
