import Lake
open Lake DSL

-- Depends on the Aeneas Lean standard library from the local Aeneas checkout
-- used for this spike (same as the Binder spike):
--   ~/aeneas-project/aeneas @ c2015b86, charon-pin 909ff09a (v0.1.220),
--   Lean/mathlib v4.31.0. Build it once before building here:
--     cd ~/aeneas-project/aeneas/backends/lean && lake exe cache get && lake build Aeneas
require aeneas from
  "../../../aeneas-project/aeneas/backends/lean"

package «uvc_parse_verif» where

@[default_target] lean_lib «UvcParse» where

@[default_target] lean_lib «NoPanic» where
