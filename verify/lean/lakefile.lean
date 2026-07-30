import Lake
open Lake DSL

-- Depends on the Aeneas Lean standard library, pinned to the exact version this
-- spike uses (same as the Binder spike): AeneasVerif/aeneas commit c2015b86,
-- charon-pin 909ff09a (v0.1.220), Lean/mathlib v4.31.0. Its Lean backend lives
-- in `backends/lean/` within the repo. Fetched as a git dependency so the
-- project builds from a clean clone (before building, run `lake exe cache get`
-- to pull the mathlib olean cache).
require aeneas from git
  "https://github.com/AeneasVerif/aeneas.git" @ "c2015b8668ba6d5b41f5f19d00a881c12bbb0b5d" / "backends/lean"

package «uvc_parse_verif» where

@[default_target] lean_lib «UvcParse» where

@[default_target] lean_lib «NoPanic» where
