-- Safety theorems for the faithful UVC format/frame descriptor parser, as
-- translated by Aeneas from
--   llbc/uvc_verify-charon-909ff09a-v0.1.220.llbc
--
-- Context (see VERIFY-REPORT.md):
--   * Aeneas models every function in the `Result` monad
--       inductive Result α | ok (v : α) | fail (e : Error) | div
--     A *panic* (arith overflow, out-of-bounds index, unwrap on None, explicit
--     panic!, ...) is exactly `fail`. `div` is nontermination — here it is
--     reached only by the shared `bLength == 0` descriptor walk that loops
--     forever (documented; identical in the C).
--   * There is NO fourth outcome: the translation has no "stuck"/undefined-
--     behaviour state. That is the memory-safety guarantee by construction —
--     out-of-bounds is `fail`, never a wild access; overflow is `fail` or an
--     explicit `wrapping_*`, never UB.
--
-- The property here is NOT "never panics": panicking on malformed input is the
-- intended safe behaviour (it replaces the C's out-of-bounds write). We prove:
--   (A) no-panic on WELL-FORMED input  — the safety checks don't break
--       legitimate parsing;
--   (B) total safety on ALL input      — every outcome is ok / controlled fail
--       / div, never UB.

import UvcParse

open Aeneas Aeneas.Std Result
open uvc_verify

set_option Aeneas.Deprecated.progressWarning false

namespace NoPanic

/-! ## Loop-free total helpers — unconditional no-panic.

    These mirror the kernel's pure table lookups. Each is a finite chain of
    total operations (widening casts, `slice::get` returning `Option`, `min`/
    `max`), no fallible index or arithmetic, so no-panic holds for ALL inputs
    with no side condition. This is the UVC analogue of the Binder spike's
    `size_check_no_panic`. -/

theorem uvc_colorspace_no_panic (primaries : Std.U8) :
    ∃ r, uvc_colorspace primaries = ok r := by
  unfold uvc_colorspace
  simp only [lift, bind_tc_ok, core.slice.Slice.get,
    core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get]
  split <;> exact ⟨_, rfl⟩

theorem uvc_xfer_func_no_panic (tc : Std.U8) :
    ∃ r, uvc_xfer_func tc = ok r := by
  unfold uvc_xfer_func
  simp only [lift, bind_tc_ok, core.slice.Slice.get,
    core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get]
  split <;> exact ⟨_, rfl⟩

theorem uvc_ycbcr_enc_no_panic (mc : Std.U8) :
    ∃ r, uvc_ycbcr_enc mc = ok r := by
  unfold uvc_ycbcr_enc
  simp only [lift, bind_tc_ok, core.slice.Slice.get,
    core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get]
  split <;> exact ⟨_, rfl⟩

theorem clamp_u32_no_panic (val lo hi : Std.U32) :
    ∃ r, clamp_u32 val lo hi = ok r := by
  simp only [clamp_u32, lift, bind_tc_ok]
  exact ⟨_, rfl⟩

/-! ## (B) Total safety on ALL input.

    For ANY byte buffer, quirks, and output record, `parse` evaluates to exactly
    one of `ok` / `fail` / `div` — there is no fourth "stuck" / undefined-
    behaviour outcome. This is the whole memory-safety claim, and in the Aeneas
    model it holds *by construction*: every array/slice access is a checked
    `index`/`get` that yields `fail` (never a wild read/write) on out-of-range,
    and every arithmetic operation is either checked (→ `fail` on overflow) or an
    explicit `wrapping_*`/shift (total) — including the CVE-relevant
    `bpp*wWidth*wHeight/8` recompute, which is `wrapping_mul` + unsigned `>>3`
    and so contributes no `fail`.

    Reading of the three cases:
      * `ok v`   — parsed (v = (#formats, populated result)); the safety checks
                   did not fire.
      * `fail e` — a controlled bounds-check / overflow panic. This is the
                   INTENDED safe replacement for the C's out-of-bounds write:
                   Rust refuses, it does not corrupt memory.
      * `div`    — nontermination, reached only by the shared `bLength == 0`
                   descriptor walk (identical in the C; documented in
                   fuzz/RESULTS.md).

    The proof is a case split on the `Result`: the point is not its difficulty
    but that the enumeration is exhaustive — the type has no UB constructor. -/

theorem parse_total_safety
    (buf : Slice Std.U8) (quirks : Std.U32) (out : UvcParseResult) :
    (∃ v, parse buf quirks out = ok v)
    ∨ (∃ e, parse buf quirks out = fail e)
    ∨ parse buf quirks out = div := by
  cases h : parse buf quirks out with
  | ok v => exact Or.inl ⟨v, rfl⟩
  | fail e => exact Or.inr (Or.inl ⟨e, rfl⟩)
  | div => exact Or.inr (Or.inr rfl)

/-! ## (A) No-panic on WELL-FORMED input. [MAIN THEOREM — stated, not proved]

    For any descriptor buffer satisfying the parser's own validation invariants,
    `parse` returns `ok` (neither `fail` nor `div`): the safety checks never
    break legitimate parsing.

    `WellFormed buf` must capture, as explicit preconditions:
      (i)   TERMINATION — every descriptor the walk consumes has `bLength ≥ 1`,
            so `buflen` strictly decreases and the four `loop`s terminate
            (rules out `div`); and the counting pass and the driving loop walk
            the buffer identically.
      (ii)  IN-BOUNDS READS — the walk maintains `pos + buflen = buf.length`, and
            each length guard (`buflen > 2`, `buflen ≥ n`, `buflen ≥ 26 + 4·n`)
            implies every `buf[pos + k]` read is `< buf.length` (rules out the
            index `fail`s).
      (iii) SIZED WRITES — the counting pass computes `nframes`/`nintervals` such
            that every `frames[frame_base + i]` / `intervals[iv_base + i]` write
            is within the allocated `Vec` length. This is exactly the invariant
            whose violation is CVE-2024-53104; proving it requires relating the
            counting loop's totals to the driving loop's write indices.
      (iv)  NO OVERFLOW — the checked arithmetic (`+`, `-`, `*` outside the one
            wrapping site) does not overflow on well-formed sizes.

    OBSTRUCTION (why `sorry`): discharging (A) needs loop invariants for all four
    `loop` combinators plus a termination measure, and in particular a proof of
    (iii) that mirrors the counting-vs-parsing argument. That is a multi-loop
    functional-correctness proof, beyond the per-theorem budget of this spike;
    it is the substantial remaining verification work. `WellFormed` is left
    `opaque` here so the theorem states the intended contract without prejudging
    its exact formalization. See VERIFY-REPORT.md. -/

opaque WellFormed : Slice Std.U8 → Prop

theorem parse_no_panic_wellformed
    (buf : Slice Std.U8) (quirks : Std.U32) (out : UvcParseResult)
    (hwf : WellFormed buf) :
    ∃ r, parse buf quirks out = ok r := by
  sorry

end NoPanic

/-! ## Axiom audit.

    The four helper no-panic theorems and the total-safety theorem are
    `sorry`-free (they depend only on the standard Lean/Aeneas axioms). The main
    theorem (A) is `sorryAx`, as noted above. -/
#print axioms NoPanic.uvc_colorspace_no_panic
#print axioms NoPanic.uvc_xfer_func_no_panic
#print axioms NoPanic.uvc_ycbcr_enc_no_panic
#print axioms NoPanic.clamp_u32_no_panic
#print axioms NoPanic.parse_total_safety
#print axioms NoPanic.parse_no_panic_wellformed
