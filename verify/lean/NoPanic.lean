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

/-- Concrete precondition on the INPUT bytes only. `WellFormed buf` says `buf`
    decomposes (witness `descs`) into a chain of class-specific descriptor
    blocks that tile the buffer exactly, each self-describing its length, with
    the buffer bounded. It mentions ONLY `buf` and constants — never `parse`,
    its result, `frame_base`, or any runtime value. The four conjuncts (i)-(iv)
    from VERIFY-REPORT are marked below. -/
def WellFormed (buf : Slice Std.U8) : Prop :=
  ∃ descs : List (List Std.U8),
    -- (ii) IN-BOUNDS: the descriptor blocks tile `buf` exactly, in order. With
    --      each block's declared bLength equal to its real length (below),
    --      walking by bLength from pos = 0 stays within `buf.length` and lands
    --      exactly at the end — so every guarded read `buf[pos+k]` is in range.
    --      Rules out the index `fail`s behind the guards (buflen > 2, ≥ n,
    --      ≥ 26 + 4·n).
    descs.flatten = buf.val ∧
    (∀ d ∈ descs,
      -- (i) TERMINATION: each block's bLength byte (byte 0) is ≥ 1, so the
      --     walk's `buflen` strictly decreases every step and all four `loop`s
      --     terminate. Rules out `div`.
      1 ≤ (d.getD 0 (0#u8)).val ∧
      -- (ii) cont.: the declared bLength equals the block's real length, so the
      --      tiling above is walked precisely by the bLength steps the parser
      --      takes; and the 3-byte header (bLength, bDescriptorType,
      --      bDescriptorSubtype) is present.
      (d.getD 0 (0#u8)).val = d.length ∧
      3 ≤ d.length) ∧
    -- (iv) NO OVERFLOW: bound the buffer so the checked arithmetic in `parse`
    --      cannot overflow. The frame size fields wWidth/wHeight (read as u16)
    --      and bpp (u8) are inherently bounded by their read widths, and the
    --      CVE-relevant `bpp*wWidth*wHeight/8` recompute is `wrapping_mul` +
    --      unsigned `>>3` (total — no `fail`), so those fields need no explicit
    --      clause. The residual checked arithmetic is `total = buf.len() as i32`
    --      and the u32 descriptor-count accumulators (`nformats`/`nframes`/
    --      `nintervals`, each += ≤ 255 per ≥3-byte descriptor, so ≤ 85·length).
    --      buf.length ≤ 2^24 keeps `total` within i32 and every accumulator
    --      within u32.
    buf.length ≤ 16777216
    -- (iii) SIZED WRITES [documented, not a separate clause; see report]. Both
    -- the counting pass and the parse pass walk THIS SAME tiling over THIS SAME
    -- buffer; the parse pass writes a frame/interval only for a descriptor whose
    -- subtype matches the current format's `ftype`, i.e. for a SUBSET of the
    -- frame-subtype descriptors the counting pass tallies. Hence
    -- (parse writes) ≤ (counting tally) structurally, so every write lands
    -- within the counting-sized `Vec`. This is a consequence of (ii) plus the
    -- fixed subtype dispatch — not an independent input condition — so it is
    -- documented here rather than added as a clause. Stating it as "writes stay
    -- in bounds" would be assuming theorem (A)'s conclusion, which the report
    -- explicitly warns against; it is deliberately NOT done.

-- ────────────────────────────────────────────────────────────────────────
-- Lemma scaffolding for (A). Statements only; every body is `sorry`. Phrased
-- against the extracted functions (`parse`, `parse_loop0`, `parse_loop1`,
-- `ParseState.uvc_parse_format`, `ParseState.uvc_parse_frame`) and the internal
-- ParseState cursors — NOT the CAP-truncated output fields. See
-- COUNTING_LEMMA_NOTES.md.
-- ────────────────────────────────────────────────────────────────────────

/-- (1) Div-freeness (termination). Under `WellFormed` — specifically conjunct
    (i): every consumed descriptor has bLength ≥ 1 — each loop's `buflen`
    measure (and the interval loop's `Range` measure) strictly decreases per
    iteration, so no loop diverges and `parse` never returns `div`. Loops
    involved: `parse_loop0` (counting), `parse_loop1` (driving),
    `ParseState.uvc_parse_format_loop0` (frame loop),
    `ParseState.uvc_parse_frame_loop` (interval copy). Rules out `div` for (A). -/
lemma parse_no_div
    (buf : Slice Std.U8) (quirks : Std.U32) (out : UvcParseResult)
    (hwf : WellFormed buf) :
    parse buf quirks out ≠ div := by
  sorry

/-- Internal-cursor in-bounds predicate: the frames committed so far
    (`frame_base`) and intervals written so far (`interval_cursor`) are within
    their allocated `Vec` lengths. Stated on ParseState's internal cursors, NOT
    on the CAP-truncated `out.nframes`/`out.nintervals`. Necessary but, on its
    own, NOT sufficient for (2) — it does not bound the current format's demand;
    that is why (2)'s precondition is phrased against `parse_loop0`. -/
def CursorsInBounds (st : ParseState) (frame_base : Std.Usize) : Prop :=
  frame_base.val ≤ st.frames.length ∧ st.interval_cursor.val ≤ st.intervals.length

-- ── Aleph's decomposition of counting_additive (statements only, `sorry`). ──

-- ── Helpers for counting_monotone (Aleph's plan). ──

/-- (Aleph plan, step 1) A successful checked U32 addition is ≥ its left
    operand: no overflow (the add returned `ok`) means the result's value is the
    exact Nat sum, hence ≥ the left summand. -/
theorem u32_add_ge_left (x y z : Std.U32) (h : x + y = ok z) : x.val ≤ z.val := by
  have he := UScalar.add_equiv x y
  simp only [h] at he
  obtain ⟨-, hz, -⟩ := he
  omega

/-- Replay a checked U32 add from a shifted base. If `0 + k = ok z0` (the
    from-zero step) and the shifted sum fits, then `base + k` succeeds with value
    `base.val + z0.val`. This is the per-counter ingredient of the one-step
    replay: `k` is the literal `1` (format/frame/DV arms) or the interval count
    `i7`, identical in the from-zero and shifted bodies. -/
theorem u32_add_replay (base k z0 : Std.U32)
    (h0 : (0#u32) + k = ok z0) (hb : base.val + z0.val ≤ Std.U32.max) :
    ∃ w, base + k = ok w ∧ w.val = base.val + z0.val := by
  have e0 := UScalar.add_equiv (0#u32) k
  simp only [h0] at e0
  obtain ⟨-, hz0, -⟩ := e0
  have hk : z0.val = k.val := by simpa using hz0
  have hba := UScalar.add_equiv base k
  cases hbk : base + k with
  | ok w =>
    simp only [hbk] at hba
    obtain ⟨-, hw, -⟩ := hba
    exact ⟨w, rfl, by omega⟩
  | fail e =>
    exfalso
    simp only [hbk] at hba
    scalar_tac
  | div => simp only [hbk] at hba; exact hba.elim

/-- Shift a checked U32 add by a constant. If `base + k = ok F` and `Sh` is
    `base` shifted up by `sh` (`Sh.val = sh.val + base.val`), then `Sh + k`
    succeeds with value `sh.val + F.val`, provided that sum fits in `U32`. This
    is the ARBITRARY-BASE generalization of `u32_add_replay` (which is the
    `base = 0` case). It is what lets the one-step replay be stated (and lifted)
    at nonzero accumulators — after the loop's first iteration the counters are
    no longer zero, so the from-zero `u32_add_replay` alone cannot carry the
    replay through the whole loop. -/
theorem u32_add_shift (base sh k F Sh : Std.U32)
    (hF : base + k = ok F) (hSh : Sh.val = sh.val + base.val)
    (hbnd : sh.val + F.val ≤ Std.U32.max) :
    ∃ w, Sh + k = ok w ∧ w.val = sh.val + F.val := by
  have eF := UScalar.add_equiv base k
  simp only [hF] at eF
  obtain ⟨-, hFv, -⟩ := eF
  have eS := UScalar.add_equiv Sh k
  cases hSc : Sh + k with
  | ok w =>
    simp only [hSc] at eS
    obtain ⟨-, hwv, -⟩ := eS
    exact ⟨w, rfl, by omega⟩
  | fail e => exfalso; simp only [hSc] at eS; scalar_tac
  | div => simp only [hSc] at eS; exact eS.elim

/-- Peel one monadic bind out of an `= ok` hypothesis. -/
theorem res_bind_eq_ok {γ δ : Type} {x : Result γ} {f : γ → Result δ} {v : δ}
    (h : (x >>= f) = ok v) : ∃ w, x = ok w ∧ f w = ok v := by
  cases x with
  | ok w => exact ⟨w, rfl, by simpa using h⟩
  | fail e => simp at h
  | div => simp at h

/-- Partial-correctness loop invariant for Aeneas' `loop` combinator. If `inv`
    holds on entry, is preserved by every `cont` step, and implies `post` on
    every `done`, then any SUCCESSFUL run (`loop body x = ok y`) satisfies
    `post y`. No termination measure is required (the `fail`/`div` outcomes are
    simply not constrained) — this is what `counting_monotone` needs.
    Proved via Lean's `loop.fixpoint_induct`; the motive
    `fun lp => ∀ x, inv x → ∀ y, lp x = ok y → post y` is admissible because it
    holds at `div` vacuously (same mechanism as Aeneas' `dspec_admissible`). -/
theorem loop_ok_inv {α β : Type} (body : α → Result (ControlFlow α β))
    (inv : α → Prop) (post : β → Prop)
    (hcont : ∀ x x', inv x → body x = ok (ControlFlow.cont x') → inv x')
    (hdone : ∀ x z, inv x → body x = ok (ControlFlow.done z) → post z)
    (x0 : α) (y0 : β) (hinv0 : inv x0) (hrun : loop body x0 = ok y0) : post y0 := by
  have key : ∀ x, inv x → ∀ y, loop body x = ok y → post y := by
    apply loop.fixpoint_induct body
      (motive := fun lp => ∀ x, inv x → ∀ y, lp x = ok y → post y)
    · -- admissibility: vacuous at `div`
      apply Lean.Order.admissible_pi; intro x
      apply Lean.Order.admissible_apply
        (fun _ (r : Result β) => inv x → ∀ y, r = ok y → post y)
      apply Lean.Order.admissible_flatOrder
      simp
    · -- one-unfold step
      intro lp ih x hinv y hlp
      cases r_eq : body x with
      | ok r =>
        cases r with
        | cont x' =>
          simp only [r_eq] at hlp
          exact ih x' (hcont x x' hinv r_eq) y hlp
        | done z =>
          simp only [r_eq] at hlp
          injection hlp with hzy
          subst hzy
          exact hdone x z hinv r_eq
      | fail e => simp only [r_eq] at hlp; simp at hlp
      | div => simp only [r_eq] at hlp; simp at hlp
  exact key x0 hinv0 y0 hrun

/-- One `loop` unfolding on a `cont` step: the run from `x` equals the run from
    the continuation state `x'`. -/
theorem loop_step_cont {α β : Type} (body : α → Result (ControlFlow α β))
    (x x' : α) (h : body x = ok (ControlFlow.cont x')) :
    loop body x = loop body x' := by rw [loop.eq_def, h]

/-- One `loop` unfolding on a `done` step: the run from `x` returns `y`. -/
theorem loop_step_done {α β : Type} (body : α → Result (ControlFlow α β))
    (x : α) (y : β) (h : body x = ok (ControlFlow.done y)) :
    loop body x = ok y := by rw [loop.eq_def, h]

/-- Div-freeness (termination) principle for Aeneas' `loop` — the counterpart of
    `loop_ok_inv`, but for ruling out `div` instead of establishing a
    postcondition. If every reachable body step is itself div-free (`hbody`) and,
    on a `cont` step, strictly decreases a `Nat` measure while preserving the
    invariant (`hstep`), then the whole loop never returns `div`.

    Unlike `loop_ok_inv`, this is NOT a `fixpoint_induct` argument: the predicate
    `· ≠ div` is FALSE at the `div` bottom, so it is not admissible and partial
    correctness cannot deliver it. Termination must be supplied by the measure —
    here via well-founded (strong) induction on `measure x : Nat`. `fail` is left
    unconstrained: this rules out `div` only, exactly the div-freeness half of a
    no-panic proof (the `fail` half is separate). -/
theorem loop_no_div {α β : Type} (body : α → Result (ControlFlow α β))
    (measure : α → Nat) (inv : α → Prop)
    (hbody : ∀ x, inv x → body x ≠ div)
    (hstep : ∀ x x', inv x → body x = ok (ControlFlow.cont x') →
        inv x' ∧ measure x' < measure x)
    (x : α) (hinv : inv x) : loop body x ≠ div := by
  suffices H : ∀ n x, measure x = n → inv x → loop body x ≠ div from
    H (measure x) x rfl hinv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hmx hix
    rw [loop.eq_def]
    cases hb : body x with
    | ok r =>
      cases r with
      | cont x' =>
        obtain ⟨hix', hlt⟩ := hstep x x' hix hb
        subst hmx
        simpa using ih (measure x') hlt x' rfl hix'
      | done y => simp
    | fail e => simp
    | div => exact absurd hb (hbody x hix)

-- ── Div-freeness toolkit: primitives never return `div`, and `div` propagates
--    only through `bind` from a diverging sub-term. These let a loop BODY (which
--    contains no nested `loop` for the structural loops) be shown `≠ div` by a
--    finite bind-peel. Reused across every structural-loop `hbody`. ──

theorem ok_ne_div' {α} (v : α) : (ok v : Result α) ≠ div := by simp
theorem fail_ne_div' {α} (e : Error) : (fail e : Result α) ≠ div := by simp
/-- `Result.ofOption` is always `ok`/`fail` — the shape of every checked scalar
    op (`+`,`-`,`*`,`<<<`, casts via `tryMk`/`ofOption`). -/
theorem ofOption_ne_div {α} (o : Option α) (e : Error) :
    Result.ofOption o e ≠ div := by cases o <;> simp [Result.ofOption]
/-- Checked `Usize` subtraction is `fail`/`ok` (not `ofOption`-shaped), so it
    needs its own div-freeness fact. -/
theorem usize_sub_ne_div (x y : Std.Usize) : (x - y) ≠ div := by
  show UScalar.sub x y ≠ div; unfold UScalar.sub; split <;> simp
/-- `div` in a bind comes only from a diverging head or tail. -/
theorem bind_ne_div {α β} {x : Result α} {f : α → Result β}
    (hx : x ≠ div) (hf : ∀ v, f v ≠ div) : (x >>= f) ≠ div := by
  cases x <;> simp_all
/-- Total correctness (`spec`) forbids `div` (`theta div = False`). -/
theorem spec_ne_div {α} {x : Result α} {p} (h : WP.spec x p) : x ≠ div := by
  intro hd; rw [hd] at h; exact h
theorem array_index_ne_div {α n} (a : Array α n) (j : Std.Usize) :
    Array.index_usize a j ≠ div := by unfold Array.index_usize; split <;> simp
theorem slice_index_ne_div {α} (b : Slice α) (j : Std.Usize) :
    Slice.index_usize b j ≠ div := by unfold Slice.index_usize; split <;> simp
theorem array_update_ne_div {α n} (a : Array α n) (i : Std.Usize) (x : α) :
    Array.update a i x ≠ div := by unfold Array.update; split <;> simp
theorem vec_index_ne_div {T} (v : alloc.vec.Vec T) (i : Std.Usize) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) v i ≠ div := by
  unfold alloc.vec.Vec.index; simp only []; exact slice_index_ne_div _ _
theorem slice_index_mut_ne_div {α} (v : Slice α) (i : Std.Usize) :
    Slice.index_mut_usize v i ≠ div := by
  unfold Slice.index_mut_usize
  exact bind_ne_div (slice_index_ne_div _ _) (fun _ => ok_ne_div' _)
theorem vec_index_mut_ne_div {T} (v : alloc.vec.Vec T) (i : Std.Usize) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice T) v i ≠ div := by
  unfold alloc.vec.Vec.index_mut; simp only []
  unfold core.slice.index.Usize.index_mut
  exact slice_index_mut_ne_div _ _
/-- The Range iterator's `next` never diverges (its total spec forbids it). -/
theorem iter_next_ne_div (it : core.ops.range.Range Std.Usize) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize it ≠ div :=
  spec_ne_div (core.iter.range.IteratorRange.next_UScalar_spec
    (ty := .Usize) (cloneInst := core.clone.CloneUsize)
    (partialOrdInst := core.cmp.PartialOrdUsize) (fun _ => rfl) (fun _ _ => rfl) it)

/-- Head-of-bind div-freeness discharger: tries each primitive fact. `exact` uses
    full transparency so `ofOption_ne_div` also matches scalar ops/casts/shifts. -/
macro "hd_ne_div" : tactic => `(tactic| first
  | exact ok_ne_div' _ | exact fail_ne_div' _
  | exact array_index_ne_div _ _ | exact slice_index_ne_div _ _
  | exact array_update_ne_div _ _ _ | exact vec_index_ne_div _ _
  | exact vec_index_mut_ne_div _ _ | exact iter_next_ne_div _
  | exact ofOption_ne_div _ _)

/-- `le32` (4 little-endian byte reads + shifts/ors) never diverges. -/
theorem le32_ne_div (buf : Slice Std.U8) (at1 : Std.Usize) : le32 buf at1 ≠ div := by
  unfold le32
  repeat' refine bind_ne_div (by hd_ne_div) (fun _ => ?_)
  hd_ne_div

/-- Range `next` on a `cont` step: `some` forces `start < end` and advances
    `start` by one, leaving `end` fixed — the strict decrease of `end - start`. -/
theorem range_next_some (iter iterN : core.ops.range.Range Std.Usize)
    (o : Option Std.Usize) (i : Std.Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
        = ok (o, iterN))
    (ho : o = some i) :
    iter.start.val < iter.end.val ∧ iterN.start.val = iter.start.val + 1
      ∧ iterN.end = iter.end := by
  have hspec := core.iter.range.IteratorRange.next_UScalar_spec
    (ty := .Usize) (cloneInst := core.clone.CloneUsize)
    (partialOrdInst := core.cmp.PartialOrdUsize) (fun _ => rfl) (fun _ _ => rfl) iter
  rw [hnext, WP.spec_ok] at hspec
  simp only [WP.uncurry'] at hspec
  obtain ⟨hif, hend⟩ := hspec
  by_cases hlt : iter.start.val < iter.end.val
  · simp only [hlt, if_true] at hif; exact ⟨hlt, hif.2, hend⟩
  · simp only [hlt, if_false] at hif; rw [ho] at hif; exact absurd hif.1 (by simp)

-- ── Structural-loop div-freeness (measure = remaining Range/index count). Each
--    consumed by `parse_no_div` for the loops that terminate independently of the
--    descriptor walk. The buffer-walk loops (`parse_loop0`, `parse_loop1`,
--    `uvc_parse_format_loop0..3`) are handled separately via the walk invariant. ──

/-- GUID 16-byte compare loop: terminates on `16 - j`. -/
theorem guid_eq16_loop_no_div (a : Array Std.U8 16#usize) (b : Slice Std.U8)
    (j : Std.Usize) (m : Bool) : guid_eq16_loop a b j m ≠ div := by
  unfold guid_eq16_loop
  apply loop_no_div _ (fun st => 16 - st.1.val) (fun _ => True) ?_ ?_ _ trivial
  · rintro ⟨j, m⟩ _
    simp only [guid_eq16_loop.body]
    split
    · refine bind_ne_div (by hd_ne_div) (fun _ => ?_)
      refine bind_ne_div (by hd_ne_div) (fun _ => ?_)
      refine bind_ne_div (by split <;> hd_ne_div) (fun _ => ?_)
      refine bind_ne_div (by hd_ne_div) (fun _ => ?_)
      hd_ne_div
    · hd_ne_div
  · rintro ⟨j, m⟩ ⟨j', m'⟩ _ hstep
    simp only [guid_eq16_loop.body] at hstep
    by_cases hj : j < 16#usize
    · rw [if_pos hj] at hstep
      obtain ⟨_, _, hstep⟩ := res_bind_eq_ok hstep
      obtain ⟨_, _, hstep⟩ := res_bind_eq_ok hstep
      obtain ⟨_, _, hstep⟩ := res_bind_eq_ok hstep
      obtain ⟨j1, hj1, hstep⟩ := res_bind_eq_ok hstep
      simp only [ok.injEq, ControlFlow.cont.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      refine ⟨trivial, ?_⟩
      have hv : j1.val = j.val + 1 := by
        have e := UScalar.add_equiv j 1#usize; rw [hj1] at e
        obtain ⟨-, hv, -⟩ := e; scalar_tac
      have hjv : j.val < 16 := by scalar_tac
      show 16 - j1.val < 16 - j.val
      omega
    · rw [if_neg hj] at hstep; simp at hstep

/-- `parse` serialization loop 3 (copy frames into the output array): terminates
    on the `Range` measure `end - start`. -/
theorem parse_loop3_no_div (v : alloc.vec.Vec UvcFrame)
    (iter : core.ops.range.Range Std.Usize) (a : Array UvcFrameOut 256#usize) :
    parse_loop3 iter a v ≠ div := by
  unfold parse_loop3
  apply loop_no_div _ (fun st => st.1.end.val - st.1.start.val) (fun _ => True) ?_ ?_ _ trivial
  · rintro ⟨it, ar⟩ _
    simp only [parse_loop3.body]
    refine bind_ne_div (by hd_ne_div) (fun p => ?_)
    obtain ⟨o, iter1⟩ := p
    cases o with
    | none => hd_ne_div
    | some i =>
      refine bind_ne_div (by hd_ne_div) (fun _ => ?_)
      refine bind_ne_div (by hd_ne_div) (fun _ => ?_); hd_ne_div
  · rintro ⟨it, ar⟩ ⟨it', ar'⟩ _ hstep
    simp only [parse_loop3.body] at hstep
    obtain ⟨⟨o, itN⟩, hnext, hstep⟩ := res_bind_eq_ok hstep
    match ho : o with
    | none => exact absurd hstep (by simp)
    | some i =>
      obtain ⟨hlt, hs, he⟩ := range_next_some it itN _ i hnext rfl
      obtain ⟨_, _, hstep⟩ := res_bind_eq_ok hstep
      obtain ⟨_, _, hstep⟩ := res_bind_eq_ok hstep
      simp only [ok.injEq, ControlFlow.cont.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      refine ⟨trivial, ?_⟩
      have he' : itN.end.val = it.end.val := by rw [he]
      show itN.end.val - itN.start.val < it.end.val - it.start.val
      scalar_tac

/-- Frame interval-copy loop: terminates on the `Range` measure `end - start`
    (independent of the buffer walk). -/
theorem uvc_parse_frame_loop_no_div (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec Std.U32) (iv_base : Std.Usize) (buf : Slice Std.U8)
    (pos : Std.Usize) : ParseState.uvc_parse_frame_loop iter v iv_base buf pos ≠ div := by
  unfold ParseState.uvc_parse_frame_loop
  apply loop_no_div _ (fun st => st.1.end.val - st.1.start.val) (fun _ => True) ?_ ?_ _ trivial
  · rintro ⟨it, vv⟩ _
    simp only [ParseState.uvc_parse_frame_loop.body]
    refine bind_ne_div (by hd_ne_div) (fun p => ?_)
    obtain ⟨o, iter1⟩ := p
    cases o with
    | none => hd_ne_div
    | some i =>
      refine bind_ne_div (by hd_ne_div) (fun _ => ?_)
      refine bind_ne_div (by hd_ne_div) (fun _ => ?_)
      refine bind_ne_div (by hd_ne_div) (fun _ => ?_)
      refine bind_ne_div (by exact le32_ne_div _ _) (fun _ => ?_)
      refine bind_ne_div (by split <;> hd_ne_div) (fun _ => ?_)
      refine bind_ne_div (by hd_ne_div) (fun _ => ?_)
      refine bind_ne_div (by hd_ne_div) (fun _ => ?_)
      hd_ne_div
  · rintro ⟨it, vv⟩ ⟨it', vv'⟩ _ hstep
    simp only [ParseState.uvc_parse_frame_loop.body] at hstep
    obtain ⟨⟨o, itN⟩, hnext, hstep⟩ := res_bind_eq_ok hstep
    match ho : o with
    | none => exact absurd hstep (by simp)
    | some i =>
      obtain ⟨hlt, hs, he⟩ := range_next_some it itN _ i hnext rfl
      obtain ⟨_, _, hstep⟩ := res_bind_eq_ok hstep   -- pos + 26
      obtain ⟨_, _, hstep⟩ := res_bind_eq_ok hstep   -- 4 * i
      obtain ⟨_, _, hstep⟩ := res_bind_eq_ok hstep   -- i1 + i2
      obtain ⟨_, _, hstep⟩ := res_bind_eq_ok hstep   -- le32
      obtain ⟨_, _, hstep⟩ := res_bind_eq_ok hstep   -- interval1 (ite)
      obtain ⟨_, _, hstep⟩ := res_bind_eq_ok hstep   -- iv_base + i
      obtain ⟨⟨_, _⟩, _, hstep⟩ := res_bind_eq_ok hstep   -- Vec.index_mut (pair)
      simp at hstep   -- reduce the index_mut pattern-let and inject cont/pair
      obtain ⟨rfl, _⟩ := hstep
      refine ⟨trivial, ?_⟩
      have he' : itN.end.val = it.end.val := by rw [he]
      show itN.end.val - itN.start.val < it.end.val - it.start.val
      scalar_tac

/-- The 41-entry `UVC_FMTS` format table is a constant `fourcc`-chain — no loop,
    hence never `div`. Needed for `uvc_format_by_guid`'s body. -/
theorem fourcc_ne_div (a b c d : Std.U8) : fourcc a b c d ≠ div := by
  unfold fourcc
  repeat' refine bind_ne_div (by hd_ne_div) (fun _ => ?_)
  hd_ne_div
theorem UVC_FMTS_ne_div : UVC_FMTS ≠ div := by
  unfold UVC_FMTS
  simp only [V4L2_PIX_FMT_BGR24,V4L2_PIX_FMT_CNF4,V4L2_PIX_FMT_GREY,V4L2_PIX_FMT_H264,V4L2_PIX_FMT_HEVC,V4L2_PIX_FMT_INZI,V4L2_PIX_FMT_M420,V4L2_PIX_FMT_MJPEG,V4L2_PIX_FMT_NV12,V4L2_PIX_FMT_P010,V4L2_PIX_FMT_RGB565,V4L2_PIX_FMT_SBGGR16,V4L2_PIX_FMT_SBGGR8,V4L2_PIX_FMT_SGBRG16,V4L2_PIX_FMT_SGBRG8,V4L2_PIX_FMT_SGRBG16,V4L2_PIX_FMT_SGRBG8,V4L2_PIX_FMT_SRGGB10P,V4L2_PIX_FMT_SRGGB16,V4L2_PIX_FMT_SRGGB8,V4L2_PIX_FMT_UYVY,V4L2_PIX_FMT_XBGR32,V4L2_PIX_FMT_Y10,V4L2_PIX_FMT_Y12,V4L2_PIX_FMT_Y12I,V4L2_PIX_FMT_Y16,V4L2_PIX_FMT_Y16I,V4L2_PIX_FMT_Y8I,V4L2_PIX_FMT_YUV420,V4L2_PIX_FMT_YUYV,V4L2_PIX_FMT_YVU420,V4L2_PIX_FMT_Z16]
  repeat' refine bind_ne_div (by first | exact fourcc_ne_div _ _ _ _ | hd_ne_div) (fun _ => ?_)
  hd_ne_div

/-- GUID→format table scan: terminates on `41 - i` (the 41-entry `UVC_FMTS`).
    Its body calls `guid_eq16` (itself a loop), so it consumes
    `guid_eq16_loop_no_div`. -/
theorem uvc_format_by_guid_loop_no_div (guid : Slice Std.U8) (i : Std.Usize) :
    uvc_format_by_guid_loop guid i ≠ div := by
  unfold uvc_format_by_guid_loop
  apply loop_no_div _ (fun i => 41 - i.val) (fun _ => True) ?_ ?_ _ trivial
  · intro i _
    simp only [uvc_format_by_guid_loop.body]
    refine bind_ne_div (by exact UVC_FMTS_ne_div) (fun a => ?_)
    refine bind_ne_div (by hd_ne_div) (fun s => ?_)
    split
    · refine bind_ne_div (by hd_ne_div) (fun _ => ?_)
      refine bind_ne_div (by exact guid_eq16_loop_no_div _ _ _ _) (fun b => ?_)
      split
      · hd_ne_div
      · refine bind_ne_div (by hd_ne_div) (fun _ => ?_); hd_ne_div
    · hd_ne_div
  · intro i i' _ hstep
    simp only [uvc_format_by_guid_loop.body] at hstep
    obtain ⟨a, ha, hstep⟩ := res_bind_eq_ok hstep
    obtain ⟨s, hs, hstep⟩ := res_bind_eq_ok hstep
    by_cases hi : i < Slice.len s
    · rw [if_pos hi] at hstep
      obtain ⟨_, _, hstep⟩ := res_bind_eq_ok hstep
      obtain ⟨b, _, hstep⟩ := res_bind_eq_ok hstep
      by_cases hbv : b
      · rw [if_pos hbv] at hstep; simp only [ok.injEq, reduceCtorEq] at hstep
      · rw [if_neg hbv] at hstep
        obtain ⟨i2, hi2, hstep⟩ := res_bind_eq_ok hstep
        simp only [ok.injEq, ControlFlow.cont.injEq] at hstep
        subst hstep
        refine ⟨trivial, ?_⟩
        have hseq : s = Array.to_slice a := by
          simp only [lift, ok.injEq] at hs; exact hs.symm
        have hlen : (Slice.len s).val = 41 := by
          rw [hseq]; simp [Array.to_slice, Slice.len]
        have hiv : i.val < 41 := by scalar_tac
        have hv : i2.val = i.val + 1 := by
          have e := UScalar.add_equiv i 1#usize; rw [hi2] at e
          obtain ⟨-, hv, -⟩ := e; scalar_tac
        show 41 - i2.val < 41 - i.val
        omega
    · rw [if_neg hi] at hstep; simp only [ok.injEq, reduceCtorEq] at hstep

-- ── Iterator specs for `parse_loop2` (Enumerate(Take(SliceIter))). Aeneas ships
--    a `Take`/`next` decrease spec only for `ChunksExact`; these supply the
--    `SliceIter`/`Take`/`Enumerate` facts for the `SliceIter` stack. The measure
--    is the `Take`'s remaining count `n`, which `Take.next` decrements by one on
--    every non-empty step — so `SliceIter`'s element behaviour is not needed for
--    termination, only that the `next`s are div-free. ──

/-- `SliceIter.next` is total (a `dite` of `ok`s): never `div`. -/
theorem sliceiter_next_ne_div {T} (it : core.slice.iter.Iter T) :
    core.slice.iter.IteratorSliceIter.next it ≠ div := by
  unfold core.slice.iter.IteratorSliceIter.next; split <;> exact ok_ne_div' _

/-- `Take.next` is div-free when its inner iterator's `next` is. -/
theorem take_next_ne_div {I Item} (inst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.take.Take I) (h_inner : ∀ it, inst.next it ≠ div) :
    core.iter.adapters.take.IteratorTake.next inst self ≠ div := by
  unfold core.iter.adapters.take.IteratorTake.next
  split
  · exact ok_ne_div' _
  · refine bind_ne_div (by exact usize_sub_ne_div _ _) (fun _ => ?_)
    refine bind_ne_div (h_inner _) (fun _ => ?_); exact ok_ne_div' _

/-- On a `some` step, `Take.next` requires `n > 0` and returns a `Take` with
    `n' = n - 1`: the strict decrease of the `Take` measure. -/
theorem take_next_some_n {I Item} (inst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.take.Take I) (a : Item) (iter' : core.iter.adapters.take.Take I)
    (h : core.iter.adapters.take.IteratorTake.next inst self = ok (some a, iter')) :
    0 < self.n.val ∧ iter'.n.val = self.n.val - 1 := by
  unfold core.iter.adapters.take.IteratorTake.next at h
  by_cases hn : self.n.val = 0
  · rw [if_pos hn] at h; simp at h
  · rw [if_neg hn] at h
    obtain ⟨n', hn', h⟩ := res_bind_eq_ok h
    obtain ⟨⟨opt, it2⟩, hinner, h⟩ := res_bind_eq_ok h
    simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
    have hv : n'.val = self.n.val - 1 := by
      have e := UScalar.sub_equiv self.n 1#usize; rw [hn'] at e; scalar_tac
    exact ⟨by omega, hv⟩

/-- On a `some` step, `Enumerate.next` delegates to its inner iterator (which also
    returned `some`) and carries the inner's new state into `self'.iter`. -/
theorem enum_next_some {I Item} (inst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.enumerate.Enumerate I) (p : Std.Usize × Item)
    (self' : core.iter.adapters.enumerate.Enumerate I)
    (h : core.iter.adapters.enumerate.IteratorEnumerate.next inst self = ok (some p, self')) :
    ∃ a it', inst.next self.iter = ok (some a, it') ∧ self'.iter = it' := by
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next at h
  obtain ⟨⟨opt, it'⟩, hinner, h⟩ := res_bind_eq_ok h
  cases opt with
  | none => simp at h
  | some a =>
    obtain ⟨_, _, h⟩ := res_bind_eq_ok h
    simp only [ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
    exact ⟨a, it', hinner, rfl⟩

/-- `Enumerate.next` is div-free when its inner iterator's `next` is. -/
theorem enum_next_ne_div {I Item} (inst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.enumerate.Enumerate I) (h_inner : ∀ it, inst.next it ≠ div) :
    core.iter.adapters.enumerate.IteratorEnumerate.next inst self ≠ div := by
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  refine bind_ne_div (h_inner _) (fun p => ?_)
  obtain ⟨opt, iter'⟩ := p
  cases opt with
  | none => exact ok_ne_div' _
  | some a => refine bind_ne_div (by exact ofOption_ne_div _ _) (fun _ => ?_); exact ok_ne_div' _

/-- `parse` serialization loop 2 (copy formats into the output array): iterates
    `Enumerate(Take(SliceIter))`; terminates on the `Take`'s remaining count. -/
theorem parse_loop2_no_div
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.iter.adapters.take.Take (core.slice.iter.Iter UvcFormat)))
    (a : Array UvcFormatOut 64#usize) : parse_loop2 iter a ≠ div := by
  unfold parse_loop2
  apply loop_no_div _ (fun st => st.1.iter.n.val) (fun _ => True) ?_ ?_ _ trivial
  · rintro ⟨it, ar⟩ _
    simp only [parse_loop2.body]
    have hnd : ∀ e, core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorTake
          (core.iter.traits.iterator.IteratorSliceIter UvcFormat)) e ≠ div :=
      fun e => enum_next_ne_div _ e
        (fun t => take_next_ne_div _ t (fun s => sliceiter_next_ne_div s))
    refine bind_ne_div (hnd _) (fun p => ?_)
    obtain ⟨o, iter1⟩ := p
    cases o with
    | none => exact ok_ne_div' _
    | some pp =>
      obtain ⟨i, f⟩ := pp
      refine bind_ne_div (by hd_ne_div) (fun _ => ?_)
      refine bind_ne_div (by hd_ne_div) (fun _ => ?_); exact ok_ne_div' _
  · rintro ⟨it, ar⟩ ⟨it', ar'⟩ _ hstep
    simp only [parse_loop2.body] at hstep
    obtain ⟨⟨o, enum2⟩, hnext, hstep⟩ := res_bind_eq_ok hstep
    match ho : o with
    | none => exact absurd hstep (by simp)
    | some p =>
      obtain ⟨aa, it2, hin, henum⟩ := enum_next_some _ it p enum2 hnext
      obtain ⟨hpos, hdec⟩ := take_next_some_n _ it.iter aa it2 hin
      obtain ⟨i, f⟩ := p
      obtain ⟨_, _, hstep⟩ := res_bind_eq_ok hstep
      obtain ⟨_, _, hstep⟩ := res_bind_eq_ok hstep
      simp only [ok.injEq, ControlFlow.cont.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      refine ⟨trivial, ?_⟩
      show enum2.iter.n.val < it.iter.n.val
      rw [henum]; omega

/-- `parse_loop0` as a bare `loop` over a projection-style body (defeq to the
    Aeneas-generated pattern-lambda). Lets the loop lemmas above refer to a
    single, syntactically stable body term. -/
theorem parse_loop0_eq (buf : Slice Std.U8) (nf nfr ni : Std.U32)
    (pos : Std.Usize) (buflen : Std.I32) :
    parse_loop0 buf nf nfr ni pos buflen
      = loop (fun (x : Std.U32 × Std.U32 × Std.U32 × Std.Usize × Std.I32) =>
          parse_loop0.body buf x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
          (nf, nfr, ni, pos, buflen) := rfl


set_option maxHeartbeats 1000000 in
/-- (Aleph decomposition, 1/3) One-step replay. A single `parse_loop0.body`
    step that succeeds from zero counters can be replayed from arbitrary shifted
    counters `(a,b,c)`, shifting the resulting counters by the same amounts,
    PROVIDED that step's own U32 additions do not overflow. Both body outcomes
    are covered: `cont` (continue — the delta counters become `a+δ`, with
    `pos'`/`buflen'` unchanged because the body never reads the accumulators for
    control flow) and `done` (loop exit — the body returns its input counters, a
    zero delta, so the exit counters shift by exactly `(a,b,c)`). -/
lemma counting_step_replay
    (buf : Slice Std.U8) (a b c : Std.U32) (pos : Std.Usize) (buflen : Std.I32) :
    (∀ df dfr di pos' buflen',
        parse_loop0.body buf 0#u32 0#u32 0#u32 pos buflen
          = ok (ControlFlow.cont (df, dfr, di, pos', buflen')) →
        a.val + df.val ≤ Std.U32.max →
        b.val + dfr.val ≤ Std.U32.max →
        c.val + di.val ≤ Std.U32.max →
        ∃ sf sfr si,
          parse_loop0.body buf a b c pos buflen
            = ok (ControlFlow.cont (sf, sfr, si, pos', buflen')) ∧
          sf.val = a.val + df.val ∧ sfr.val = b.val + dfr.val ∧ si.val = c.val + di.val)
    ∧
    (∀ df dfr di,
        parse_loop0.body buf 0#u32 0#u32 0#u32 pos buflen
          = ok (ControlFlow.done (df, dfr, di)) →
        a.val + df.val ≤ Std.U32.max →
        b.val + dfr.val ≤ Std.U32.max →
        c.val + di.val ≤ Std.U32.max →
        ∃ sf sfr si,
          parse_loop0.body buf a b c pos buflen
            = ok (ControlFlow.done (sf, sfr, si)) ∧
          sf.val = a.val + df.val ∧ sfr.val = b.val + dfr.val ∧ si.val = c.val + di.val) := by
  refine ⟨?cont, ?done⟩
  case cont =>
    intro df dfr di pos' buflen' h0 hoa hob hoc
    simp only [parse_loop0.body] at h0 ⊢
    by_cases hbl : buflen > 2#i32
    · rw [if_pos hbl] at h0; simp only [if_pos hbl] at ⊢
      obtain ⟨i, hi, h0⟩ := res_bind_eq_ok h0; simp only [hi, bind_tc_ok] at ⊢
      obtain ⟨i1, hi1, h0⟩ := res_bind_eq_ok h0; simp only [hi1, bind_tc_ok] at ⊢
      by_cases hcs : i1 = USB_DT_CS_INTERFACE
      · rw [if_pos hcs] at h0; simp only [if_pos hcs] at ⊢
        obtain ⟨i2, hi2, h0⟩ := res_bind_eq_ok h0; simp only [hi2, bind_tc_ok] at ⊢
        obtain ⟨i3, hi3, h0⟩ := res_bind_eq_ok h0; simp only [hi3, bind_tc_ok] at ⊢
        split at h0
        all_goals
          (obtain ⟨⟨mf, mfr, mi⟩, hM0, h0⟩ := res_bind_eq_ok h0
           obtain ⟨i4, hi4, h0⟩ := res_bind_eq_ok h0
           obtain ⟨i5, hi5, h0⟩ := res_bind_eq_ok h0
           obtain ⟨tbl, htbl, h0⟩ := res_bind_eq_ok h0
           obtain ⟨i6, hi6, h0⟩ := res_bind_eq_ok h0
           obtain ⟨tpos, htpos, h0⟩ := res_bind_eq_ok h0
           simp only [ok.injEq, ControlFlow.cont.injEq, Prod.mk.injEq] at h0
           obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h0)
        -- arms in match order: 4,6,16 | 12 | 10,18 | 5,7 | 17 | default
        case h_1 | h_2 | h_3 =>            -- nformats += 1
          obtain ⟨z, hz, hM0⟩ := res_bind_eq_ok hM0
          simp only [ok.injEq, Prod.mk.injEq] at hM0
          obtain ⟨rfl, rfl, rfl⟩ := hM0
          obtain ⟨w, hw, hwv⟩ := u32_add_replay a 1#u32 z hz hoa
          exact ⟨w, b, c, by simp [hw, hi4, hi5, htbl, hi6, htpos, bind_tc_ok],
                 hwv, by scalar_tac, by scalar_tac⟩
        case h_4 =>                        -- DV: all three += 1
          obtain ⟨z1, hz1, hM0⟩ := res_bind_eq_ok hM0
          obtain ⟨z2, hz2, hM0⟩ := res_bind_eq_ok hM0
          obtain ⟨z3, hz3, hM0⟩ := res_bind_eq_ok hM0
          simp only [ok.injEq, Prod.mk.injEq] at hM0
          obtain ⟨rfl, rfl, rfl⟩ := hM0
          obtain ⟨w1, hw1, hwv1⟩ := u32_add_replay a 1#u32 z1 hz1 hoa
          obtain ⟨w2, hw2, hwv2⟩ := u32_add_replay b 1#u32 z2 hz2 hob
          obtain ⟨w3, hw3, hwv3⟩ := u32_add_replay c 1#u32 z3 hz3 hoc
          exact ⟨w1, w2, w3,
                 by simp [hw1, hw2, hw3, hi4, hi5, htbl, hi6, htpos, bind_tc_ok],
                 hwv1, hwv2, hwv3⟩
        case h_5 | h_6 | h_10 =>           -- unchanged counters
          simp only [ok.injEq, Prod.mk.injEq] at hM0
          obtain ⟨rfl, rfl, rfl⟩ := hM0
          exact ⟨a, b, c, by simp [hi4, hi5, htbl, hi6, htpos, bind_tc_ok],
                 by scalar_tac, by scalar_tac, by scalar_tac⟩
        case h_7 | h_8 =>                  -- frame, interval byte at offset 25
          obtain ⟨z1, hz1, hM0⟩ := res_bind_eq_ok hM0
          obtain ⟨z4, hz4, hM0⟩ := res_bind_eq_ok hM0
          simp only [ok.injEq, Prod.mk.injEq] at hM0
          obtain ⟨rfl, rfl, rfl⟩ := hM0
          obtain ⟨w2, hw2, hwv2⟩ := u32_add_replay b 1#u32 z1 hz1 hob
          by_cases hb25 : buflen > 25#i32
          · rw [if_pos hb25] at hz4
            obtain ⟨j5, hj5, hz4⟩ := res_bind_eq_ok hz4
            obtain ⟨j6, hj6, hz4⟩ := res_bind_eq_ok hz4
            obtain ⟨j7, hj7, hz4⟩ := res_bind_eq_ok hz4
            obtain ⟨w3, hw3, hwv3⟩ := u32_add_replay c j7 z4 hz4 hoc
            refine ⟨a, w2, w3, ?_, by scalar_tac, hwv2, hwv3⟩
            simp only [hj6, bind_tc_ok] at hj7
            simp only [hw2, if_pos hb25, hj5, hj6, hj7, hw3, hi4, hi5, htbl,
              hi6, htpos, bind_tc_ok] <;> rfl
          · rw [if_neg hb25] at hz4
            simp only [ok.injEq] at hz4; subst hz4
            refine ⟨a, w2, c, ?_, by scalar_tac, hwv2, by scalar_tac⟩
            simp only [hw2, if_neg hb25, hi4, hi5, htbl, hi6, htpos, bind_tc_ok] <;> rfl
        case h_9 =>                        -- frame, interval byte at offset 21
          obtain ⟨z1, hz1, hM0⟩ := res_bind_eq_ok hM0
          obtain ⟨z4, hz4, hM0⟩ := res_bind_eq_ok hM0
          simp only [ok.injEq, Prod.mk.injEq] at hM0
          obtain ⟨rfl, rfl, rfl⟩ := hM0
          obtain ⟨w2, hw2, hwv2⟩ := u32_add_replay b 1#u32 z1 hz1 hob
          by_cases hb21 : buflen > 21#i32
          · rw [if_pos hb21] at hz4
            obtain ⟨j5, hj5, hz4⟩ := res_bind_eq_ok hz4
            obtain ⟨j6, hj6, hz4⟩ := res_bind_eq_ok hz4
            obtain ⟨j7, hj7, hz4⟩ := res_bind_eq_ok hz4
            obtain ⟨w3, hw3, hwv3⟩ := u32_add_replay c j7 z4 hz4 hoc
            refine ⟨a, w2, w3, ?_, by scalar_tac, hwv2, hwv3⟩
            simp only [hj6, bind_tc_ok] at hj7
            simp only [hw2, if_pos hb21, hj5, hj6, hj7, hw3, hi4, hi5, htbl,
              hi6, htpos, bind_tc_ok] <;> rfl
          · rw [if_neg hb21] at hz4
            simp only [ok.injEq] at hz4; subst hz4
            refine ⟨a, w2, c, ?_, by scalar_tac, hwv2, by scalar_tac⟩
            simp only [hw2, if_neg hb21, hi4, hi5, htbl, hi6, htpos, bind_tc_ok] <;> rfl
      · rw [if_neg hcs] at h0; simp at h0
    · rw [if_neg hbl] at h0; simp at h0
  case done =>
    intro df dfr di h0 hoa hob hoc
    simp only [parse_loop0.body] at h0 ⊢
    by_cases hbl : buflen > 2#i32
    · rw [if_pos hbl] at h0; simp only [if_pos hbl] at ⊢
      obtain ⟨i, hi, h0⟩ := res_bind_eq_ok h0; simp only [hi, bind_tc_ok] at ⊢
      obtain ⟨i1, hi1, h0⟩ := res_bind_eq_ok h0; simp only [hi1, bind_tc_ok] at ⊢
      by_cases hcs : i1 = USB_DT_CS_INTERFACE
      · rw [if_pos hcs] at h0
        exfalso
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        simp at h0
      · rw [if_neg hcs] at h0; simp only [if_neg hcs] at ⊢
        simp only [ok.injEq, ControlFlow.done.injEq, Prod.mk.injEq] at h0
        obtain ⟨e1, e2, e3⟩ := h0; subst e1; subst e2; subst e3
        exact ⟨a, b, c, rfl, by scalar_tac, by scalar_tac, by scalar_tac⟩
    · rw [if_neg hbl] at h0; simp only [if_neg hbl] at ⊢
      simp only [ok.injEq, ControlFlow.done.injEq, Prod.mk.injEq] at h0
      obtain ⟨e1, e2, e3⟩ := h0; subst e1; subst e2; subst e3
      exact ⟨a, b, c, rfl, by scalar_tac, by scalar_tac, by scalar_tac⟩

/-- (Aleph decomposition, 2/3) Monotonicity. A successful `parse_loop0` run
    never decreases any counter (output ≥ input). Combined with (1) this makes
    every INTERMEDIATE shifted sum ≤ the FINAL shifted sum, so the `ha`/`hb`/`hc`
    bounds on the final sum discharge every per-step overflow check in the
    replay induction. -/
lemma counting_monotone
    (buf : Slice Std.U8) (a b c : Std.U32) (pos : Std.Usize) (buflen : Std.I32)
    (sf sfr si : Std.U32)
    (h : parse_loop0 buf a b c pos buflen = ok (sf, sfr, si)) :
    a.val ≤ sf.val ∧ b.val ≤ sfr.val ∧ c.val ≤ si.val := by
  unfold parse_loop0 at h
  refine loop_ok_inv _
    (fun st => a.val ≤ st.1.val ∧ b.val ≤ st.2.1.val ∧ c.val ≤ st.2.2.1.val)
    (fun y => a.val ≤ y.1.val ∧ b.val ≤ y.2.1.val ∧ c.val ≤ y.2.2.val)
    ?hcont ?hdone _ _ ?hinv0 h
  case hinv0 => exact ⟨le_refl _, le_refl _, le_refl _⟩
  case hcont =>
    intro x x' hinv hbody
    obtain ⟨nf, nfr, ni, p, bl⟩ := x
    obtain ⟨ha, hb, hc⟩ := hinv
    simp only [parse_loop0.body] at hbody
    -- peel to the subtype-match result and the cont tail
    split at hbody
    · -- bl > 2
      obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody          -- p + 1
      obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody          -- index (pos+1)
      split at hbody
      · -- byte[1] = CS_INTERFACE : the cont path
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody        -- p + 2
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody        -- index (pos+2)
        obtain ⟨⟨nf1, nfr1, ni1⟩, hM, hbody⟩ := res_bind_eq_ok hbody  -- subtype match
        -- peel the 5 tail binds that compute pos1/buflen1 (counters untouched)
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
        -- hbody : ok (cont (nf1,nfr1,ni1,_,_)) = ok (cont x')  ⇒  x' = (nf1,nfr1,ni1,_,_)
        simp only [ok.injEq, ControlFlow.cont.injEq] at hbody
        subst hbody
        -- monotonicity of the subtype-match block: (nf,nfr,ni) ≤ (nf1,nfr1,ni1)
        have hmono : nf.val ≤ nf1.val ∧ nfr.val ≤ nfr1.val ∧ ni.val ≤ ni1.val := by
          split at hM <;>
            first
            | -- unchanged arms
              (simp only [ok.injEq, Prod.mk.injEq] at hM; obtain ⟨e1, e2, e3⟩ := hM;
               subst e1; subst e2; subst e3; exact ⟨le_refl _, le_refl _, le_refl _⟩)
            | -- single +1 (nformats)
              (obtain ⟨w1, hw1, hM⟩ := res_bind_eq_ok hM;
               simp only [ok.injEq, Prod.mk.injEq] at hM; obtain ⟨e1, e2, e3⟩ := hM;
               subst e1; subst e2; subst e3;
               exact ⟨u32_add_ge_left _ _ _ hw1, le_refl _, le_refl _⟩)
            | -- triple +1 (DV)
              (obtain ⟨w1, hw1, hM⟩ := res_bind_eq_ok hM;
               obtain ⟨w2, hw2, hM⟩ := res_bind_eq_ok hM;
               obtain ⟨w3, hw3, hM⟩ := res_bind_eq_ok hM;
               simp only [ok.injEq, Prod.mk.injEq] at hM; obtain ⟨e1, e2, e3⟩ := hM;
               subst e1; subst e2; subst e3;
               exact ⟨u32_add_ge_left _ _ _ hw1, u32_add_ge_left _ _ _ hw2,
                      u32_add_ge_left _ _ _ hw3⟩)
            | -- frame arms: nframes+1, intervals += (byte?:3)
              (obtain ⟨w1, hw1, hM⟩ := res_bind_eq_ok hM;
               obtain ⟨w4, hi4, hM⟩ := res_bind_eq_ok hM;
               simp only [ok.injEq, Prod.mk.injEq] at hM; obtain ⟨e1, e2, e3⟩ := hM;
               subst e1; subst e2; subst e3;
               refine ⟨le_refl _, u32_add_ge_left _ _ _ hw1, ?_⟩;
               split at hi4
               · obtain ⟨_, _, hi4⟩ := res_bind_eq_ok hi4;
                 obtain ⟨_, _, hi4⟩ := res_bind_eq_ok hi4;
                 obtain ⟨_, _, hi4⟩ := res_bind_eq_ok hi4;
                 exact u32_add_ge_left _ _ _ hi4
               · simp only [ok.injEq] at hi4; subst hi4; exact le_refl _)
        obtain ⟨hm1, hm2, hm3⟩ := hmono
        exact ⟨le_trans ha hm1, le_trans hb hm2, le_trans hc hm3⟩
      · -- byte[1] ≠ CS_INTERFACE : done branch, contradicts cont
        simp at hbody
    · -- bl ≤ 2 : done branch, contradicts cont
      simp at hbody
  case hdone =>
    intro x z hinv hbody
    obtain ⟨nf, nfr, ni, p, bl⟩ := x
    obtain ⟨ha, hb, hc⟩ := hinv
    simp only [parse_loop0.body] at hbody
    split at hbody
    · -- bl > 2
      obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
      obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
      split at hbody
      · -- CS_INTERFACE : cont path, contradicts done
        exfalso
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
        obtain ⟨_, _, hbody⟩ := res_bind_eq_ok hbody
        simp at hbody
      · -- ¬CS : done (nf,nfr,ni)
        simp only [ok.injEq, ControlFlow.done.injEq] at hbody
        subst hbody
        exact ⟨ha, hb, hc⟩
    · -- bl ≤ 2 : done (nf,nfr,ni)
      simp only [ok.injEq, ControlFlow.done.injEq] at hbody
      subst hbody
      exact ⟨ha, hb, hc⟩

set_option maxHeartbeats 1000000 in
/-- ARBITRARY-BASE one-step replay. Same statement as `counting_step_replay`
    but the reference run starts from arbitrary accumulators `(nf,nfr,ni)`
    rather than `(0,0,0)`, and the replayed run starts from `(Nf,Nfr,Ni)` with
    `Nf.val = a.val + nf.val` etc. This is the ingredient the loop lift actually
    needs: after the loop's FIRST iteration the accumulators are nonzero, so the
    from-zero `counting_step_replay` (its `nf=nfr=ni=0` special case) cannot by
    itself be threaded through the whole loop. The proof is the from-zero one
    with `u32_add_replay` replaced by the arbitrary-base `u32_add_shift`; the
    control flow / reads / `pos`,`buflen` updates are counter-independent, so
    the goal's shifted body reduces by exactly the base body's peeled facts. -/
lemma counting_step_replay_gen
    (buf : Slice Std.U8) (a b c : Std.U32)
    (nf nfr ni Nf Nfr Ni : Std.U32) (pos : Std.Usize) (buflen : Std.I32)
    (hNf : Nf.val = a.val + nf.val)
    (hNfr : Nfr.val = b.val + nfr.val)
    (hNi : Ni.val = c.val + ni.val) :
    (∀ df dfr di pos' buflen',
        parse_loop0.body buf nf nfr ni pos buflen
          = ok (ControlFlow.cont (df, dfr, di, pos', buflen')) →
        a.val + df.val ≤ Std.U32.max →
        b.val + dfr.val ≤ Std.U32.max →
        c.val + di.val ≤ Std.U32.max →
        ∃ sf sfr si,
          parse_loop0.body buf Nf Nfr Ni pos buflen
            = ok (ControlFlow.cont (sf, sfr, si, pos', buflen')) ∧
          sf.val = a.val + df.val ∧ sfr.val = b.val + dfr.val ∧ si.val = c.val + di.val)
    ∧
    (∀ df dfr di,
        parse_loop0.body buf nf nfr ni pos buflen
          = ok (ControlFlow.done (df, dfr, di)) →
        a.val + df.val ≤ Std.U32.max →
        b.val + dfr.val ≤ Std.U32.max →
        c.val + di.val ≤ Std.U32.max →
        ∃ sf sfr si,
          parse_loop0.body buf Nf Nfr Ni pos buflen
            = ok (ControlFlow.done (sf, sfr, si)) ∧
          sf.val = a.val + df.val ∧ sfr.val = b.val + dfr.val ∧ si.val = c.val + di.val) := by
  refine ⟨?cont, ?done⟩
  case cont =>
    intro df dfr di pos' buflen' h0 hoa hob hoc
    simp only [parse_loop0.body] at h0 ⊢
    by_cases hbl : buflen > 2#i32
    · rw [if_pos hbl] at h0; simp only [if_pos hbl] at ⊢
      obtain ⟨i, hi, h0⟩ := res_bind_eq_ok h0; simp only [hi, bind_tc_ok] at ⊢
      obtain ⟨i1, hi1, h0⟩ := res_bind_eq_ok h0; simp only [hi1, bind_tc_ok] at ⊢
      by_cases hcs : i1 = USB_DT_CS_INTERFACE
      · rw [if_pos hcs] at h0; simp only [if_pos hcs] at ⊢
        obtain ⟨i2, hi2, h0⟩ := res_bind_eq_ok h0; simp only [hi2, bind_tc_ok] at ⊢
        obtain ⟨i3, hi3, h0⟩ := res_bind_eq_ok h0; simp only [hi3, bind_tc_ok] at ⊢
        split at h0
        all_goals
          (obtain ⟨⟨mf, mfr, mi⟩, hM0, h0⟩ := res_bind_eq_ok h0
           obtain ⟨i4, hi4, h0⟩ := res_bind_eq_ok h0
           obtain ⟨i5, hi5, h0⟩ := res_bind_eq_ok h0
           obtain ⟨tbl, htbl, h0⟩ := res_bind_eq_ok h0
           obtain ⟨i6, hi6, h0⟩ := res_bind_eq_ok h0
           obtain ⟨tpos, htpos, h0⟩ := res_bind_eq_ok h0
           simp only [ok.injEq, ControlFlow.cont.injEq, Prod.mk.injEq] at h0
           obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h0)
        case h_1 | h_2 | h_3 =>            -- nformats += 1
          obtain ⟨z, hz, hM0⟩ := res_bind_eq_ok hM0
          simp only [ok.injEq, Prod.mk.injEq] at hM0
          obtain ⟨rfl, rfl, rfl⟩ := hM0
          obtain ⟨w, hw, hwv⟩ := u32_add_shift nf a 1#u32 z Nf hz hNf hoa
          exact ⟨w, Nfr, Ni, by simp [hw, hi4, hi5, htbl, hi6, htpos, bind_tc_ok],
                 hwv, by scalar_tac, by scalar_tac⟩
        case h_4 =>                        -- DV: all three += 1
          obtain ⟨z1, hz1, hM0⟩ := res_bind_eq_ok hM0
          obtain ⟨z2, hz2, hM0⟩ := res_bind_eq_ok hM0
          obtain ⟨z3, hz3, hM0⟩ := res_bind_eq_ok hM0
          simp only [ok.injEq, Prod.mk.injEq] at hM0
          obtain ⟨rfl, rfl, rfl⟩ := hM0
          obtain ⟨w1, hw1, hwv1⟩ := u32_add_shift nf a 1#u32 z1 Nf hz1 hNf hoa
          obtain ⟨w2, hw2, hwv2⟩ := u32_add_shift nfr b 1#u32 z2 Nfr hz2 hNfr hob
          obtain ⟨w3, hw3, hwv3⟩ := u32_add_shift ni c 1#u32 z3 Ni hz3 hNi hoc
          exact ⟨w1, w2, w3,
                 by simp [hw1, hw2, hw3, hi4, hi5, htbl, hi6, htpos, bind_tc_ok],
                 hwv1, hwv2, hwv3⟩
        case h_5 | h_6 | h_10 =>           -- unchanged counters
          simp only [ok.injEq, Prod.mk.injEq] at hM0
          obtain ⟨rfl, rfl, rfl⟩ := hM0
          exact ⟨Nf, Nfr, Ni, by simp [hi4, hi5, htbl, hi6, htpos, bind_tc_ok],
                 by scalar_tac, by scalar_tac, by scalar_tac⟩
        case h_7 | h_8 =>                  -- frame, interval byte at offset 25
          obtain ⟨z1, hz1, hM0⟩ := res_bind_eq_ok hM0
          obtain ⟨z4, hz4, hM0⟩ := res_bind_eq_ok hM0
          simp only [ok.injEq, Prod.mk.injEq] at hM0
          obtain ⟨rfl, rfl, rfl⟩ := hM0
          obtain ⟨w2, hw2, hwv2⟩ := u32_add_shift nfr b 1#u32 z1 Nfr hz1 hNfr hob
          by_cases hb25 : buflen > 25#i32
          · rw [if_pos hb25] at hz4
            obtain ⟨j5, hj5, hz4⟩ := res_bind_eq_ok hz4
            obtain ⟨j6, hj6, hz4⟩ := res_bind_eq_ok hz4
            obtain ⟨j7, hj7, hz4⟩ := res_bind_eq_ok hz4
            obtain ⟨w3, hw3, hwv3⟩ := u32_add_shift ni c j7 z4 Ni hz4 hNi hoc
            refine ⟨Nf, w2, w3, ?_, by scalar_tac, hwv2, hwv3⟩
            simp only [hj6, bind_tc_ok] at hj7
            simp only [hw2, if_pos hb25, hj5, hj6, hj7, hw3, hi4, hi5, htbl,
              hi6, htpos, bind_tc_ok] <;> rfl
          · rw [if_neg hb25] at hz4
            simp only [ok.injEq] at hz4; subst hz4
            refine ⟨Nf, w2, Ni, ?_, by scalar_tac, hwv2, by scalar_tac⟩
            simp only [hw2, if_neg hb25, hi4, hi5, htbl, hi6, htpos, bind_tc_ok] <;> rfl
        case h_9 =>                        -- frame, interval byte at offset 21
          obtain ⟨z1, hz1, hM0⟩ := res_bind_eq_ok hM0
          obtain ⟨z4, hz4, hM0⟩ := res_bind_eq_ok hM0
          simp only [ok.injEq, Prod.mk.injEq] at hM0
          obtain ⟨rfl, rfl, rfl⟩ := hM0
          obtain ⟨w2, hw2, hwv2⟩ := u32_add_shift nfr b 1#u32 z1 Nfr hz1 hNfr hob
          by_cases hb21 : buflen > 21#i32
          · rw [if_pos hb21] at hz4
            obtain ⟨j5, hj5, hz4⟩ := res_bind_eq_ok hz4
            obtain ⟨j6, hj6, hz4⟩ := res_bind_eq_ok hz4
            obtain ⟨j7, hj7, hz4⟩ := res_bind_eq_ok hz4
            obtain ⟨w3, hw3, hwv3⟩ := u32_add_shift ni c j7 z4 Ni hz4 hNi hoc
            refine ⟨Nf, w2, w3, ?_, by scalar_tac, hwv2, hwv3⟩
            simp only [hj6, bind_tc_ok] at hj7
            simp only [hw2, if_pos hb21, hj5, hj6, hj7, hw3, hi4, hi5, htbl,
              hi6, htpos, bind_tc_ok] <;> rfl
          · rw [if_neg hb21] at hz4
            simp only [ok.injEq] at hz4; subst hz4
            refine ⟨Nf, w2, Ni, ?_, by scalar_tac, hwv2, by scalar_tac⟩
            simp only [hw2, if_neg hb21, hi4, hi5, htbl, hi6, htpos, bind_tc_ok] <;> rfl
      · rw [if_neg hcs] at h0; simp at h0
    · rw [if_neg hbl] at h0; simp at h0
  case done =>
    intro df dfr di h0 hoa hob hoc
    simp only [parse_loop0.body] at h0 ⊢
    by_cases hbl : buflen > 2#i32
    · rw [if_pos hbl] at h0; simp only [if_pos hbl] at ⊢
      obtain ⟨i, hi, h0⟩ := res_bind_eq_ok h0; simp only [hi, bind_tc_ok] at ⊢
      obtain ⟨i1, hi1, h0⟩ := res_bind_eq_ok h0; simp only [hi1, bind_tc_ok] at ⊢
      by_cases hcs : i1 = USB_DT_CS_INTERFACE
      · rw [if_pos hcs] at h0
        exfalso
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        obtain ⟨_, _, h0⟩ := res_bind_eq_ok h0
        simp at h0
      · rw [if_neg hcs] at h0; simp only [if_neg hcs] at ⊢
        simp only [ok.injEq, ControlFlow.done.injEq, Prod.mk.injEq] at h0
        obtain ⟨e1, e2, e3⟩ := h0; subst e1; subst e2; subst e3
        exact ⟨Nf, Nfr, Ni, rfl, by scalar_tac, by scalar_tac, by scalar_tac⟩
    · rw [if_neg hbl] at h0; simp only [if_neg hbl] at ⊢
      simp only [ok.injEq, ControlFlow.done.injEq, Prod.mk.injEq] at h0
      obtain ⟨e1, e2, e3⟩ := h0; subst e1; subst e2; subst e3
      exact ⟨Nf, Nfr, Ni, rfl, by scalar_tac, by scalar_tac, by scalar_tac⟩

/-- (Aleph decomposition, 3/3) General replay. `parse_loop0` from `(a,b,c)`
    follows the same control path as from `(0,0,0)` and returns the from-zero
    counters shifted by `(a,b,c)`, under the no-overflow bounds `ha`/`hb`/`hc`.
    Proved by induction on the loop: `counting_step_replay` (1) replays each
    body step, and `counting_monotone` (2) discharges the per-step overflow
    checks from the final-sum bounds. `counting_additive` below is the direct
    specialization of this theorem. -/
lemma counting_replay
    (buf : Slice Std.U8) (a b c : Std.U32) (pos : Std.Usize) (buflen : Std.I32)
    (nf0 nfr0 ni0 : Std.U32)
    (hbase : parse_loop0 buf 0#u32 0#u32 0#u32 pos buflen = ok (nf0, nfr0, ni0))
    (ha : a.val + nf0.val ≤ Std.U32.max)
    (hb : b.val + nfr0.val ≤ Std.U32.max)
    (hc : c.val + ni0.val ≤ Std.U32.max) :
    ∃ s0 s1 s2,
      parse_loop0 buf a b c pos buflen = ok (s0, s1, s2) ∧
      s0.val = a.val + nf0.val ∧
      s1.val = b.val + nfr0.val ∧
      s2.val = c.val + ni0.val := by
  rw [parse_loop0_eq] at hbase ⊢
  refine loop_ok_inv
    (fun (x : Std.U32 × Std.U32 × Std.U32 × Std.Usize × Std.I32) =>
      parse_loop0.body buf x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    -- INVARIANT: from a from-zero state `st = (nf,nfr,ni,p,bl)` there exist
    -- shifted counters `(Nf,Nfr,Ni) = (a,b,c) + (nf,nfr,ni)` such that the
    -- ORIGINAL shifted run equals the shifted run advanced to here, and the
    -- from-zero run from here still reaches the final `(nf0,nfr0,ni0)`.
    (fun st => ∃ (Nf Nfr Ni : Std.U32),
        Nf.val = a.val + st.1.val ∧ Nfr.val = b.val + st.2.1.val ∧
        Ni.val = c.val + st.2.2.1.val ∧
        loop (fun x => parse_loop0.body buf x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
            (a, b, c, pos, buflen)
          = loop (fun x => parse_loop0.body buf x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
            (Nf, Nfr, Ni, st.2.2.2.1, st.2.2.2.2) ∧
        loop (fun x => parse_loop0.body buf x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) st
          = ok (nf0, nfr0, ni0))
    (fun y => ∃ s0 s1 s2,
        loop (fun x => parse_loop0.body buf x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
            (a, b, c, pos, buflen)
          = ok (s0, s1, s2) ∧
        s0.val = a.val + y.1.val ∧ s1.val = b.val + y.2.1.val ∧
        s2.val = c.val + y.2.2.val)
    ?hcont ?hdone (0#u32, 0#u32, 0#u32, pos, buflen) (nf0, nfr0, ni0) ?hinv0 hbase
  case hinv0 =>
    exact ⟨a, b, c, by simp, by simp, by simp, rfl, hbase⟩
  case hcont =>
    intro x x' hinv hstep
    obtain ⟨nf, nfr, ni, p, bl⟩ := x
    obtain ⟨nf', nfr', ni', p', bl'⟩ := x'
    obtain ⟨Nf, Nfr, Ni, hNf, hNfr, hNi, hshift, hanchor⟩ := hinv
    have hstep' : parse_loop0.body buf nf nfr ni p bl
        = ok (ControlFlow.cont (nf', nfr', ni', p', bl')) := hstep
    have hanchor' :
        loop (fun x => parse_loop0.body buf x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
          (nf', nfr', ni', p', bl') = ok (nf0, nfr0, ni0) := by
      rw [← loop_step_cont _ (nf, nfr, ni, p, bl) (nf', nfr', ni', p', bl') hstep']
      exact hanchor
    have hpl : parse_loop0 buf nf' nfr' ni' p' bl' = ok (nf0, nfr0, ni0) := by
      rw [parse_loop0_eq]; exact hanchor'
    obtain ⟨hm1, hm2, hm3⟩ :=
      counting_monotone buf nf' nfr' ni' p' bl' nf0 nfr0 ni0 hpl
    obtain ⟨sf, sfr, si, hstepS, hsf, hsfr, hsi⟩ :=
      (counting_step_replay_gen buf a b c nf nfr ni Nf Nfr Ni p bl hNf hNfr hNi).1
        nf' nfr' ni' p' bl' hstep' (by omega) (by omega) (by omega)
    refine ⟨sf, sfr, si, hsf, hsfr, hsi, ?_, hanchor'⟩
    exact hshift.trans
      (loop_step_cont _ (Nf, Nfr, Ni, p, bl) (sf, sfr, si, p', bl') hstepS)
  case hdone =>
    intro x y hinv hstep
    obtain ⟨nf, nfr, ni, p, bl⟩ := x
    obtain ⟨f, fr, i⟩ := y
    obtain ⟨Nf, Nfr, Ni, hNf, hNfr, hNi, hshift, hanchor⟩ := hinv
    have hstep' : parse_loop0.body buf nf nfr ni p bl
        = ok (ControlFlow.done (f, fr, i)) := hstep
    have hfd : ok (f, fr, i)
        = (ok (nf0, nfr0, ni0) : Result (Std.U32 × Std.U32 × Std.U32)) := by
      rw [← loop_step_done
        (fun x => parse_loop0.body buf x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
        (nf, nfr, ni, p, bl) (f, fr, i) hstep']
      exact hanchor
    simp only [ok.injEq, Prod.mk.injEq] at hfd
    obtain ⟨rfl, rfl, rfl⟩ := hfd
    obtain ⟨sf, sfr, si, hstepS, hsf, hsfr, hsi⟩ :=
      (counting_step_replay_gen buf a b c nf nfr ni Nf Nfr Ni p bl hNf hNfr hNi).2
        f fr i hstep' ha hb hc
    refine ⟨sf, sfr, si, ?_, hsf, hsfr, hsi⟩
    rw [hshift]
    exact loop_step_done
      (fun x => parse_loop0.body buf x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (Nf, Nfr, Ni, p, bl) (sf, sfr, si) hstepS

/-- Additivity of the counting pass in its accumulators. In `parse_loop0.body`
    the three accumulators (`nformats`/`nframes`/`nintervals`) are used ONLY as
    operands of the CHECKED additions `nformats + 1#u32`, `nframes + 1#u32`,
    `nintervals + 1#u32`, `nintervals + i7`; they never appear in a branch
    condition (the control flow is decided solely by `buflen`, `buf[pos+1]`,
    `buf[pos+2]`). So from a fixed `(pos, buflen)` the loop's control path,
    step count, and termination are independent of the starting accumulators —
    running with `(a, b, c)` yields `(a, b, c)` plus the run from zero, PROVIDED
    no checked add overflows.
    FALSITY OF THE PREVIOUS FORM (Aleph counterexample): with `a b c`
    unconstrained, take `a = U32.max` and any `buf` whose walk counts ≥ 1 format;
    then `nformats + 1#u32` overflow-checks and the loop returns `fail`, so
    `parse_loop0 buf a b c … = fail`, contradicting the claimed `∃ … = ok`. (The
    same overflow would also break the `.val` equality via wraparound, but the
    `fail` hits first.) `WellFormed (iv)` bounds the run-from-zero totals but NOT
    the free `a, b, c`, so it does not save the old statement.
    FIX: require the final accumulator sums to fit in `U32` (`ha`/`hb`/`hc`).
    This is exactly the no-overflow condition; it makes every intermediate add
    (whose operand ≤ the final sum, since tallies only grow) succeed, so the run
    is `ok` and each `.val` equals the exact Nat sum. In (A) these bounds are
    discharged from `WellFormed (iv)`: the accumulators are block deltas and the
    from-zero totals are counts over the buffer, whose sum is ≤ the whole-buffer
    tally ≤ 85·2^24 < 2^32 (buf.length ≤ 2^24). Non-vacuous (holds for `a=b=c=0`
    and for all realistic bounded counts). `WellFormed` itself is not needed here
    (termination transfers from `hbase`); it is where (A) obtains `ha`/`hb`/`hc`.
    THIS IS THE ADDITIVITY the (A) induction needs: with the loop reaching the
    next driving-loop position it gives the positional split
    `count(pos) = block-delta + count(pos+ret)`. Most self-contained lemma (a
    pure fact about `parse_loop0`); to be proved first. -/
lemma counting_additive
    (buf : Slice Std.U8) (a b c : Std.U32) (pos : Std.Usize) (buflen : Std.I32)
    (nf0 nfr0 ni0 : Std.U32)
    (hbase : parse_loop0 buf 0#u32 0#u32 0#u32 pos buflen = ok (nf0, nfr0, ni0))
    -- accumulator sums fit in U32 (no checked-add overflow); discharged in (A)
    -- from `WellFormed (iv)`.
    (ha : a.val + nf0.val ≤ Std.U32.max)
    (hb : b.val + nfr0.val ≤ Std.U32.max)
    (hc : c.val + ni0.val ≤ Std.U32.max) :
    ∃ s0 s1 s2,
      parse_loop0 buf a b c pos buflen = ok (s0, s1, s2) ∧
      s0.val = a.val + nf0.val ∧
      s1.val = b.val + nfr0.val ∧
      s2.val = c.val + ni0.val := by
  -- Direct specialization of `counting_replay` (identical statement): the
  -- whole-loop shifted replay, whose per-step overflow checks are discharged by
  -- `counting_monotone` from the final-sum bounds `ha`/`hb`/`hc`. No base-case
  -- special handling is needed (`a=b=c=0` is just the trivial shift).
  exact counting_replay buf a b c pos buflen nf0 nfr0 ni0 hbase ha hb hc

-- ════════════════════════════════════════════════════════════════════════
-- THE DESCRIPTOR-WALK INVARIANT — the shared positional functional-correctness
-- core of theorem (A). Everything the 6 buffer-walk loops and the write-bounds
-- proof still need bottoms out here. STATED ONLY (sorry): this is the named,
-- checkable remaining goal, not prose.
--
-- `WellFormed buf` gives a tiling `descs` of `buf` into self-describing blocks,
-- each with `bLength = block-length ≥ 3 ≥ 1` (byte 0). A *boundary* is a
-- position equal to the total length of a prefix of `descs`. The claim is that
-- the parser's `pos`-walk only ever lands on boundaries, never reads out of
-- range, and advances by a positive whole number of descriptors per step:
--
--   • `descriptor_walk_step`  — one counting step (`pos += buf[pos]`):
--       `buf[pos] = bLength ≥ 1`, lands on the next boundary, stays in `buf`.
--       CONSUMED BY: `parse_loop0`'s `loop_no_div.hstep` (measure `buflen`
--       strictly drops since `buf[pos] ≥ 1`) and its guarded in-bounds reads.
--   • `uvc_parse_frame_walk`   — one frame step (`pos += ret`):
--       `ret ≥ 1`, `pos+ret` is a boundary in `buf`.
--       CONSUMED BY: `uvc_parse_format_loop0..3`'s `loop_no_div.hstep`.
--   • `uvc_parse_format_walk`  — one driving step (`pos += ret`):
--       `ret ≥ 1`, `pos+ret` is a boundary in `buf` (so `ret` = exact bytes
--       consumed = a contiguous run of descriptors — this is what makes the
--       parse walk and the counting walk share ONE tiling, so `counting_additive`
--       splits at `pos+ret`).
--       CONSUMED BY: `parse_loop1`'s `loop_no_div.hstep`, AND (via the shared
--       tiling) `frame_loop_invariant`'s room re-establishment.
--   • `format_writes_le_count` — conjunct (iii), the write⊆count subset:
--       the frames/intervals a format WRITES over `[pos, pos+ret)` are ≤ what
--       `parse_loop0` TALLIES over the same block (same tiling; the parse pass
--       writes only for `buf[pos+2] == ftype`, a subset of the tallied frame
--       subtypes — COUNTING_LEMMA_NOTES §2/§4).
--       CONSUMED BY: `frame_loop_invariant` (LOCAL FIT + room re-establishment)
--       and thereby the final (A) write-bounds assembly.
--
-- Together these are the real shared core: the first three are the positional
-- structure (boundary + bLength/ret ≥ 1 + in-buf), serving termination and
-- in-bounds reads; the fourth is the write⊆count relation, serving in-bounds
-- writes. No single lemma serves all cleanly because the walks step by three
-- different quantities (`buf[pos]`, frame `ret`, format `ret`) and writes are a
-- distinct concern from position — but this is the minimal set, and each names
-- exactly which loop / obligation it discharges.
-- ════════════════════════════════════════════════════════════════════════

/-- A *descriptor boundary*: `q` (a byte offset into `buf`) is the total length
    of some prefix `descs.take k` of the tiling. The parser's walk lands only on
    boundaries; the block occupying `[boundary k, boundary (k+1))` is `descs[k]`. -/
def AtBoundary (descs : List (List Std.U8)) (q : ℕ) : Prop :=
  ∃ k, k ≤ descs.length ∧ q = ((descs.take k).flatten).length

/-- (WALK-1, structural) One counting-walk step. `htile`/`hblk`/`hbound` are
    `WellFormed buf` unpacked at its ∃-witness `descs`. At a non-final boundary
    `pos` (block index `k`), the guarded length read at `pos` succeeds, equals
    the block's `bLength`, is `≥ 1`, and stepping by it reaches boundary `k+1`,
    still within `buf`. This is the fact that makes `parse_loop0`'s `buflen`
    measure strictly decrease and every `buf[pos+j]` read stay in range. -/
lemma descriptor_walk_step
    (buf : Slice Std.U8) (descs : List (List Std.U8))
    (htile : descs.flatten = buf.val)
    (hblk : ∀ d ∈ descs, 1 ≤ (d.getD 0 (0#u8)).val ∧
              (d.getD 0 (0#u8)).val = d.length ∧ 3 ≤ d.length)
    (hbound : buf.length ≤ 16777216)
    (pos : Std.Usize) (k : ℕ) (hk : k < descs.length)
    (hpos : pos.val = ((descs.take k).flatten).length) :
    ∃ b : Std.U8,
      Slice.index_usize buf pos = ok b ∧
      1 ≤ b.val ∧
      b.val = (descs.getD k []).length ∧
      pos.val + b.val = ((descs.take (k + 1)).flatten).length ∧
      pos.val + b.val ≤ buf.length := by
  sorry

/-- (WALK-2, `uvc_parse_frame`) One frame-walk step. Under the tiling, at a
    boundary `pos` with the walk in range (`pos + buflen = buf.length`), a
    successful `uvc_parse_frame` returns `ret ≥ 1` and advances to another
    boundary still within `buf`. Feeds termination of the frame loops
    `uvc_parse_format_loop0..3` and their in-bounds reads. -/
lemma uvc_parse_frame_walk
    (self : ParseState) (quirks : Std.U32) (fmt : UvcFormat) (frame_idx : Std.Usize)
    (ftype : Std.U8) (wm : Std.I32)
    (buf : Slice Std.U8) (descs : List (List Std.U8))
    (htile : descs.flatten = buf.val)
    (hblk : ∀ d ∈ descs, 1 ≤ (d.getD 0 (0#u8)).val ∧
              (d.getD 0 (0#u8)).val = d.length ∧ 3 ≤ d.length)
    (hbound : buf.length ≤ 16777216)
    (pos : Std.Usize) (buflen : Std.I32)
    (hpb : (pos.val : ℤ) + buflen.val = (buf.length : ℤ))
    (hbdry : AtBoundary descs pos.val)
    (ret : Std.I32) (st' : ParseState)
    (hok : ParseState.uvc_parse_frame self quirks fmt frame_idx ftype wm buf pos buflen
        = ok (ret, st')) :
    1 ≤ ret.val ∧
    pos.val + ret.val.toNat ≤ buf.length ∧
    AtBoundary descs (pos.val + ret.val.toNat) := by
  sorry

/-- (WALK-3, `uvc_parse_format`) One driving-walk step. Under the tiling, at a
    boundary `pos` with the walk in range, a successful `uvc_parse_format`
    returns `ret ≥ 1` and advances to another boundary still within `buf` — so
    `ret` is exactly the bytes consumed, a contiguous run of descriptors. This
    shared tiling is what lets `counting_additive` split the counting tally at
    `pos + ret`. Feeds termination of the driving loop `parse_loop1`, its
    in-bounds reads, and `frame_loop_invariant`'s room re-establishment. -/
lemma uvc_parse_format_walk
    (self : ParseState) (quirks : Std.U32) (fmt : UvcFormat) (frame_base : Std.Usize)
    (buf : Slice Std.U8) (descs : List (List Std.U8))
    (htile : descs.flatten = buf.val)
    (hblk : ∀ d ∈ descs, 1 ≤ (d.getD 0 (0#u8)).val ∧
              (d.getD 0 (0#u8)).val = d.length ∧ 3 ≤ d.length)
    (hbound : buf.length ≤ 16777216)
    (pos : Std.Usize) (buflen : Std.I32)
    (hpb : (pos.val : ℤ) + buflen.val = (buf.length : ℤ))
    (hbdry : AtBoundary descs pos.val)
    (ret : Std.I32) (st' : ParseState) (fmt' : UvcFormat)
    (hok : ParseState.uvc_parse_format self quirks fmt frame_base buf pos buflen
        = ok (ret, st', fmt')) :
    1 ≤ ret.val ∧
    pos.val + ret.val.toNat ≤ buf.length ∧
    AtBoundary descs (pos.val + ret.val.toNat) := by
  sorry

/-- (WALK-4, conjunct (iii): write ⊆ count) A format writes no more frames /
    intervals over the block `[pos, pos+ret)` than `parse_loop0` tallies over the
    same block. The block tally is `count(pos) − count(pos+ret)` (both from-zero
    counting runs). Because the parse pass writes a frame only for
    `buf[pos+2] == ftype`, a subset of the frame subtypes the counting pass
    tallies (same tiling, identical interval offsets — COUNTING_LEMMA_NOTES
    §2/§4), the writes are bounded by the tally. This is what
    `frame_loop_invariant` turns into LOCAL FIT + room re-establishment, and
    hence what the final (A) assembly uses for in-bounds writes. -/
lemma format_writes_le_count
    (self : ParseState) (quirks : Std.U32) (fmt : UvcFormat) (frame_base : Std.Usize)
    (buf : Slice Std.U8) (descs : List (List Std.U8))
    (htile : descs.flatten = buf.val)
    (hblk : ∀ d ∈ descs, 1 ≤ (d.getD 0 (0#u8)).val ∧
              (d.getD 0 (0#u8)).val = d.length ∧ 3 ≤ d.length)
    (hbound : buf.length ≤ 16777216)
    (pos : Std.Usize) (buflen : Std.I32)
    (hpb : (pos.val : ℤ) + buflen.val = (buf.length : ℤ))
    (hbdry : AtBoundary descs pos.val)
    (ret : Std.I32) (st' : ParseState) (fmt' : UvcFormat)
    (hok : ParseState.uvc_parse_format self quirks fmt frame_base buf pos buflen
        = ok (ret, st', fmt'))
    (nf cnt_f cnt_i : Std.U32)
    (hcount : parse_loop0 buf 0#u32 0#u32 0#u32 pos buflen = ok (nf, cnt_f, cnt_i))
    (pos' : Std.Usize) (buflen' : Std.I32) (nf' cf' ci' : Std.U32)
    (hpos' : pos'.val = pos.val + ret.val.toNat)
    (hbuflen' : buflen'.val = buflen.val - ret.val)
    (hcount' : parse_loop0 buf 0#u32 0#u32 0#u32 pos' buflen' = ok (nf', cf', ci')) :
    fmt'.nframes.val ≤ cnt_f.val - cf'.val ∧
    st'.interval_cursor.val - self.interval_cursor.val ≤ cnt_i.val - ci'.val := by
  sorry

/-- (2) Frame-loop invariant — THE WORKHORSE (in-bounds writes, internal
    cursors), strengthened to be directly chainable as the induction step of the
    driving loop `parse_loop1`. `parse_loop0 buf 0 0 0 pos buflen = (nf,cnt_f,
    cnt_i)` is the counting pass run from `pos` to the end. The sufficient,
    INDUCTIVE room precondition is that the allocation leaves room for that
    remaining tally on top of what is already committed:
        frame_base + cnt_f ≤ frames.length,  interval_cursor + cnt_i ≤ intervals.length.
    Because the parse pass writes, for this format, a SUBSET of what counting
    tallies from `pos` (COUNTING_LEMMA_NOTES §2/§4: same tiling; subtype dispatch
    `buf[pos+2] == ftype ∈ {tallied subtypes}`; identical interval offsets),
    `uvc_parse_format` returns `ok`, every write lands in bounds (LOCAL FIT), and
    — the strengthening — the room bound is RE-ESTABLISHED at the next driving-
    loop position `pos+ret` for the advanced cursor `frame_base + fmt'.nframes`.
    The re-establishment is exactly `count(pos) = block-delta + count(pos+ret)`
    (via `counting_additive`) minus the subset-consumed writes, so
    `(2)-out` at `pos` IS `(2)-in` at `pos+ret`: the driving-loop induction
    closes with no prose gap. -/
lemma frame_loop_invariant
    (st : ParseState) (quirks : Std.U32) (fmt : UvcFormat)
    (frame_base : Std.Usize) (buf : Slice Std.U8) (pos : Std.Usize) (buflen : Std.I32)
    (hwf : WellFormed buf)
    (nf cnt_f cnt_i : Std.U32)
    (hcount : parse_loop0 buf 0#u32 0#u32 0#u32 pos buflen = ok (nf, cnt_f, cnt_i))
    (hroom_f : frame_base.val + cnt_f.val ≤ st.frames.length)
    (hroom_i : st.interval_cursor.val + cnt_i.val ≤ st.intervals.length) :
    ∃ ret st' fmt',
      ParseState.uvc_parse_format st quirks fmt frame_base buf pos buflen
        = ok (ret, st', fmt') ∧
      -- LOCAL FIT: this format's frame/interval writes landed in bounds.
      frame_base.val + fmt'.nframes.val ≤ st'.frames.length ∧
      st'.interval_cursor.val ≤ st'.intervals.length ∧
      -- ROOM RE-ESTABLISHED at the next driving-loop position `pos+ret`
      -- (`pos += ret as usize`, `buflen -= ret`): for the counting tally there,
      -- the advanced cursor `frame_base + fmt'.nframes` still fits. This is
      -- literally `(2)`'s room precondition at the next position, so the
      -- driving-loop induction step is closed.
      (∀ pos' buflen' nf' cf' ci',
          pos'.val = pos.val + ret.val.toNat →
          buflen'.val = buflen.val - ret.val →
          parse_loop0 buf 0#u32 0#u32 0#u32 pos' buflen' = ok (nf', cf', ci') →
          (frame_base.val + fmt'.nframes.val) + cf'.val ≤ st'.frames.length ∧
          st'.interval_cursor.val + ci'.val ≤ st'.intervals.length) := by
  sorry

/-- (3) Output-level bound (COUNTING_LEMMA_NOTES §3). Human-readable form: on
    success, the committed counts do not exceed the counting-pass allocation.
    WEAK / VACUOUS ON THE FAIL PATH (the `--features vuln` control returns
    `fail`, making the implication trivially true) and CAP-truncated, so it is
    NOT the workhorse — (A) uses (2), not this. It is a corollary of (2) through
    the serialization loops, kept only for readability. -/
lemma counting_bounds_writes
    (buf : Slice Std.U8) (quirks : Std.U32) (out0 : UvcParseResult)
    (hwf : WellFormed buf) :
    ∀ ret out, parse buf quirks out0 = ok (ret, out) →
      out.nframes.val ≤ out.nframes_alloc.val ∧
      out.nintervals.val ≤ out.nintervals_alloc.val := by
  sorry

theorem parse_no_panic_wellformed
    (buf : Slice Std.U8) (quirks : Std.U32) (out : UvcParseResult)
    (hwf : WellFormed buf) :
    ∃ r, parse buf quirks out = ok r := by
  -- PROOF SKETCH (to be discharged — currently `sorry`). Every step cites a
  -- lemma; no informal step remains.
  -- A `Result` is `ok | fail | div`; it suffices to rule out `fail` and `div`.
  --  • `div`  — ruled out by `parse_no_div` (1) [which internally rests on
  --             conjunct (i): each loop's measure strictly decreases].
  --  • `fail` — ruled out branch by branch:
  --      – reads:  conjunct (ii) of `WellFormed` (buf tiles exactly; bLength =
  --                block length) gives the invariant `pos + buflen = buf.length`,
  --                so every guarded index `buf[pos+k]` is `< buf.length`;
  --      – writes: induct over the driving loop `parse_loop1` with the invariant
  --                "room bound at the current `(pos, buflen)`", i.e. `(2)`'s
  --                precondition `frame_base + cnt_f ≤ frames.length ∧
  --                interval_cursor + cnt_i ≤ intervals.length` where
  --                `(cnt_f, cnt_i) = parse_loop0 … pos buflen`.
  --                · BASE: at `pos = 0`, `frames.length` / `intervals.length`
  --                  ARE `parse_loop0 … 0 total` (the allocation is that
  --                  counting result), and `frame_base = interval_cursor = 0`,
  --                  so the invariant holds with equality.
  --                · STEP (format descriptor): `frame_loop_invariant` (2) gives
  --                  `uvc_parse_format = ok` (LOCAL FIT ⇒ this block's writes are
  --                  in bounds) and, in its strengthened postcondition, the room
  --                  bound RE-ESTABLISHED at `pos+ret` for `frame_base +
  --                  fmt'.nframes` — which is exactly the invariant at the next
  --                  `parse_loop1` state. That postcondition is where
  --                  `counting_additive` is applied: `count(pos) = block-delta +
  --                  count(pos+ret)` and the writes are a subset of block-delta.
  --                · STEP (non-format / skip): advances by one bLength; the
  --                  invariant is preserved by `counting_additive` (one-descriptor
  --                  split), cursors unchanged.
  --                Hence every `frames[frame_base+i]` / `intervals[iv_base+i]`
  --                write index is `<` its Vec length;
  --      – arith:  conjunct (iv) bounds the checked `+`/`−`/`×`; the one
  --                CVE-relevant product is `wrapping_mul` + `>>3`, total.
  --  Combining `parse_no_div` (1) with the (2)+`counting_additive` induction and
  --  (ii)/(iv), `parse` returns `ok`. (`counting_bounds_writes` (3) is the weak
  --  human-readable corollary, not used in this proof.)
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
#print axioms NoPanic.u32_add_ge_left
#print axioms NoPanic.u32_add_shift
#print axioms NoPanic.res_bind_eq_ok
#print axioms NoPanic.loop_ok_inv
#print axioms NoPanic.loop_no_div
#print axioms NoPanic.guid_eq16_loop_no_div
#print axioms NoPanic.uvc_format_by_guid_loop_no_div
#print axioms NoPanic.parse_loop3_no_div
#print axioms NoPanic.uvc_parse_frame_loop_no_div
#print axioms NoPanic.fourcc_ne_div
#print axioms NoPanic.UVC_FMTS_ne_div
#print axioms NoPanic.sliceiter_next_ne_div
#print axioms NoPanic.take_next_ne_div
#print axioms NoPanic.take_next_some_n
#print axioms NoPanic.enum_next_some
#print axioms NoPanic.enum_next_ne_div
#print axioms NoPanic.parse_loop2_no_div
#print axioms NoPanic.loop_step_cont
#print axioms NoPanic.loop_step_done
#print axioms NoPanic.parse_loop0_eq
#print axioms NoPanic.parse_no_div
#print axioms NoPanic.descriptor_walk_step
#print axioms NoPanic.uvc_parse_frame_walk
#print axioms NoPanic.uvc_parse_format_walk
#print axioms NoPanic.format_writes_le_count
#print axioms NoPanic.counting_step_replay
#print axioms NoPanic.counting_step_replay_gen
#print axioms NoPanic.counting_monotone
#print axioms NoPanic.counting_replay
#print axioms NoPanic.counting_additive
#print axioms NoPanic.frame_loop_invariant
#print axioms NoPanic.counting_bounds_writes
#print axioms NoPanic.parse_no_panic_wellformed

