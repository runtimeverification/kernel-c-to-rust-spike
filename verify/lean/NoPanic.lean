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
#print axioms NoPanic.parse_no_div
#print axioms NoPanic.counting_additive
#print axioms NoPanic.frame_loop_invariant
#print axioms NoPanic.counting_bounds_writes
#print axioms NoPanic.parse_no_panic_wellformed
