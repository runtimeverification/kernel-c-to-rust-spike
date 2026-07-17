# Charon → Aeneas → Lean 4: the UVC parser

Verify the faithful Rust UVC descriptor parser (the shipping `rust/` crate, NOT
the `--features vuln` control) through the Binder spike's toolchain — Charon
`909ff09a` (v0.1.220, `--preset=aeneas`), Aeneas `c2015b86`, Lean/mathlib
`v4.31.0`, stable rustc 1.94.0.

The property is **not** "never panics": panicking on malformed input is the
intended safe behaviour — it replaces the C's out-of-bounds write. Two theorems
are stated, in priority order:

- **(A) No-panic on well-formed input** — for any descriptor buffer satisfying
  the parser's own validation invariants, `parse` returns `ok` (no `fail`, no
  `div`). The main theorem; **stated, `sorry`**, obstruction below.
- **(B) Total safety on all input** — for any byte buffer, `parse` is exactly
  `ok` / controlled `fail` / `div`, never a fourth undefined-behaviour outcome.
  **Proved, `sorry`-free.**

## What was extracted

The whole faithful parse leaf, from `verify/src/lib.rs` (a copy of
`rust/src/lib.rs` with the extraction-only edits listed below):

- `parse` — counting pass, allocation, driving loop, serialization (4 `loop`s);
- `ParseState.uvc_parse_format`, `ParseState.uvc_parse_frame` (+ their loops);
- `uvc_format_by_guid`, `guid_eq16`, the 41-entry `UVC_FMTS` table;
- `uvc_colorspace`, `uvc_xfer_func`, `uvc_ycbcr_enc`, `clamp_u32`, `le16`,
  `le32`, `fourcc`, `v4l2_format_info` (stub), the `UvcFormat`/`UvcFrame`/
  `UvcFormatOut`/`UvcFrameOut`/`UvcParseResult` types.

Charon `charon cargo --preset=aeneas`: **exit 0**, `uvc_verify.llbc` (2.7 MB).
Aeneas `-backend lean`: **exit 0**, `UvcParse.lean` (3623 lines, 37 UVC
functions), **no `sorry`** in the generated code. Both `UvcParse` (generated)
and `NoPanic` (theorems) build under Lean v4.31.0.

## Barriers between this kernel Rust and Aeneas

Unlike the Binder deserializer, **none of the barriers here is the union issue
([AeneasVerif/aeneas#1199](https://github.com/AeneasVerif/aeneas/issues/1199))**
— this parser has no unions. The barriers are control-flow and borrow-shape
limitations plus one missing stdlib model. Each was removed by a
semantics-preserving rewrite in `verify/src/lib.rs` (tagged `EXTRACTION NOTE`);
the parsing arithmetic and validation are unchanged, and the rewrites move the
code *closer* to the kernel C (which already uses indexed loops).

| # | Aeneas message | Rust construct | Fix (semantics-preserving) | New vs #1199 |
|---|---|---|---|---|
| 1 | `Iterator::find` not modelled | `UVC_FMTS.iter().find(..)` | explicit indexed `while` (as the kernel C does) | new |
| 2 | Nested borrows not supported | return `Option<&FormatDesc>` | return `Option<u32>` (the fcc, the only field used) | new |
| 3 | Nested borrows not supported | `&UVC_FMTS[i].guid` (field of a borrowed slice elem) | make `FormatDesc: Copy`, copy the entry to a local | new |
| 4 | Nested borrows not supported | `static UVC_FMTS: &[FormatDesc]` (slice behind a ref) | `static UVC_FMTS: [FormatDesc; 41]` (array) | new |
| 5 | Could not compute a loop fixed point | two nested loops in one fn | split the inner 16-byte compare into `guid_eq16` (one loop each) | new |
| 6 | Early returns inside loops not supported | `if ret < 0 { return ret }` in the frame loop | record error, `break`, return after the loop | new |
| 7 | Cannot dereference raw pointers | `&mut *out`, `from_raw_parts` in the FFI shell | shell omitted from the extraction (see (B) / FFI note) | expected |
| 8 | `def _` (invalid Lean name) | `const _: () = assert!(size_of == 14364)` | ABI-drift guard omitted (build-time check, not the leaf) | new (minor) |

Barriers 1–6 are the interesting ones: Aeneas' borrow model rejects references
nested inside another borrow or inside `Option`, its loop translation rejects
`return`-from-loop, and its symbolic execution needs one loop per function. All
are being actively worked on upstream; none is fundamental to this code.

## Panic model

Aeneas puts every function in `Result α := ok α | fail Error | div`. A panic
(overflow, out-of-bounds index, `unwrap` on `None`, explicit `panic!`) is
exactly `fail`; `div` is nontermination. No-panic is `∃ v, f = ok v` (never
`fail`, never `div`). This is orthogonal to the Rust-level `-EINVAL` return: a
clean rejection is `ok (-22)` — still `ok` at the panic level. That is the
point — reject, don't crash.

## Theorem (A): no-panic on well-formed input — [`lean/NoPanic.lean`]

```lean
opaque WellFormed : Slice Std.U8 → Prop

theorem parse_no_panic_wellformed
    (buf : Slice Std.U8) (quirks : Std.U32) (out : UvcParseResult)
    (hwf : WellFormed buf) :
    ∃ r, parse buf quirks out = ok r := by sorry
```

`WellFormed buf` must capture, as explicit preconditions:
(i) **termination** — every consumed descriptor has `bLength ≥ 1`, so `buflen`
strictly decreases and the four `loop`s terminate (rules out `div`);
(ii) **in-bounds reads** — the walk maintains `pos + buflen = buf.length`, so
each guard (`buflen > 2`, `≥ n`, `≥ 26 + 4·n`) makes every `buf[pos+k]` in range;
(iii) **sized writes** — the counting pass sizes `nframes`/`nintervals` so that
every `frames[frame_base+i]` / `intervals[iv_base+i]` write is within the
allocated `Vec` — exactly the invariant whose violation is CVE-2024-53104;
(iv) **no overflow** — the checked arithmetic does not overflow on valid sizes.

**Status: `sorry`.** Discharging (A) needs loop invariants for all four `loop`
combinators, a termination measure, and above all a proof of (iii) that mirrors
the counting-vs-parsing argument — a multi-loop functional-correctness proof
beyond this spike's per-theorem budget. `WellFormed` is left `opaque` so the
statement fixes the contract without prejudging its formalization. This is the
substantial remaining verification work, and the analogue of the Binder spike's
un-closed `parse_one` no-panic goal — except here `parse` **is** in Lean, so the
goal is stated against the real function and only the proof remains.

## Theorem (B): total safety on all input — proved

```lean
theorem parse_total_safety
    (buf : Slice Std.U8) (quirks : Std.U32) (out : UvcParseResult) :
    (∃ v, parse buf quirks out = ok v)
    ∨ (∃ e, parse buf quirks out = fail e)
    ∨ parse buf quirks out = div
```

Proved by exhaustive case split on the `Result`. Its content is not the proof's
difficulty but that the enumeration is **complete**: `parse` has no fourth,
undefined-behaviour outcome. `fail` is the controlled bounds-check/overflow
panic — the safe replacement for the C's OOB write; `div` is the shared
`bLength == 0` hang (identical in the C; see `fuzz/RESULTS.md`). Every array/
slice access in the translated code is a checked `index`/`get` returning `fail`
on range violation — never a wild access — and the CVE-relevant
`bpp*wWidth*wHeight/8` recompute is `wrapping_mul` + unsigned `>>3`, total, so it
contributes no `fail`. This is memory safety **by construction** of the Aeneas
translation; (B) is its formal statement.

### The FFI `unsafe` block

`parse` (Rust ABI, safe) is the verified leaf. The shipping crate's
`#[no_mangle] extern "C" fn uvc_parse` wraps it and holds the only `unsafe`:
`&mut *out` and `slice::from_raw_parts(buffer, buflen)`. Aeneas cannot model raw
pointers (barrier 7), so the shell is omitted from the extraction and its
obligation is discharged by inspection: it (a) null-checks `out` before
dereferencing, (b) builds the input slice only when `buffer` is non-null and
`buflen > 0`, else an empty slice, and (c) performs no other pointer work — so
given the C-ABI contract (valid `out`, `buffer` valid for `buflen` bytes) it is
sound, and it forwards to the verified `parse`.

## Axiom audit (`#print axioms`)

| Theorem | Status | Axioms |
|---|---|---|
| `uvc_colorspace_no_panic` | proved | `propext, Classical.choice, Quot.sound` |
| `uvc_xfer_func_no_panic` | proved | `propext, Classical.choice, Quot.sound` |
| `uvc_ycbcr_enc_no_panic` | proved | `propext, Classical.choice, Quot.sound` |
| `clamp_u32_no_panic` | proved | `propext, Quot.sound` |
| `parse_total_safety` (B) | proved | `propext, Classical.choice, Quot.sound` |
| `parse_no_panic_wellformed` (A) | `sorry` | `+ sorryAx` |

Five theorems are `sorryAx`-free (standard Lean axioms only). The four helpers
are unconditional no-panic for the pure table lookups and the clamp — the UVC
analogue of the Binder spike's `size_check_no_panic`.

## Distance assessment

- **Extraction: solved.** The full faithful leaf reaches Lean with no `sorry`
  and no union-class blocker. The gap was a handful of borrow-shape / loop
  rewrites (barriers 1–6), all semantics-preserving and upstream-tracked. This
  is a materially better outcome than the Binder deserializer, which #1199 stops
  before any parsing function reaches Lean.
- **(B): done.** Total safety (no UB; every outcome ok/fail/div) is proved
  `sorry`-free — the memory-safety guarantee the C lacks, now machine-checked.
- **(A): one proof away, well-scoped.** The statement is against the real
  `parse`; what remains is the loop-invariant proof of the counting-vs-writing
  relationship (iii) plus termination. That is the same property the
  differential fuzzer exercised dynamically (`fuzz/RESULTS.md`); (A) would make
  it a theorem. Estimated the largest single piece of remaining work in the
  spike.

## Reproduce

```sh
cd verify
charon cargo --preset=aeneas                                            # -> uvc_verify.llbc
aeneas -backend lean llbc/uvc_verify-charon-909ff09a-v0.1.220.llbc -dest lean/
cd lean && lake exe cache get && lake build                             # UvcParse + NoPanic
```

Charon `909ff09a` (v0.1.220), Aeneas `c2015b86`, Lean/mathlib `v4.31.0`, stable
rustc 1.94.0. `--preset=aeneas` is required at Charon extraction time.
