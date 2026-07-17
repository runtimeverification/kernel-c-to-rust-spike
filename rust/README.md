# Rust reimplementation of the UVC descriptor parser

This is the "rewrite the untrusted parser in a memory-safe language" step. It
reimplements the same parsing leaf as [`../c`](../c) — the counting pass, the
allocation, `uvc_parse_format`, and `uvc_parse_frame` — in idiomatic safe
Rust, and exposes it through the **same C ABI and the same flat result
struct**, so one differential-fuzzing harness can drive both.

```rust
#[no_mangle]
pub unsafe extern "C" fn uvc_parse(
    buffer: *const u8, buflen: i32, quirks: u32, out: *mut UvcParseResult,
) -> i32
```

`cargo build` produces a `cdylib` (`libuvc_parse_rs.so`, the C-ABI shared
object), a `staticlib` (`libuvc_parse_rs.a`), and an `rlib` (for the in-crate
tests and, later, `cargo-fuzz`). `cargo test` runs three equivalence tests
against known-good outputs (the same vectors the C smoke test uses).

## What is the same

Control flow, validation order, and the exact integer arithmetic are matched
to the C line-for-line. In particular:

- The **counting pass sizes the allocation** (`frames: Vec`, `intervals:
  Vec`), and the parse pass writes into it. This preserves the CVE-2024-53104
  bug *class*: a parse that writes more frames/intervals than the counting
  pass reserved is an out-of-bounds access.
- The buffer walk maintains the kernel invariant `pos + buflen == total`, so
  every guarded read (`buflen > 2`, `buflen < n`, `buflen < 26 + 4*n`) is
  in-bounds for well-formed input — matching where the C is safe.
- `clamp` is `min(max(val, lo), hi)`, including the `lo > hi` case.
- Unsigned comparisons (`(buflen as u32) < 26 + 4*n`) reproduce the C integer
  promotions rather than the "natural" signed Rust comparison.

The flat `UvcParseResult` is `#[repr(C)]` and a compile-time assertion pins
its size to the C struct's (14364 bytes on x86-64), so ABI drift breaks the
build.

## The memory-safety difference (the whole point)

Where the C, on a malformed descriptor, would write past the single
`kzalloc`'d block (silent corruption; an ASan build turns it into an abort),
this code indexes a `Vec` and **panics** instead. That divergence — C
corrupts/aborts, Rust panics — is exactly what the differential fuzzer is
built to detect. The rewrite does not *hide* the bug; it converts an
exploitable OOB write into a safe, deterministic panic.

There is one unavoidable `unsafe` block: reconstructing the input `&[u8]` from
the raw `(buffer, buflen)` FFI pair, and dereferencing the `out` pointer. That
is the FFI contract, identical to the C entry taking a `const uint8_t *`. All
parsing above it is safe Rust.

## Deviations from the C (each tagged `// DEVIATION` in the source)

1. **`v4l2_format_info()` stubbed to `None`.** Same decision as the C side:
   it is a v4l2-core helper, not UVC parsing, and only the
   `UVC_QUIRK_FORCE_BPP` branch touches it. Stubbed identically on both sides,
   so the branch is inert and the differential comparison stays valid. This is
   the only intentional behavioural difference from the running kernel; C and
   Rust still agree with each other.

2. **Signed-overflow site made explicit.** The uncompressed buffer-size
   recompute `bpp * wWidth * wHeight / 8` is 32-bit signed arithmetic that can
   overflow in the C — undefined behaviour, so the result is compiler-dependent.
   Phase 3's differential fuzzer showed this: the Rust models the
   **clang-compiled** C (which the harness links), computing a wrapping `u32`
   product then an unsigned `>> 3`, so the equivalence holds for the clang
   build; gcc resolves the same UB differently (signed `/8`), re-proving it is
   genuinely UB.

3. **Structural, not behavioural:** pointers become indices. The C
   `format->frames` pointer and `frame->dwFrameInterval` pointer are carried
   as `usize`/`i32` offsets (`frame_base`, `interval_base`) into the backing
   `Vec`s. The serialized offsets are identical to the C pointer differences.

4. **`overflow-checks = true` in release.** Kept on deliberately: outside the
   one wrapping site above, any integer overflow in this parser would be a bug
   worth catching, not silently wrapping. The fuzzer benefits from the extra
   checks.

## Build & test

```sh
cargo build            # debug cdylib/staticlib/rlib
cargo build --release  # optimized, what the fuzzer links
cargo test             # 3 equivalence tests
```

Stable `rustc`/`cargo` (built and tested on 1.94.0). No nightly features.
