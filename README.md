# kernel-c-to-rust-spike: UVC parser hardening loop

Demonstrate the C-to-Rust hardening loop on one real Linux kernel parser:
extract the untrusted C leaf, rewrite it in memory-safe Rust behind the same
C ABI, then differentially fuzz the two against each other (and, later,
formally verify the Rust). Style and stubbing philosophy follow the Binder
spike (`~/kernel-rust-verification-spike`): stub the *environment*, keep the
parsing logic byte-for-byte.

## Target

`uvc_parse_format` and its helper `uvc_parse_frame` in
`drivers/media/usb/uvc/uvc_driver.c` (kernel **v7.2-rc2**, read-only tree at
`~/linux`). This function had two independent memory-safety CVEs sixteen years
apart — **CVE-2008-3496** (buffer overflow) and **CVE-2024-53104** (out-of-
bounds write from a frame-count / allocation mismatch) — which is why it is
the target. The extracted leaf deliberately includes the counting pass and the
sized allocation from `uvc_parse_streaming`, because CVE-2024-53104 lives in
the relationship between allocation sizing and parse writes.

## Status

- **Phase 1 — C leaf** (`c/`): parsing functions copied byte-for-byte from
  v7.2-rc2, kernel environment stubbed (`// SPIKE-STUB`). Builds to
  `libuvcparse_c.{so,a}` and exposes `uvc_parse` with a C ABI. Runs clean under
  ASan+UBSan on valid input. Details: [c/README.md](c/README.md). ✅
- **Phase 2 — Rust rewrite** (`rust/`): idiomatic safe Rust reimplementation of
  the same logic, same control flow, same arithmetic, exposed via
  `#[no_mangle] extern "C" fn uvc_parse` with a `#[repr(C)]` result struct
  whose layout is pinned to the C struct at compile time. `cargo build` and
  `cargo test` pass on stable rustc. Driving the Rust `.so` through the C
  test harness produces byte-identical output. Details:
  [rust/README.md](rust/README.md). ✅
- **Phase 3 — differential fuzzing** (`fuzz/`): LibAFL harness on stable rustc
  drives both libraries from one split input and compares results field-wise.
  54k executions at 93% edge coverage found one divergence — the signed-
  overflow UB site — which was fixed so the implementations converge; no OOB is
  reachable in the patched v7.2-rc2 code. A negative control reintroduces the
  CVE-2024-53104 mismatch and shows the payoff: C does an out-of-bounds write
  (ASan), Rust safely panics. Plan: [fuzz/PLAN.md](fuzz/PLAN.md); results:
  [fuzz/RESULTS.md](fuzz/RESULTS.md). ✅

## Layout

- `c/` — the extracted C leaf, `uvc_parse.{c,h}`, `Makefile`, `README.md`
- `rust/` — the Rust crate (`cdylib`/`staticlib`/`rlib`), `README.md`
- `fuzz/` — `PLAN.md` for the differential-fuzzing phase (no code yet)

## Shared entry point

Both implementations expose exactly:

```c
int32_t uvc_parse(const uint8_t *buffer, int32_t buflen, uint32_t quirks,
                  struct uvc_parse_result *out);
```

`struct uvc_parse_result` (in [c/uvc_parse.h](c/uvc_parse.h)) is a flat,
pointer-free record of the counting-pass allocation sizes and every scalar
field written into the parsed formats, frames, and intervals — the comparison
surface for differential fuzzing.

## Build

```sh
cd c    && make && make asan     # C libs (+ ASan build for the fuzzer)
cd rust && cargo build --release && cargo test
```

Kernel v7.2-rc2 (tree not modified). Stable rustc/cargo 1.94.0, gcc 11 /
clang 19.
