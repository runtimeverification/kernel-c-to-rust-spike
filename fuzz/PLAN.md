# Phase 3 (scaffold only): differential fuzzing plan

**Status: plan, not implemented.** This file describes how the C extraction
(`../c`) and the Rust reimplementation (`../rust`) will be fuzzed against each
other through their shared C ABI. No harness code exists yet.

## Goal and oracles

One untrusted byte buffer drives both implementations of `uvc_parse`. We are
hunting for two things at once:

1. **Memory-safety bugs** (the reason this target was chosen — CVE-2008-3496,
   CVE-2024-53104). Oracle: the C library, built with AddressSanitizer, aborts
   on any out-of-bounds access on the `kzalloc`'d formats/frames/intervals
   block. The Rust library `panic`s (bounds-checked `Vec` access) on the same
   input. Either abort is a finding, with the reproducing input saved.

2. **Semantic divergence** between C and Rust. Oracle: for inputs where
   *neither* side crashes, the two `uvc_parse_result` structs must be equal
   field-by-field. Any difference is a finding — it means the rewrite is not
   faithful (a porting bug), or it localizes a place where the C's behaviour is
   input-dependent in a way we mis-modelled.

The memory-safety oracle and the divergence oracle are complementary: the
first catches "C corrupts memory / Rust panics", the second catches "both run
but disagree".

## Input model

The fuzzer produces a single byte buffer. We split it so `quirks` is also
fuzzable without a second input channel:

```
[ 4 bytes LE = quirks ] [ rest = descriptor buffer ]
```

- `quirks` is masked to the bits the parser actually reads
  (`UVC_QUIRK_FORCE_Y8 | UVC_QUIRK_FORCE_BPP | UVC_QUIRK_RESTRICT_FRAME_RATE`)
  so the mutator does not waste energy on irrelevant bits. (Masking is applied
  identically before both calls, so it does not affect the comparison.)
- The descriptor buffer is passed verbatim as `(buffer, buflen)` to both
  libraries. `buflen` is the byte length; the harness never lies about it.

Both libraries are called with the **identical** `(buffer, buflen, quirks)`.

## Harness architecture

```
        fuzzer input bytes
                │
        split → quirks, descriptor buffer
                │
        ┌───────┴────────┐
        ▼                ▼
  uvc_parse (C)     uvc_parse (Rust)
  ASan+UBSan+sancov  safe, panic=abort
  → result_c         → result_rs
        └───────┬────────┘
                ▼
     field-wise compare(result_c, result_rs)
        equal? continue : report divergence
   (a crash on either side is caught by the runtime)
```

Both targets are linked into **one harness process** so a single input hits
both in-process (fast, no IPC). The C side is the coverage-instrumented target
that guides mutation; the Rust side rides along as the differential oracle.

## Equivalence comparison — field-wise, not `memcmp`

`struct uvc_parse_result` contains padding (mixed `u8`/`i32`/`u32` fields), and
padding bytes are not guaranteed equal even when both sides are "the same".
The comparator therefore compares **only the meaningful fields**, and only the
populated prefix of each array:

- `ret`, `nformats_alloc`, `nframes_alloc`, `nintervals_alloc`
- `nformats`, `nframes`, `nintervals` (and require these to match first)
- `formats[0 .. nformats]` — every scalar field, including `frame_base`
- `frames[0 .. nframes]` — every scalar field, including `interval_base`
- `intervals[0 .. nintervals]`

Both libraries already fully zero the struct on entry (`memset` / explicit
zeroing), so unpopulated tail entries are equal trivially, but the comparator
still restricts to the populated prefix to keep a divergence report readable.

## Crash / divergence handling

- **C OOB** → ASan `abort()` → runtime saves the crashing input.
- **Rust OOB** → `panic` → with `panic = "abort"` in the fuzz build, becomes an
  `abort()` the runtime catches. (Alternatively wrap the Rust call in
  `catch_unwind` and report the panic as a divergence when the C side did *not*
  crash — that asymmetry is itself an interesting finding.)
- **Divergent output, no crash** → the comparator returns "differ" and the
  harness triggers a finding with a dump of the first mismatching field.

## Recommended harness: LibAFL

**Recommendation: LibAFL**, primarily because this repo builds with **stable**
Rust and LibAFL's fuzzer crates compile and run on stable — we do not have to
introduce a nightly toolchain to fuzz. Concretely:

1. **Stable-only.** `cargo-fuzz` drives libFuzzer and, to instrument the Rust
   target and enable `-Zsanitizer=address`, requires a **nightly** toolchain.
   That would put the fuzzer on a different toolchain than the libraries it
   tests. LibAFL builds the fuzzer as an ordinary stable binary.
2. **First-class differential fuzzing.** LibAFL models exactly this shape: a
   `DiffExecutor` running two executors over the same input plus a
   `DiffFeedback` comparing their observed outputs. Our field-wise comparator
   slots straight into a `DiffFeedback`.
3. **Mixed C/Rust target, our choice of coverage source.** We compile the C
   target with the `libafl_cc` clang wrapper
   (`-fsanitize=address -fsanitize-coverage=trace-pc-guard`) to get both the
   memory-safety oracle and an edge-coverage map, and link the Rust `rlib`
   in-process for the differential side. Because the two implement the *same*
   logic, coverage from the C side is a sufficient guide; the Rust target
   needs no special instrumentation and stays on plain stable rustc. (If
   Rust-side coverage is later wanted, LibAFL can consume it too, but it is not
   required to make progress.)
4. **Multiple oracles in one run.** Crash (ASan/panic) and diff feedback
   coexist in one LibAFL harness, which is awkward to express in a single
   `cargo-fuzz` target.

**Alternative, if a nightly toolchain is acceptable:** `cargo-fuzz`
(libFuzzer). It is much faster to stand up — a single `fuzz_target!` that
calls the Rust function directly and the C function via FFI to
`libuvcparse_c_asan.a`, comparing the two results. The cost is the nightly
requirement for the Rust target's sanitizer/coverage, and clumsier handling of
the two-oracle setup. Good for a quick first bring-up; LibAFL is the better
home for the real campaign.

## Build integration (when implemented)

- C oracle target: `cd c && make asan` → `libuvcparse_c_asan.a` (rebuilt via
  the `libafl_cc` wrapper for the coverage map).
- Rust target: `cd rust && cargo build --release` → `libuvc_parse_rs.a`
  (staticlib) or the `rlib`, linked into the harness. Add a
  `panic = "abort"` profile for the fuzz build.
- Harness crate under `fuzz/` (stable): links both, defines the split input
  model, the field-wise comparator, and the LibAFL state/feedback/executor
  wiring.

## Corpus, dictionary, structure-awareness

- **Seed corpus:** the valid vectors already used by the smoke test and the
  Rust unit tests (uncompressed+frame, MJPEG, DV), plus real descriptors
  dumped from `lsusb -v` on actual UVC webcams. Good seeds matter a lot here.
- **Dictionary:** the descriptor subtype bytes are high-value tokens —
  `0x24` (`USB_DT_CS_INTERFACE`), `0x03`–`0x12` (the `UVC_VS_*` subtypes) — so
  the mutator can assemble plausible descriptor chains.
- **Structure-awareness:** descriptors are length-prefixed; `buffer[0]`
  (`bLength`) drives the walk, and the counting pass and parse pass both step
  by it. Purely byte-level mutation rarely keeps `bLength` fields consistent,
  so coverage of the deep frame/interval logic may plateau. Plan: start
  byte-level with strong seeds + the dictionary, measure coverage, and if it
  stalls, add a LibAFL custom mutator (or a small grammar) that preserves the
  `bLength`/`buflen` relationship while mutating field contents. The
  count-vs-parse mismatch behind CVE-2024-53104 specifically needs descriptor
  chains where the frame *types* between the counting pass and a format's
  `ftype` disagree — worth encoding as a targeted generator once basic
  coverage is in.

## Explicitly out of scope for this phase

No harness code, no LibAFL wiring, no corpus files are created yet. This is the
plan that Phase 3 implementation will follow.
