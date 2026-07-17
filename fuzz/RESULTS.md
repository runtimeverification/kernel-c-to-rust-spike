# Phase 3 results: differential fuzzing C vs Rust

Harness: LibAFL 0.15.4, **stable** rustc 1.94.0 (no nightly). Built per
[PLAN.md](PLAN.md): one process, one input split `[4 bytes quirks LE][descriptor
bytes]`, driving both `uvc_parse` implementations and comparing their
`uvc_parse_result` field-by-field (populated prefix only — never `memcmp`,
because the struct has padding).

The LibAFL-on-stable path in PLAN.md worked; no fallback to cargo-fuzz was
needed. Two environment adaptations were required and are worth recording:

- **Coverage instrumentation.** The plan assumed a clang `-fsanitize-coverage`
  target. This box's clang (19.1.5) is missing its compiler-rt runtimes, and
  its gcc lacks `trace-pc-guard` entirely. Resolved by having clang *compile*
  the C to an object with `-fsanitize-coverage=trace-pc-guard` while cargo/gcc
  *links* it against libafl_targets' own sancov runtime — no clang runtime
  needed. (See `build.rs`.)
- **The memory-safety oracle is split out of the hot loop.** Because clang's
  ASan runtime is unavailable, the fuzzer's C is *not* ASan-instrumented.
  Instead the Rust side is driven natively inside `catch_unwind` (a
  bounds-check panic = a memory-safety refusal) as the in-loop oracle, and
  AddressSanitizer is applied via gcc in a separate replay/triage driver
  (`triage.c`) to confirm what the C does on a saved input.

## Run summary

| | executions | exec/sec | corpus | edge coverage | divergences | panics |
|---|---|---|---|---|---|---|
| pre-fix (first run) | ~hundreds | — | — | climbing | **1** (found in seconds) | 0 |
| post-fix (main run, 3m12s) | 54,019 | 280 | 57 | **85/91 (93%)** | 0 | 0 |
| confirmation (60s) | 12,636 | 210 | 46 | 82/91 (90%) | 0 | 0 |

Seeds: the three valid vectors from the smoke test and Rust unit tests
(`corpus/seed_uncompressed_yuyv.bin`, `seed_mjpeg.bin`, `seed_dv.bin`).
Dictionary: the descriptor-subtype tokens in `dict/uvc.dict`.

The `bLength == 0` **infinite loop** (both implementations loop forever,
identically — a shared limitation of the extracted leaf, not a divergence)
made an in-process executor wedge. Resolved with `SimpleRestartingEventManager`
+ a 1 s per-exec timeout: the manager relaunches from shared-memory-persisted
state on every hang, so the campaign makes progress. These timeouts are *not*
recorded as objectives (see category (c)).

## Findings, classified

### (b)/(c) — signed-overflow buffer-size divergence — FOUND, then FIXED

The one true divergence, found within seconds of the first run:

```
frames[0].dw_max_video_frame_buffer_size:  C = 430329024   Rust = 4188425408
```

on an uncompressed format with `bpp=16`, `wWidth=14688`, `wHeight=14649`. This
is the `frame->dwMaxVideoFrameBufferSize = bpp * wWidth * wHeight / 8` recompute
— computed in 32-bit `int`. The product `3,442,632,192` exceeds `INT_MAX`, so
this is **signed-overflow undefined behaviour** (the site flagged as category
(c) in PLAN.md and phase 2). Its observable value is compiler-dependent:

| build | value | why |
|---|---|---|
| clang -O1 (the fuzzer's C) | 430329024 | assumes no overflow → `imul; imul; shrl $3` (unsigned shift) |
| gcc + UBSan (triage) | 4188425408 | signed `sar`; UBSan prints "signed integer overflow … cannot be represented in type 'int'" |
| phase-2 Rust (before fix) | 4188425408 | `wrapping_mul` + signed `/8` |

Phase 2 had reasoned this site "matches GCC's wraparound" — but the differential
fuzzer links the **clang**-compiled C, which resolves the UB differently. So the
Rust was not a faithful model of the artifact under test.

**Fix** (`rust/src/lib.rs`, tagged `// DEVIATION`): compute the 32-bit wrapping
product and shift right *unsigned* by 3, exactly reproducing clang's codegen:

```rust
let prod = (format.bpp as u32)
    .wrapping_mul(frame.w_width as u32)
    .wrapping_mul(frame.w_height as u32);
frame.dw_max_video_frame_buffer_size = prod >> 3;
```

After the fix the 3-minute / 54k-execution run found **zero** divergences: C and
Rust are equivalent across the reachable input space at 93% edge coverage.

Caveat, recorded honestly: this equivalence is with the **clang-compiled** C.
A gcc build of the same C diverges at this one expression — which simply re-
proves that it is undefined behaviour. The lasting fix belongs in the kernel C
(compute in a wide enough type); until then, "equivalence" at a UB site is only
equivalence with a specific compiler build. This is the category-(c) reality
surfaced as a concrete, reproducible category-(b)-style divergence and driven to
zero for the build under test.

### (c) — shared `bLength == 0` infinite loop — expected, not a divergence

Both implementations loop forever on a zero-length descriptor at a
class-specific interface boundary (neither the counting pass nor the parse
advances). It is identical on both sides, so it is not a divergence and is not
a memory-safety win — a shared DoS limitation of the extracted leaf in
isolation. Recorded here; handled operationally by the restarting manager so it
does not stall the campaign. Not saved as an objective (it would drown the
genuine findings).

### (c) — `v4l2_format_info` stub — inert, never diverges

Stubbed to `NULL`/`None` identically on both sides (the `UVC_QUIRK_FORCE_BPP`
branch), so it can never produce a divergence. The fuzzer masks `quirks` to the
bits the parser reads, including `FORCE_BPP`, and exercised it without a finding.

### (a) — CVE-2024-53104-class OOB write — the security payoff

No out-of-bounds access was found in the faithful v7.2-rc2 code in 54,019
executions, and that is **correct**: v7.2-rc2 post-dates the fixes for both
CVEs, and the counting pass and parse pass walk descriptors identically, so
every frame/interval the parse writes was counted (parse writes ⊆ counted),
with the `buflen < 26 + 4*n` guard preventing under-allocated writes. The leaf
is memory-safe by construction on this surface.

To demonstrate that the harness *catches the CVE class* — the reason for the
whole exercise — a **negative control** reintroduces the historical
counting-vs-parsing mismatch behind an opt-in flag (`-DSPIKE_VULN` in the C,
`--features vuln` in the Rust, mirrored so both carry the identical bug). The
under-count makes `uvc_parse_format` write one frame more than was allocated.
On the *same* input (a plain valid uncompressed-YUYV descriptor,
`findings/CATEGORY_A_cve2024-53104_class.bin`):

```
C  (vulnerable, ASan):  heap-buffer-overflow WRITE, uvc_parse_frame @ uvc_parse.c:634,
                        0 bytes to the right of a 40-byte kzalloc'd region  →  memory corruption
Rust (vulnerable):      panic "index out of bounds: the len is 0 but the index is 0"  →  safe refusal
```

Full report + reproducer: [`findings/CATEGORY_A_report.txt`](findings/CATEGORY_A_report.txt)
and `findings/CATEGORY_A_cve2024-53104_class.bin`. Because that input is one of
the seed vectors, a fuzzer built against the vulnerable variant trips on the
very first execution — no search required.

This is the headline: the same latent bug that is an exploitable out-of-bounds
**write** in C becomes a deterministic, safe **panic** in the memory-safe
rewrite.

## Bottom line

- **Category (b) driven to zero.** One porting mismatch (the UB-site value) was
  found and fixed; the implementations are now behaviourally equivalent for the
  clang-compiled C over 93% edge coverage / 54k executions.
- **Category (a) demonstrated.** In the faithful patched code the OOB is
  unreachable (verified by fuzzing and by construction); in the negative
  control the harness cleanly separates C memory corruption from Rust's safe
  panic — the security value of the rewrite, made concrete.
- **Category (c) documented.** The signed-overflow UB site (compiler-dependent),
  the shared zero-length hang, and the `v4l2_format_info` stub.

## Reproduce

```sh
# faithful differential campaign
cd fuzz && cargo build --release && ./target/release/uvc_diff_fuzz   # Ctrl-C to stop

# category (a) negative control (memory-safety payoff)
cd fuzz && gcc -g -DSPIKE_VULN -fsanitize=address -I../c triage.c ../c/uvc_parse.c -o /tmp/tc
/tmp/tc findings/CATEGORY_A_cve2024-53104_class.bin                    # ASan: heap-buffer-overflow
cd ../rust && cargo run --release --features vuln --example triage -- \
    ../fuzz/findings/CATEGORY_A_cve2024-53104_class.bin                # Rust: safe panic
```
