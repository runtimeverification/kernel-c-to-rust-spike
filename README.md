# Kernel C-to-Rust hardening spike: UVC descriptor parser

Can a security-critical Linux kernel C parser be hardened by rewriting it in
Rust, with the rewrite shown equivalent to the original and then formally
verified? This spike runs the full loop on one target: the UVC video descriptor
parser (`uvc_parse_format`/`uvc_parse_frame` from `drivers/media/usb/uvc/`,
v7.2-rc2), chosen because it carried two independent memory-safety CVEs sixteen
years apart (CVE-2008-3496, CVE-2024-53104, the latter in the CISA KEV catalog).

## The loop, and what each step established

1. **Extract the C leaf** (`c/`). The parsing logic copied byte-for-byte from
   the kernel; only the environment stubbed (`// SPIKE-STUB`). Compiles to a
   C-ABI library. The extracted leaf includes the counting pass and sized
   allocation, so the CVE-2024-53104 bug class (parse writing past what the
   count allocated) is reachable, not abstracted away.

2. **Rewrite in Rust** (`rust/`). The same parsing leaf in safe Rust, same C
   ABI and result struct. Every deviation from the C is tagged `// DEVIATION`
   and documented.

3. **Differential fuzzing** (`fuzz/`). A LibAFL harness on stable rustc drives
   both implementations from one input and compares outputs field-by-field.
   Result: after fixing one porting mismatch at a compiler-dependent
   signed-overflow site, zero divergences over 54,019 executions at 93% edge
   coverage. On the faithful v7.2-rc2 code no out-of-bounds access is reachable
   (both CVEs are patched). An opt-in negative control (`--features vuln`,
   mirrored in both languages) reintroduces the CVE-2024-53104 mismatch: on the
   same input the C does a heap out-of-bounds write (ASan), the Rust panics
   safely. Details: `fuzz/RESULTS.md`.

4. **Formal verification** (`verify/`). The faithful Rust leaf extracts through
   Charon and Aeneas into Lean 4 with no `sorry` in the generated code, and
   with no union blocker (unlike the Binder spike). Two theorems, in
   `verify/VERIFY-REPORT.md`:
   - Total safety on all input (every outcome is `ok` / controlled `fail` /
     nontermination, never an undefined-behaviour outcome): proved, `sorry`-free.
     This makes explicit, as a checked statement, the memory-safety property the
     C lacks.
   - No-panic on well-formed input (panic occurs only on malformed input, where
     it is the intended safe behavior replacing the C's OOB write): stated
     against the real extracted function, proof left open. Its core is the
     counting-pass-versus-write-index invariant whose violation is
     CVE-2024-53104; the differential fuzzer exercised this dynamically, and
     closing the proof is the main remaining verification work.

## Status

The loop is demonstrated end to end on one target. The rewrite is shown
equivalent to the C by differential fuzzing; the memory-safety difference is
made concrete by the negative control; the Rust extracts cleanly into Lean and
its total-safety property is machine-checked. The functional-correctness theorem
(no-panic on well-formed input) is formalized and scoped, not yet proved.

## Layout

- `c/` — the extracted C leaf and its stubs
- `rust/` — the safe-Rust rewrite
- `fuzz/` — the LibAFL differential fuzzer, results, and CVE-class control
- `verify/` — Charon/Aeneas/Lean extraction and theorems
- `*/README.md`, `fuzz/RESULTS.md`, `verify/VERIFY-REPORT.md` — per-stage detail

## Environment

Kernel v7.2-rc2 (read-only reference). Rust stable 1.94.0. LibAFL 0.15.
Charon 909ff09a (v0.1.220, `--preset=aeneas`), Aeneas c2015b86, Lean/mathlib
v4.31.0.
