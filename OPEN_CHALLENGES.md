# Open Challenges

This spike is built to be extended. The loop it demonstrates
(extract -> rewrite in safe Rust -> differential-fuzz for conformance ->
selective formal verification) is repeatable, and the harness plus the
loop-reasoning infrastructure are reusable. The tasks below are concrete pieces
of that work that a contributor can pick up. Each is scoped so it can be done and
reviewed on its own.

A contribution here is judged by the assurance it carries, not by lines of code:
a rewrite is only useful once it passes differential fuzzing against the original
C, and a proof is only counted once `#print axioms` shows it `sorryAx`-free.

## Verification (this target): the four walk-invariant lemmas

The counting invariant, the two loop-reasoning principles (`loop_ok_inv`,
`loop_no_div`), and div-freeness for the 5 structurally-terminating loops are
already proved. What remains for theorem (A) reduces to four stated lemmas in
`verify/lean/NoPanic.lean`, each currently `sorry`. They are the positional-walk
functional-correctness core, and they are independent enough to be taken
separately.

- **`descriptor_walk_step`** — at each visited position, `buf[pos]` is the
  descriptor `bLength >= 1`, and stepping by it lands on the next boundary within
  the buffer. Discharges `parse_loop0`'s termination (via `loop_no_div`) and its
  in-bounds reads.
- **`uvc_parse_frame_walk`** — a successful `uvc_parse_frame` consumes `ret >= 1`
  bytes and lands on a descriptor boundary. Feeds the `uvc_parse_format_loop0..3`
  terminations.
- **`uvc_parse_format_walk`** — the same for `uvc_parse_format`: `ret` equals the
  bytes consumed, landing on a boundary. Feeds `parse_loop1`'s termination and
  `frame_loop_invariant`'s room re-establishment.
- **`format_writes_le_count`** — the writes are a subset of what the counting
  pass tallied over the consumed block (the CVE-2024-53104 conjunct). Feeds
  `frame_loop_invariant` and the final (A) write-bounds.

Proving these unblocks `parse_no_div`, `frame_loop_invariant`, and the assembly
of (A), which are already stated to consume them. The reusable `loop_no_div` /
`loop_ok_inv` principles and the `*_ne_div` toolkit are the tools.

## New rewrite targets

Pick a self-contained untrusted-input parser, apply the full loop, and submit the
result with its differential-fuzz evidence. Good candidates share the shape of
this one: bytes-in, structured-data-out, small, security-relevant. See the parent
proposal's target list for ideas (USB-audio, USB-HID, virtio ring decode, ASN.1
engine, and others). A target is "done" when the rewrite passes differential
fuzzing against the original C at good coverage, with the negative control
demonstrating the memory-safety difference.

## Assurance infrastructure

- **Reusable differential-fuzz harness** — generalize the `fuzz/` harness so a new
  target needs only its FFI shim and seed corpus, not a bespoke rig.
- **Panic-as-divergence in the harness** — treat a Rust panic where the C returns
  a value as a reported divergence (not a harness crash), via `catch_unwind`.
- **Divergence classification** — report the direction of a divergence
  (implementation more permissive / more strict / value mismatch) and an
  error-code correspondence table, so a triage reader knows what a divergence
  means.

## How to contribute

Open an issue describing the target or lemma you want to take, so work is not
duplicated. Rewrites go in their own directory mirroring this one
(`c/`, `rust/`, `fuzz/`); proofs extend `verify/`. Include the reproduction
commands and, for proofs, the `#print axioms` output.
