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

## Verification (this target)

- **`parse_no_div`** — prove the UVC parser's loops terminate (div-freeness) under
  `WellFormed`. The `loop_ok_inv` principle in `verify/lean/NoPanic.lean` is the
  intended tool. Well-scoped; the counting block it can lean on is already proved.
- **`frame_loop_invariant`** — prove every frame/interval write lands inside the
  allocated `Vec`, consuming the proved `counting_*` lemmas. This is the
  in-bounds-writes half of the CVE-2024-53104 property.
- **Assemble theorem (A)** — once the two above land, compose (A) from
  termination + in-bounds reads (`WellFormed`) + sized writes + no-overflow.

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
