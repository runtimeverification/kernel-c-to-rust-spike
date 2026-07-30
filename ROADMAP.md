# Roadmap

This spike demonstrates one full C-to-Rust hardening loop on the UVC descriptor
parser (extract -> rewrite -> differential fuzz -> verify). This document records
what is done, what is in progress, and where the work is going. Status is stated
honestly: a theorem is only called proved when it is machine-checked and
`#print axioms` shows it `sorryAx`-free.

## Where the loop stands

| Stage | Status |
|---|---|
| Extract the C leaf (`c/`) | done |
| Safe-Rust rewrite (`rust/`) | done |
| Differential fuzzing, C vs Rust (`fuzz/`) | done: 54,019 execs, 93% edge coverage, zero divergences; CVE-class negative control separates C's OOB write from Rust's safe panic |
| Extraction to Lean via Charon/Aeneas (`verify/`) | done: the faithful leaf reaches Lean with no `sorry` in the generated code, no union blocker |
| Formal proof of properties (`verify/lean/NoPanic.lean`) | in progress, see below |

## Verification status (proofs)

Two theorems are stated against the real extracted `parse` function.

**(B) Total safety on all input** — every outcome is `ok` / controlled `fail` /
nontermination, never an undefined-behaviour outcome.
**Proved, `sorryAx`-free.**

**(A) No-panic on well-formed input** — under the parser's own validation
invariants (`WellFormed`), `parse` returns `ok` without panicking. Panicking on
malformed input is the intended safe behaviour and is not ruled out.
**Stated; proof in progress.** (A) decomposes into termination, in-bounds reads,
sized writes (the CVE-2024-53104 core), and no-overflow arithmetic.

### The counting invariant (CVE-2024-53104 core) — proved

The heart of (A) is the relationship between the counting pass (which sizes the
allocation) and the parse pass (which writes into it). Its violation is exactly
CVE-2024-53104. This block is fully machine-checked, `sorryAx`-free:

| Lemma | What it establishes |
|---|---|
| `u32_add_ge_left`, `u32_add_shift` | checked-U32-add arithmetic facts |
| `loop_ok_inv` | reusable partial-correctness loop-invariant principle for Aeneas-extracted loops |
| `counting_monotone` | a successful counting run never decreases a counter |
| `counting_step_replay` / `counting_step_replay_gen` | one loop-body step replays from shifted counters, under per-step no-overflow bounds |
| `counting_replay` | whole-loop replay: the parse pass follows the counting pass's path, counters shifted |
| `counting_additive` | the counting pass is additive over the buffer (the fact (A) consumes) |

All show axioms `[propext, Classical.choice, Quot.sound]` only.

### Remaining for (A)

| Piece | Status | Note |
|---|---|---|
| `counting_additive` and its supporting block | proved | above |
| `parse_no_div` (termination / div-freeness) | `sorry` | a loop-termination argument; `loop_ok_inv` should carry it |
| `frame_loop_invariant` (writes stay in the allocated `Vec`) | `sorry` | consumes the counting block above |
| assembling (A) from the pieces | not started | reads via `WellFormed`, arithmetic via the overflow bounds |

## Known hard problems

- **Reasoning about Aeneas-extracted loops.** Aeneas lowers loops to Lean
  `partial_fixpoint` combinators, not ordinary recursive definitions, so naive
  structural induction does not apply. The working idiom here is a
  partial-correctness loop invariant (`= ok -> post`, admissible because it holds
  vacuously at `div`), packaged as `loop_ok_inv` and reused across the counting
  block. The same principle is expected to carry `parse_no_div` and
  `frame_loop_invariant`.
- **Compiler-dependent UB at one arithmetic site.** The differential equivalence
  holds against the clang-compiled C; a gcc build resolves the one
  signed-overflow site differently, which simply re-proves it is undefined
  behaviour. The lasting fix belongs upstream in the kernel C (compute in a wide
  enough type). Documented in `rust/README.md` and `fuzz/RESULTS.md`.

## Direction

- Close (A): `parse_no_div`, `frame_loop_invariant`, then assemble.
- Apply the same loop (extract -> rewrite -> differential fuzz -> selective proof)
  to further untrusted-input parsers; the fuzzing harness and the loop-reasoning
  infrastructure are built to be reused.
- Engage kernel maintainers with concrete results on their subsystems rather than
  with proposals; a proved property about a real CVE class is the useful artifact.

## How the AI tooling is used, and why it is trustworthy

Proofs are produced with AI assistance (an automated prover and a coding agent)
but every proof is checked by the Lean kernel, and every "proved" claim here is
backed by a `#print axioms` audit showing no `sorryAx` and no non-standard
axioms. The AI proposes; the kernel decides. Along the way the prover also
disproved an earlier, too-strong statement of the counting lemma (an unbounded
accumulator that could overflow), which is the intended behaviour: a false
"obvious" property is caught, not waved through.
