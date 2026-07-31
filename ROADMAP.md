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
**In progress.** (A) decomposes into termination, in-bounds reads, sized writes
(the CVE-2024-53104 core), and no-overflow arithmetic. Large parts are proved;
the remainder is reduced to a named functional-correctness core (below).

### Proved, `sorryAx`-free

Everything below is machine-checked with axioms `[propext, Classical.choice,
Quot.sound]` only.

**The counting invariant (CVE-2024-53104 core).** The relationship between the
counting pass (which sizes the allocation) and the parse pass (which writes into
it); its violation is exactly CVE-2024-53104.

| Lemma | What it establishes |
|---|---|
| `u32_add_ge_left`, `u32_add_shift` | checked-U32-add arithmetic facts |
| `loop_ok_inv` | reusable partial-correctness loop-invariant principle for Aeneas-extracted loops |
| `counting_monotone` | a successful counting run never decreases a counter |
| `counting_step_replay` / `counting_step_replay_gen` | one loop-body step replays from shifted counters, under per-step no-overflow bounds |
| `counting_replay` | whole-loop replay: the parse pass follows the counting pass's path, counters shifted |
| `counting_additive` | the counting pass is additive over the buffer (the fact (A) consumes) |

**Termination infrastructure and the structurally-terminating loops.**

| Lemma | What it establishes |
|---|---|
| `loop_no_div` | reusable measure-based termination principle for Aeneas loops (the div-only counterpart of `loop_ok_inv`) |
| `guid_eq16_loop_no_div`, `uvc_format_by_guid_loop_no_div`, `parse_loop3_no_div`, `uvc_parse_frame_loop_no_div`, `parse_loop2_no_div` | div-freeness for the 5 structurally-terminating loops |
| the `*_ne_div` toolkit + `hd_ne_div` tactic | reusable div-freeness discharge for binds, indexing, iterators, and arithmetic |

### The remaining core, named (stated, proofs pending)

The rest of (A) — the 6 buffer-walk loops' termination, the write-bounds
invariant, and the final assembly — all reduce to four stated lemmas. Together
they are the positional-walk functional-correctness core: they relate
`WellFormed`'s abstract descriptor tiling to the parser's concrete `pos`-walk.

| Lemma | What it will establish | Feeds |
|---|---|---|
| `descriptor_walk_step` | each visited position is a descriptor boundary with `bLength >= 1`, and stepping by it stays in-buffer | `parse_loop0` termination + in-bounds reads |
| `uvc_parse_frame_walk` | a successful `uvc_parse_frame` consumes `ret >= 1` bytes and lands on a boundary | `uvc_parse_format_loop0..3` termination |
| `uvc_parse_format_walk` | same for `uvc_parse_format` (`ret` = exact bytes consumed, lands on a boundary) | `parse_loop1` termination + `frame_loop_invariant` room |
| `format_writes_le_count` | writes are a subset of what the counting pass tallied over the consumed block (conjunct iii) | `frame_loop_invariant` + the final (A) write-bounds |

`parse_no_div`, `frame_loop_invariant`, and the assembly of (A) are stated and
consume the four lemmas above. Proving those four is the next milestone.

## Known hard problems

- **Reasoning about Aeneas-extracted loops.** Aeneas lowers loops to Lean
  `partial_fixpoint` combinators, not ordinary recursive definitions, so naive
  structural induction does not apply. Two reusable principles handle this: a
  partial-correctness invariant (`= ok -> post`, admissible because it holds
  vacuously at `div`), packaged as `loop_ok_inv`; and a measure-based
  termination principle, `loop_no_div`. Both are proved and reused across the
  work above.
- **The positional-walk invariant is the hard core.** The four stated lemmas are
  functional correctness of the buffer walk: that the parser's `pos`-walk visits
  exactly the descriptor boundaries `WellFormed` describes, and that `ret` equals
  the bytes consumed. This is the substantial remaining proof work, and it is the
  same core whether approached via termination or via write-bounds.
- **Compiler-dependent UB at one arithmetic site.** The differential equivalence
  holds against the clang-compiled C; a gcc build resolves the one
  signed-overflow site differently, which simply re-proves it is undefined
  behaviour. The lasting fix belongs upstream in the kernel C (compute in a wide
  enough type). Documented in `rust/README.md` and `fuzz/RESULTS.md`.

## Direction

- Close (A): prove the four walk-invariant lemmas, from which `parse_no_div`,
  `frame_loop_invariant`, and the assembly follow.
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
