# Glaurung correctness-oracle case study

Status: measured methods result
Last updated: 2026-07-20

## Purpose

Consolidate the consumer soundness defects exposed during the Axeyum/Glaurung
integration into one reviewer-auditable methods result. The key result is not
that one solver disagreed with another. It is that a strict typed boundary,
fail-closed model handling, original-term replay, and independent oracles made
invalid consumer states visible before they could be counted as solver work or
used to steer symbolic execution.

## Scope

In scope:

- the empty-model steering, declared extension-width, and declared concat-width
  defects found in Glaurung;
- the separate 128-bit truncation defect in Glaurung's native Z3 adapter;
- the exact Axeyum regression and multi-oracle evidence that preserves those
  boundaries; and
- the claim limits needed to keep the result scientifically honest.

Out of scope:

- claiming that differential agreement proves solver correctness;
- attributing consumer-adapter defects to the Z3 solver core;
- treating malformed consumer metadata as valid-formula fuzz coverage; and
- reviving the retired warm-Axeyum versus fresh-Z3 speed headline.

## What the integration found

| Defect | Invalid state | Fail-closed signal | How permissive handling masked it | Fix and regression owner |
|---|---|---|---|---|
| Empty-model steering | `eval_concrete` and `concretize_addr` evaluated an empty/default model after UNSAT, Unknown, unavailable, or failed checks. The resulting zero could steer exploration. | Exact ordered replay exposed a model read not justified by a SAT result. This is a consumer state-machine failure, **not** an `IrError` or a strict-sort failure. | Default values allowed the path to continue, making the invalid choice look like an ordinary model decision. | Glaurung `57c6c092` requires an immediately preceding SAT result and tests that UNSAT produces neither a value nor a concretization assertion. Axeyum's named control keeps contradictory UNSAT model-less while allowing a legitimate empty model for a closed SAT formula. |
| Declared extension width | A zero/sign-extension node declared a 32-bit source around a 64-bit child and a 64-bit target. Applying the declared extension directly would produce 96 bits. | Axeyum's strict construction reaches `operands must share a sort: (_ BitVec 96) vs (_ BitVec 64)` when the malformed result meets its declared 64-bit context. | Glaurung's Z3 AST adapter implicitly normalized the child to the declared source width. The malformed metadata therefore did not fail at the boundary. | Glaurung `d450d2a7` explicitly coerces the child to the declared source width in the renderer and both native adapters. The Axeyum fuzzer retains both the exact negative and the normalized positive control. |
| Declared concat width | A one-bit `setcc` child was recorded as an eight-bit low concat half. With a 56-bit high half, ignoring the metadata constructed 57 bits while the consumer treated the node as 64 bits. | The next slice fails exactly as `extract [63:8] out of range for width 57`. | Later Z3 coercion accepted the malformed child and shifted the high half by one bit rather than eight, changing the represented program value. | Glaurung `d60ed0f5` coerces both children to their declared half-widths at the SMT-LIB, Z3, and Axeyum boundaries. The archived split corpus and the Axeyum exact negative/normalized positive controls remain standing regressions. |
| Native Z3 wide-value truncation | Glaurung narrowed 128-bit constants and projected models through `u64`, silently dropping high bits. This was a valid-formula adapter boundary, not malformed IR. | A W128 control pins bit 100 and requires exact full-width model replay through the linked adapter. | Z3 solved the well-sorted but truncated formula supplied by the adapter; backend agreement could therefore grade the wrong query. | Glaurung `4ae96cfd` constructs and parses full-width numerals. Axeyum's named W128 control permanently checks the linked adapter boundary. |

The distinction in the first row is load-bearing. “Strict typing caught three
bugs” is useful shorthand, but it is not exact: strict width/sort checking
directly exposed the extension and concat defects; fail-closed result typing and
ordered model-read replay exposed empty-model steering. The paper should call
the combined method a **strict typed and replay-checked consumer boundary**.

## Standing Axeyum evidence

[`bv_differential_fuzz.rs`](../../../crates/axeyum-solver/tests/bv_differential_fuzz.rs)
separates invalid consumer contracts from well-typed solver fuzzing:

- exact negative controls reject malformed concat, extension, and over-wide
  constants before solving;
- normalized positive controls cover the intended concat and extension
  semantics;
- contradictory UNSAT has no model payload, while a closed SAT formula may
  legitimately have an empty model;
- the W128 control crosses the actual linked Z3 adapter and replays the high
  bit; and
- every accepted Axeyum SAT result in the generated lane is replayed on the
  untouched original assertions.

[ADR-0224](../09-decisions/adr-0224-standing-qfbv-multi-oracle-fuzz.md) records
4,000/4,000 Axeyum/Z3 agreements, 250/250 cvc5 samples, and 1,487 original-model
replays with zero disagreement or skip. [ADR-0237](../09-decisions/adr-0237-independent-edge-qfbv-four-oracle-fuzz.md)
adds two untouched uniform seed ranges and one edge-directed range: all 12,000
rows decide and agree in Axeyum, Z3, cvc5, and Bitwuzla; all 4,471 Axeyum SAT
models replay; and every declared width, operator class, and semantic-corner
family is observed. The retained [initial report](../../../bench-results/qfbv-multi-oracle-fuzz-20260717/README.md)
and [independent four-oracle report](../../../bench-results/qfbv-four-oracle-independent-20260718-600s/README.md)
carry exact revisions, binary hashes, counters, failed attempts, and claim
limits.

## Methods contribution

The reusable method is a layered gate, not “compare with Z3”:

1. Reject malformed typed construction with actionable operation/sort/width
   diagnostics. Never normalize it inside `axeyum-ir`.
2. Represent SAT, UNSAT, Unknown, and operational errors distinctly. Only SAT
   carries a model that may authorize an exploration choice.
3. Replay SAT models against original Axeyum terms, then replay consumer
   witnesses in the program semantics where available.
4. Compare valid formulas with multiple independent implementations. A parser,
   process, timeout, or protocol failure is not an agreement or a skip in a
   publication gate.
5. Preserve the malformed consumer states as named negative controls instead
   of coercing them into the valid-formula generator.
6. Count decisions, nondecisions, errors, replay, and exact work before timing.
   Fast failure is not solver speed.

This is consistent with Axeyum's identity: untrusted fast search, trusted small
checking. The external solvers are differential witnesses, not the trusted
kernel, and agreement remains bounded empirical evidence.

## Design implications

- Keep ordinary IR builders strict. Width adaptation remains explicit through
  `TermArena::coerce_to` at consumer-owned boundaries.
- Treat the exact `IrError` wording pinned by the named controls as integration
  tooling: it must retain the operation, offending bounds/sorts, and widths.
- Never translate Unknown or an operational error into UNSAT or a default
  model.
- Keep original terms and model/proof lift maps available through every
  optimization.
- Extend correctness evidence with independent seeds, semantic-corner counts,
  proof coverage, and source-level witness replay rather than merely repeating
  the same oracle pair.

## Claim limits and open work

- The 12,000-row four-oracle campaign is bounded by its generators, depths,
  widths, and resource limits. It is not a completeness proof.
- The empty-model and malformed-width cases are consumer regressions; a
  well-typed formula fuzzer cannot honestly claim to rediscover them.
- The wide-value defect is in Glaurung's Z3 adapter, not the Z3 solver core.
- Broader labeled real-world recall, nontrivial proof prevalence/cost, and
  whole-CFG witness composition remain open publication work.

## Source pointers

- Glaurung reviewer checklist:
  `docs/axeyum-integration/benchmark/REVIEWER-CHECKLIST.md`
- Glaurung decision log: ADR-016, ADR-024
- Glaurung capture diary: ordered-replay findings around revisions `57c6c092`,
  `d450d2a7`, and `d60ed0f5`
- Axeyum ADR-0213, ADR-0224, ADR-0225, ADR-0234, and ADR-0237
- [`Differential testing`](differential-testing.md)
- [`Evidence and checking`](evidence-and-checking.md)
