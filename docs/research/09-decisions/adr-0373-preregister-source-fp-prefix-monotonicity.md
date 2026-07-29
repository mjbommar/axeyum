# ADR-0373: Preregister source FP prefix monotonicity refutation

Status: accepted

Date: 2026-07-27

## Context

ADR-0372 rejects serial Boolean branch splitting on the selected
`prefix_sum_klee_bug_double/query.17.smt2`: two branches are cheap, but the FP
ordering branch takes about 2.893 s and makes the split slower than the
1.70--1.80 s monolithic baseline. The source obligation is nevertheless simple:
RNE additions extend a prefix with nonnegative, non-NaN values, and the final
assertion asks one such prefix to become NaN or decrease.

That semantic shape is absent from solver IR. SMT-LIB FP arithmetic is eagerly
expanded into BV formulas during parsing; the selected 55-line source becomes a
3,856-node IR DAG and then a 318,370-node AIG. Reverse-matching those generated
circuits would be brittle. Introducing first-class FP arithmetic operators would
change the public IR, evaluator, lowering, and evidence boundaries and is not
justified by one measured family.

The parser already retains conservative raw-source side facts for FP trust usage
and exact string contradictions. A source-only FP fact can preserve the semantic
boundary without changing public term operators or the default pure-Rust build.

## Decision

Add one fail-closed source refuter for a non-incremental, macro-free conjunction.
It normalizes bounded `let` bindings and reasons only about exact S-expression
identity under RNE:

1. asserted `not(fp.isNaN x)` records `non_nan(x)`;
2. asserted `not(fp.lt x +zero)` plus `non_nan(x)` records `nonnegative(x)`;
3. asserted `not(fp.lt x y)` plus non-NaN operands and `nonnegative(y)` records
   `nonnegative(x)`;
4. `s = fp.add RNE x y` with both operands non-NaN and nonnegative records
   `non_nan(s)`, `nonnegative(s)`, `not_lt(s,x)`, and `not_lt(s,y)`; and
5. an asserted negation of a two- or three-leaf conjunction is contradictory
   only when every leaf is independently re-derived as `not(fp.isNaN t)` or
   `not(fp.lt x y)`.

Rule 4 is the sole semantic theorem: correctly rounded IEEE addition is monotone,
and the exact sum of two nonnegative non-NaNs is nonnegative and cannot be NaN.
The exact leaf bound is a pre-acceptance correction from the selected sources:
the double row's final counterexample has three leaves, while both float rows
have two. The proposal admits only literal RNE (`RNE` or
`roundNearestTiesToEven`), exact same-format zero syntax, 512 normalized source
nodes per expression, normalization depth 64, and 32 fixpoint rounds. Any
unsupported Boolean shape, scope command, macro, symbolic mode, format
ambiguity, normalization cap, or unproved leaf declines with no solver behavior
change.

The parsed script records one Boolean side fact. The ordinary single-query
SMT-LIB solver may return UNSAT from that fact before BV SAT search. Direct arena
APIs and incremental scripts are unchanged. Evidence production remains
fail-closed: unless a separate checkable certificate is added, the existing
Fpa2Bv trust step stays uncertified.

## Acceptance gate

- Parser tests cover the exact double and float prefix shapes, operand-order and
  RNE spelling, and rejection of RTN, a negative addend, missing non-NaN facts,
  disjunction, macros, incremental scopes, post-query assertions, and over-cap
  `let` normalization.
- An independent `rustc_apfloat` FP8 E5M2 sweep validates the RNE monotonicity
  theorem for every 65,536 operand pair, including NaNs, infinities, subnormals,
  and signed zeros.
- The three selected prefix-sum rows remain declared/Z3-matching UNSAT and each
  completes with repeatable headroom below 250 ms at a two-second product limit;
  the double row must materially beat the immutable 1.70--1.80 s baseline.
- The frozen 108-family process sample has zero wrong verdicts and no retained
  decision loss; the binary79 eight-row and ESBMC 34-row gates retain all
  decisions.
- Focused parser/solver tests, warning-denied Clippy, fmt, and links pass. Any
  wrong verdict, admitted near miss, theorem-oracle disagreement, material
  retained loss, or failure to beat the selected row rejects the candidate.

## Acceptance result

Accepted. Five release repetitions per selected row returned declared UNSAT in
less than the timer's 10 ms resolution. Three immutable-baseline repetitions
had medians of 1.61 s for the double row, 0.44 s for the bug-float row, and
0.16 s for the no-bug-float row.

The frozen 108-family process diagnostic returned 90 correct, zero wrong, 17
unknown, and one five-second process timeout when run serially with a two-second
solver budget. A separate no-loss comparison ran the immutable baseline on all
18 candidate nondecisions; none was baseline-decided. This avoids attributing
host-sensitive aggregate timeout variation to the rule. The retained binary79
gate is 8/8 and the serial ESBMC gate is 34/34, with every result matching its
declared status.

All parser and SMT-LIB front-door tests pass, including exact two- and
three-leaf positive shapes and fail-closed near misses. The independent FP8 E5M2
sweep covers all 65,536 pairs. Warning-denied Clippy passes for `axeyum-smtlib`,
`axeyum-solver`, and `axeyum-fp`; formatting and repository gates are recorded
in the result note.

## Alternatives

### Reverse-match the lowered FP circuits

Rejected. The relevant source terms are hundreds of thousands of generated AIG
nodes by the SAT boundary; recognizing one current encoding would couple
semantics to incidental circuit layout.

### Add first-class FP arithmetic operators to IR

Deferred. That is the principled long-term route for theory lemmas and proof
objects, but it changes public builders, evaluation, lowering, rewriting, and
evidence. This measured family does not yet justify that foundational expansion.

### Keep tuning or splitting SAT

Rejected by the exact measurements: BatSat option sweeps were net-neutral,
inprocessing/native search are slower, and ADR-0372 shows serial splitting makes
the hard ordering obligation worse.

## Consequences

Generated nonnegative FP prefix checks can bypass an avoidable BV
mountain while every unrecognized shape retains the existing solver route. The
result is a trusted source semantic refutation, not a general FP proof system,
not a public IR operator, and not evidence that arbitrary FP addition constraints
are solved symbolically. Wider modes, subtraction, mixed signs, algebraic
rewrites, or checkable proof reconstruction require separate decisions.
