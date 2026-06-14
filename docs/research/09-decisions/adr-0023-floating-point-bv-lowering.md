# ADR-0023: Floating-Point (IEEE 754) as Bit-Vector Formula Builders

Status: accepted (non-arithmetic core implemented 2026-06-14; arithmetic deferred)
Date: 2026-06-14

## Context

The `FloatingPoint` theory (QF_FP) is a Z3/cvc5 parity gap and matters directly
for the program-verification north star: real programs compute on `float`/
`double`. An IEEE 754 value of format `(eb, sb)` is a finite `eb + sb`-bit pattern,
so the theory is decidable by bit-blasting — exactly the finite-domain style the
stack already uses for QF_BV.

The question is how to introduce it without (a) a premature first-class
`Sort::Float` (the ~18-file IR cascade ADR-0022 measured), or (b) the large,
correctness-critical rounding machinery that arithmetic (`fp.add`/`mul`/`div`/
`sqrt`/`fma`/`roundToIntegral`) requires.

## Decision

**Introduce floating point the way enums/records were introduced (ADR-0008): as
lowering helpers over bit-vectors, with no new IR sort. Ship the *non-arithmetic
core* (classification, sign ops, equality, ordering) first; defer rounded
arithmetic to a later, separately-validated layer.**

Concretely (`axeyum-solver`'s `fp` module):

- A value of format `(eb, sb)` is a `BitVec(eb + sb)`. `FloatFormat` carries the
  widths; `F16`/`F32`/`F64` are provided. Layout MSB→LSB: sign(1), biased
  exponent(`eb`), trailing significand(`sb − 1`).
- Builders construct bit-vector/Boolean **formulas** over such terms:
  `is_nan`/`is_infinite`/`is_zero`/`is_normal`/`is_subnormal`/`is_negative`/
  `is_positive`, `abs`/`neg`, `eq`, and `lt`/`leq`/`gt`/`geq`.
- Semantics follow SMT-LIB/IEEE 754: `fp.eq` is **not** bit equality
  (`NaN ≠ NaN`, `+0 = +0 = −0`); `fp.lt`/`leq` order by value (NaN unordered,
  `±0` equal); `isNegative`/`isPositive` exclude NaN and zeros. Ordering uses the
  standard monotone-key transform (flip all bits if sign set, else set the sign
  bit; then unsigned `<`), with the `±0` case handled explicitly.

Because the result is ordinary QF_BV, **solving and model replay reuse the
existing sound, replayed bit-vector path with no changes** — an FP `sat` model is
a bit-vector model, replayed against the original term by the ground evaluator.

## Evidence

- Z3/cvc5 decide QF_FP by bit-blasting; the bit-level encodings of
  classification/comparison are standard and rounding-free.
- The enum/record helpers (ADR-0008) already established the "finite theory as
  BV lowering, no new sort" pattern; FP predicates/comparisons fit it exactly.
- Tests (`tests/fp.rs`): concrete single-precision patterns through the ground
  evaluator (NaN/inf/zero classification, `+0 = −0`, `NaN ≠ NaN`, `1.0 < 2.0`,
  `−2.0 < 1.0`, `¬(−0 < +0)`, NaN unordered, `abs(−2.0) = 2.0`, `neg(2.0) = −2.0`,
  sign predicates), plus two symbolic queries through the solver:
  `fp.lt(x, x)` is **unsat** (irreflexivity over a free 32-bit `x`) and
  `1.0 < x` is **sat**.

## Alternatives

- **First-class `Sort::Float` now.** Deferred: it forces the multi-crate `Sort`
  cascade before the theory has proven its shape; the BV-lowered helpers deliver
  the capability immediately and a first-class sort can follow (its own ADR) if
  sort-level typing (distinguishing a `float32` from an arbitrary 32-bit vector)
  is wanted.
- **Do arithmetic now.** Rejected for this slice: correct rounding (all five
  modes, subnormals, NaN propagation, sticky/guard/round bits) is large and
  error-prone; shipping it unvalidated would risk wrong `sat`/`unsat`. The
  non-arithmetic core is independently useful (classification, comparison,
  sign) and a sound foundation.

## Consequences

- **Easier:** any QF_FP query restricted to predicates/comparisons/sign decides
  today, soundly, via the BV backend, with replayable models — directly useful
  for program paths that branch on FP classification/comparison.
- **Harder / next:** rounded arithmetic (`add`/`sub`/`mul`/`div`/`fma`/`sqrt`/
  `roundToIntegral`) and conversions (`fp ↔ real/int`, `fp ↔ fp`) are the next
  layer; each rounding mode needs careful guard/round/sticky-bit encoding and its
  own differential validation. Until then those operations are simply absent.
- **Watch:** values are typed as `BitVec`, so the format is a caller convention,
  not sort-checked; a first-class `Sort::Float` is the upgrade path if that
  looseness bites.
- **Revisited when:** a workload needs FP arithmetic (then the rounded-arithmetic
  ADR), or sort-level FP typing is wanted (then the `Sort::Float` ADR).
