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
  `is_positive`, `abs`/`neg`, `eq`, `lt`/`leq`/`gt`/`geq`, and `min`/`max`. The
  last two are the rounding-*free* part of FP arithmetic: they return one operand
  unchanged, so they are exact and correct-by-construction (NaN propagates the
  other operand; opposite-sign zeros take a deterministic SMT-allowed choice).
- Semantics follow SMT-LIB/IEEE 754: `fp.eq` is **not** bit equality
  (`NaN ≠ NaN`, `+0 = +0 = −0`); `fp.lt`/`leq` order by value (NaN unordered,
  `±0` equal); `isNegative`/`isPositive` exclude NaN and zeros. Ordering uses the
  standard monotone-key transform (flip all bits if sign set, else set the sign
  bit; then unsigned `<`), with the `±0` case handled explicitly.

Because the result is ordinary QF_BV, **solving and model replay reuse the
existing sound, replayed bit-vector path with no changes** — an FP `sat` model is
a bit-vector model, replayed against the original term by the ground evaluator.

**Rounded arithmetic — constant folding first (`add_rne`/`sub_rne`/`mul_rne`/
`div_rne`/`sqrt_rne`).** For *constant* F32/F64 operands, rounded arithmetic is
computed by delegating to the platform's native IEEE 754 arithmetic (which is
round-nearest-even and correct), so the folds are **sound by construction** with
no hand-written rounding, and compose with the symbolic predicates (e.g.
`fp.lt(1.0 + 2.0, x)` folds the add to `3.0` then solves the comparison). This
native arithmetic is *also the differential oracle* for the future symbolic
bit-blaster: validate the blaster against it (exhaustively on small formats)
before trusting it for `unsat`. Symbolic FP arithmetic and non-default rounding
modes are deliberately **not** done yet — a bit-blasted rounding encoding cannot
be replay-guarded (replay would only re-check the encoding), so a subtle bug is a
wrong `unsat`; it needs the validation harness, not a rushed encoding.

**Rounding keystone (`round_to_format`).** The hardest part of FP arithmetic is
correct rounding. `round_to_format(eb, sb, v: f64)` rounds an exact `f64` to the
nearest `(eb, sb)` value (round-nearest-ties-to-even), via the exact integer
significand `m·2^e` decoded from `v` with explicit guard/round/sticky, handling
normal/subnormal/overflow. It is **validated against native `f32`** —
`round_to_format(8, 24, v) == (v as f32).to_bits()` — over specials, a wide
structured battery, and ~200k pseudo-random `f64` patterns (subnormals, ties,
overflow). This is the algorithm a symbolic bit-vector rounding circuit must
encode; having it implemented and validated in concrete arithmetic de-risks the
symbolic bit-blaster (which becomes a faithful BV transcription of a checked
reference, re-validated differentially against this oracle).

**Symbolic multiplication (`fp::mul`).** The first *symbolic* rounded operation:
an IEEE 754 `fp.mul` bit-blaster built from the validated primitives — unpack
(subnormal-aware), significand `bv_mul` + exponent add, the round-and-pack core
`pack_value` (= `pack_params` + `round_variable` + `count_leading_zeros`), then
NaN/`0·∞`/∞/zero muxing. A pure bit-vector formula, so it solves and replays on
the existing path with no new machinery.

**Assurance: validated, not proven** (cf. ADR-0007 for BatSat's UNSAT). Every
sub-circuit is checked against native arithmetic, and `mul` itself is
differentially validated against native `f32` over structured values
(specials/subnormals/normals, products that overflow and underflow) plus a
pseudo-random sweep. This is the same assurance basis production bit-blasters
(Z3/cvc5/bitwuzla) rest on — strong, but not a machine-checked proof. A
formally-verified blaster, or a relaxation+replay route via an IR `fp` op, could
raise assurance later if a workload demands it.

**Symbolic addition (`fp::add`).** Exact-alignment adder: both significands are
shifted to the common (minimum) exponent and added/subtracted *exactly* (no
sticky, hence borrow-free), then rounded by `pack_value`, with NaN / `∞ + −∞` /
`∞` / signed-zero muxing. Validated against the `round_to_format` reference
(applied to the exact f64 sum) for **F16**. Exact alignment needs
`sig_bits + (2^exp_bits − 3) + 2 ≤ 128`, which holds for F16 only; F32/F64 return
`InvalidWidth`.

**Width cap and the bounded-width path.** Bit-vectors are capped at
`MAX_BV_WIDTH = 128` (`Value::Bv` is a `u128`). The current `mul` (`3·sb+4`) and
`add` (exact alignment) intermediates exceed this for F64 (and F32 for add), so
those formats error cleanly rather than return a wrong result. A **bounded-width
encoding** (cap the alignment/normalization window and fold the rest into a
sticky bit, `W ≈ 2·sb + guard ≤ 128`) is the single piece that lifts both `mul`
and `add` to F32/F64; the sticky/borrow handling is its careful part. It is the
next FP unit, after which `div`/`sqrt`/`rem` and non-default rounding modes
follow.

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
