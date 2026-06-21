# ADR-0045: Arbitrary-precision (bignum) on the algebraic path — `num-bigint`/`num-rational`, feature-gated

Status: accepted
Date: 2026-06-21

## Context

[ADR-0044](adr-0044-algebraic-field-arithmetic.md) gave `RealAlgebraic` exact
field arithmetic (`α+β`, `α·β`) via the univariate resultant + Sturm single-root
isolation, on `i128` coefficients with overflow-→-decline. That ceiling bites
*immediately* on the multivariate ladder: a Sylvester resultant of two
degree-`m`/`n` polynomials is an `(m+n)`-square determinant whose **intermediate**
entries are products and sums of the input coefficients — they overflow `i128`
long before the *final* minimal polynomial does. Concretely, combining two
modest algebraic numbers can blow the `i128` intermediate even though the answer
is a small polynomial (`√2 + √3 ⇒ x⁴ − 10x² + 1`). Every such case currently
declines to `unknown`. The [NRA durability plan](../05-algorithms/nra-cad-nlsat-plan.md)
step 2 calls for arbitrary precision on the algebraic path so the decline becomes
a *decision* — and it is the genuine prerequisite for a *useful* CAD/nlsat engine
(step 3), whose projection resultants overflow `i128` on nearly all real input.

Two constraints shape the decision. (1) The default build must stay free of any
C/C++ dependency (a hard rule) — so the bignum library must be **pure Rust** and
pass `cargo deny`. (2) The core `Rational` is `i128` and is used pervasively (LRA
tableau, models, evaluation) where it must stay fast and `Copy`-cheap — bignum
must **not** infect that type. Arbitrary precision belongs *only* on the
algebraic path.

## Decision

Introduce **`num-bigint` + `num-rational`** (pure Rust, MIT/Apache — clean under
`cargo deny`) as **optional** dependencies of `axeyum-ir` behind a **`bignum`
feature, off by default**. `axeyum-solver` enables `axeyum-ir/bignum`, so the real
solver always has arbitrary precision while a minimal non-NRA embedder of
`axeyum-ir` stays dependency-free. The core `i128` `Rational` is untouched.

### Scope of this slice (intermediate bignum, `i128` storage)

Bignum covers the **intermediate** resultant + squarefree-part + Sturm isolation
*computation*. `RealAlgebraic`'s stored representation stays `Vec<i128>` poly +
`i128`-`Rational` interval (no `Value`-enum change, no match-arm churn). The flow:

1. Run field arithmetic on the `i128` fast path (unchanged).
2. On its overflow `None`, with `bignum` enabled, re-run the *same algorithm*
   (resultant → squarefree → Sturm single-root identification) over
   `BigRational`.
3. Convert the final defining polynomial and isolating interval back to
   `i128`/`Rational`. If they fit, build the `RealAlgebraic`; **if the final
   result genuinely exceeds `i128`, decline gracefully (`None`)** — a
   bignum-backed `Value::RealAlgebraic` representation is a deliberately-deferred
   later slice.

This removes the common "intermediate overflows, answer is small" decline with
the smallest sound footprint. The `i128` path stays byte-for-byte behaviorally
identical when the feature is off.

### One isolation implementation (soundness)

Isolation is soundness-critical (a divergence is a wrong-root risk), so the
preferred realization keeps **one** implementation: the `poly.rs` primitives are
generic over an exact-ordered-field scalar trait, instantiated at both the `i128`
`Rational` (the solver's existing NRA path + the fast path) and `BigRational` (the
overflow retry). A focused *duplicated* bignum module is admissible only with a
**differential test** pinning the two paths to the identical minimal polynomial on
small inputs — the genericized single-implementation route is the default for
exactly this reason.

## Evidence

- `crates/axeyum-ir/tests/real_algebraic_field_bignum.rs` (`cfg(feature =
  "bignum")`): a degree-3/4 combination whose `i128` intermediate overflows
  (i128 path → `None`) now decides under bignum and replays
  (`sign_at(min_poly) == Zero`); `√2+√3` / `√2·√3` still yield the *identical*
  `i128` minimal polynomials (`x⁴−10x²+1` / `x²−6`); a combination whose final
  min-poly exceeds `i128` still declines (`None`, no panic).
- Both configs green: `cargo test -p axeyum-ir` (feature off — `i128`-decline
  unchanged) and `--features bignum`, plus `cargo test -p axeyum-solver` (feature
  on via the solver). `cargo deny check` confirms the new deps' licenses.

## Alternatives

- **Make the core `Rational` bignum.** Rejected: it is on the hot path of every
  LRA solve and model; arbitrary precision there is a large, unwarranted slowdown
  for a feature exercised only by the algebraic path.
- **Bignum `Value::RealAlgebraic` now (full ceiling removal).** Deferred: it
  changes the `Value` representation and every exhaustive match across the IR /
  rewrite / solver crates. This slice delivers the common-case win first with no
  enum change; the full representation change is a clean follow-on.
- **A hard (non-gated) bignum dependency on `axeyum-ir`.** Rejected: it is pure
  Rust and would not violate the no-C/C++ rule, but it needlessly pulls bignum
  into minimal non-NRA embeddings of the IR. The `bignum` feature, enabled by the
  solver, keeps both the leaf minimal *and* the product fully precise. Both
  configs are covered by the gate (off: `-p axeyum-ir`; on: `--features bignum`
  and `-p axeyum-solver`), so neither path bit-rots.
- **`dashu` / `malachite`.** `malachite` is LGPL (a `cargo deny` licensing risk);
  `dashu` is viable but `num-bigint`/`num-rational` are the mature, ubiquitous,
  MIT/Apache choice with `BigRational` built in.

## Consequences

- Easier: the common multivariate combinations decide instead of declining; the
  CAD/nlsat engine (step 3) can be built on a precision base that actually
  computes its projection resultants rather than overflowing them.
- Bounded: the final-result-exceeds-`i128` case still declines (sound) until the
  deferred bignum-`Value` slice; the bignum retry remains degree/round-bounded →
  graceful `unknown`, never OOM.
- Structural: `axeyum-ir` gains its first (optional, pure-Rust) dependency,
  scoped to the algebraic path by the `bignum` feature; the core `i128`
  `Rational` and every non-NRA fragment are unaffected.
