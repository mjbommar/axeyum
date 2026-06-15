# ADR-0028: A software-float oracle for validating wide-format FP arithmetic

Status: accepted (implemented for F128 add/mul/div/fma, 2026-06-14)
Date: 2026-06-14

## Context

The floating-point arithmetic circuits (`add`/`mul`/`div`/`sqrt`/`fma`/`rem`/
conversions in `axeyum-fp`) are **validated, not proven** (ADR-0023): each is a
bit-vector formula builder whose correctness rests on a differential sweep
against a trusted oracle. To date that oracle has been the platform's native
IEEE types — `f32` and `f64` — which bounds validation to formats representable
in `f64` (`exp ≤ 11`, `sig ≤ 53`).

Two facts make this binding now:

1. **There is no first-class FP op in the IR.** FP arithmetic exists *only* as a
   lowered bit-vector circuit; the ground evaluator evaluates that same circuit.
   So **model replay cannot catch a wrong FP circuit** — the solver and the
   replay check share the bug and agree. The *only* assurance that an FP
   arithmetic result is correct is the differential validation of its circuit
   against an independent oracle. (This was made concrete on 2026-06-14: a
   `sconst` sign-extension bug made the 164-bit symbolic F64 `fma` circuit
   mis-evaluate `fma(2,3,1)→0`; native `f64::mul_add` caught it, replay did not.)

2. **Wide bit-vectors removed the width ceiling** (`MAX_BV_WIDTH = 1<<16`), so
   F64 `fp.fma` (164-bit intermediate) and F128 arithmetic (200–344-bit
   intermediates) are now *constructible*. F64 is validated against native
   `f64`. **F128 has no native oracle on stable Rust** (`f128` is unstable), and
   the in-tree exact-rational helpers cannot stand in: `Rational` is `i128`-backed
   and `round_rational_to_format` caps numerators at 53 significant bits — far
   short of F128's 113-bit significand.

Consequently F128 (and any format wider than f64) arithmetic is currently gated
`unsupported` for soundness. Closing that gap — a real Z3/cvc5 parity item —
requires a trusted oracle for arbitrary IEEE formats. This expands the
validation basis of ADR-0023, so it is recorded here rather than decided
silently in code.

Closes the wide-format half of the FP-arithmetic question opened under ADR-0023
and ADR-0026.

## Decision

**Validate wide-format FP arithmetic against `rustc_apfloat` as a
dev-dependency** of `axeyum-fp` — a pure-Rust port of LLVM's APFloat that
implements correctly-rounded IEEE 754 arithmetic for arbitrary `(exp, sig)`
formats, including quad (F128). A wide FP circuit's gate is lifted from the
native-validatable regime to a given format **only after** a differential sweep
(structured corners + randomized) shows the circuit matches `rustc_apfloat` for
that format, with NaN compared by payload-class and signs/zeros bit-exact.

Until that sweep exists for a format, the format's wide circuit stays
`unsupported` (sound), exactly as F128 is today.

Preconditions (met at acceptance):

- `rustc_apfloat` is a **dev-dependency** of `axeyum-fp` only; it does not enter
  the default/runtime dependency graph, so the C-free, minimal-runtime guarantees
  hold. Its license `Apache-2.0 WITH LLVM-exception` and its transitive
  dev-deps (`smallvec`, `bitflags`: MIT/Apache-2.0) are all already in
  `deny.toml`'s allow-list — CI's `cargo deny check` confirms.
- The oracle is used exclusively in `#[cfg(test)]` validation, never in the
  shipped lowering path.

Implemented 2026-06-14: F128 `add`/`mul`/`div`/`fma` are validated against
`ieee::Quad` (structured corners + 2000 random pairs/triples each, RNE) and
their `128` gates lifted. F128 `sqrt` stays `unsupported` — `rustc_apfloat` does
not implement square root, so there is no oracle for it. F128 `fp.rem` already
decides via the iterative reduction (`rem_iterative`).

## Evidence

- The 2026-06-14 `sconst` bug is direct evidence that width-specific FP faults
  are real and that replay does not catch them — so an independent oracle is
  load-bearing, not belt-and-suspenders.
- `rustc_apfloat` is the reference the Rust compiler itself uses for const-eval
  of floating point; it is pure Rust (no C/C++), supports IEEE half/single/
  double/quad and `x87` 80-bit, and exposes round-to-nearest-even plus the
  directed modes the circuits implement.
- The same harness shape already works for F64 against native `f64`
  (`symbolic_f64_fma_matches_native`: 1728 structured + 3000 random triples);
  swapping the oracle to `rustc_apfloat` generalizes it to F128 and arbitrary
  formats with no change in methodology.

## Alternatives

- **Native `f128`.** Rejected: unstable on the MSRV (1.85) and stable
  toolchains; cannot run in CI.
- **In-tree exact-rational/bignum oracle.** Build an arbitrary-precision
  rational FP rounder (on `num-bigint`, or hand-rolled on the existing
  `WideUint`). Rejected as the primary route: it re-implements correctly-rounded
  IEEE arithmetic — error-prone in exactly the special-case handling (subnormals,
  ties, inf/NaN, sign of zero) that the circuits also get wrong — so it is not a
  *more trusted* oracle than `rustc_apfloat`, which is battle-tested. A
  `WideUint`-based oracle additionally shares `WideUint` with the evaluator's
  `apply_wide`, weakening independence on the eval path.
- **Leave F128 unsupported indefinitely.** Rejected: `unsupported` is sound but
  it is a standing parity gap; double-precision-and-wider FP appears in real
  verification workloads, and the wide-BV foundation to support it already exists.

## Consequences

- *Easier:* F128 and arbitrary-format FP arithmetic (`add`/`mul`/`div`/`sqrt`/
  `fma`) become validatable and can have their `128` gates lifted format by
  format, each behind a passing differential sweep.
- *Harder / to watch:* a new dev-dependency to keep licensed (`cargo deny`) and
  maintained; the validation sweeps lengthen CI test time (mitigate with bounded
  random counts, per the benchmarking methodology and the
  `avoid-public-benchmark-runs` discipline).
- *Revisited when:* a format's sweep reveals a circuit bug (fix the circuit, not
  the gate), or if `rustc_apfloat` becomes unmaintained (fall back to the
  in-tree bignum oracle, accepting its higher authoring risk).
- *Unchanged:* the default build stays C-free and the runtime dependency graph is
  untouched; FP semantics remain "validated, not proven" — this ADR widens the
  validation basis, it does not introduce a proof.
