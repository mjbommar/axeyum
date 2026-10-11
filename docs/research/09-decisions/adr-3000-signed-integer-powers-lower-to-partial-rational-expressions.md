# ADR-3000: signed integer powers lower to partial rational expressions

Status: proposed; pending full validation and domain-aware trace integration
Date: 2026-10-10

## Decision

Expose Rust `CasExpr::pow_signed(i64) -> Option<CasExpr>` and signed Python
`Expr.pow`/`**`. Keep the existing unsigned Rust constructor. Magnitudes must
fit u32, preserving its positive range; unsigned_abs handles i64::MIN without
negation overflow. Rust declines larger magnitudes; Python reports ValueError
for that range and OverflowError for integers outside i64.

For a negative exponent -n, construct exactly `Div(1, Pow(base,n))`, retaining
the existing partial rational-expression semantics. No new term head, SMT
operator or totalized zero division is introduced. At concrete nonzero inputs,
exact evaluation gives the reciprocal power; zero or a missing binding gives
None. The existing 0^0 convention remains one for a defined zero base, while an
undefined base remains undefined even at exponent zero. Symbolic construction
does not discharge the base-nonzero obligation. Modulus, symbolic and fractional
exponents remain unsupported.

A constructor and computed value are not a kernel admission or a conditional
rewrite certificate. Existing rational-function identity evidence has its own
domain contract; domain-carrying trace rules must record base != 0 before
cancelling a negative power. That connection and kernel footprints remain
required rather than implied by this syntax extension.

## Validation

Require constructor shape, exact signed/rational reciprocal values, zero,
missing-binding, undefined-base, exponent boundaries, modulo/type controls and
independent 360-period Fraction agreement. Verify existing positive syntax and
big rational transport regressions. Public source/API documentation and generated
stubs must describe the signed range and partial domain.
