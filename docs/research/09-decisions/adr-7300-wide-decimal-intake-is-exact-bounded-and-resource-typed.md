# ADR-7300: Wide decimal intake is exact, bounded, and resource typed

Status: proposed
Date: 2026-10-11

## Decision

SMT-LIB nonnegative decimal literals reuse the existing promoted Rational
carrier. Keep the small i128 path, then parse the decimal numerator and power-of-
ten denominator with existing workspace BigInt/BigRational dependencies. Limit
atomic conversion to 4096 decimal digits; excess digits or exhausted rational
pool return ResourceLimit rather than malformed syntax or a narrowed value.
Existing accepted decimal spellings and declared-symbol precedence remain.
Negative values retain canonical unary subtraction syntax.

Promoted constant unary negation uses wide_neg; the existing small-expression
negation shape is retained. Constant quotient folding uses wide_div. Constant to_int uses exact arbitrary-
precision floor and a WideInt result; is_int checks the full denominator. The
bounded FP integer rounder explicitly declines promoted operands. Formatting
an unsupported conversion must also avoid narrow accessors. NRA even-power
sign probes compare full rationals instead of narrowing the numerator.

## Evidence boundary

This expands exact source intake and serialization, not the coverage claim for
LRA solver coefficients, arithmetic model evaluation, FP rounding, or portable
arithmetic proofs. Unsupported representation bridges remain explicit declines.
Primitive BigInt conversion is atomic within the digit cap; this is cooperative
resource budgeting, not a hard real-time guarantee.

## Validation

Wide signed numerators and denominators round-trip through source text; long
fractional decimals preserve exact values. Constant floor and integer tests have
concrete discriminating inputs. Nonlinear and zero-divisor syntax stays intact.
Malformed decimals and resource excess must have distinct controls. Promoted
Real-to-FP conversion declines without panic. Record actual gate counts in the
lane record before integration.
