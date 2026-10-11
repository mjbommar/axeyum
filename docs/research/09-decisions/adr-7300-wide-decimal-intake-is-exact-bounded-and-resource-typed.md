# ADR-7300: Wide decimal intake is exact, bounded, and resource typed

Status: accepted; bounded source/evidence contract adopted, final integration gates remain open
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

## Adoption and evidence scope

The bounded source/evidence contract is adopted. See the
[current receipts](../../plan/notes/28-wide-real-smtlib-writer.md) and
[completion audit](../../plan/user-feedback-completion-audit-2026-10-11.md).
The implementation retains unsupported-route declines and source identity;
source-bound replay never substitutes search for checking. Parser/solver gates,
fresh native public-route tests and private source-binding controls supply the
recorded evidence. SAT clausal checking, checked source correspondence, external
proof checking and kernel admission remain separate claims. External reference
checks retain the pinned guard patches documented in
[scripts/patches](../../../scripts/patches/README.md); no unmodified-checker
credit or hole acceptance is inferred. Integer-only `lia_generic` proofs remain
internal-only; scopes/macros and broader portable theory reconstruction remain
explicit open coverage. This adoption does not declare the final workspace or
main integration gates complete.
