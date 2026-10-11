# ADR-2900: Python CAS rationals reuse the promoted carrier

Status: accepted; bounded surface adopted, final integration gates remain open
Date: 2026-10-10

## Decision

Extend Python rational and expression constructors, operand conversion, getters,
Fraction conversion and rendering through the existing small/promoted Rust
Rational carrier. Python expression evaluation uses a private bounded evaluator
with exact BigRational intermediates, 4,096 visits, depth 128 and 16,384 bits per
normalized intermediate component; exponentiation uses repeated squaring. Missing
variables, undefined division and unsupported unary heads remain None; binding
resource refusals raise BudgetExceeded. Rust narrow eval stays unchanged. Use the shared arithmetic crate's BigInt/BigRational types;
do not introduce another carrier. Transfer Python integers using signed little
endian bytes, with a 16,384-bit input/result limit per integer. This avoids float
intermediates and Python's decimal-string conversion limit. Zero denominators,
invalid integer types, exhausted interning and transport limits fail explicitly.
Omitted denominator means one; an explicit None also selects that default.

Keep the existing narrow `checked(i128,i128)` helper for unrelated consumers.
Wide transport does not certify all CAS operations or their kernel bridges.
Each result/certificate route must support promoted values or explicitly decline.
Rational equality and hashing follow Python numeric equality: delegate hashes to
an exact Fraction, so equal Int/Fraction/Rational dictionary keys agree.

## Validation

Require wide signed constructor/getter/Fraction round trips, expression operands
and evaluation, exact 360-payment arithmetic against an independently written
Fraction calculation, zero/invalid/resource controls, and discrimination of
Python decimal conversion settings. Recheck big CAS witnesses and tampering.
Fresh extension identity and actual collected test counts are required; follow
with generated stubs, affected Rust tests and workspace integration.

## Adoption and validation boundary

This bounded surface is adopted on the feedback implementation branch. Current
CAS library tests and the fresh native consumer suites cover exact values,
transport, parser/domain controls and explicit unsupported/resource outcomes;
see the [validation receipts](../../plan/notes/28-wide-real-smtlib-writer.md).
Signed-power fuzzing includes guaranteed zero-base negative-exponent and
undefined-base seed classes. Private Pi/source-binding controls remain recorded
with exact intended failures. Production Python parsing uses ADR-6900; ADR-3100
is historical and superseded. Promoted transport does not widen every arithmetic
operation, and Pi bounds or parsed expressions do not grant kernel admission.
The final workspace/all-target gates and main integration remain open.
