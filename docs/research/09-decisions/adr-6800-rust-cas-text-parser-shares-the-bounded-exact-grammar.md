# ADR-6800: Rust CAS text parser shares the bounded exact grammar

Status: accepted; bounded surface adopted, final integration gates remain open
Date: 2026-10-11

Expose a Rust CasExpr parser for the existing ADR3100 Python grammar: exact
integers/decimals, ASCII identifiers, distinguished pi/π, parentheses,
+ - * /, ^/** signed integer powers, and admitted unary heads. Preserve
precedence (-x^2 is -(x^2)), left-associated division and explicit refusal of
unparenthesized chained powers. Parsing constructs syntax; it never certifies
an identity or establishes denominator/nonzero assumptions.

Bound input8192 UTF8 bytes,512 tokens,64 constructed nodes,depth32,1024 literal
digits and16384 coefficient bits. Error offsets are UTF8 byte spans, explicitly
distinct from Python's existing character offsets for non-ASCII input. Decimal
conversion uses integers and positive powers of ten, never floats. Negative
powers reuse pow_signed and its domain contract; reject unsupported exponents
and unknown calls. Parser intake must not panic on malformed or oversized text.

Reuse existing expression-wire encoding for structural round trips, π identity,
and exact rational transport. Validate constructor agreement, precedence,
negative-power domains, promoted literals, unary heads, malformed text and every
resource boundary. Python/native grammar differential fixtures prevent drift;
shared native use is a follow-up migration, not an implicit API replacement.

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
