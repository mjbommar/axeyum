# ADR-6800: Rust CAS text parser shares the bounded exact grammar

Status: proposed
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
