# ADR-3100: Bounded Python CAS text parsing constructs the existing exact IR

Status: superseded by ADR-6800 and ADR-6900
Date: 2026-10-10

The public Python CAS surface needs text input without executing host code.
A bounded recursive-descent parser constructs existing Expr nodes: ASCII names,
exact integer/decimal literals, parentheses, +, -, *, /, ^ or ** with a signed
integer exponent, and named unary heads. Multiplication/division associate left;
powers bind before unary minus. Chained powers require parentheses. No implicit
multiplication, attributes, indexing, scientific notation or host evaluation.

Limits: 8192 source characters, 1024 digits per literal, 512 tokens, 64
constructed nodes and 32 recursive levels. ParseError is ValueError with source
start/end offsets. Limits are parse failures; native construction/evaluation
resource declines retain existing semantics. Fractions remain partial Div nodes;
zero denominators are accepted as expressions and evaluate to None. Parsing
never discharges nonzero assumptions or certifies an identity. Existing solver
and kernel proof contracts apply to the resulting expression unchanged.

pi and Unicode π are reserved until the distinguished constant constructor is
available. This initial implementation does not fulfill the symbolic π milestone.
There is no canonical serialization or Rust text-parser claim yet. Unary calls
retain existing symbolic domain semantics; arbitrary function calls are rejected.

Validation compares constructor-built expressions, exact independent Fraction
results, precedence, signed powers, zero denominators, malformed inputs and each
limit. Later constant/serialization work must extend this contract explicitly.

## Superseded production route

The original Python implementation is retained only as a private differential
reference. Production `axeyum.cas.parse` calls `Expr._parse_text`, uses native
UTF-8 byte and final lowered-AST limits, and translates diagnostic byte spans
back to Python character offsets. See
[ADR-6800](adr-6800-rust-cas-text-parser-shares-the-bounded-exact-grammar.md) and
[ADR-6900](adr-6900-python-cas-parsing-uses-the-native-bounded-grammar.md).
Distinguished pi support is governed by
[ADR-6000](adr-6000-distinguished-cas-pi-has-constant-identity.md).
The original character/builder bounds and pending-pi statement above describe
the initial implementation, not the current public route.
