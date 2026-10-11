# ADR-3100: Bounded Python CAS text parsing constructs the existing exact IR

Status: proposed
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
