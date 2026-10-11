# Exact CAS expression transport — 2026-10-11

Version1 source encoding implements the canonical-expression requirement in
[X2](cas-certified-trace-plan-2026-10-10.md#x2--symbolic-π-and-bounded-text-parsing).
Contract: [ADR-6100](../research/09-decisions/adr-6100-cas-expression-wire-preserves-source-identity.md).
Scheduling remains in [PLAN.md](../../PLAN.md).

```python
from fractions import Fraction
from axeyum.cas import Expr

expr = Expr.pi() + Expr.var("pi") + Expr.rat((1 << 512) + 1, 7)
encoded = expr.to_json()
restored = Expr.from_json(encoded)
assert restored == expr
assert restored.to_json() == encoded
assert Expr.pi().to_json() != Expr.var("pi").to_json()
```

Rust uses `axeyum_cas::expression_wire::{to_json, from_json}`. JSON has a
`version` and `expression`; nodes use `kind` and, when applicable, `args`.
Pi: `{"version":1,"expression":{"kind":"pi"}}`. The variable pi:
`{"version":1,"expression":{"kind":"var","args":"pi"}}`.
Rationals have canonical decimal numerator/denominator strings; no floating
conversion and no i128 narrowing. Empty Add/Mul, literal quotient-by-zero and
all unary heads preserve their source trees. Transport does not validate their
mathematical domains or establish an equality.

Malformed syntax, duplicate/unknown fields, unsupported tags/versions, trailing
JSON, zero/negative denominators and unreduced or noncanonical rational spelling
raise ValueError in Python (Rust WireError::Invalid). Transport hard limits
raise BudgetExceeded (Rust WireError::ResourceLimit): 1 MiB, 4096 nodes, depth32,
16384 bits/component and 1024 UTF-8 bytes/name. A conservative syntax-size budget
also screens encoding work before building the recursive JSON tree. These limits
are independent of convenience parsing and evaluation limits.

Object-key order and whitespace may vary on input. Re-encoding produces fixed
field order and normalized whitespace. Operator ordering is preserved, so this
is canonical transport for a tree, not an algebraic normal form. Source variables
with reserved-looking names remain variables; transport grants no special atom
identity. Human `str` is separate and does not distinguish Pi from Var(pi).

This format carries expressions, not certificates. The polynomial trace wire,
enclosure evidence and kernel reconstruction remain separate contracts. No
kernel admission or universal replay claim follows from round-trip success.

## Verification

Four focused Rust tests pass (zero skips/ignored): all unary heads, every node,
wide components, ordered syntax, identity tags and paired malformed/resource
controls. Fresh native build passes, followed by 279 Python tests/zero skips
including eight transport controls. Stub generation, runtime signature/type
ratchets and private canonical-guard mutation pass; broader gates remain pending.
[Lane notes](notes/cas-expression-wire.md) retain source identities and logs.
