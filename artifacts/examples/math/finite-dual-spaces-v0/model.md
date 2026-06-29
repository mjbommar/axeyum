# Model

The pack is table based.

## Covectors

A covector is a finite function from a vector-space carrier to the field:

```json
{"covector": "x", "vector": "10", "value": "1"}
```

The validator checks that every covector table preserves addition and scalar
multiplication.

## Dual Operations

The dual vector-space addition and scalar-action tables are checked pointwise:

```text
(phi + psi)(v) = phi(v) + psi(v)
(a * phi)(v) = a * phi(v)
```

## Transpose Maps

For a finite linear map `T : V -> W`, the transpose row checks:

```text
(T* phi)(v) = phi(T v)
```

for every listed finite covector and vector.

General duality over arbitrary vector spaces, topological duals, adjoints, and
Hahn-Banach-style theorems remain Lean-horizon.
