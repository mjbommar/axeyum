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

## Bad Covector Certificate

For the rejected functional, exact replay computes:

```text
10 + 01 = 11
f(10) = 1
f(01) = 1
f(11) = 1
1 + 1 = 0
```

Additivity of a covector would require:

```text
f(10 + 01) = f(10) + f(01)
```

The separate `qf-uf-bad-covector-additivity` row links the `QF_UF` artifact that
is unsatisfiable by equality reasoning. The resource regression checks that
Axeyum emits independently rechecked `UnsatAletheProof` evidence with no trusted
reduction step.

General duality over arbitrary vector spaces, topological duals, adjoints, and
Hahn-Banach-style theorems remain Lean-horizon.
