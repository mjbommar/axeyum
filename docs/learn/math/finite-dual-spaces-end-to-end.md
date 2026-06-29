# End To End: Finite Dual Spaces

This lesson follows one finite dual-space resource from covector evaluation
tables to replayed result and proof/evidence status. It uses the
[finite-dual-spaces-v0](../../../artifacts/examples/math/finite-dual-spaces-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra`, `curriculum_fields`, and `curriculum_groups` in
  the [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_linear_algebra`, `field_abstract_algebra`,
  `field_set_theory_and_foundations`, and
  `field_functional_analysis_and_operator_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `dual-space-table-replay` | `sat` | replay-only |
| `dual-basis-pairing-replay` | `sat` | checked |
| `annihilator-replay` | `sat` | checked |
| `transpose-map-replay` | `sat` | checked |
| `bad-covector-rejected` | `unsat` | checked |
| `general-duality-theory-lean-horizon` | `not-run` | lean-horizon |

The finite rows are table checks over `F2^2`. The pack does not claim general
duality, bidual isomorphism, adjoint-map theory, Hahn-Banach, topological
duals, or weak-star compactness.

## Encode

The primal vector space is still `F2^2`:

```text
vectors = 00, 10, 01, 11
10 + 01 = 11
```

A covector is a finite function from vectors to `F2`. The pack names the four
linear covectors:

```text
zero, x, y, x+y
```

The evaluation table includes rows such as:

```text
x(10) = 1
x(01) = 0
y(10) = 0
y(01) = 1
(x+y)(11) = 0
```

## Replay Covector Linearity

The checker verifies that every listed covector preserves vector addition and
scalar multiplication:

```text
phi(v + w) = phi(v) + phi(w)
phi(a*v) = a*phi(v)
```

For `x`, one addition row is:

```text
x(10 + 01) = x(11) = 1
x(10) + x(01) = 1 + 0 = 1
```

The validator repeats this over every listed covector, vector pair, and scalar.

## Replay Pointwise Dual Operations

The dual-space operation tables are checked against pointwise evaluation:

```text
(phi + psi)(v) = phi(v) + psi(v)
(a*phi)(v) = a*phi(v)
```

For example:

```text
(x + y)(10) = 1
x(10) + y(10) = 1 + 0 = 1

(x + y)(01) = 1
x(01) + y(01) = 0 + 1 = 1
```

So the dual addition table must agree with the evaluation table, not just with
the names of the covectors.

## Replay The Dual Basis

The primal basis is:

```text
10, 01
```

The claimed dual basis is:

```text
x, y
```

The checker recomputes the pairing matrix:

```text
      10  01
x      1   0
y      0   1
```

That is the identity matrix, so `x` and `y` are accepted as the listed dual
basis for this finite example.

## Replay An Annihilator

The pack asks for the annihilator of the x-axis subspace:

```text
S = {00, 10}
```

The annihilator is the set of covectors that vanish on every vector in `S`:

```text
Ann(S) = {phi | phi(00) = 0 and phi(10) = 0}
```

The checker recomputes:

```text
zero(00) = 0, zero(10) = 0
y(00) = 0, y(10) = 0
x(10) = 1
(x+y)(10) = 1
```

So the annihilator is exactly:

```text
{zero, y}
```

The pack also checks the listed dimension:

```text
|Ann(S)| = 2 = 2^1
dim(Ann(S)) = 1
```

## Replay A Transpose Map

The linear map `T` is first-coordinate projection:

```text
T(00) = 00
T(10) = 10
T(01) = 00
T(11) = 10
```

The claimed transpose sends covectors by precomposition:

```text
T*(zero) = zero
T*(x) = x
T*(y) = zero
T*(x+y) = x
```

The checker verifies the defining equation for every covector and vector:

```text
(T*phi)(v) = phi(T(v))
```

For `phi = y` and `v = 01`:

```text
(T*y)(01) = zero(01) = 0
y(T(01)) = y(00) = 0
```

The row is accepted only because every finite pair agrees.

## Check The Refutation

The bad row proposes this function as a covector:

```text
f(00) = 0
f(10) = 1
f(01) = 1
f(11) = 1
```

Additivity fails on `10 + 01`:

```text
f(10 + 01) = f(11) = 1
f(10) + f(01) = 1 + 1 = 0
```

Because `1 != 0`, the function is not linear and the covector claim is
rejected.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-dual-spaces-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for finite duality:

```text
untrusted fast search -> covector tables, pairings, annihilator, transpose map
trusted small checking -> linearity, pointwise operations, evaluation identities
```

General duality, bidual theorems, adjoints, topological duals,
Hahn-Banach-style theorems, and functional-analysis structure require
Lean/mathlib-scale proof support.
