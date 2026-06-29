# End To End: Complex Plane Transforms

This lesson follows one exact complex-plane resource from real-pair arithmetic
to finite transform replay. It uses
[complex-plane-transforms-v0](../../../artifacts/examples/math/complex-plane-transforms-v0/).

Concept rows:

- `curriculum_complex`, `curriculum_reals`, and `curriculum_polynomials` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_complex_analysis`, `field_linear_algebra`, `field_real_analysis`, and
  `field_abstract_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `unit-root-cycle-replay` | `sat` | replay-only |
| `conjugation-product-replay` | `sat` | replay-only |
| `mobius-transform-witness` | `sat` | replay-only |
| `bad-unit-square-real-part-rejected` | `unsat` | checked |
| `general-complex-analysis-lean-horizon` | `not-run` | lean-horizon |

Every checked row is exact rational real-pair replay. The pack does not prove
Cauchy-Riemann equations, Cauchy's theorem, residues, analytic continuation, or
the fundamental theorem of algebra.

## Replay The Unit-Root Cycle

The first row represents `i` as the real pair:

```text
i = [0, 1]
```

and lists its powers:

```text
i^0 = [1, 0]
i^1 = [0, 1]
i^2 = [-1, 0]
i^3 = [0, -1]
i^4 = [1, 0]
```

The validator recomputes each multiplication with exact rational arithmetic and
checks that every nonzero power in the cycle has norm squared `1`.

## Replay Conjugation Over Products

For:

```text
z = [1, 2]
w = [3, -1]
```

the pack records:

```text
z*w = [5, 5]
conjugate(z*w) = [5, -5]
conjugate(z) = [1, -2]
conjugate(w) = [3, 1]
conjugate(z)*conjugate(w) = [5, -5]
```

The checker recomputes the product, each conjugate, and the product of
conjugates. This is a concrete finite witness for a familiar algebraic identity,
not a proof of the universally quantified theorem.

## Replay A Rational Mobius Transform

The transform row evaluates:

```text
T(z) = (z - 1) / (z + 1)
z = 2 + i = [2, 1]
```

The numerator and denominator are:

```text
z - 1 = [1, 1]
z + 1 = [3, 1]
```

The validator divides by multiplying with the conjugate and the denominator
norm:

```text
norm_squared([3,1]) = 10
T(2+i) = [2/5, 1/5]
norm_squared(T(2+i)) = 1/5
```

This gives a finite rational-function replay shape for complex-plane
transforms. It does not claim general conformality or half-plane mapping
theorems.

## Reject A False Unit-Square Claim

The negative row claims:

```text
Every square of a unit complex number has nonnegative real part.
```

The checked counterexample is:

```text
z = i = [0, 1]
norm_squared(z) = 1
z^2 = [-1, 0]
real_part(z^2) = -1
```

The checker rejects the universal claim over this finite counterexample. That
is the reusable pattern: broad mathematical prose becomes a concrete witness
or counterexample row before it is trusted.

## Name The Lean Horizon

The pack intentionally stops before analytic complex analysis:

```text
Cauchy-Riemann equations
Cauchy's theorem
residue theorem
analytic continuation
fundamental theorem of algebra
conformal-map theorems
```

Those require theorem-prover reconstruction or dedicated proof artifacts. This
pack only checks exact finite real-pair arithmetic and rational transform
replay.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-plane-transforms-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current complex-plane resource pattern:

```text
untrusted fast search -> complex transform, cycle, identity, or counterexample
trusted small checking -> exact rational real-pair replay
remaining horizon -> holomorphic, contour-integral, and global algebraic theorems
```

The graduation target is deterministic real-pair NRA obligations plus Axeyum
model replay for witnesses and emitted certificates for checked false rows.
