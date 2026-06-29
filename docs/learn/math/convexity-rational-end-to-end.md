# End To End: Rational Convexity

This lesson follows one exact rational convexity resource from midpoint Jensen
replay to finite second differences, affine threshold monotonicity, and a
checked bad midpoint-convexity rejection. It uses the
[convexity-rational-v0](../../../artifacts/examples/math/convexity-rational-v0/)
pack.

Concept rows:

- `curriculum_reals`, `curriculum_rationals`, and
  `curriculum_linear_algebra` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_optimization_and_convexity`, `field_real_analysis`, and
  `field_linear_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `quadratic-midpoint-jensen-witness` | `sat` | replay-only |
| `finite-convex-grid-second-differences` | `sat` | replay-only |
| `affine-monotone-threshold-witness` | `sat` | replay-only |
| `bad-midpoint-convexity-rejected` | `unsat` | checked |
| `general-convex-analysis-lean-horizon` | `not-run` | lean-horizon |

The positive rows replay finite exact-rational inequalities. The negative row
is a checked counterexample to a false midpoint-convexity claim. The pack does
not claim general convex analysis.

## Replay Midpoint Jensen

The fixed convex function is:

```text
f(x) = x^2
left = -1
right = 3
midpoint = 1
```

The witness records:

```text
f(-1) = 1
f(3) = 9
(f(-1) + f(3)) / 2 = 5
f(1) = 1
```

The validator recomputes every value and checks:

```text
f((left + right) / 2) <= (f(left) + f(right)) / 2
1 <= 5
```

## Replay Finite Second Differences

The grid row samples the same quadratic on equally spaced points:

```text
x:     -2  -1   0   1   2
f(x):   4   1   0   1   4
```

The validator checks equal spacing and recomputes the second differences:

```text
4 - 2*1 + 0 = 2
1 - 2*0 + 1 = 2
0 - 2*1 + 4 = 2
```

All listed second differences are nonnegative, so the finite convexity shadow
checks on this grid.

## Replay An Affine Threshold

The affine threshold row uses:

```text
g(x) = 3*x - 2
threshold input = 1
threshold output = 1
sample points = 1, 3/2, 2
```

The validator evaluates the samples exactly:

```text
g(1) = 1
g(3/2) = 5/2
g(2) = 4
```

Each sample has `x >= 1` and `g(x) >= 1`. This is finite threshold replay, not
a proof of global monotonicity over all reals.

## Reject A Bad Midpoint Claim

The bad row claims that this finite function is midpoint convex:

```text
f(-1) = 0
f(0) = 1
f(1) = 0
```

The midpoint of `-1` and `1` is `0`, and the endpoint average is:

```text
(f(-1) + f(1)) / 2 = 0
```

The validator rejects the claim because:

```text
f(0) = 1 > 0
```

That gives a small checked `unsat` row for false finite convexity claims.

## Name The Lean Horizon

The final row records the theorem-prover boundary:

```text
general Jensen inequalities
convex sets and functions over vector spaces
separation and supporting-hyperplane theorems
strong duality beyond fixed Farkas certificates
semidefinite programming certificates
algorithm convergence proofs
```

Those require Lean modules, proof-producing optimization certificates, or
carefully scoped numerical metadata. This pack only checks finite exact-rational
convexity evidence.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/convexity-rational-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current convexity resource pattern:

```text
untrusted fast search -> midpoint, grid, threshold, or counterexample candidate
trusted small checking -> exact Fraction arithmetic and finite inequality replay
remaining horizon -> general convex analysis, duality, and convergence proofs
```

The graduation route is deterministic exact-rational inequality checking plus
checked proof objects for the finite rows before broader analytic or algorithmic
claims are promoted.
