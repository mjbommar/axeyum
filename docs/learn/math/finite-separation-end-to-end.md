# End To End: Finite Hyperplane Separation

This lesson follows one convexity resource from exact convex-hull replay through
checked bad convex-combination and bad-separator rejections. It uses the
[finite-separation-v0](../../../artifacts/examples/math/finite-separation-v0/)
pack.

Concept rows:

- `curriculum_reals` and `curriculum_linear_algebra` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_optimization_and_convexity`, `field_real_analysis`, and
  `field_linear_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_rational_convexity_shadow` in the atlas bridge vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `convex-combination-replay` | `sat` | replay-only |
| `separating-hyperplane-replay` | `sat` | replay-only |
| `supporting-face-replay` | `sat` | replay-only |
| `bad-convex-combination-point-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-separator-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-separation-theorem-lean-horizon` | `not-run` | Lean horizon |

Every positive row is one finite exact-rational calculation. The pack does not
prove the general separating hyperplane theorem, Farkas theorem, Hahn-Banach, or
SDP duality.

## Replay A Convex Combination

The finite convex set is the triangle:

```text
v0 = (0,0)
v1 = (1,0)
v2 = (0,1)
```

The witness uses weights:

```text
w0 = 1/3
w1 = 1/3
w2 = 1/3
```

The validator checks:

```text
w0,w1,w2 >= 0
w0 + w1 + w2 = 1
w0*v0 + w1*v1 + w2*v2 = (1/3, 1/3)
```

That is a finite convex-hull membership witness, not a general convex-set
theorem.

## Check The Convex-Combination Refutation

The first promoted bad row keeps the weights fixed and claims:

```text
w0*v0 + w1*v1 + w2*v2 = (1/2, 1/3)
```

Exact replay computes:

```text
w0*v0 + w1*v1 + w2*v2 = (1/3, 1/3)
1/2 - 1/3 = 1/6
```

The committed SMT-LIB artifact
[`bad-convex-combination-point-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-separation-v0/smt2/bad-convex-combination-point-farkas-conflict.smt2)
records the tiny contradiction:

```text
point_x_error = 1/6
point_x_error = 0
```

The accepted evidence is checked `UnsatFarkas` arithmetic over the original
source artifact.

## Replay A Separator

The separator is:

```text
normal = (1,1)
threshold = 1
```

For every triangle vertex:

```text
normal . v0 = 0
normal . v1 = 1
normal . v2 = 1
```

The outside point is:

```text
p = (2,2)
normal . p = 4
```

The validator checks that every vertex is on the `<= 1` side and the outside
point is strictly beyond the threshold, with margin `3`.

## Replay The Supporting Face

The tight scores are exactly:

```text
normal . v1 = 1
normal . v2 = 1
```

The pack records tight indices:

```text
1, 2
```

The validator recomputes those indices from the score table. This finite face
check is useful for optimization and polyhedral examples.

## Check The Separator Refutation

The promoted bad row claims:

```text
outside_score <= 1
```

Exact replay computes:

```text
outside_score = 4
```

The committed SMT-LIB artifact
[`bad-separator-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-separation-v0/smt2/bad-separator-farkas-conflict.smt2)
records the tiny contradiction:

```text
outside_score = 4
outside_score <= 1
```

Axeyum may search for the contradiction, but the accepted evidence is checked
`UnsatFarkas` arithmetic over the original source artifact.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-separation-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_separation_bad_
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> proposed hull point, separator, face, or Farkas certificate
trusted small checking -> exact weight replay, exact dot products, tight-face replay, checked QF_LRA evidence
remaining horizon -> general separation theorems, Hahn-Banach, SDP duality, convergence
```

Use this page after
[End To End: Rational Convexity](convexity-rational-end-to-end.md)
or
[End To End: Linear Optimization](linear-optimization-end-to-end.md)
when the goal is to reason about finite separating certificates without
pretending they prove general convex analysis.
