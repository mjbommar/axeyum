# End To End: Finite Calculus Shadows

This lesson follows two finite calculus resources:
[calculus-algebraic-shadow-v0](../../../artifacts/examples/math/calculus-algebraic-shadow-v0/)
and
[calculus-riemann-sum-v0](../../../artifacts/examples/math/calculus-riemann-sum-v0/).
Together they show what Axeyum can check today: exact polynomial derivative
algebra, tangent and critical-point witnesses, finite Riemann sums,
antiderivative endpoint replay, and rejected false calculus claims.

Concept rows:

- `curriculum_calculus`, `curriculum_polynomials`,
  `curriculum_sequences_and_limits`, `curriculum_reals`, and
  `curriculum_rationals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_real_analysis`, `field_numerical_analysis`, and
  `field_differential_equations_and_dynamical_systems` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

Algebraic derivative rows:

| Check | Expected | Evidence Status |
|---|---|---|
| `polynomial-derivative-coefficients` | `sat` | replay-only |
| `product-rule-polynomial-identity` | `sat` | checked |
| `tangent-line-value-witness` | `sat` | replay-only |
| `convex-quadratic-critical-point` | `sat` | replay-only |
| `false-derivative-value-rejected` | `unsat` | checked |
| `general-calculus-lean-horizon` | `not-run` | lean-horizon |

Finite integration rows:

| Check | Expected | Evidence Status |
|---|---|---|
| `riemann-sums-linear-partition` | `sat` | checked |
| `midpoint-rule-affine-exact` | `sat` | checked |
| `antiderivative-endpoint-replay` | `sat` | checked |
| `monotone-quadratic-lower-upper-bounds` | `sat` | checked |
| `false-integral-claim-rejected` | `unsat` | checked |
| `fundamental-theorem-lean-horizon` | `not-run` | lean-horizon |

Every executable row is a fixed rational or polynomial calculation. These
packs do not prove differentiability from limits, the mean value theorem,
general Riemann integrability, convergence of arbitrary tagged partitions, or
the fundamental theorem of calculus.

## Replay Polynomial Derivatives

The algebraic pack represents polynomials as low-to-high coefficient lists:

```text
[1, -2, 0, 1] means 1 - 2*x + x^3
```

The derivative row checks:

```text
d/dx (1 - 2*x + x^3) = -2 + 3*x^2
```

as coefficient lists:

```text
polynomial = [1, -2, 0, 1]
derivative = [-2, 0, 3]
```

The validator recomputes the coefficient transformation exactly.

## Replay A Product-Rule Identity

For fixed polynomials:

```text
f = x^2
g = x + 1
```

the validator recomputes both sides of:

```text
(f*g)' = f'*g + f*g'
```

as coefficient lists. The checked row is a polynomial identity for this fixed
instance, not a proof of the product rule from the limit definition.

## Replay Tangents And Critical Points

The tangent row uses `p(x) = x^2` at `x = 3` and evaluates the tangent line at
`x = 4`:

```text
p(3) = 9
p'(3) = 6
p(3) + p'(3)*(4 - 3) = 15
```

The critical-point row checks:

```text
p(x) = (x - 2)^2 + 1 = x^2 - 4*x + 5
p'(2) = 0
p''(2) = 2
p(2) = 1
```

These are algebraic witness replays over fixed polynomials.

## Reject A False Derivative Claim

The checked `unsat` derivative row claims:

```text
d/dx (x^2) at x = 3 is 5
```

The validator differentiates exactly and computes:

```text
2*3 = 6
```

so the false value is rejected.

## Replay Finite Riemann Sums

The Riemann-sum pack fixes rational partitions and polynomial values. For
`f(x) = x` on `[0, 1]` with partition:

```text
0, 1/4, 1/2, 3/4, 1
```

the validator recomputes:

```text
left_sum = 3/8
right_sum = 5/8
trapezoid_sum = 1/2
exact_integral = 1/2
```

Every cell width and sample value is checked from the partition.

## Replay Midpoint And Antiderivative Rows

For `f(x) = 1 + 2*x` on `[0, 2]`, the midpoint row checks the listed midpoints:

```text
1/4, 3/4, 5/4, 7/4
```

and recomputes the midpoint sum:

```text
6
```

For `f(x) = 2*x`, the antiderivative row differentiates `x^2` and replays the
endpoint difference:

```text
x^2 | from 1 to 3 = 9 - 1 = 8
```

Again, this is a fixed polynomial endpoint replay, not the fundamental theorem
of calculus.

## Replay Lower And Upper Sums

For `f(x) = x^2` on `[0, 1]` with partition:

```text
0, 1/2, 1
```

the validator checks the monotone increasing direction and recomputes:

```text
lower_sum = 1/8
upper_sum = 5/8
exact_integral = 1/3
```

The checked claim is that the listed lower and upper sums bound the exact
polynomial integral for this fixed partition.

## Reject A False Integral Claim

The checked `unsat` integral row claims:

```text
integral of x on [0, 1] = 3/4
```

The validator recomputes the polynomial antiderivative endpoint difference:

```text
integral of x on [0, 1] = 1/2
```

so the false integral claim is rejected. The promoted source artifact records
the final exact-linear contradiction:

```text
integral_value = 1/2
integral_value = 3/4
```

The `math_resource_lra_routes` regression parses
`artifacts/examples/math/calculus-riemann-sum-v0/smt2/false-integral-farkas-conflict.smt2`,
emits `UnsatFarkas` evidence, and checks the certificate independently. This is
still a fixed polynomial-integral row, not the fundamental theorem of calculus.

## Why This Matters

Finite calculus shadows let Axeyum exercise useful solver and proof shapes
without pretending to have full analysis:

```text
untrusted search proposes derivative, tangent, partition, or integral data
trusted checker recomputes exact rational/polynomial arithmetic and Farkas certificates
analytic theorems stay Lean-horizon
```

These rows are the executable bridge between algebraic polynomial reasoning,
numerical-analysis examples, and future Lean-backed calculus theorems.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/calculus-algebraic-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/calculus-riemann-sum-v0
cargo test -p axeyum-solver --test math_resource_lra_routes calculus_riemann_sum_false_integral_artifact_emits_checked_farkas
```

## Trust Boundary

The validators check coefficient differentiation, fixed product-rule
identities, tangent-line arithmetic, critical-point witnesses, rational
partitions, finite Riemann sums, midpoint sums, lower/upper sums, and exact
polynomial antiderivative endpoint differences. The promoted false-integral
row also checks a source QF_LRA/Farkas certificate for the final exact-linear
conflict. These resources do not prove the limit definition of derivative,
arbitrary integrability, tagged-partition convergence, or the fundamental
theorem of calculus.
