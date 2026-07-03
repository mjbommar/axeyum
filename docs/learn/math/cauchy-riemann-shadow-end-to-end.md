# End To End: Finite Cauchy-Riemann Shadow

This lesson follows one exact complex-analysis shadow from real-pair arithmetic
to a checked bad derivative-coordinate claim. It uses the
[finite-cauchy-riemann-shadow-v0](../../../artifacts/examples/math/finite-cauchy-riemann-shadow-v0/)
pack.

Concept rows:

- `curriculum_complex`, `curriculum_reals`, `curriculum_calculus`, and
  `curriculum_polynomials` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_complex_analysis` and `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_complex_real_pair_transform`,
  `bridge_derivative_identity_shadow`, and
  `bridge_polynomial_coefficient_factor_replay` in the atlas

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `complex-square-real-pair-witness` | `sat` | replay-only |
| `partial-derivative-witness` | `sat` | replay-only |
| `cauchy-riemann-equality-witness` | `sat` | replay-only |
| `complex-derivative-witness` | `sat` | replay-only |
| `bad-derivative-real-part-rejected` | `unsat` | replay-only |
| `qf-lra-bad-derivative-real-part` | `unsat` | checked |
| `general-cauchy-riemann-lean-horizon` | `not-run` | lean-horizon |

The pack uses exact rational polynomial replay. It does not prove
holomorphicity or the general Cauchy-Riemann theorem.

## Replay The Complex Square

The fixed function is:

```text
f(z) = z^2
z = x + iy
```

The real and imaginary components are:

```text
u(x,y) = x^2 - y^2
v(x,y) = 2xy
```

At `(x,y)=(1,2)`, the real-pair square is:

```text
(1 + 2i)^2 = -3 + 4i
u(1,2) = -3
v(1,2) = 4
```

The validator recomputes both `z*z` and the component-polynomial values.

## Replay The Partials

The symbolic partial derivatives are:

```text
u_x = 2x
u_y = -2y
v_x = 2y
v_y = 2x
```

At `(1,2)`, those become:

```text
u_x = 2
u_y = -4
v_x = 4
v_y = 2
```

The finite Cauchy-Riemann shadow is the two exact equalities:

```text
u_x = v_y
u_y = -v_x
```

This is one checked polynomial at one rational point. It is not a proof that
arbitrary functions satisfying the equations are holomorphic, or that arbitrary
holomorphic functions satisfy the equations under the right hypotheses.

## Replay The Complex Derivative

For this fixed polynomial:

```text
f'(z) = 2z
```

So at `1+2i`:

```text
f'(1+2i) = 2 + 4i
```

The validator also checks that this derivative matches the real-pair component
formula:

```text
f'(z) = u_x + i v_x
```

at the fixed point.

## Reject A Bad Derivative Coordinate

The malformed row claims:

```text
real(f'(1+2i)) = 3
```

Exact replay computes:

```text
real(f'(1+2i)) = 2
```

The separate checked row isolates the final contradiction as `QF_LRA`:

```text
derivative_real = 2
derivative_real = 3
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

## Boundary

This pack is useful because it shows how a complex-analysis topic can be
grounded in finite exact data before theorem proving starts. Axeyum checks the
listed real-pair arithmetic, bivariate polynomial partials, fixed
Cauchy-Riemann equalities, and final scalar contradiction.

General complex differentiability, the Cauchy-Riemann theorem, holomorphicity,
Cauchy's theorem, residues, analytic continuation, and conformal mapping
theorems need Lean theorem statements and no-`sorry` proof artifacts before
they can be displayed as theorem coverage.

Run the focused checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cauchy-riemann-shadow-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cauchy_riemann_bad_derivative_real_part_artifact_emits_checked_farkas
```
