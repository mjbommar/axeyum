# Finite Cauchy-Riemann Shadow Checks

This pack is for learners, solver contributors, and proof-route reviewers who
need a tiny exact bridge between complex arithmetic and real partial
derivatives. It checks one polynomial, one rational point, and one bad
derivative claim. It does not prove the general Cauchy-Riemann theorem,
holomorphicity, Cauchy's theorem, residues, or analytic continuation.

The fixed function is:

```text
f(z) = z^2
z = x + iy
u(x,y) = x^2 - y^2
v(x,y) = 2xy
```

At the fixed point `(x,y)=(1,2)`:

```text
f(1+2i) = -3 + 4i
u_x = 2
u_y = -4
v_x = 4
v_y = 2
```

The finite Cauchy-Riemann shadow is:

```text
u_x = v_y = 2
u_y = -v_x = -4
```

The complex derivative replay is:

```text
f'(z) = 2z
f'(1+2i) = 2 + 4i
```

The checked bad row rejects the claim that the real part of `f'(1+2i)` is `3`.
The QF_LRA artifact isolates only the scalar contradiction:

```text
derivative_real = 2
derivative_real = 3
```

## Concept Rows

- `curriculum_complex`
- `curriculum_reals`
- `curriculum_calculus`
- `curriculum_polynomials`
- `field_complex_analysis`
- `field_real_analysis`
- `bridge_complex_real_pair_transform`
- `bridge_derivative_identity_shadow`
- `bridge_polynomial_coefficient_factor_replay`

## Trust Boundary

```text
untrusted fast search -> candidate complex value, partials, or derivative
trusted small checking -> exact real-pair replay, polynomial partial replay, and checked Farkas evidence
theorem horizon       -> general complex differentiability and Cauchy-Riemann theorems
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cauchy-riemann-shadow-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cauchy_riemann_bad_derivative_real_part_artifact_emits_checked_farkas
```
