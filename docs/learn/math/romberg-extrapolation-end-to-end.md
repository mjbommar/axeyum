# End To End: Finite Romberg Extrapolation

This lesson follows one exact finite Romberg/Richardson extrapolation resource
from composite trapezoid replay to checked Farkas evidence:
[finite-romberg-extrapolation-v0](../../../artifacts/examples/math/finite-romberg-extrapolation-v0/).

The point is small and deliberate:

```text
untrusted fast search -> trapezoid values, extrapolated value, error row, or Farkas certificate
trusted small checking -> exact rational replay plus checked QF_LRA evidence
```

## Resource Row

The pack is anchored in:

- `field_real_analysis`
- `field_numerical_analysis`
- `curriculum_calculus`
- `curriculum_polynomials`
- `bridge_integration_horizon`
- `bridge_exact_vs_floating_arithmetic`
- `bridge_bounded_family_asymptotic_boundary`

It has six rows:

| Row | Result | Status |
|---|---|---|
| `romberg-quadratic-exact-witness` | `sat` | replay-only |
| `romberg-quadratic-error-cancellation-witness` | `sat` | replay-only |
| `romberg-quartic-error-witness` | `sat` | replay-only |
| `bad-romberg-value-rejected` | `unsat` | replay-only |
| `qf-lra-bad-romberg-value` | `unsat` | checked QF_LRA/Farkas |
| `general-romberg-extrapolation-theory-lean-horizon` | `not-run` | Lean horizon |

## Finite Claim

Every checked value is finite and exact-rational. The pack uses one
Romberg/Richardson step:

```text
R = (4*T(h/2) - T(h)) / 3
```

For `f(x)=x^2` on `[0,1]`, the listed data is:

```text
T(h)   = 1/2
T(h/2) = 3/8
R      = (4*(3/8) - 1/2) / 3 = 1/3
exact integral = integral_0^1 x^2 dx = 1/3
```

The same row records the finite error cancellation:

```text
coarse error = 1/6
fine error   = 1/24
ratio        = 4
Romberg error = 0
```

For `f(x)=x^4` on `[0,1]`, the validator checks a nonzero residual:

```text
T(h)   = 1/2
T(h/2) = 9/32
R      = 5/24
exact integral = 1/5
residual = 1/120
```

Those rows do not prove a general Romberg error theorem. They replay two fixed
polynomial examples.

## Bad Source Row

The malformed source row says:

```text
For f(x)=x^2 on [0,1], the one-step Romberg value is 1/4.
```

Exact replay computes:

```text
(4*(3/8) - 1/2) / 3 = 1/3
```

So the replay-only row rejects the malformed claim and records the gap:

```text
1/3 - 1/4 = 1/12
```

## Checked Farkas Row

The separate `qf-lra-bad-romberg-value` row owns the proof-object refutation.
Its source artifact is:

[`bad-romberg-value-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-romberg-extrapolation-v0/smt2/bad-romberg-value-farkas-conflict.smt2)

The artifact isolates this scalar contradiction:

```text
romberg_value = 1/3
romberg_value = 1/4
```

The route test parses that SMT-LIB file, emits `UnsatFarkas` evidence, and
independently checks the certificate. The source extrapolation arithmetic is
still checked by the pack validator; the Farkas row is only the compact scalar
contradiction.

## Theorem Horizon

The finite resource does not prove:

- general Richardson extrapolation theory;
- Romberg convergence;
- Euler-Maclaurin error expansions;
- adaptive quadrature termination or correctness;
- floating-point implementation correctness;
- numerical stability claims.

Those require future Lean theorem statements or numerical-honesty artifacts.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-romberg-extrapolation-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_romberg_extrapolation_bad_value_artifact_emits_checked_farkas
```

To find the row through the public query surface:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-romberg-extrapolation-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-romberg-value \
  --require-any
```

## Trust Boundary

The split is:

```text
untrusted fast search -> trapezoid values, extrapolated value, error row, or Farkas certificate
trusted small checking -> exact rational replay and checked QF_LRA/Farkas evidence
```

This is the same pattern used by
[Calculus Theorem Boundary](calculus-theorem-boundary.md),
[End To End: Finite Simpson Rule](simpson-rule-end-to-end.md), and
[Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md).
