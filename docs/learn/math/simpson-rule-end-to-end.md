# End To End: Finite Simpson Rule

This lesson follows one exact finite Simpson-rule resource from quadrature
replay to checked Farkas evidence:
[finite-simpson-rule-v0](../../../artifacts/examples/math/finite-simpson-rule-v0/).

The point is small and deliberate:

```text
untrusted fast search -> Simpson panel, quadrature value, exactness row, or Farkas certificate
trusted small checking -> exact rational replay plus checked QF_LRA evidence
```

## Resource Row

The pack is anchored in:

- `field_real_analysis`
- `field_numerical_analysis`
- `curriculum_calculus`
- `curriculum_polynomials`
- `bridge_integration_horizon`
- `bridge_bounded_family_asymptotic_boundary`

It has five rows:

| Row | Result | Status |
|---|---|---|
| `simpson-cubic-exact-witness` | `sat` | replay-only |
| `simpson-quadratic-exact-witness` | `sat` | replay-only |
| `bad-simpson-value-rejected` | `unsat` | replay-only |
| `qf-lra-bad-simpson-value` | `unsat` | checked QF_LRA/Farkas |
| `general-simpson-rule-theory-lean-horizon` | `not-run` | Lean horizon |

## Finite Claim

Every row is finite and exact-rational. The pack treats Simpson's rule as a
fixed three-node weighted sum:

```text
S(f,[a,b]) = ((b-a)/6) * (f(a) + 4*f((a+b)/2) + f(b))
```

For `f(x)=x^3` on `[0,2]`, the listed data is:

```text
nodes         = 0, 1, 2
sample values = 0, 1, 8
weights       = 1, 4, 1
scale         = 1/3
weighted sum  = 12
Simpson value = 4
exact integral = integral_0^2 x^3 dx = 4
```

For `f(x)=1+x^2` on `[0,2]`, the validator checks the same finite arithmetic:

```text
sample values = 1, 2, 5
weighted sum  = 14
Simpson value = 14/3
exact integral = integral_0^2 (1+x^2) dx = 14/3
```

Those rows do not prove the general degree-of-exactness theorem. They replay
two fixed polynomial panels.

## Bad Source Row

The malformed source row says:

```text
For f(x)=x^3 on [0,2], the single-panel Simpson value is 7/2.
```

Exact replay computes:

```text
(1/3) * (0 + 4*1 + 8) = 4
```

So the replay-only row rejects the malformed claim and records the gap:

```text
4 - 7/2 = 1/2
```

## Checked Farkas Row

The separate `qf-lra-bad-simpson-value` row owns the proof-object refutation.
Its source artifact is:

[`bad-simpson-value-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-simpson-rule-v0/smt2/bad-simpson-value-farkas-conflict.smt2)

The artifact isolates this scalar contradiction:

```text
simpson_value = 4
simpson_value = 7/2
```

The route test parses that SMT-LIB file, emits `UnsatFarkas` evidence, and
independently checks the certificate. The source panel is still checked by the
pack validator; the Farkas row is only the compact arithmetic contradiction.

## Theorem Horizon

The finite resource does not prove:

- the general Simpson degree-of-exactness theorem;
- composite Simpson convergence;
- quadrature error bounds;
- adaptive quadrature termination or correctness;
- floating-point implementation correctness;
- numerical stability claims.

Those require future Lean theorem statements or numerical-honesty artifacts.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simpson-rule-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_simpson_rule_bad_value_artifact_emits_checked_farkas
```

To find the row through the public query surface:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-simpson-rule-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-simpson-value \
  --require-any
```

## Trust Boundary

The split is:

```text
untrusted fast search -> Simpson panel, quadrature value, exactness row, or Farkas certificate
trusted small checking -> exact rational replay and checked QF_LRA/Farkas evidence
```

This is the same pattern used by
[Calculus Theorem Boundary](calculus-theorem-boundary.md),
[Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md),
and [End To End: Finite Integration](finite-integration-end-to-end.md).
