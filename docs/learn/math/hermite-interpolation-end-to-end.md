# End To End: Finite Cubic Hermite Interpolation

This lesson follows one exact cubic Hermite interpolation resource from
endpoint value/slope replay to checked QF_LRA/Farkas evidence:
[finite-cubic-hermite-interpolation-v0](../../../artifacts/examples/math/finite-cubic-hermite-interpolation-v0/).

```text
untrusted fast search -> Hermite coefficients, endpoint slopes, value, or Farkas certificate
trusted small checking -> exact rational Hermite replay plus checked QF_LRA/Farkas evidence
```

## What The Pack Checks

The pack has three exact Hermite witnesses and one malformed value:

| Row | Result | Evidence |
|---|---|---|
| `smoothstep-hermite-witness` | `sat` | replay-only |
| `quadratic-unit-interval-hermite-witness` | `sat` | replay-only |
| `quadratic-nonunit-interval-hermite-witness` | `sat` | replay-only |
| `bad-hermite-value-rejected` | `unsat` | replay-only |
| `qf-lra-bad-hermite-value` | `unsat` | checked QF_LRA/Farkas |
| `general-hermite-interpolation-theory-lean-horizon` | `not-run` | Lean horizon |

Every finite row is exact rational arithmetic. The pack treats cubic Hermite
interpolation as fixed endpoint value/slope replay, not as a theorem about
arbitrary interpolation data, spline spaces, error estimates, monotonicity,
shape preservation, or floating-point interpolation code.

## Replay The Basis

For interval `[a,b]`, set:

```text
h = b - a
t = (x - a) / h
```

The cubic Hermite basis is:

```text
h00 = 2*t^3 - 3*t^2 + 1
h10 = t^3 - 2*t^2 + t
h01 = -2*t^3 + 3*t^2
h11 = t^3 - t^2
```

The value replay is:

```text
H(x) = y0*h00 + h*m0*h10 + y1*h01 + h*m1*h11
```

The validator also checks that the listed polynomial has the endpoint values
and endpoint slopes:

```text
p(a) = y0
p(b) = y1
p'(a) = m0
p'(b) = m1
```

## Replay The Smoothstep Row

For endpoint values `0` and `1` with zero endpoint slopes on `[0,1]`, the
listed polynomial is:

```text
p(x) = 3*x^2 - 2*x^3
```

At `x=1/2`, the basis values are:

```text
h00 = 1/2
h10 = 1/8
h01 = 1/2
h11 = -1/8
```

The finite replay checks:

```text
0*(1/2) + 1*0*(1/8) + 1*(1/2) + 1*0*(-1/8) = 1/2
```

## Replay The Quadratic Row

For `p(x)=1+x+x^2` on `[0,1]`, the endpoint data is:

```text
p(0) = 1, p'(0) = 1
p(1) = 3, p'(1) = 3
```

At `x=1/2`, the finite replay checks:

```text
1*(1/2) + 1*1*(1/8) + 3*(1/2) + 1*3*(-1/8) = 7/4
```

That matches `p(1/2)=7/4`.

## Replay The Nonunit Interval Row

For `p(x)=x^2` on `[1,3]`, the interval length is `2`. At `x=2`, the replay
uses the same normalized `t=1/2` but scales derivative terms by `h=2`:

```text
1*(1/2) + 2*2*(1/8) + 9*(1/2) + 2*6*(-1/8) = 4
```

That matches `p(2)=4`.

## Reject The Bad Value

The malformed replay row says:

```text
For the quadratic unit-interval Hermite row, the Hermite value is 2.
```

The trusted replay recomputes `7/4`. That is enough to reject the row as a
finite resource claim. It is not yet a proof object.

## Checked Farkas Row

The separate `qf-lra-bad-hermite-value` row owns the proof-object refutation.
Its source artifact is
[`bad-hermite-value-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-cubic-hermite-interpolation-v0/smt2/bad-hermite-value-farkas-conflict.smt2)
and it isolates:

```text
hermite_value = 7/4
hermite_value = 2
```

The route regression parses the SMT-LIB file, emits `UnsatFarkas` evidence,
and checks that evidence independently.

## Theorem Boundary

This pack does not prove:

- uniqueness for arbitrary Hermite interpolation data;
- equivalence to divided-difference or Newton constructions;
- Hermite interpolation error formulas;
- spline assembly, boundary-condition, or smoothness theorems;
- monotonicity or shape-preservation guarantees;
- floating-point Hermite or spline evaluation accuracy.

Those belong in Lean theorem resources or numerical-honesty resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cubic-hermite-interpolation-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cubic_hermite_interpolation_bad_value_artifact_emits_checked_farkas

python3 scripts/query-foundational-resources.py checks \
  --pack finite-cubic-hermite-interpolation-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-hermite-value \
  --require-any
```

Expected trust boundary:

```text
untrusted fast search -> Hermite coefficients, endpoint slopes, value, or Farkas certificate
trusted small checking -> exact rational Hermite replay plus checked QF_LRA/Farkas evidence
theorem horizon       -> Hermite uniqueness, error formulas, spline theory, shape preservation, and floating-point behavior
```
