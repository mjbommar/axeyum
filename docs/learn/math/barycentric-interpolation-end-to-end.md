# End To End: Finite Barycentric Interpolation

This lesson follows one exact finite interpolation resource from barycentric
weight replay to checked QF_LRA/Farkas evidence:
[finite-barycentric-interpolation-v0](../../../artifacts/examples/math/finite-barycentric-interpolation-v0/).

```text
untrusted fast search -> barycentric weights, interpolation value, or Farkas certificate
trusted small checking -> exact rational replay plus checked QF_LRA/Farkas evidence
```

## What The Pack Checks

The pack has two regular barycentric interpolation witnesses, one node-hit
witness, and one malformed value:

| Row | Result | Evidence |
|---|---|---|
| `linear-barycentric-evaluation-witness` | `sat` | replay-only |
| `quadratic-barycentric-evaluation-witness` | `sat` | replay-only |
| `node-hit-barycentric-witness` | `sat` | replay-only |
| `bad-barycentric-value-rejected` | `unsat` | replay-only |
| `qf-lra-bad-barycentric-value` | `unsat` | checked QF_LRA/Farkas |
| `general-barycentric-interpolation-theory-lean-horizon` | `not-run` | Lean horizon |

Every finite row is exact rational arithmetic. The pack treats barycentric
interpolation as a table-replay problem, not as a theorem about arbitrary node
sets, interpolation error, conditioning, Runge phenomena, splines, or
floating-point code.

## Replay The Linear Row

For `f(x)=1+2x` at nodes `0,2`, the barycentric weights are:

```text
w0 = 1/(0-2) = -1/2
w1 = 1/(2-0) = 1/2
```

At `x=1`, the denominator terms are:

```text
(-1/2)/(1-0), (1/2)/(1-2) = -1/2, -1/2
```

The numerator terms are:

```text
(-1/2)*1/(1-0), (1/2)*5/(1-2) = -1/2, -5/2
```

So the finite replay checks:

```text
numerator_sum / denominator_sum = -3 / -1 = 3
```

## Replay The Quadratic Row

For `f(x)=x^2` at nodes `0,1,3`, the barycentric weights are:

```text
1/3, -1/2, 1/6
```

At `x=2`, the denominator terms are:

```text
1/6, -1/2, -1/6
```

and the numerator terms are:

```text
0, -1/2, -3/2
```

So the finite replay checks:

```text
(-2) / (-1/2) = 4
```

## Node Hit

Barycentric interpolation has a removable singularity at a node. The pack keeps
that case explicit instead of evaluating the regular quotient formula at
`x = x_i`. For the quadratic row at `x=1`, the trusted replay returns the
sample value:

```text
f(1) = 1
```

## Reject The Bad Value

The malformed replay row says:

```text
For the quadratic barycentric row, the interpolated value at x=2 is 5.
```

The trusted replay recomputes `4`. That is enough to reject the row as a finite
resource claim. It is not yet a proof object.

## Checked Farkas Row

The separate `qf-lra-bad-barycentric-value` row owns the proof-object
refutation. Its source artifact is
[`bad-barycentric-value-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-barycentric-interpolation-v0/smt2/bad-barycentric-value-farkas-conflict.smt2)
and it isolates:

```text
barycentric_value = 4
barycentric_value = 5
```

The route regression parses the SMT-LIB file, emits `UnsatFarkas` evidence,
and checks that evidence independently.

## Theorem Boundary

This pack does not prove:

- uniqueness of polynomial interpolation for arbitrary distinct nodes;
- Newton/Lagrange/barycentric equivalence;
- interpolation error formulas;
- conditioning, Runge-phenomenon, or node-choice theorems;
- spline interpolation theory;
- floating-point barycentric interpolation correctness.

Those belong in Lean theorem resources or numerical-honesty resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-barycentric-interpolation-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_barycentric_interpolation_bad_value_artifact_emits_checked_farkas

python3 scripts/query-foundational-resources.py checks \
  --pack finite-barycentric-interpolation-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-barycentric-value \
  --require-any
```

Expected trust boundary:

```text
untrusted fast search -> barycentric weights, interpolation value, or Farkas certificate
trusted small checking -> exact rational replay plus checked QF_LRA/Farkas evidence
theorem horizon       -> interpolation uniqueness, error, conditioning, and floating-point behavior
```
