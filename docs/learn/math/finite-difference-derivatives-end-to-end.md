# End To End: Finite Difference Derivatives

This lesson follows one exact finite-difference resource from stencil replay to
checked QF_LRA/Farkas evidence:
[finite-difference-derivatives-v0](../../../artifacts/examples/math/finite-difference-derivatives-v0/).

```text
untrusted fast search -> stencil weights, derivative value, or Farkas certificate
trusted small checking -> exact rational stencil replay plus checked QF_LRA/Farkas evidence
```

## What The Pack Checks

The pack has three exact stencil witnesses and one malformed value:

| Row | Result | Evidence |
|---|---|---|
| `forward-difference-affine-exact-witness` | `sat` | replay-only |
| `central-difference-quadratic-exact-witness` | `sat` | replay-only |
| `second-central-difference-quadratic-exact-witness` | `sat` | replay-only |
| `bad-finite-difference-value-rejected` | `unsat` | replay-only |
| `qf-lra-bad-finite-difference-value` | `unsat` | checked QF_LRA/Farkas |
| `general-finite-difference-theory-lean-horizon` | `not-run` | Lean horizon |

Every finite row is exact rational arithmetic. The pack treats finite
differences as fixed stencil replay, not as a theorem about arbitrary
functions, Taylor error, convergence order, stability, PDE schemes, boundary
conditions, or floating-point derivative code.

## Replay The Forward Row

For `f(x)=1+3x`, `x=2`, and `h=1/2`, the forward first-difference stencil is:

```text
(f(x+h) - f(x)) / h
```

The listed samples are:

```text
f(2)   = 7
f(5/2) = 17/2
```

So the finite replay checks:

```text
((17/2) - 7) / (1/2) = (3/2) * 2 = 3
```

That matches the symbolic derivative of `1+3x`.

## Replay The Central Row

For `f(x)=1+2x+x^2`, `x=1`, and `h=1/2`, the central first-difference stencil is:

```text
(f(x+h) - f(x-h)) / (2h)
```

Because `2h = 1`, the scale is `1`. The samples are:

```text
f(1/2) = 9/4
f(3/2) = 25/4
```

So the finite replay checks:

```text
25/4 - 9/4 = 4
```

That matches the symbolic derivative `2+2x` at `x=1`.

## Replay The Second Difference

For the same quadratic, the central second-difference stencil is:

```text
(f(x-h) - 2f(x) + f(x+h)) / h^2
```

The weighted sum is:

```text
9/4 - 8 + 25/4 = 1/2
```

With `h=1/2`, the scale is `1/h^2 = 4`, so the finite replay checks:

```text
4 * 1/2 = 2
```

That matches the symbolic second derivative of `1+2x+x^2`.

## Reject The Bad Value

The malformed replay row says:

```text
For the central first-difference row, the finite-difference value is 5.
```

The trusted replay recomputes `4`. That is enough to reject the row as a finite
resource claim. It is not yet a proof object.

## Checked Farkas Row

The separate `qf-lra-bad-finite-difference-value` row owns the proof-object
refutation. Its source artifact is
[`bad-finite-difference-value-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-difference-derivatives-v0/smt2/bad-finite-difference-value-farkas-conflict.smt2)
and it isolates:

```text
finite_difference_value = 4
finite_difference_value = 5
```

The route regression parses the SMT-LIB file, emits `UnsatFarkas` evidence,
and checks that evidence independently.

## Theorem Boundary

This pack does not prove:

- general finite-difference exactness for arbitrary polynomial degrees;
- Taylor truncation-error formulas;
- convergence order under grid refinement;
- stability or consistency for ODE/PDE discretizations;
- boundary-stencil correctness;
- automatic-differentiation implementation behavior;
- floating-point finite-difference accuracy.

Those belong in Lean theorem resources or numerical-honesty resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-difference-derivatives-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_difference_derivatives_bad_value_artifact_emits_checked_farkas

python3 scripts/query-foundational-resources.py checks \
  --pack finite-difference-derivatives-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-finite-difference-value \
  --require-any
```

Expected trust boundary:

```text
untrusted fast search -> stencil weights, derivative value, or Farkas certificate
trusted small checking -> exact rational stencil replay plus checked QF_LRA/Farkas evidence
theorem horizon       -> truncation error, convergence order, stability, PDE schemes, and floating-point behavior
```
