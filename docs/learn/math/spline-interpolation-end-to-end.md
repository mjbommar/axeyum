# End To End: Finite Cubic Spline Interpolation

This lesson follows one exact natural cubic spline resource from piecewise
polynomial replay to checked QF_LRA/Farkas evidence:
[finite-cubic-spline-interpolation-v0](../../../artifacts/examples/math/finite-cubic-spline-interpolation-v0/).

```text
untrusted fast search -> spline pieces, knot derivatives, value, or Farkas certificate
trusted small checking -> exact rational spline replay plus checked QF_LRA/Farkas evidence
```

## What The Pack Checks

The pack has three exact spline witnesses and one malformed value:

| Row | Result | Evidence |
|---|---|---|
| `natural-spline-left-midpoint-witness` | `sat` | replay-only |
| `natural-spline-right-midpoint-witness` | `sat` | replay-only |
| `natural-spline-knot-smoothness-witness` | `sat` | replay-only |
| `bad-spline-value-rejected` | `unsat` | replay-only |
| `qf-lra-bad-spline-value` | `unsat` | checked QF_LRA/Farkas |
| `general-spline-interpolation-theory-lean-horizon` | `not-run` | Lean horizon |

Every finite row is exact rational arithmetic. The pack treats natural cubic
spline interpolation as one fixed assembly transcript, not as a theorem about
arbitrary knots, boundary conditions, spline spaces, error estimates,
convergence, shape preservation, or floating-point spline code.

## Replay The Pieces

For knots `0, 1, 2` and sample values `0, 1, 0`, the listed natural spline has
second derivatives:

```text
M0 = 0
M1 = -3
M2 = 0
```

The two cubic pieces are:

```text
S0(x) = 3/2*x - 1/2*x^3
S1(x) = -1 + 9/2*x - 3*x^2 + 1/2*x^3
```

The validator checks endpoint samples:

```text
S0(0) = 0
S0(1) = 1
S1(1) = 1
S1(2) = 0
```

It also checks the natural boundary constraints:

```text
S0''(0) = 0
S1''(2) = 0
```

## Replay Knot Smoothness

At the interior knot `x=1`, the validator recomputes:

```text
S0(1)  = S1(1)  = 1
S0'(1) = S1'(1) = 0
S0''(1)= S1''(1)= -3
```

That is the finite `C1`/`C2` smoothness check. It is still a fixed rational
row, not a proof that all natural splines exist or are unique.

## Replay Midpoint Values

On the left interval:

```text
S0(1/2) = 3/2*(1/2) - 1/2*(1/8) = 11/16
```

On the right interval:

```text
S1(3/2) = -1 + 9/2*(3/2) - 3*(9/4) + 1/2*(27/8) = 11/16
```

Both rows are replay-only exact arithmetic.

## Reject The Bad Value

The malformed replay row says:

```text
For the left-midpoint natural spline row, the spline value is 3/4.
```

The trusted replay recomputes `11/16`. That is enough to reject the row as a
finite resource claim. It is not yet a proof object.

## Checked Farkas Row

The separate `qf-lra-bad-spline-value` row owns the proof-object refutation.
Its source artifact is
[`bad-spline-value-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-cubic-spline-interpolation-v0/smt2/bad-spline-value-farkas-conflict.smt2)
and it isolates:

```text
spline_value = 11/16
spline_value = 3/4
```

The route regression parses the SMT-LIB file, emits `UnsatFarkas` evidence,
and checks that evidence independently.

## Theorem Boundary

This pack does not prove:

- existence or uniqueness for arbitrary spline interpolation data;
- equivalence between spline bases or construction algorithms;
- spline error estimates or convergence;
- boundary-condition theory beyond the listed natural endpoint row;
- monotonicity or shape-preservation guarantees;
- floating-point spline evaluation accuracy.

Those belong in Lean theorem resources or numerical-honesty resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cubic-spline-interpolation-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cubic_spline_interpolation_bad_value_artifact_emits_checked_farkas

python3 scripts/query-foundational-resources.py checks \
  --pack finite-cubic-spline-interpolation-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-spline-value \
  --require-any
```

Expected trust boundary:

```text
untrusted fast search -> spline pieces, knot derivatives, value, or Farkas certificate
trusted small checking -> exact rational spline replay plus checked QF_LRA/Farkas evidence
theorem horizon       -> spline existence, uniqueness, error formulas, convergence, shape preservation, and floating-point behavior
```
