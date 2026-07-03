# End To End: Finite Divided Differences

This lesson follows one exact finite interpolation resource from Newton
divided-difference replay to checked QF_LRA/Farkas evidence:
[finite-divided-differences-v0](../../../artifacts/examples/math/finite-divided-differences-v0/).

```text
untrusted fast search -> divided-difference table, interpolation value, or Farkas certificate
trusted small checking -> exact rational replay plus checked QF_LRA/Farkas evidence
```

## What The Pack Checks

The pack has two exact Newton divided-difference witnesses and one malformed
value:

| Row | Result | Evidence |
|---|---|---|
| `quadratic-divided-difference-table` | `sat` | replay-only |
| `quadratic-newton-evaluation-witness` | `sat` | replay-only |
| `cubic-divided-difference-table` | `sat` | replay-only |
| `bad-interpolation-value-rejected` | `unsat` | replay-only |
| `qf-lra-bad-interpolation-value` | `unsat` | checked QF_LRA/Farkas |
| `general-interpolation-theory-lean-horizon` | `not-run` | Lean horizon |

Every finite row is exact rational arithmetic. The pack treats divided
differences as a table-replay problem, not as a theorem about arbitrary node
sets, interpolation error, conditioning, splines, or floating-point code.

## Replay The Quadratic Table

For `f(x)=1+x^2` at nodes `0,1,2`:

```text
values = 1, 2, 5
first differences = 1, 3
second difference = 1
Newton coefficients = 1, 1, 1
```

At `x=3`, the Newton basis values are:

```text
1, 3, 6
```

So the finite replay checks:

```text
1*1 + 1*3 + 1*6 = 10
```

## Replay The Cubic Table

For `f(x)=x^3` at nodes `0,1,2,3`, the divided-difference rows are:

```text
values = 0, 1, 8, 27
first differences = 1, 7, 19
second differences = 3, 6
third difference = 1
```

At `x=4`, the Newton terms are:

```text
0, 4, 36, 24
```

and the replayed interpolation value is `64`.

## Reject The Bad Value

The malformed replay row says:

```text
For the quadratic Newton table, the interpolated value at x=3 is 9.
```

The trusted replay recomputes `10`. That is enough to reject the row as a
finite resource claim. It is not yet a proof object.

## Checked Farkas Row

The separate `qf-lra-bad-interpolation-value` row owns the proof-object
refutation. Its source artifact is
[`bad-interpolation-value-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-divided-differences-v0/smt2/bad-interpolation-value-farkas-conflict.smt2)
and it isolates:

```text
interpolated_value = 10
interpolated_value = 9
```

The route regression parses the SMT-LIB file, emits `UnsatFarkas` evidence,
and checks that evidence independently.

## Theorem Boundary

This pack does not prove:

- uniqueness of polynomial interpolation for arbitrary distinct nodes;
- Newton/Lagrange/barycentric equivalence;
- interpolation error formulas;
- conditioning or node-choice theorems;
- spline interpolation theory;
- floating-point interpolation correctness.

Those belong in Lean theorem resources or numerical-honesty resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-divided-differences-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_divided_differences_bad_interpolation_value_artifact_emits_checked_farkas

python3 scripts/query-foundational-resources.py checks \
  --pack finite-divided-differences-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-interpolation-value \
  --require-any
```

Expected trust boundary:

```text
untrusted fast search -> divided-difference table, interpolation value, or Farkas certificate
trusted small checking -> exact rational replay plus checked QF_LRA/Farkas evidence
theorem horizon       -> interpolation uniqueness, error, conditioning, and floating-point behavior
```
