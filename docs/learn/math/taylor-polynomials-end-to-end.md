# End To End: Finite Taylor Polynomials

This lesson follows one exact Taylor-polynomial resource from coefficient replay
to checked QF_LRA/Farkas evidence:
[finite-taylor-polynomials-v0](../../../artifacts/examples/math/finite-taylor-polynomials-v0/).

```text
untrusted fast search -> Taylor coefficients, truncated value, or Farkas certificate
trusted small checking -> exact rational Taylor replay plus checked QF_LRA/Farkas evidence
```

## What The Pack Checks

The pack has two exact Taylor-polynomial witnesses, one truncated
linearization witness, and one malformed value:

| Row | Result | Evidence |
|---|---|---|
| `quadratic-taylor-at-one-witness` | `sat` | replay-only |
| `cubic-taylor-at-zero-witness` | `sat` | replay-only |
| `truncated-linearization-witness` | `sat` | replay-only |
| `bad-taylor-value-rejected` | `unsat` | replay-only |
| `qf-lra-bad-taylor-value` | `unsat` | checked QF_LRA/Farkas |
| `general-taylor-theory-lean-horizon` | `not-run` | Lean horizon |

Every finite row is exact rational arithmetic. The pack treats Taylor
polynomials as fixed coefficient replay, not as a theorem about arbitrary
smooth functions, remainder bounds, convergence, analytic continuation,
multivariable expansions, or floating-point approximation code.

## Replay The Quadratic Row

For `f(x)=1+2x+x^2`, center `a=1`, and evaluation point `x=3/2`, the replayed
derivative values are:

```text
f(1)   = 4
f'(1)  = 4
f''(1) = 2
```

Dividing by factorials gives Taylor coefficients:

```text
4/0! = 4
4/1! = 4
2/2! = 1
```

The basis powers are:

```text
(x-a)^0 = 1
(x-a)^1 = 1/2
(x-a)^2 = 1/4
```

So the finite replay checks:

```text
4 + 4*(1/2) + 1*(1/4) = 25/4
f(3/2) = 25/4
```

## Replay The Cubic Row

For `f(x)=1+x+x^2+x^3` at center `0`, the derivative values are:

```text
1, 1, 2, 6
```

After factorial division, the Taylor coefficients are again:

```text
1, 1, 1, 1
```

At `x=2`, the replay checks:

```text
1 + 2 + 4 + 8 = 15
```

which matches the original polynomial.

## Replay The Truncated Row

The linearization row deliberately uses only degree `1` for the quadratic at
center `1`:

```text
4 + 4*(1/2) = 6
```

The original polynomial value is `25/4`, so the replay records the exact
remainder:

```text
25/4 - 6 = 1/4
```

This row is useful because it shows how to keep finite truncation arithmetic
separate from a general Taylor-remainder theorem.

## Reject The Bad Value

The malformed replay row says:

```text
For the exact quadratic Taylor row, the Taylor value is 6.
```

The trusted replay recomputes `25/4`. That is enough to reject the row as a
finite resource claim. It is not yet a proof object.

## Checked Farkas Row

The separate `qf-lra-bad-taylor-value` row owns the proof-object refutation.
Its source artifact is
[`bad-taylor-value-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-taylor-polynomials-v0/smt2/bad-taylor-value-farkas-conflict.smt2)
and it isolates:

```text
taylor_value = 25/4
taylor_value = 6
```

The route regression parses the SMT-LIB file, emits `UnsatFarkas` evidence,
and checks that evidence independently.

## Theorem Boundary

This pack does not prove:

- Taylor theorem hypotheses for arbitrary differentiable or smooth functions;
- Lagrange, integral, Peano, or asymptotic remainder formulas;
- analytic convergence or radius-of-convergence claims;
- approximation error bounds for function families;
- multivariable Taylor theorem variants;
- floating-point Taylor-series evaluation accuracy.

Those belong in Lean theorem resources or numerical-honesty resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-taylor-polynomials-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_taylor_polynomials_bad_value_artifact_emits_checked_farkas

python3 scripts/query-foundational-resources.py checks \
  --pack finite-taylor-polynomials-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-taylor-value \
  --require-any
```

Expected trust boundary:

```text
untrusted fast search -> Taylor coefficients, truncated value, or Farkas certificate
trusted small checking -> exact rational Taylor replay plus checked QF_LRA/Farkas evidence
theorem horizon       -> Taylor theorem, remainder bounds, convergence, multivariable expansions, and floating-point behavior
```
