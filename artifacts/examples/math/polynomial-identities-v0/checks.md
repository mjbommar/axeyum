# Checks

## `binomial-square-identity`

Expected result: `sat`.

The witness lists `(x + 1)`, its square, and the expected expanded polynomial
`x^2 + 2x + 1`. The validator multiplies `[1, 1]` by itself and compares the
result to `[1, 2, 1]`.

## `factor-theorem-root-witness`

Expected result: `sat`.

The witness checks `p(x) = x^2 - 5x + 6` at `x = 2`. The validator confirms
`p(2) = 0`, then checks:

```text
p(x) = (x - 2)(x - 3)
```

## `false-rational-root-rejected`

Expected result: `unsat`.

The checked query is the fixed false claim that `1` is a rational root of
`x^2 + 1`. The validator evaluates the polynomial exactly and confirms the
result is `2`, not `0`.
