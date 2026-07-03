# Model

Taylor rows are stored as exact rational coefficient-list replay obligations.
For a polynomial `p(x)`, center `a`, degree `d`, and evaluation point `x`, the
validator recomputes:

```text
p^(k)(a)
k!
p^(k)(a) / k!
(x - a)^k
(p^(k)(a) / k!) * (x - a)^k
sum_k terms
p(x)
```

Rows with `match_mode = exact` must have the Taylor sum equal to the original
polynomial value. Rows with `match_mode = truncated` must instead list the
exact rational remainder `p(x) - Taylor_d(x)`.

This model is intentionally finite. It does not encode Taylor theorem
hypotheses, analytic convergence, radius of convergence, or floating-point
rounding behavior.
