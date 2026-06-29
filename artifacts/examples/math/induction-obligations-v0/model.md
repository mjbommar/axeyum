# Model

The bounded model uses exact natural-number arithmetic.

For the checked finite rows, the property is:

```text
P(n): sum(0..n) = n * (n + 1) / 2
```

The validator checks:

- base case: `P(0)`;
- step obligation: no bounded `k` has `P(k)` true and `P(k + 1)` false;
- bounded conclusion: no bounded `n` falsifies `P(n)`;
- bad-step witness: the candidate property `n = 0` has a base case but fails
  the step at `k = 0`.

The general induction schema is not encoded as a solver claim. It is metadata
for a future Lean proof route.
