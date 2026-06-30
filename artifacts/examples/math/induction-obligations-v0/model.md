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

For the promoted solver row, finite replay over `k = 0..8` computes:

```text
bad_step_count = 0
```

The rejected solver artifact asks for `bad_step_count >= 1`, so Axeyum can
check the final bounded-step obstruction as a tiny QF_LIA arithmetic-DPLL
certificate without pretending to prove the universal induction theorem.

The general induction schema is not encoded as a solver claim. It is metadata
for a future Lean proof route.
