# Model

All values are exact rationals written as strings accepted by Python's
`Fraction` type.

Examples:

```text
1/3, 2/3, -5/7, 0
```

No floating-point arithmetic is used.

## Checks

### Density

If `a < b`, then `(a + b) / 2` is strictly between them. The pack checks the
fixed instance:

```text
a = 1/3
b = 2/3
(a + b) / 2 = 1/2
```

### Additive Inverse

For `x = 5/7`, the additive inverse is `-5/7`, and the sum is exactly `0`.

### Trichotomy

For the fixed pair `1/4` and `3/4`, exactly one of `<`, `=`, and `>` holds.
The Axeyum regression turns the impossible branches into conjunctive `QF_LRA`
queries. Each branch includes the fixed values and one extra violating
condition:

```text
left = 1/4
right = 3/4
branch 1: left >= right
branch 2: left = right
branch 3: left > right
```

Each branch is refuted separately with an `UnsatFarkas` certificate whose
rational multipliers are rechecked independently.

### Order Transitivity

For the fixed chain `1/5 < 2/5 < 3/5`, transitivity gives `1/5 < 3/5`.
The checked violating branch is:

```text
a = 1/5
b = 2/5
c = 3/5
a < b
b < c
a >= c
```

That system is linear and unsatisfiable, so the regression emits and rechecks a
Farkas certificate.

These fixed checks are not general theorem proofs. They are exact replay
targets; the listed fixed `unsat` branches now have QF_LRA/Farkas evidence.
