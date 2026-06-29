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

### Order Transitivity

For the fixed chain `1/5 < 2/5 < 3/5`, transitivity gives `1/5 < 3/5`.

These fixed checks are not general theorem proofs. They are exact replay
targets that should later graduate to QF_LRA encodings and Farkas evidence where
the query shape is UNSAT.
