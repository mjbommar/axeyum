# Model

The pack models induction as a family of finite obligations plus one explicit
proof-assistant horizon.

For weak induction, the checker replays the prefix:

```text
P(n): n * (n + 1) is even
n = 0..6
values = 0, 2, 6, 12, 20, 30, 42
step differences = 2, 4, 6, 8, 10, 12
```

For strong induction, the checker replays the Fibonacci recurrence and bound:

```text
fib(0) = 0
fib(1) = 1
fib(n) = fib(n - 1) + fib(n - 2)
fib(n) <= 2^n for n = 0..8
```

For loop-invariant induction, each trace row must satisfy:

```text
acc = i * (i + 1) / 2
```

and each transition must move from `(i, acc)` to:

```text
(i + 1, acc + i + 1)
```

For the invalid-step row, the checker treats `P(n) := n < 3` as a concrete
predicate table and requires a true step counterexample at `k = 2`.

## Limitations

The examples are fixed finite prefixes. They are enough to teach the executable
shape of induction obligations and bad-step rejection, but they are not a proof
of the full natural-number induction schema.
