# Checks

## `weak-induction-even-sum-prefix`

Expected result: `unsat`.

The validator replays the prefix table for `n * (n + 1)` over `0..6`. It checks
that the base value is even, every listed finite step adds `2 * (k + 1)`, and no
listed value is odd.

## `qf-lia-even-product-odd-obstruction`

Expected result: `unsat`.

The SMT-LIB artifact isolates a false oddness witness for
`6 * (6 + 1) = 42`: after evaluating the bad witness `2*20 + 1` to `41`, the
same integer product is forced to be both `42` and `41`. Axeyum emits and
checks an `UnsatDiophantine` certificate for the inconsistent equalities.

## `strong-induction-fibonacci-bound-prefix`

Expected result: `unsat`.

The validator replays `fib(0)..fib(8)` and `2^0..2^8`. It checks the two base
cases, the Fibonacci recurrence, and the strong-induction style bound
`fib(n - 1) + fib(n - 2) <= 2^n` for every finite step in the prefix.

## `loop-invariant-prefix-sum-trace`

Expected result: `sat`.

The validator replays a loop trace for summing `1..5`. At every row it checks
the invariant `acc = i * (i + 1) / 2`, and between adjacent rows it checks that
`i` increments by one and `acc` receives the new `i`.

## `bad-induction-step-rejected`

Expected result: `sat`.

The validator checks the false predicate `P(n) := n < 3` over `0..5`. The listed
failure at `k = 2` is accepted only because `P(2)` is true and `P(3)` is false.

## `general-induction-schema-lean-horizon`

Expected result: `not-run`.

This row records the future proof-assistant target: the general theorem that a
base case and step proof imply `P(n)` for all natural numbers, not just a finite
prefix replay.
