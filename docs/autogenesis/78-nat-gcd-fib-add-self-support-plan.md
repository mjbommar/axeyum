# `Nat.gcd_fib_add_self` support-first plan

## Decision

One fixed, independently authored plan is preregistered before implementation
or target submission. It treats the newly ready theorem as demand for two
reusable library supports rather than hiding those obligations inside one
target-shaped proof:

1. Fibonacci addition at a successor index;
2. divisibility cancellation through a factor coprime to the modulus.

Only after both supports reconstruct twice with replayable empty-footprint
receipts may the same private-kernel route construct the gcd-shift target twice
and compare its type to the exact r091 source goal.

## Fixed mathematical route

The successor-addition theorem is proved by induction from the already checked
Fibonacci recurrence. The cancellation theorem is proved constructively from
the balanced natural Bézout certificate already present in the native Nat
library: transport `gcd a c` to one, multiply the identity by `b`, and remove
only summands whose divisibility has already been proved.

For the target, split `m` into zero and `k + 1`. In the successor case, rewrite
the shifted Fibonacci number with the addition theorem, remove the summand that
is visibly divisible by `fib (k + 1)`, and use the admitted theorem that
`fib k` and `fib (k + 1)` are coprime. Both gcds then admit exactly the same
common divisors.

## Frozen ceiling

The policy permits one template, two support theorem declarations, one target
theorem declaration, and two fresh reconstructions of each: at most six native
kernel theorem submissions. It separately permits at most two exact r091 target
submissions, one executor invocation, and no retry. Support must precede the
target; partial private kernels cannot publish.

There is no proof, semantic receipt, evaluation, operation registration,
execution, admission, or ledger credit in this increment. Held-out rows,
historical target outcomes, and the upstream Mathlib proof body remain outside
the authority boundary.

## Reproduce

```sh
python3 scripts/check-autogenesis-nat-gcd-fib-add-self-support-plan.py
python3 -m unittest scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_support_plan
```

The exact route, inputs, gates, and budget are in
[`mathlib-nat-gcd-fib-add-self-support-plan-v1.json`](../../artifacts/autogenesis/mathlib-nat-gcd-fib-add-self-support-plan-v1.json).
