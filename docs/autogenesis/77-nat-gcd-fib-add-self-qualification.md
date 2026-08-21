# `Nat.gcd_fib_add_self` qualification

## Result

The exact Fibonacci coprimality admission made one train fact newly ready:
`Nat.gcd_fib_add_self`. A proof-free measurement now classifies it as a
two-binder, non-reflexive equality. Its 46-declaration type slice abstracts
only the two occurrences of `Nat.gcd`; the old reflexivity producer submitted
the wrong six-node candidate and was correctly rejected by the kernel.

This is qualification evidence, not theorem credit. No upstream proof body,
held-out row, proof search, target submission, executor invocation, or ledger
write was used.

## Bottom-up boundary

For `m = 0`, both sides reduce to the same gcd. For `m = k + 1`, an
independently derived route is:

```text
fib (n + (k + 1))
  = fib (k + 1) * fib (n + 1) + fib k * fib n
```

The first summand is divisible by `fib (k + 1)`. Removing it leaves the
product `fib k * fib n`; the admitted consecutive-coprimality theorem permits
the `fib k` factor to be cancelled. The two gcds then have exactly the same
divisors.

That analysis identifies three local construction obligations:

1. the successor form of Fibonacci addition;
2. divisibility cancellation through a factor coprime to the fixed modulus;
3. equality of gcds from equality of their divisors.

The existing checked surface already includes the recurrence and the required
gcd/divisibility introduction and elimination lemmas. The next operation must
therefore be support-first: construct and independently check these obligations
before it may submit the exact r091 target.

## Top-down consequence

The target remains the next rung toward `Nat.fib_gcd`, which in turn unlocks
the natural Fibonacci divisibility theorem and contributes to the integer
Fibonacci gcd chain. The immediate work is nevertheless foundational rather
than target-shaped: the coprime-factor cancellation theorem is reusable far
beyond Fibonacci.

## Reproduce

```sh
python3 scripts/check-autogenesis-nat-gcd-fib-add-self-qualification.py
python3 -m unittest scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_qualification
```

The relation observation itself can be reproduced without proof authority:

```sh
cargo run -q -p axeyum-lean-import --example relation_goal_probe -- \
  /nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams/r091.ndjson \
  Axeyum.Autogenesis.Coverage.r091
```

The machine-readable authority and exact input identities are in
[`mathlib-nat-gcd-fib-add-self-qualification-v1.json`](../../artifacts/autogenesis/mathlib-nat-gcd-fib-add-self-qualification-v1.json).
