# Fibonacci/GCD premise sequence

Date: 2026-08-19

## Strategic choice

Choose `Nat.fib_gcd` before `Int.fib_neg`. This is not merely the easier-looking
statement:

| Candidate | Checked abstractions | Retained declarations | Direct reviewed unlocks |
|---|---:|---:|---:|
| `Nat.fib_gcd` | 1 | 46 | 2 |
| `Int.fib_neg` | 2 | 93 | 1 |

`Nat.fib_gcd` unlocks both `Int.gcd_fib` and `Nat.fib_dvd`; `Int.fib_neg`
unlocks only `Int.gcd_fib`. Both remain evaluation-eligible and open.

## Bottom-up foothold

Do not attack `Nat.fib_gcd` cold. The statement-only dependency evidence exposes
the reusable lower chain:

```text
Nat.fib_add_two
        │
        ▼
Nat.fib_coprime_fib_succ
        │
        ▼
Nat.gcd_fib_add_self
        │
        ▼
Nat.fib_gcd ─┬─> Nat.fib_dvd
             └─> Int.gcd_fib
```

The immediate target is `Nat.fib_add_two`:

```text
forall n : Nat,
  Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1)
```

It has no ledger dependencies, and its exact `r080.ndjson` type-slice receipt
retains 46 proof-free declarations with zero abstractions. The boundary is
already representable. The missing capability is reasoning about Mathlib's
stream-iterator implementation of `Nat.fib`.

## Frozen operation

The next producer increment may implement `bounded-iterate-recurrence-v1` with:

- one generic helper schema;
- at most two plan templates;
- at most two kernel submissions in one executor invocation;
- zero retries;
- no upstream proof body, historical target outcome, or held-out access.

The policy has not executed. A failed bounded search is a retained capability
measurement, not permission to widen the budget. A successful candidate still
requires an axiom-free semantic theorem receipt and a separate admission
transaction before evaluation or ledger credit.

## Over the horizon

This sequence deliberately buys a reusable capability. Iterator recurrence is
useful beyond Fibonacci; coprimality and GCD transport then exercise induction,
relation-valued goals, and theorem composition. Those are precisely the proof
planning capabilities the broader autogenesis flywheel needs after the
contract-to-theorem seam.

## Reproduction

```sh
python3 -m unittest scripts.tests.test_check_autogenesis_nat_fib_gcd_premise_selection_policy
python3 scripts/check-autogenesis-nat-fib-gcd-premise-selection-policy.py
```
