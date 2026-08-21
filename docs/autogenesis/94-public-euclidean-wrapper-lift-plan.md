# Public Euclidean wrapper-lift plan

Date: 2026-08-20

## Goal

Lift the accepted private fuel invariant through official Lean's `Nat.div` and
`Nat.mod` wrappers and reconstruct this exact public proposition:

```text
Nat.div_add_mod : forall m n, n * (m / n) + m % n = m
```

The authored theorem has a private Axeyum name, but its kernel type must be
canonically alpha-expression-identical to the official target. Pretty printing
alone is not sufficient.

## Fixed proof

The proof splits only on the divisor:

- zero uses `Nat.div_zero`, `Nat.mod_zero`, `Nat.zero_mul`, and `Nat.zero_add`;
- a successor divisor unfolds the transparent `Nat.div` and `Nat.modCore`
  wrappers, relates `modCore` to public `%`, and instantiates the accepted
  `divModGoReconstruct` theorem at fuel `m.succ`.

Exactly eight proof-free statements are bound from the immutable v4.30
inventory. The official `Nat.div_add_mod` proof, any additional statement name,
proof search, and upstream proof bodies are forbidden.

## Gates and budget

The first public theorem reconstruction must have an empty footprint and exact
target type. Only then may the second fresh reconstruction run; both theorem
identities must match and dependencies must be enumerated.

This is one public support declaration and at most two kernel submissions. It
does not spend either reserved Fibonacci target submission and grants no
balanced-Bézout, cancellation, executor, fact, evaluation, or ledger authority.

## Verification

```sh
python3 scripts/gen-autogenesis-euclidean-public-lift-plan.py --check
python3 -m unittest \
  scripts.tests.test_gen_autogenesis_euclidean_public_lift_plan
```
