# Public Euclidean bounded-induction plan

Date: 2026-08-21

## Decision

Replace Lean's generated well-founded recursion carrier with ordinary primitive
induction over an inclusive dividend bound. The authored local claim is:

```text
for every k <= bound and every n,
  n * (k / n) + k % n = k
```

At the successor bound, `Nat.le_or_eq_of_le_succ` either delegates an older
dividend to the induction hypothesis or identifies the new dividend exactly.
In the recursive public-equation branch, `Nat.sub_lt` and
`Nat.le_of_lt_succ` place `k - n` inside the predecessor bound. This supplies
the same mathematical recurrence without a generated `_unary` theorem,
`Nat.strongRecOn`, or an imported strong-induction theorem.

## Exact boundary

The plan binds fifteen proof-free statements: the previous public recurrence
surface plus exactly three bound-management facts. The one authored theorem
must match official `Nat.div_add_mod` at Lean expression representation level,
have no generated recursion dependency, and reconstruct twice with an empty
footprint and identical declaration identity. A failed first run forbids the
second.

No official proof body, private `div.go` invariant, proof search, balanced
Bézout work, cancellation reconstruction, Fibonacci target submission,
executor call, fact mutation, evaluation credit, or ledger write is allowed.

## Verification

```sh
python3 scripts/gen-autogenesis-euclidean-bounded-induction-plan.py --check
python3 -m unittest \
  scripts.tests.test_gen_autogenesis_euclidean_bounded_induction_plan
```
