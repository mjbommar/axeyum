# Public Euclidean bounded-induction decline

Date: 2026-08-21

## Result

Primitive induction over an inclusive dividend bound successfully removes the
generated well-founded-recursion theorem. The authored theorem compiles, has
the exact official `Nat.div_add_mod` type representation, and its first Axeyum
kernel import reports no generated recursion dependency.

The import still has footprint `[propext]`, so the preregistered first-run gate
forbids the second submission. The footprint now lies behind an explicit set
of 22 direct theorem dependencies rather than one generated `_unary` wrapper.

## Why this is progress

The representation problem is now finite and auditable. The public quotient
and remainder equations work; primitive induction works; and no hidden
recursive theorem remains. The next task is not another whole-proof rewrite.
It is to submit each exact direct dependency to the existing kernel footprint
auditor and identify only the `propext` carriers.

This result accepts no public support theorem and grants no balanced-Bézout,
cancellation, Fibonacci target, evaluation, fact, or ledger authority.

## Verification

```sh
python3 scripts/check-autogenesis-euclidean-bounded-induction-decline.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_euclidean_bounded_induction_decline
```
