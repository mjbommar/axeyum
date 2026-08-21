# Bounded-induction dependency-footprint audit result

Date: 2026-08-21

## Result

The single preregistered importer pass classified all 22 direct dependencies of
the primitive-induction public Euclidean proof:

- 20 have empty kernel-derived footprints;
- 2 carry `propext`; and
- 0 carry any other assumption.

The exact carriers are `Nat.div_eq` and `Nat.mod_eq`. Every induction,
ordering, algebra, congruence, and branch-selection dependency in the authored
proof is axiom-free.

## Consequence

The bottom-up repair is now only the synchronized public computation interface.
Another induction rewrite would solve the wrong problem. The next separately
preregistered construction should derive local equivalents of `Nat.div_eq` and
`Nat.mod_eq` from the already accepted, empty-footprint quotient/remainder
worker equations and audited wrapper identities, then rerun the unchanged
bounded-induction proof against those local equations.

This audit rendered no proof term or theorem value and grants no source
revision, support theorem, target, evaluation, fact, or ledger credit.

## Verification

```sh
python3 \
  scripts/check-autogenesis-euclidean-bounded-induction-dependency-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_euclidean_bounded_induction_dependency_audit_result
```
