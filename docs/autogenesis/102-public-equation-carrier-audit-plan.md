# Public equation carrier audit plan

Date: 2026-08-21

## Question

Which declarations immediately beneath `Nat.div_eq` and `Nat.mod_eq` carry
their measured `propext` footprints?

The fixed population is the sorted set union of those two theorems' direct
dependency lists: 23 exact names. It includes the private quotient
fuel-congruence theorem, the two remainder wrapper equations, the audited
worker equation, and their propositional simplification support.

## Boundary

One importer pass may read the same sealed public-proof stream and emit only
declaration identities, theorem dependency names, and kernel-derived
footprints. Proof terms, theorem values, source bodies, and raw stream text
remain forbidden. No retry or replacement source is authorized by this audit.

The result must precede any attempt to reconstruct `Nat.div_eq`, `Nat.mod_eq`,
or a local substitute. That keeps the next proof change tied to measured
assumption carriers rather than a guessed rewrite.

## Verification

```sh
python3 scripts/check-autogenesis-euclidean-public-equation-carrier-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_euclidean_public_equation_carrier_audit_plan
```
