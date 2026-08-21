# Public equation carrier audit result

Date: 2026-08-21

## Result

The one preregistered importer pass classified the 23-theorem direct closure
beneath `Nat.div_eq` and `Nat.mod_eq`:

- 13 declarations have empty footprints;
- 10 carry `propext`; and
- none carry another assumption.

The private quotient fuel-congruence theorem is empty-footprint. The carriers
are `Nat.modCore_eq`, `Nat.modCore_eq_mod`, and eight generic proposition or
conditional simplifiers: `and_false`, `and_self`, `eq_false`, `eq_self`,
`eq_true`, `false_and`, `ite_cond_eq_false`, and `ite_cond_eq_true`.

## Consequence

The quotient worker and its proof-argument congruence are not the problem.
`Nat.div_eq` acquired `propext` by simplifying proposition-valued conditions,
while the remainder side also passes through assumption-bearing wrapper
equations. A replacement should therefore use explicit case splits and the
already audited worker equations, avoiding equality proofs between propositions
and avoiding `Nat.modCore_eq` / `Nat.modCore_eq_mod` as dependencies.

This is diagnostic only. No replacement source was compiled, no theorem was
submitted, and no target, evaluation, fact, or ledger authority was granted.

## Verification

```sh
python3 scripts/check-autogenesis-euclidean-public-equation-carrier-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_euclidean_public_equation_carrier_audit_result
```
