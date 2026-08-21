# Subtractive gcd dependency audit plan

Date: 2026-08-21

## Decision

Descend exactly one measured layer beneath the declined gcd convenience roots.
Their direct-dependency union has 17 names; three are roots already classified
by the preceding pass. The next population is therefore the exact ordered set
of 14 previously unmeasured dependencies, derived mechanically in the checker.

## Reuse before reacquisition

The immutable seven-root export already contains these dependencies. This pass
uses that sealed stream and the general batch auditor again, so it needs zero
new exporter invocations and one importer read. Proof terms, theorem types,
theorem values, and raw NDJSON remain hidden.

The most informative candidates are the private gcd equation, the two general
subtraction/multiplication equations, and `Nat.gcd_succ`. Their measured
footprints will distinguish contaminated convenience wrappers from a
contaminated computational gcd core. Equality and proposition helpers remain
in the population because the derivation is exact rather than hand-selected.

## Boundary

This is measurement only. It authorizes no replacement source, theorem
submission, Bézout construction, target attempt, executor, evaluation, fact,
or ledger operation. A later plan may reconstruct only carriers this pass
actually measures as assumption-bearing.

## Verification

```sh
python3 scripts/check-autogenesis-subtractive-gcd-dependency-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_subtractive_gcd_dependency_audit_plan
```
