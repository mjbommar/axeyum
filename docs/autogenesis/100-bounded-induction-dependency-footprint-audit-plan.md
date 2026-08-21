# Bounded-induction dependency-footprint audit plan

Date: 2026-08-21

## Question

Which of the 22 explicit direct theorem dependencies in the primitive-induction
public Euclidean proof carry its remaining `propext` footprint?

The target footprint, stream identity, and complete dependency names are already
known. The carrier set is not. This plan freezes that measurement before the
auditor or any replacement source is written.

## Fixed audit

One importer-only pass may consume the immutable proof stream. It reports only
canonical declaration identities, axiom footprints, direct theorem dependency
names, and the fixed footprint class for each preregistered declaration. Every
name must resolve as a theorem and aggregate counts must be derived from those
rows.

The proof stream may be read only by the importer. Proof terms, theorem values,
source bodies, and raw stream text must not be rendered. The audit has no retry
and grants no proof revision, support theorem, target, executor, fact,
evaluation, or ledger authority.

## Verification

```sh
python3 \
  scripts/check-autogenesis-euclidean-bounded-induction-dependency-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_euclidean_bounded_induction_dependency_audit_plan
```
