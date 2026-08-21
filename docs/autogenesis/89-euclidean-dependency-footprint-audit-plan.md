# Euclidean dependency-footprint audit plan

Date: 2026-08-20

## Question

Which of the 15 direct theorem dependencies in the first failed joint
quotient/remainder proof carry its measured `propext` footprint?

The target footprint and dependency names are already known. The exact carrier
set is not. This plan freezes that remaining measurement before another
importer run.

## Fixed audit

One importer-only pass may consume the immutable failed stream. For each of the
15 preregistered names it reports only:

- canonical declaration identity;
- kernel-derived axiom footprint;
- direct theorem dependency names; and
- one of `empty-footprint`, `propext-bearing`, or
  `other-assumption-bearing`.

Every name must resolve to a theorem and aggregate counts must be derived from
the rows. Proof terms, theorem values, source bodies, and raw stream text must
not be rendered or supplied as model context.

## Authority

The audit permits one stream read and one importer run, with no retry. It grants
no revised-proof compilation, new support submission, target submission,
executor call, theorem credit, fact transition, evaluation credit, or ledger
write.

If the result identifies assumption-bearing dependencies, a later separately
preregistered construction may replace exactly that set with independently
proved or already-audited empty-footprint equivalents. This audit cannot adapt
the source after seeing its own result.

## Verification

```sh
python3 scripts/check-autogenesis-euclidean-dependency-footprint-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_euclidean_dependency_footprint_audit_plan
```
