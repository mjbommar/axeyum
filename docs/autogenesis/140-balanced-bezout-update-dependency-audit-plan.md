# Balanced-Bézout update dependency-local audit plan

Date: 2026-08-21

V1's target reaches `propext`, but its direct theorem surface is only nine
names. Before changing source, this increment audits exactly those nine names
in their measured order from the already sealed stream.

The ordered batch auditor may read the proof-bearing stream once. It emits only
declaration identities, direct theorem dependencies, and kernel-derived axiom
footprints; proof terms, theorem types, and theorem values remain unrendered.
No compilation, export, theorem submission, retry, or second stream read is
authorized.

The result must name the exact subset of the nine roots carrying `propext`.
An empty subset is meaningful: it would show that the footprint is introduced
directly or through a non-theorem definition/elaboration boundary, and would
require a source-shape isolation before V2. A nonempty subset authorizes
replacement of only those roots. Either outcome prevents another broad rewrite
of arithmetic that is already clean.

```sh
python3 scripts/check-autogenesis-balanced-bezout-euclidean-update-dependency-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_balanced_bezout_euclidean_update_dependency_audit_plan
```
