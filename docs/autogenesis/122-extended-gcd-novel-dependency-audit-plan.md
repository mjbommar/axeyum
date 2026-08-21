# Extended-gcd novel-dependency audit plan

Date: 2026-08-21

## Decision

Classify the unmeasured dependency frontier beneath `Nat.xgcdAux_val` and the
private xgcd invariant. Their union contains eighteen names, but `Eq.symm` is
already measured empty-footprint under the same pinned stream identity and
canonical declaration hash. This pass reuses that durable result and audits the
remaining seventeen roots once.

The sealed root export already contains the full closure. Therefore no exporter
runs, the batch importer reads the stream once, and no proof term, theorem type,
or theorem value is rendered. The pass has no reconstruction or ledger
authority.

The next route is selected only after the kernel footprints are frozen. This
avoids assuming that familiar arithmetic or propositional helper names are
clean, while also avoiding a redundant reread for `Eq.symm`.

## Verification

```sh
python3 scripts/check-autogenesis-extended-gcd-novel-dependency-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_extended_gcd_novel_dependency_audit_plan
```
