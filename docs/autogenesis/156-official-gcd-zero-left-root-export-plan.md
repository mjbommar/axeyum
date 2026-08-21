# Official gcd zero-left theorem-root export plan

Date: 2026-08-21

The source proof already compiles. The failed increment exported too much. This
retry changes only evidence extraction: the pinned exporter receives the exact
separator and one declaration root:

```text
AxeyumAutogenesisNatGcdFixEqV2 -- Axeyum.Autogenesis.nat_gcd_zero_left
```

The selected stream must be nonempty and no larger than two megabytes. The
importer's two-million-record limit is unchanged. Two fresh imports must emit
byte-identical empty-footprint audits with the local model theorem present and
the official zero-left, fix-equality, extensionality, and proposition axioms
absent.

No proof edit, limit increase, closed balanced-Bézout submission, or downstream
credit is authorized by this plan.

```sh
python3 scripts/check-autogenesis-official-gcd-zero-left-root-export-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_zero_left_root_export_plan
```
