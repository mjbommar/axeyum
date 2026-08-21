# Extended-gcd coefficient root audit plan

Date: 2026-08-21

## Decision

Measure the exact official Mathlib 4.30 theorem `Nat.gcd_eq_gcd_ab` before
using its `gcdA` and `gcdB` coefficients as the target-side bridge around the
opaque public `Nat.gcd` computation equations.

The preceding descent localized the official recursive equation's only
generated assumption carrier to `WellFounded.Nat.fix_eq`; the direct public
`Nat.gcd_def` reconstruction then failed even in the zero branch because
`Nat.gcd` is opaque. This theorem is a distinct route: it already states an
integer linear combination equal to the public gcd, so a clean footprint could
support cancellation without transporting the gcd implementation.

## Fixed execution

The one allowed root-selected export runs over SSH on `s5` (`server5`) against
the clean Mathlib checkout at commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
It binds Lean 4.30.0 commit `d024af099ca4bf2c86f649261ebf59565dc8c622`,
the existing `Mathlib.Data.Int.GCD` olean, and lean4export 3.1.0 commit
`a3e35a584f59b390667db7269cd37fca8575e4bf`.

The exporter may run once and the general batch auditor may read the resulting
stream once. The raw NDJSON, theorem type, theorem value, and proof term remain
hidden from model context. This increment has no reconstruction, theorem
submission, evaluation, fact-status, or ledger authority.

If the footprint is empty, the next increment may preregister a target-side
integer coefficient adapter. If it is not empty, the next increment may audit
only the novel direct theorem dependencies reported by this measurement.

## Verification

```sh
python3 scripts/check-autogenesis-extended-gcd-root-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_extended_gcd_root_audit_plan
```
