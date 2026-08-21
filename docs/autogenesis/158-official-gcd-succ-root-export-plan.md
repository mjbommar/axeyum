# Official gcd successor root export plan

Date: 2026-08-21

The successor computation theorem was previously accepted into a native-support
kernel. That result is mathematically valid, but its `WellFounded` representation
cannot be composed with the generic balanced-Bezout stream's official Mathlib
representation. This increment therefore reconstructs the already-authored
proof in the required official kernel; it does not count the native theorem a
second time.

The unchanged Lean 4.30 source is compiled once and exported with exactly one
root:

```text
AxeyumAutogenesisNatGcdFixEqV2 -- Axeyum.Autogenesis.nat_gcd_succ
```

The stream must be nonempty and no larger than two megabytes. Two fresh imports
must produce byte-identical empty-footprint audits whose only direct theorem
dependency is `Axeyum.Autogenesis.gcdModel_succ`. No proof material may be
rendered, no retry is allowed, and the closed balanced-Bezout theorem remains
unauthorized.

```sh
python3 scripts/check-autogenesis-official-gcd-succ-root-export-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_succ_root_export_plan
```
