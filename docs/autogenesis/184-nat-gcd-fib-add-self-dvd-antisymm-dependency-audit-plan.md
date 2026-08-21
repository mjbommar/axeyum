# `Nat.gcd_fib_add_self` divisibility-antisymmetry dependency audit

Date: 2026-08-21

Official coprime-factor cancellation is now available in the r091
representation. The remaining independently identified target obligation is
closing equality from mutual gcd divisibility. Mathlib's convenient
`Nat.dvd_antisymm` theorem is not acceptable as-is: its kernel-derived footprint
contains `propext`.

Before constructing a replacement, one nonrendering reread of the already
sealed gcd-root stream will audit its exact five direct theorem dependencies:
`Eq.symm`, `Nat.eq_zero_of_zero_dvd`, `Nat.le_antisymm`, `Nat.le_of_dvd`, and
`Nat.succ_pos`. The output may contain only declaration identities, direct
dependency names, and kernel-derived footprints—never theorem types, values,
or proof expressions.

The result will determine which clean leaves can be reused and which exact
assumption carriers must be replaced or parameterized. This turn permits no
source compilation, theorem submission, Fibonacci target submission, or ledger
change.

```sh
python3 scripts/check-autogenesis-nat-gcd-fib-add-self-dvd-antisymm-dependency-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_dvd_antisymm_dependency_audit_plan
```
