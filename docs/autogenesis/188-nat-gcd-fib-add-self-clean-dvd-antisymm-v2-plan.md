# Single-kernel clean divisibility antisymmetry plan

Date: 2026-08-21

The first replacement mixed numeric handles from two kernels. V2 keeps every
`NatPrelude`, `NameId`, `ExprId`, proof construction, and source evidence query
inside one native kernel. Only the checked theorem-composition API may cross
the boundary into the exact r091 kernel, and it does so by stable declaration
names and independently checked types.

The native kernel constructs the clean divisor-bound clone and a revised
antisymmetry theorem. Its zero branch builds equality symmetry structurally via
`Eq.rec`, so the exact direct dependency set is the clean divisor bound plus
`Nat.eq_zero_of_zero_dvd`, `Nat.le_antisymm`, and `Nat.succ_pos`. Both named
roots are transported together and the composition must replay.

Two fresh invocations may read r091 once each. Across both, the ceiling is two
compositions, four support submissions, zero exact target submissions, and no
retry. Source and target evidence must match, footprints must remain empty, and
no proof material may be rendered.

```sh
python3 scripts/check-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v2.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_clean_dvd_antisymm_plan_v2
```
