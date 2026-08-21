# Generic-kernel-base balanced-Bézout composition plan

Date: 2026-08-21

The first official-only attempt used r082 as its base and later tried to import
the generic theorem. That direction failed because the theorem's closure already
contains the recursive `Acc` package, which theorem-slice composition correctly
refuses to synthesize when absent.

This increment reverses only that direction. The accepted generic theorem
kernel becomes the base, preserving `Acc` and its complete official closure.
Four small roots are then composed into it: `Nat.mod_lt`, the accepted
`modLtSucc` adapter, and the two newly accepted official-representation gcd
leaves. The same modulo-bound, closed-successor, and balanced-Bézout
specializations follow under fresh names. The generic theorem itself is never
composed because it is already present in the base.

Two complete executions must be byte-identical, all operations must replay, and
all three new footprints must be empty. Native gcd equations, generated fix
equations, and extensionality remain forbidden. No downstream authority is
granted before acceptance.

```sh
python3 scripts/check-autogenesis-official-gcd-balanced-bezout-generic-base-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_balanced_bezout_generic_base_plan
```
