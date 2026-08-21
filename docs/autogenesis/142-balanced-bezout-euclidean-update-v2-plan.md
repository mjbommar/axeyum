# Balanced-Bézout Euclidean update V2 plan

Date: 2026-08-21

The dependency audit found exactly two contaminated V1 leaves:
`Nat.mul_assoc` and `Nat.right_distrib`. V2 retains the witness map, both clean
permutation helpers, and every equality-chain step. It adds two proof parameters
with the exact arithmetic contracts and substitutes those parameters at the
four former official-leaf call sites.

The source diff is intentionally narrow: versioned declaration names, two
parameters, and four substitutions. `Nat.mul_assoc` and `Nat.right_distrib`
are now forbidden direct dependencies alongside `propext`, `funext`, public
division, and the ring family.

One compilation, one export, and at most two fresh imports are authorized on
pinned `s5`. Acceptance requires byte-identical empty-footprint audits. Exact
cleanup must restore the three-file baseline. Success grants only the generic
parameterized Euclidean update; supplying the clean leaves is a separate future
composition gate.

```sh
python3 scripts/check-autogenesis-balanced-bezout-euclidean-update-plan-v2.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_balanced_bezout_euclidean_update_plan_v2
```
