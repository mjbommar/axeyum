# Clean multiplication leaves for balanced Bézout

Date: 2026-08-21

The accepted V2 update needs two exact arithmetic contracts. Instead of
transporting same-name native theorems across environments, this increment
reconstructs target-owned versions directly over the official Nat operations.

Both proofs follow the native kernel design: primitive induction on the
argument multiplication recurses over, pointwise equality transport, clean
`Nat.left_distrib`, and an explicit four-term addition permutation. The source
uses no rewriting, simplification, ring normalization, official
`Nat.mul_assoc`, or official `Nat.right_distrib`.

One compilation, one export, and two fresh imports are authorized. Both roots
must reconstruct twice with matching empty footprints. Success grants only the
two leaves; applying them to V2 is a later closed-wrapper gate.

```sh
python3 scripts/check-autogenesis-balanced-bezout-clean-mul-leaves-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_balanced_bezout_clean_mul_leaves_plan
```
