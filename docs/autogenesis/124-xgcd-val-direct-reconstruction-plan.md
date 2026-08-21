# Direct xgcd projection reconstruction plan

Date: 2026-08-21

## Decision

Test the smallest target-owned replacement forced by the dependency census:

```text
∀ (x y : ℕ), x.xgcd y = (x.gcdA y, x.gcdB y)
```

The official `Nat.xgcd_val` theorem carries `propext` and has no direct theorem
dependency, but its statement appears to expose projections of the same public
definition. The tracked candidate uses only `rfl`. It does not invoke the
official theorem, its sibling `Nat.xgcd.eq_1`, simplification, or proof search.

The exact Lean 4.30/Mathlib v4.30 environment on `s5` may compile the source
once. On success, lean4export may emit the authored root once and Axeyum must
independently import and measure it twice. Both imports must report the exact
target type, an empty footprint, and no forbidden dependency. There are no
retries and no theorem or ledger credit until the result is frozen separately.

## Verification

```sh
python3 scripts/check-autogenesis-xgcd-val-direct-reconstruction-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_xgcd_val_direct_reconstruction_plan
```
