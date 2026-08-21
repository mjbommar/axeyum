# Corrected official-gcd balanced-Bézout plan

Date: 2026-08-21

## Corrections

V2 changes only the two source shapes localized by the V1 compiler decline:

1. The quotient-witness statement and proof use direct `Nat.mod` applications,
   matching the audited `Nat.mod.eq_1` and `Nat.mod.eq_2` roots.
2. The quotient equation is lifted with `congrArg` into exactly `n * mn` and
   `n * mp`. Those two equalities are rewritten only in their coefficient
   contexts, so the gcd remainder is never rewritten.

The mathematical route is unchanged: the private joint invariant supplies an
existential quotient, the carrier remains four natural positive/negative parts,
and the two gcd equations remain explicit parameters for later checked target
specialization. Public `/`, public division equations, official xgcd, and the
assumption-bearing official gcd-equation proofs remain forbidden.

## Execution boundary

The exact absolute Lean 4.30 `lake` binary is now bound in addition to the
toolchain commit. After the three-file `s5` baseline and six absent temporary
paths pass, the two sources may each compile once, one root-selected export may
run, and the two roots may be audited in two fresh Axeyum kernels. Proof-bearing
streams remain inaccessible to the model.

A compilation or first-import failure stops without retry. Acceptance requires
two matching audits per root, empty footprints, and no forbidden dependency.
It still grants no closed specialization, cancellation, Fibonacci target,
receipt, evaluation, fact, or ledger authority.

## Verification

```sh
python3 scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-plan-v2.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_balanced_bezout_reconstruction_plan_v2
```
