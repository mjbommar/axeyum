# Pointwise public-remainder quotient-witness plan

Date: 2026-08-21

V3 showed that the mathematical helper compiles but rewriting under the
existential pulls in `funext` and Quotient axioms. This isolated increment
rebuilds only that helper. It performs constructor cases and transports
equalities solely beneath concrete `Nat` addition contexts with `congrArg`.
There is no public quotient, binder-level rewrite, function equality, or ring
normalization.

The helper must compile once, export once, and reconstruct twice with identical
empty footprints. Its direct dependencies must omit `funext`, `propext`, public
division equations, and the Mathlib ring family. The exact `s5` baseline and
six-path cleanup remain mandatory. Acceptance grants only the quotient witness;
balanced Bézout and every target/ledger action remain separate future gates.

```sh
python3 scripts/check-autogenesis-mod-quotient-witness-kernel-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_mod_quotient_witness_kernel_plan
```
