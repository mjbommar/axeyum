# Public gcd definition direct-reconstruction plan

Date: 2026-08-21

## Decision

Attempt the stable public equation from the proof-free Lean 4.30 inventory:

```text
Nat.gcd_def : ∀ x y, x.gcd y = if x = 0 then y else (y % x).gcd x
```

The authored theorem splits on `x` and uses definitional reduction only. It may
not call the public or private gcd equation theorem,
`WellFounded.Nat.fix_eq`, any quotient axiom, a simplifier, or proof search.

## Ceiling

Exactly one source compilation is allowed. A compilation failure ends the
increment. A successful source may be exported once and reconstructed twice;
both kernel imports must have identical identities, an empty footprint, and no
forbidden dependency.

This plan grants no equation credit in advance and no Bézout, Fibonacci,
executor, evaluation, fact, or ledger authority.

## Verification

```sh
python3 scripts/check-autogenesis-public-gcd-def-direct-reconstruction-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_public_gcd_def_direct_reconstruction_plan
```
