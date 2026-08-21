# Public gcd definition direct-reconstruction decline

Date: 2026-08-21

## Result

The single authorized Lean compilation failed in both constructor branches:

- `Nat.gcd 0 y` is not definitionally equal to the zero branch of
  `Nat.gcd_def`;
- `(Nat.succ x).gcd y` is not definitionally equal to the recursive branch.

Thus even the zero case cannot be recovered by `rfl`. The official function is
opaque at exactly the generic `WellFounded.Nat.fix_eq` seam measured in the
preceding audits. No export or kernel import occurred, and the zero-retry budget
ended the increment.

## Consequence

The direct official-gcd computation route is closed. A target-owned gcd remains
valid replacement mathematics, but it cannot by itself rewrite an exact
official target. Before choosing that broader architecture, the next bounded
route should audit the proof-free official extended-gcd identity
`Nat.gcd_eq_gcd_ab`, whose integer coefficients may provide the target-side
Bézout content without exposing the opaque recursive equation.

No public gcd equation, balanced Bézout theorem, Fibonacci target, evaluation,
fact, or ledger credit was issued.

## Immutable evidence

The read-only pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/a3b075724-public-gcd-def-direct-decline-v1/manifest.json`

Its manifest SHA-256 is
`e53376f7beae3a29cfed9244434a7f4db2d94559a3c39fec27f70b4e68d68be1`.

## Verification

```sh
python3 scripts/check-autogenesis-public-gcd-def-direct-reconstruction-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_public_gcd_def_direct_reconstruction_result
```
