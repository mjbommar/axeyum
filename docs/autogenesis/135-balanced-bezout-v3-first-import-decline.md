# Balanced-Bézout V3 first-import decline

Date: 2026-08-21

## Result

V3 compiled both sources and produced one root-selected Lean 4.30 export, but
the first Axeyum audit failed the empty-footprint gate. The required second
fresh import therefore did not run.

The quotient witness reaches `Quot.sound` through the convenient conditional-
rewriting closure, including `funext`. The balanced theorem inherits that
footprint and adds `propext` through Mathlib's ring-normalization proof family.
Compiler acceptance is not kernel-clean acceptance: neither theorem receives
credit.

This closes the tactic-level route. The next proof must build explicit kernel
terms from clean arithmetic equalities and recursors, avoiding function
extensionality, proposition/conditional simplification, and `ring`. The private
fuel invariant and official `Nat.gcd.induction` remain usable clean inputs.

The sealed manifest is
`/nas3/data/axeyum/autogenesis/reference-packs/f96a2319d-official-gcd-balanced-bezout-v3-v1/manifest.json`,
SHA-256 `683fab713611a5fc3ceb1e0ed4e84cdad0833b46b9cb7d7ff4a3381f62d27ba0`.
The 1,597,091-byte proof stream remains unreadable. All six temporary paths
were removed and the exact three-file `s5` baseline is unchanged.

## Verification

```sh
python3 scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-result-v3.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_balanced_bezout_reconstruction_result_v3
```
