# Euclidean dependency-footprint audit result

Date: 2026-08-20

## Result

The one preregistered importer pass classified all 15 direct theorem
dependencies of the failed joint quotient/remainder proof:

| class | count |
|---|---:|
| empty footprint | 14 |
| `propext`-bearing | 1 |
| other assumption-bearing | 0 |

The sole carrier is official `Nat.sub_add_cancel`. Its direct theorem
dependencies are `Nat.add_comm`, `Nat.add_sub_of_le`, and `congrArg`; its own
kernel-derived footprint is `[propext]`.

Every other direct dependency is empty-footprint, including the two recursive
computation roots, `Nat.div_rec_fuel_lemma`, all multiplication/addition facts,
the contradiction at zero fuel, equality congruence, and `dif_pos`/`dif_neg`.

## Consequence

The constructive Euclidean route does not need a new division algorithm or a
broad trusted import. It needs one bottom-up subtraction-restoration proof that
does not reuse official `Nat.sub_add_cancel` or another assumption-bearing path.

That replacement should be separately preregistered and independently authored
from primitive Nat recursion/equations. Only after its own footprint is empty
may a new joint-invariant source replace the single contaminated dependency and
resume the two-reconstruction requirement.

## Assurance boundary

The audit read the immutable stream exactly once through Axeyum's importer. It
reported declaration identities, direct theorem dependencies, and axiom
footprints only. It rendered no proof term or theorem value and granted no
support theorem, target, evaluation, fact, or ledger credit.

The exact producer source and its exact JSON output were frozen before three
Clippy-only cleanups to the reusable tracked example. The audit was not rerun.
The external receipt binds both versions and has SHA-256
`fc6cffc7baec14790cc4f23461389c5ef229ccb5281ffea5c317efc91b7031f5`.

## Verification

```sh
python3 scripts/check-autogenesis-euclidean-dependency-footprint-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_euclidean_dependency_footprint_audit_result
```
