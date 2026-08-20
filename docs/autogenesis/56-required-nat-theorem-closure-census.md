# Required Nat theorem closure census

Date: 2026-08-20

## Result

The seven native lemmas in the frozen Fibonacci-coprimality proof plan do not
need one monolithic prelude-composition repair. Their checked declaration
closures expose a smaller first step:

| Required theorem | Native dependencies | Missing from `r082` | Structural mismatches reached |
|---|---:|---:|---|
| `Nat.add_comm` | 10 | 2 | none |
| `Nat.dvd_add_iff_right` | 47 | 27 | `Nat.le_trans`, `Nat.zero_le` |
| `Nat.dvd_gcd` | 90 | 51 | 6 |
| `Nat.eq_one_of_dvd_one` | 33 | 12 | 4 |
| `Nat.gcd_dvd_left` | 94 | 55 | 6 |
| `Nat.gcd_dvd_right` | 94 | 55 | 6 |
| `Nat.gcd_zero_left` | 54 | 17 | 6 |

The six-name structural set reached by the larger closures is `Bool.rec`,
`Nat.le_of_succ_le_succ`, `Nat.le_trans`, `Nat.mod_lt`,
`Nat.not_succ_le_zero`, and `Nat.zero_le`. The other two unresolved overlaps,
`Nat.lt_irrefl` and `Nat.lt_of_lt_of_le`, are irrelevant to this seven-lemma
surface and should not block it.

## First composition slice

`Nat.add_comm` depends on exactly ten declarations:

- exact in the import: `Nat`, `Nat.zero`;
- alpha-type compatible: `Nat.add`, `Nat.rec`, `Nat.succ`;
- kernel-type-shape compatible: `Eq`, `Eq.rec`, `Eq.refl`;
- absent and therefore to be constructed: `Nat.succ_add`, `Nat.zero_add`;
- structurally mismatched: none.

This is the next bottom-up increment. A fresh imported kernel should first
validate the eight reused declaration types under the conservative compatibility
contract, then transactionally add `Nat.zero_add`, `Nat.succ_add`, and
`Nat.add_comm` through the ordinary trusted gate. A negative control must alter
one reused type and prove the entire attempt rolls back. Success establishes
only this three-theorem slice; it does not authorize the remaining six lemmas or
the Fibonacci target.

## Why this sequence is holistic

Bridging all eight representation mismatches up front would mix independent
problems: recursor branch order, typeclass-expanded order relations, numeric
literal elaboration, and modular arithmetic. The closure census instead orders
work by what the target actually reaches. It gives the flywheel one reusable
arithmetic theorem early while retaining a fail-closed boundary around the
genuinely different imported representations.

## Evidence and authority

The immutable observation is
`/nas3/data/axeyum/autogenesis/probes/8dbd18c82-fib-coprime-required-closure-v4/observation.json`.
The checker verifies every closure is a sorted, disjoint, exhaustive partition
of its measured dependency count. The run displayed no proof bodies, invoked no
proof search, submitted no target theorem, and wrote no ledger fact.

Verify it with:

```sh
python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
```

The subsequent
[checked composition result](57-first-native-nat-composition.md) admits the
three-theorem `Nat.add_comm` slice over the imported environment and confirms
the structural-mismatch rollback control.
