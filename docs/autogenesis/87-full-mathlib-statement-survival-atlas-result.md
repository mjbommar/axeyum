# Full Mathlib statement-survival atlas result

Date: 2026-08-20

## Result

The single pass preregistered in the
[atlas plan](86-full-mathlib-statement-survival-atlas-plan.md) classified every
`Nat.*` and `Int.*` theorem-statement name in the union of the immutable
Mathlib v4.30.0 and v4.32.1 inventories:

| class | Nat | Int | total |
|---|---:|---:|---:|
| structurally identical | 5,423 | 3,534 | 8,957 |
| module-only drift | 31 | 0 | 31 |
| pretty-type-only drift | 4 | 0 | 4 |
| structural-type drift | 541 | 179 | 720 |
| removed after v4.30.0 | 9 | 8 | 17 |
| added by v4.32.1 | 82 | 28 | 110 |
| **union** | **6,090** | **3,749** | **9,839** |

Of the 9,712 shared names, 8,957 (92.23%) retain exact structural statement
identity. The frozen 240-candidate nursery is more stable than the whole
surface: its previously measured 234 of 240 exact matches (97.5%) project from
the full atlas exactly, including all six exceptional rows.

## What the 720 structural drifts mean

They are not 720 changed mathematical propositions. Structural identity also
records elaborated typeclass projection paths and expression shape:

- 444 rows remove at least one `Monoid.toPow`; 414 have only the corresponding
  `Monoid.toNPow` / `NPow.toPow` and `Nat` or `Int` projection signature. This
  one representation migration accounts for 57.5% of all structural drifts.
- 65 rows change expression structure while retaining the same constant
  multiset.
- 122 structurally drifting names are visibly generated or internal names such
  as `_proof_`, `eq_def`, `_unary`, or match-congruence declarations. This
  category overlaps the two categories above.

The atlas therefore separates two questions that a raw changed-row count would
conflate: whether the proposition changed, and whether Lean's elaborated
representation changed. Alpha- or compatibility-based transport remains a
separate, fail-closed analysis; neither class authorizes declaration grafting.

## Additions, removals, and moves

Most removed names are generated instance proofs. The material public removal
cluster is the old implementation-facing square-root iterator surface,
including `Nat.sqrt.iter_sq_le` and `Nat.sqrt.lt_iter_succ_sq`. Public
`Nat.sqrt_le` and `Nat.lt_succ_sqrt` survive with exact types and move from
`Mathlib.Data.Nat.Sqrt` into `Init.Data.Nat.Sqrt.Lemmas`.

The 110 additions include useful public facts such as `Nat.gcd_right_comm`,
`Int.gcd_right_comm`, the strong divisibility-sequence API around Fibonacci,
and prime-factor/radical lemmas. They are observations about a newer reference
library, not imports and not automatic additions to Axeyum's target population.

## Durable evidence

The row-level delta remains outside Git at
`/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-v4.32.1-nat-int-statement-delta-v1.ndjson`.
It is 7,263,057 bytes, has 9,839 sorted rows, mode `0444`, and SHA-256
`718b06f2665b0539076ff4c1b598850b0a0a213e7fc6fa1281ee02e56cf50c44`.

Git tracks the aggregate atlas, its input and output identities, the generator,
the selected-population projection gate, tests, and this interpretation. The
artifact records zero proof-body reads, theorem-value reads, searches, kernel
submissions, executor calls, fact changes, evaluation credit, and ledger
writes.

## Consequence for the flywheel

The v4.30.0 statement nursery is not a disposable snapshot: most of its full
Nat/Int surface, and an even larger fraction of the selected bottom-up
population, survives two stable releases unchanged. The immediate proof path
should therefore continue against the frozen baseline while treating version
survival as measured metadata. A future baseline migration should normalize
known representation-wide projection changes before escalating the much
smaller residual set to theorem-level review.

## Verification

```sh
python3 scripts/gen-autogenesis-mathlib-full-statement-survival-atlas.py --check
python3 -m unittest \
  scripts.tests.test_gen_autogenesis_mathlib_full_statement_survival_atlas
```
