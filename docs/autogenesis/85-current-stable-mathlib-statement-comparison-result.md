# Current-stable Mathlib statement comparison result

Date: 2026-08-20

## Result

The unchanged statement-only extractor successfully ran against pinned stable
Mathlib v4.32.1 and Lean v4.32.1. The new external inventory contains 9,822
sorted unique Nat/Int theorem rows—93 more than the v4.30.0 baseline—and no
field other than name, module, universe parameters, pretty type, and structural
type representation.

Across the 240 previously selected v4.30 candidates:

| Classification | Count |
|---|---:|
| Structurally identical, same pretty type and module | 234 |
| Module-only drift | 2 |
| Structural type drift | 3 |
| Absent in v4.32.1 | 1 |
| Pretty-type-only drift | 0 |

This is strong statement-surface stability: 97.5% of the selected population is
unchanged in every measured type dimension, and 98.3% retains the same
structural proposition after ignoring module provenance.

## Exact drift

The six non-identical rows are concentrated in three themes:

- `Nat.fib_dvd` changes from the expanded implication
  `∀ m n, m ∣ n → fib m ∣ fib n` to the packaged statement
  `IsDvdSequence Nat.fib`.
- `Nat.Coprime.symmetric` changes its symmetry wrapper from `Symmetric` to
  `Std.Symm`.
- `Nat.Prime.dvd_of_dvd_pow` keeps the identical pretty-printed proposition but
  has a different structural expression identity.
- `Nat.sqrt_le` and `Nat.lt_succ_sqrt` retain identical propositions but move
  from `Mathlib.Data.Nat.Sqrt` to `Init.Data.Nat.Sqrt.Lemmas`.
- `Nat.sqrt.iter_sq_le` is absent under its old name.

The comparator deliberately labels the prime row structural drift despite its
identical pretty text. Human-readable equality is not kernel identity, so that
row requires a later expression-level explanation before it can count as
portable. The generated result now binds the exact constant-multiset deltas:
`IsDvdSequence` replaces the expanded Fibonacci relation, `Std.Symm` replaces
`Symmetric`, and the prime theorem's power instance changes from
`Monoid.toPow` to `NPow.toPow` through `Monoid.toNPow`.

## External inventory

The bulk artifact remains outside Git:

`/nas3/data/axeyum/autogenesis/sources/mathlib-v4.32.1-nat-int-statement-inventory-v1.ndjson`

| Property | Value |
|---|---|
| SHA-256 | `22246f40ae5a9b7f44a914313a5a212104b541d48974df4bf439da4006e61e5e` |
| Bytes | 39,619,602 |
| Records | 9,822 |
| Mode | `0444` |
| Mathlib | v4.32.1, `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| Lean | v4.32.1, `f054605aea4b840552cca2e725580bffd1e1b704` |

The tracked comparison is
[`mathlib-v4.30.0-v4.32.1-selected-statement-delta-v1.json`](../../artifacts/autogenesis/mathlib-v4.30.0-v4.32.1-selected-statement-delta-v1.json).
It binds every candidate and current row by hash, includes all 240
classifications, and records zero proof, execution, evaluation, fact, or ledger
authority.

## Interpretation

The result supports keeping v4.30.0 as Axeyum's current executable baseline
while treating cross-version statement survival as a generalization measure.
It does not justify mixing environments or importing v4.32.1 proofs. A future
migration should first explain the four structural/absent rows, rerun the
proof-isolated importer corpus against a separately pinned toolchain, and only
then compare reconstruction outcomes.

Over the horizon, the two module moves are positive architectural evidence:
some basic square-root facts are descending from Mathlib into Lean's `Init`
surface, reducing the external library layer Axeyum must eventually replace.

## Verification

```sh
python3 scripts/gen-autogenesis-mathlib-stable-statement-comparison.py --check
python3 -m unittest \
  scripts.tests.test_gen_autogenesis_mathlib_stable_statement_comparison
```
