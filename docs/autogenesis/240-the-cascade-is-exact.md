# 240 — The adapter cascade is exact, measured rather than predicted

**Measured 2026-08-22** at `50307d833`, through
`cargo run -p axeyum-lean-import --example statement_reflexivity_coverage`
against the real archive
(`26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1`, 138 streams).

## What was predicted

Commit `ef0e23447` bridged four statement-adapter first-blockers —
`Nat.lt_irrefl`, `Or.elim`, `if_pos`, `of_decide_eq_true`. Its message recorded
the resulting distribution as **NOT MEASURED**, and said so explicitly rather
than quoting the prediction as a number. This document is that measurement.

## What was measured

The census is unchanged, which was expected: bridging a blocker moves a row to
its *next* blocker, it does not admit the row.

    adapter-rejection                     114
    producer-decline:terminal-not-exact-equality  15
    kernel-rejection:candidate-typecheck-failed    7
    admissible-proof                               2

The first-blocker distribution, before and after:

| before | rows | after | moved |
|---|---:|---|---|
| `Nat.lt_irrefl` | 38 | `Nat.div_rec_lemma` | ✓ |
| `eq_self` | 20 | `eq_self` | — genuine decline |
| `Quot` | 19 | `Quot` | — architectural |
| `if_pos` | 18 | `dif_neg` | ✓ |
| `Or.elim` | 15 | `Or.resolve_right` | ✓ |
| `of_decide_eq_true` | 3 | `ne_true_of_eq_false` | ✓ |
| `propext` | 1 | `propext` | — architectural |

**Every bridged name vanished, and every count is preserved to the unit**:
38 → 38, 18 → 18, 15 → 15, 3 → 3. The three untouched names are unchanged.

## Why the exactness is the finding

A bridge could have failed in two ways that a census total cannot distinguish.
It could have admitted nothing, leaving its name in place — the counts would be
identical and the name would still be there. Or it could have moved *some* rows
and not others, splitting a block across two successors. Neither happened: each
block moved intact to a single successor.

That tells us something the totals do not. **The blocker sets are per-row
ordered and highly uniform** — the 38 rows blocked on `Nat.lt_irrefl` were all
also blocked on `Nat.div_rec_lemma`, in that order, and on nothing between them.
So the wall is a small number of deep, homogeneous columns rather than a broad
scatter, and clearing it is a sequence of cheap steps rather than a long tail.

Two of the four successors are things this repository already has. Our own logic
prelude proved `Or.resolve_right` the same day, and `ne_true_of_eq_false` is a
near-relative of the `Bool.false ≠ Bool.true` discriminator built for
`of_decide_eq_true`. That is the third consecutive round where the largest
blocker turned out to be already reconstructed and merely unexposed
(`Nat.zero_le`, then `Nat.lt_irrefl`).

## Isolation

Rows by partition: **train 78, development 60, held-out 0**. The archive is
`train-development` by construction, so no held-out statement is read by this
diagnostic at all. The observation is stamped
`state: diagnostic-no-ledger-credit` with `ledger_writes: 0` and
`executor_invocations: 0`.

## What this does not say

It does not say the 114 are close to admitted. Bridging four blockers moved four
blocks one step; `eq_self` (20 rows) needs `propext`, which this kernel does not
have, and `Quot` (19 rows) is architectural. Those 39 rows are not a queue item.
The measurement says the *remaining* 75 are moving predictably, not that the
wall is nearly down.
