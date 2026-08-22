# What the adapter wall is actually made of, and what it costs to get through

Date: 2026-08-22

Supersedes the central claim of
[`233`](233-adapter-blocker-is-three-theorems.md), which was wrong.
Companion: [`235`](235-congrarg-congr-mt-substitution-result.md).

## The error being corrected

`233` reported that the 114 statements which never reach a producer are blocked
by four declarations — `congrArg` 56, `congr` 38, `mt` 19, `propext` 1 — and
called that "three theorems and one axiom, 114 of 114, no tail".

The counts were right. **`StatementImportError::TrustedDeclaration { name, kind }`
carries a single name**: it is raised on the *first* trusted declaration the
adapter hits, not on the closure. `233` read a first-hit distribution as a
complete one.

All three theorems have since been made self-derived and are never trusted
(`235`). Re-running the census with that active: they block **zero** of 114 rows,
and the outcome distribution is **unchanged at 114 / 15 / 7 / 2**. Five new
first-blockers took their place — `eq_of_heq` 41, `eq_self` 20, `Quot` 19,
`if_neg` 18, `ite_self` 15, `propext` 1.

## The real measurement

The streams carry their own trusted closure as `thm` records. Measured over all
114 adapter-rejected rows:

| | |
|---|---:|
| trusted theorems per statement | min **32** · p25 32 · median **86** · max **1,488** |
| total trusted theorem records | 27,237 |
| distinct trusted theorems | **1,615** |
| appear in **all 114** rows | 20 |

*(The first attempt at this counted `"theorem"` records and got zero, because the
export key is `thm`. An empty answer from a wrong query — the same failure this
document exists to correct, one level down.)*

The universal core is almost entirely the `Nat` order development:
`le_refl`, `le_trans`, `le_succ`, `succ_le_succ`, `zero_le`, `lt_succ_self`,
`sub_le`, `pred_le`, `pred_le_pred`, `le_of_lt_succ`, `succ_sub_succ_eq_sub`,
the `ble` ↔ `le` bridge, plus `congrArg`, `eq_of_heq` and `noConfusion_of_Nat`.

## What it costs — the planning curve

Greedy, most-shared-first, counting a row as unblocked only when its **entire**
closure is covered:

```text
prove    20 theorems  ->    0 of 114 rows      the universal core alone unblocks nothing
prove    50 theorems  ->   38 of 114  (33%)
prove   100 theorems  ->   53 of 114  (46%)
prove   200 theorems  ->   86 of 114  (75%)
prove   300–800       ->   86 of 114             a long plateau
prove 1,200 theorems  ->  101 of 114
prove 1,615 theorems  ->  114 of 114
```

Two things to read off it. **The first 20 buy nothing** — no row's closure is a
subset of the universal core, because the smallest closure is 32. And **the
curve is steep then flat**: 200 theorems buys 75% of the population, and the
remaining 28 rows cost 1,400 more.

For scale, our own `Nat` prelude is 139 theorems today. The 200 is not a research
programme; it is roughly doubling a development we have already done once.

## What this means for P4

Not a short substitution list, and not a config change. The route to those 114
rows is **building the elementary `Nat` order development ourselves** and
substituting our own proofs for the imported ones, exactly as `congrArg`,
`congr` and `mt` now are.

Of the top 50 most-shared theorems we already prove 8. The 42 we do not are
elementary: `Nat.le_refl`, `Nat.le_succ`, `Nat.succ_le_succ`, `Nat.pred_le`,
`Nat.sub_le`, `Nat.lt_succ_self`, `Nat.zero_lt_succ`, `Eq.symm`, and the
`Nat.ble` ↔ `Nat.le` bridge.

`Quot` and `propext` remain architecturally out of reach by substitution, and
`noConfusion_of_Nat` / `Nat.le.brecOn` / `Nat.div_rec_lemma` are kernel-generated
rather than hand-provable — they need a different treatment and are excluded from
the tranche above.

## The lesson, which is the point of keeping `233`

The numbers in `233` were checked. What was never checked is what the field
containing them *meant*. Verifying an arithmetic and verifying an interpretation
are different acts, and only the first one happened.
