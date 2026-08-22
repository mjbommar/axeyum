# Where the Nat tranche got us, and why the next blockers are a different kind

Date: 2026-08-22

Follows [`236`](236-the-real-adapter-closure-and-what-it-costs.md), which measured
the wall. This measures what one day of proving moved, and what it exposed.

## What moved

| | morning | now |
|---|---:|---:|
| distinct theorems in the kernel | 418 | **440** |
| of the 50 most-needed blockers, proved by us | 8 | **28** |
| distinct theorems still missing across all closures | 1,615 | **1,497** |
| rows whose entire closure we prove ourselves | 0 | 0 |

Twenty-one elementary `Nat` order lemmas (`le_refl`, `le_succ`, `succ_le_succ`,
`sub_le`, `sub_lt`, `pred_le`, the `ble` ↔ `le` bridge, `Eq.symm`) plus
`CReal.archimedean`. All axiom-free, all from our own definitions, trusted
surface still 0 everywhere.

**Rows fully covered is still 0, and that is expected**: the smallest closure is
32 theorems and the curve in `236` says the first rows clear around 50 names.

One caveat on that zero, so it is not over-read: it counts only theorems our
kernel *declares*. `congrArg`, `congr` and `mt` are handled by **substitution at
import time** rather than by a declaration of ours, so they appear "missing" in
this measure while in fact blocking no row. The true covered count is therefore
slightly better than zero — the point stands that no row is clear yet.

## What it exposed

The universal blockers that remain are not more ordinary lemmas. Every one of
these is needed by all 114 rows:

| Blocker | Kind |
|---|---|
| `Nat.le.brecOn` | **kernel-generated** — course-of-values recursor |
| `noConfusion_of_Nat`, `noConfusion_of_Nat.aux` | **kernel-generated** — constructor disjointness |
| `Nat.div_rec_lemma`, `Nat.div_rec_fuel_lemma` | well-founded-recursion scaffolding |
| `eq_of_heq` | heterogeneous equality elimination |

These were deliberately excluded from the tranche, and the reason has now been
confirmed by measurement rather than assumed: **they are not theorems anyone
wrote.** Lean generates `brecOn` and `noConfusion` for an inductive type, and
`div_rec_lemma` exists to discharge a termination obligation.

So the next step is not "prove twenty more lemmas". Our kernel **also generates**
recursors for its inductives. The route is to generate our own equivalents and
substitute those, exactly as `congrArg` is now built from `Eq.rec` rather than
borrowed — a mechanism question, not a mathematics one.

`Nat.not_lt_zero` (76 rows) is the exception: an ordinary lemma, and the obvious
next hand-proved target.

## Why this is the right shape of finding

`233` claimed the wall was three theorems and was wrong. `236` measured it
properly: median 86 per statement, 1,615 distinct. This note is the first
evidence that the measurement is *actionable* — a day of work moved top-50
coverage from 8 to 28 and cut the missing set by 118, and the residue sorted
itself into two clearly different piles.

Hand-proving works and should continue for the ordinary lemmas. It will never
reach the generated ones, and now we know that before spending a week finding
out.
