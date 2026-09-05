# Two deficiencies found by lanes on 2026-08-27

Both were found by lanes doing something else, and both were reported rather
than worked around. Neither is fixed here.

## 1. RETRACTED — the `Rat.sumRange` reindexing already existed

**This section originally asserted that `Rat.sumRange` had no diagonal/rectangle
<!-- was-absent: Rat.sumRange -->
double-sum reindexing, and dispatched an Opus lane against it. That was wrong,
and the error was the coordinator's.**
<!-- was-absent: Rat.sumRange_diagonal, Rat.sumRange_rect_eq_diag_add_corner, Complex.sumRange_mul_eq_diag_add_corner -- the retracted claim; `scripts/check-absence-claims.py` would have gone red on the `absent:` form the day these landed -->

It already existed, in two places:

- **`rat_prelude/diagonal.rs`** — `Rat.sumRange_split`,
  `Rat.sumRange_diagonal`, `Rat.sumRange_rect_eq_diag_add_corner`, landed
  earlier by lane `rat-cauchy-diagonal` (`a9fd852cb`).
- **`complex.rs`** — `Complex.sumRange_mul`, `Complex.sumRange_mul_double`,
  `Complex.sumRange_mul_eq_diag_add_corner` had already run the same argument
  over ℂ's setoid, **including the two-bound form that `diagonal.rs`'s own
  module doc said was missing.**

The second is hiding place #1 exactly: general infrastructure filed under its
first consumer's module, invisible to any ℚ- or ℕ-shaped search.

### What the lane did with the retraction, which was the right thing

Rather than stopping, it **transported from `complex.rs`** — deliberately not
from `nat_prelude`, because the argument touches no `Nat.sub` and no index
arithmetic at all (`mul_comm` + `mul_sumRange` + `sumRange_congr`), making the
port a substitution: `Equiv`/`equiv_trans` → `Eq`/`rchain`,
`const_app(p.mul,…)` → `rmul`. Re-deriving would have left a **fourth** proof of
one fact to keep in sync across `Nat`, `ℂ`, `CReal` and `ℚ`.

**All five theorems were kernel-accepted on the first attempt.** Landed:

    Rat.sumRange_mul, Rat.sumRange_mul_double (two INDEPENDENT bounds),
    Rat.sumRange_mul_eq_diag_add_corner, Rat.pow_add, Rat.pow_sub_add

The two-bound gap closed **without touching the rectangle theorem**:
`diagonal.rs`'s premise was right (the square is same-bound) and its conclusion
wrong — the generality comes from the step *before* the rectangle, which cannot
care whether the bounds agree.

### The one real ℚ-vs-ℕ divergence

**`Rat.mul` renormalises, so unit and zero laws are laws rather than `Eq.refl`.**
`pow_add`'s base case needs `Rat.mul_one` where `Nat.pow_add` needed nothing —
the same place `Rat.mul_sumRange` needs `Rat.mul_zero`. Nothing else about ℚ is
harder; the reindexing is index-level and ℚ never sees it.

### A vacuous test the lane caught on itself

Its first corner test at `n = 2` **could not fail**: the corner is the single
cell `i = 1`, where `n−i = 1 = i`, so `g((n−i)+k)` and `g(i+k)` are literally the
same term and a transposed index is invisible. At `n = 3` the same transposition
moves the corner 66 → 150. Both tests now carry in-test discriminators, so a
`def_eq` returning `true` for everything would fail *there* rather than silently
passing the negative control.

It also recorded a limit worth keeping: `Σ_{i≤k} f i·g(k−i)` and
`Σ_{i≤k} f(k−i)·g i` are the same sum reindexed, so **no instance can separate
them** — that swap is caught by reading, never by computing.

### Still open

`Rat.polyEval_mul` did **not** land, and the lane recommends it not land under
that name: the corner does not simplify to a `polyEval`, so the honest statement
is a three-term identity. General-degree `Rat` Taylor was not attempted; its
offset reindexing (`Σ_{i=k+1}^{n-1}`) is now supplied by `Rat.sumRange_split`,
but the fit was not verified.

## 2. Two tools disagree on how many `Nat` theorems exist, and the ledger's
   denominator is the loser

The fact-generation lane found:

| tool | `Nat.*` theorems |
| --- | --- |
| `kernel_declaration_projection` (the generator's source) | **338** |
| `prelude_theorem_inventory --include-constructed` (coverage's denominator) | **329** |

The 9-theorem gap traces exactly to the **`Nat.Peano.*` family**, which the first
tool enumerates and the second does not.

The consequence is quiet and specific: all 9 facts were generated and pass
`--audit`, but they **cannot move the `registered` counter**, because the
denominator never reaches them. So the ledger under-reports its own coverage, and
nothing fails — the numbers simply do not add up, in a direction nobody would
notice.

This is a variant of a trap CLAUDE.md already documents: *an empty result from a
tool that was never pointed at your subject is indistinguishable from a strong
negative result.* Here it is not empty, just short by nine, which is worse —
a partial answer is far more convincing than a blank one.

**Do not assume the inventory is the one that is wrong.** It excludes
`Axiom`, `Definition`, `Opaque`, `Inductive`, `Constructor`, `Recursor` and
`Quotient` by construction, and those exclusions are deliberate. The question to
answer first is *what kind of declaration `Nat.Peano.*` actually is* — read it
from `kernel.environment()`, not from either tool's output, and not from the
name.
