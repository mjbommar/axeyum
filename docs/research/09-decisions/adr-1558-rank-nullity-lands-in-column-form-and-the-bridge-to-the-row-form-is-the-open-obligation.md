# ADR-1558: rank-nullity lands in COLUMN form, and the bridge to the row form is the open obligation — which needs a counting law the ℕ prelude does not have, not only `rowEchelon_isEchelon`

Status: accepted
Date: 2026-09-02
Index-summary: `Rat.rank_nullity : ∀ M rows cols,
Nat.add (rankCols M rows cols) (nullity M rows cols) = cols` lands as ONE
application of `Nat.countRange_compl`, symbolic in all three arguments and
using no property of `Rat.rowEchelon` whatever. Sixteen axiom-free
declarations in `rat_prelude/nullity.rs`. Three things are decided. (1)
`nullity` is NOT `cols - rank`: the subtraction form inherits `rank ≤ cols`,
which is open (ADR-1555, ADR-1554 obligation 4), whereas counting the
COMPLEMENT of the pivot-column predicate makes the theorem a fact about
counting rather than about elimination. The obligation does not vanish; it is
relocated, entirely, into the single bridge `rank = rankCols`. (2) The
relocation already pays: `rankCols ≤ cols` and `nullity ≤ cols` are both FREE
(one `Nat.countRange_le` each) where the row-form `rank ≤ cols` is not, because
a count over `[0, cols)` cannot exceed `cols` whatever the predicate does. (3)
**ADR-1555's sizing of the bridge is corrected.** It is not "where
`rowEchelon_isEchelon` is genuinely required" and nothing more. Measured here:
at symbolic arguments both sides `whnf` to a `Nat.rec` stuck on a DIFFERENT
free variable — `rows` on the row-form side, `cols` on the column-form side —
and all 23 `Nat.countRange_*` lemmas in the tree keep the SAME bound on both
sides of their equation. The bridge therefore needs a cross-bound counting law
that does not exist in this tree, IN ADDITION to obligation 4. The range half
of obligation 2 (`pivotSearch_le_rows`) lands here as its own commit, and
building it turned up a second gap: `Nat` has `le_of_ble_eq_true` and not its
false-side twin.
Index-status: accepted

Related: ADR-1554 (the row-echelon form and its four obligations), ADR-1555
(`Rat.rank`, and why invariance does not follow from the inverse laws),
ADR-0603 (graded statement families), ADR-0601 (one trust anchor).

## Context

ADR-1555's handoff sized rank-nullity downward and correctly: define the
counting on COLUMNS rather than subtracting, and `rankCols + nullity = cols`
becomes `Nat.countRange_compl`, which already exists in the ℕ prelude and needs
nothing about echelon form. That is exactly what happened, and it is worth being
precise about why it works, because the same move is available elsewhere.

The expensive definition is `nullity := cols - rank`. It is expensive not
because subtraction is hard but because the statement `rank + (cols - rank) =
cols` is FALSE in ℕ unless `rank ≤ cols` — truncated subtraction makes the
identity a theorem *about the bound*. And `rank ≤ cols` is precisely the claim
that the echelon form has at most one pivot per column, i.e. `rowEchelon_isEchelon`,
ADR-1554's obligation 4, which nobody has proved. So the subtraction form makes
rank-nullity strictly harder than the hardest open obligation in the family.

## Decision

### 1. Count the complement; do not subtract

```text
isPivotColB E rows cols j := some r < rows has leadingIndex E r cols = j
rankCols M rows cols      := countRange (isPivotColB (rowEchelon M rows cols) rows cols) cols
nullity  M rows cols      := countRange (setCompl (isPivotColB …)) cols
```

`isPivotColB` is a bounded scan over the rows, built on the same fuel idiom as
`Rat.pivotSearchAux`: fuel `rows`, both exhaustion answers `false`. The column
index comes LAST in the signature so that `isPivotColB E rows cols` is already
the `Nat → Bool` predicate `Nat.countRange` consumes — the same
argument-order discipline `Rat.nonzeroRowB` follows, and for the same reason
(a lambda at the use site is what `Nat.countRange_congr` cannot see through).

`nullity` is stated with `Nat.setCompl` and not with an inline
`fun j => if … then false else true`, so that `rank_nullity` is one application
of `Nat.countRange_compl` and not a re-proof of it.

The theorem is then:

```text
Rat.rank_nullity : ∀ M rows cols, Nat.add (rankCols M rows cols) (nullity M rows cols) = cols
                 := Nat.countRange_compl (isPivotColB (rowEchelon M rows cols) rows cols) cols
```

Symbolic in all three arguments. The matrix is never evaluated, `rowEchelon` is
never run, and no property of it is used — the theorem would hold verbatim if
`rowEchelon` were the identity. **That is the point, and it is also the limit:**
what the column form gives is a true and general partition of the columns; what
it does not give is that the partition is the one linear algebra means.

### 2. Both dimension bounds are free in the column form

`rankCols ≤ cols` and `nullity ≤ cols` are one `Nat.countRange_le` each. The
asymmetry with the row form is the whole payoff while the bridge is open: the
row-form count runs over `[0, rows)`, so bounding it by `cols` is a claim about
the echelon form; the column-form count runs over `[0, cols)`, and the bound
holds whatever the predicate does. The two statements are the same statement
only once the bridge is proved.

Both degenerate dimensions land as well. `rankCols M rows 0 = 0` and
`nullity M rows 0 = 0` are `Eq.refl`. `rankCols M 0 cols = 0` needs an
induction with the matrix generalised — the same shape
`Rat.countRange_nonzeroRowB_zero` needed, and for the same reason: in
`rankCols M 0 cols` the matrix is `rowEchelon M 0 cols`, which itself depends
on the row count. And `nullity M 0 cols = cols` is the **discriminating**
member of the four: a `nullity` that returned `0` identically satisfies the
other three and fails this one. Its proof reads `rank_nullity` backwards and
needs `Nat.zero_add`, because `Nat.add` recurses on its RIGHT argument and
`add 0 x` is not `x` by reduction here.

### 3. The bridge, measured — and it needs more than obligation 4

`Rat.rank M rows cols = Rat.rankCols M rows cols` did not land. ADR-1555 sized
it as "where `rowEchelon_isEchelon` is genuinely required". That is true and it
is not the whole cost. Measured on this tree, 2026-09-02:

```text
whnf(rank     M rows cols) : head=Nat.rec  spine=4  major premise = FVAR (rows) -- STUCK
whnf(rankCols M rows cols) : head=Nat.rec  spine=4  major premise = FVAR (cols) -- STUCK
def_eq(rank, rankCols) at symbolic arguments = false
declaring the bridge by Eq.refl -> Err(DeclarationValueMismatch { … })
```

Both sides reduce to a `Nat.rec` stuck on a **different** free variable. No
amount of reduction can bring them together, because they are counts over two
different ranges. And every counting law available:

- all 23 `Nat.countRange_*` declarations in the tree keep the SAME bound `n` on
  both sides of their equation (`countRange_permute` included — it permutes
  within `[0, n)` and does not relate two different bounds; `countRange_split`
  and `countRange_product` relate `n + m` and `n * m` to their parts, not two
  independent bounds under a bijection).

So the bridge needs a **cross-bound counting law** — informally, "a bijection
between the `p`-true part of `[0, n)` and the `q`-true part of `[0, m)` makes
the two counts equal" — which does not exist here, in addition to obligation 4
supplying the bijection (`r ↦ leadingIndex E r cols`, injective on the nonzero
rows because the leading indices strictly increase, and onto the pivot columns
by definition). Sizing the bridge as one obligation understates it by one
genuinely new ℕ theorem.

The bridge IS checked where it is decidable: `rank` and `rankCols` reduce to
the same number at all six evaluation matrices, including the rectangular one.
That is ADR-0603 row 3, not a substitute for the general statement.

### 4. Obligation 2's range half lands, and turns up a second gap

`Rat.pivotSearchAux_le_rows` and `Rat.pivotSearch_le_rows` — *the pivot scan
never returns an index past the row count* — land in `rat_prelude/pivot_bound.rs`.
ADR-1554's obligation 2 is a disjunction (the answer is `rows` and the column
is zero throughout the scanned range, or it is in range with a nonzero entry
there); both disjuncts assert `result ≤ rows`, and that much needs neither the
`Or` nor the bounded `∀`. The content half stays open.

Two things about the route are worth carrying forward.

The step splits twice, and **the two splits are not the same shape**. The inner
split on `isZeroB (M r c)` needs no hypothesis at all — one branch is the
induction hypothesis at `succ r`, the other is the row index `r`, and both are
already bounded — so it is a bare `Bool.rec` at a `Prop` motive rather than a
case analysis. Only the outer split on `Nat.ble rows r` needs its hypothesis,
because in the `false` branch the answer is `r` and `Le r rows` is simply false
without it. Recognising which splits are free is most of what made this cheap.

And the outer branch wants `ble a b = false → Le b a`, which **`Nat` does not
have**: the prelude carries `le_of_ble_eq_true` and not its false-side twin.
The `ipc` prelude has exactly the statement (`ipc_le_of_ble_eq_false`) and the
`rat` build does not carry it. It is rebuilt here as an INLINE step from
`Nat.le_total` and `Nat.ble_eq_true_of_le`, discharging the contradicting
disjunct through `Bool.true_ne_false`. Inline and not a declaration on purpose:
it is a ℕ fact, and a `Rat`-namespaced declaration of a ℕ fact is the naming
hazard `CLAUDE.md` warns about. A second consumer moves it to `nat_prelude`.

## Consequences

- **Rank-nullity is available now, in a form that is true, general, and
  axiom-free, and whose limits are stated rather than implied.** Anything that
  wants "the pivot columns and the free columns partition the columns" can have
  it today. Anything that wants "the number of free columns is the dimension of
  the kernel" still needs the bridge and needs a notion of kernel.
- **The cheapest next step toward the bridge is a ℕ theorem, not a ℚ one.** The
  cross-bound counting law is independent of everything about matrices and can
  be built and tested in `nat_prelude` against `countRange` alone. Doing it
  first turns the bridge into "supply the bijection", which is obligation 4 and
  nothing else.
- **`Nat.le_of_ble_eq_false` should exist.** Two preludes have now needed it and
  one of them (`ipc`) declared it under a non-`Nat` name. A third consumer
  should move it into `nat_prelude` rather than inline it again.
- The evaluation table gained a RECTANGULAR case (2×3). Every square matrix is
  blind to a rows/cols confusion by construction, and this family has four
  index arguments where such a confusion is easy; the rank lane's six-matrix
  table was all square. Any future definition here should carry one
  non-square case.
- ADR-0603 grading for this family: row 1 is the general constructive form
  (`rank_nullity`, `rankCols_le_cols`, `nullity_le_cols`, `nullity_zero_rows`);
  row 2 is **empty by proof**, as for ADR-1554 and ADR-1555 — the order on the
  constructed rationals is decidable and `isPivotColB` is total and
  `Bool`-valued, so there is no Markov-style boundary to refute; row 3 is the
  six-matrix table plus the bridge-by-reduction check in `nullity_tests.rs`;
  row 4 is empty — no import, nothing taken from Mathlib.

## Alternatives rejected

- **`nullity := cols - rank`.** Rejected in §1: it makes rank-nullity depend on
  `rank ≤ cols`, which is open, so it converts a free theorem into one strictly
  harder than the family's hardest obligation.
- **Redefining `rank` as `rankCols`.** This would make the bridge `Eq.refl` and
  is exactly the move ADR-1555 refused for the cap: a statement that holds
  because two things were defined to be the same is not a theorem relating them.
  The row form and the column form are different constructions and their
  agreement is a real fact about Gaussian elimination; collapsing them deletes
  the fact rather than proving it.
- **Capping `rankCols` at `cols`.** Unnecessary — the bound is already free —
  and it would hide a broken `isPivotColB`, the same objection ADR-1555 raised
  against capping `rank`.
- **Declaring the missing `ble`/`le` bridge as `Rat.le_of_ble_eq_false`.**
  Rejected: it is a ℕ fact and would sit in the wrong namespace, where nobody
  searching ℕ would find it. Inline until a second consumer justifies moving it
  to `nat_prelude` under its proper name.
