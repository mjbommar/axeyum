# ADR-1562: the `rank = rankCols` bridge's ORIENTATION is the finding, and it collapses ADR-1554 obligation 4 to a single section equation

Status: accepted
Date: 2026-09-02
Index-summary: `Rat.rank_eq_rankCols_of_pivotSection` closes ADR-1558's open
bridge modulo ONE statement, and `Rat.rank_le_cols_of_pivotSection` (ADR-1555's
stated open bound) and `Rat.rank_nullity_rows_of_pivotSection` (rank-nullity in
the ROW form) fall out of it. Thirteen axiom-free declarations in
`rat_prelude/rank_bridge.rs`. Three things are decided. (1) **The orientation
of the counting law is not a presentation choice, it is the whole cost.**
Applying `Nat.countRange_bij` with the COLUMNS as the left-hand count — σ :=
`pivotRowOfCol`, τ := `pivotColOfRow` — makes the INJECTIVITY hypothesis free,
because `σ c₁ = σ c₂` gives `c₁ = c₂` by applying the leading index to both
sides. The other orientation needs injectivity of the leading index on the
nonzero rows, which IS obligation 4. Choosing the direction turned the hardest
hypothesis into a one-line one. (2) After that choice, four and a half of the
five hypotheses come from properties of the two SEARCHES and use nothing about
echelon form, so all of obligation 4 collapses into
`∀ r, Lt r rows → nonzeroRowB E cols r = true → pivotRowOfCol E rows cols
(pivotColOfRow E cols r) = r` — *the first row whose leading index is row `r`'s
is `r` itself*. That is strictly weaker than `isEchelon`: it says nothing about
zero rows sitting last. (3) The pivot-row map is declared as a `Definition` and
proved to be the SAME SCAN as ADR-1558's `Bool`-valued `isPivotColB`
(`isPivotColB E rows cols j = ble (succ (pivotRowOfCol E rows cols j)) rows`),
which is why nothing here re-derives a search. `Nat.le_of_ble_eq_false` is now
wanted by a THIRD consumer, and this one needs the STRICT form.
Index-status: accepted

Related: ADR-1554 (the row-echelon form and its four obligations), ADR-1555
(`Rat.rank`, and why `rank ≤ cols` is not free), ADR-1558 (rank-nullity in
column form, and the bridge as the open obligation), ADR-0603 (graded statement
families), ADR-0601 (one trust anchor).

## Context

ADR-1558 measured the bridge `Rat.rank M rows cols = Rat.rankCols M rows cols`
and found two things missing: a cross-bound counting law, and ADR-1554's
obligation 4 (`rowEchelon_isEchelon`) to supply the bijection. The counting law
landed on 2026-09-02 as `Nat.countRange_bij`. This ADR records what happened
when the bridge was actually attempted with it, and the result is not what
either previous ADR predicted.

`rank` counts the NONZERO ROWS of `E := rowEchelon M rows cols` over
`[0, rows)`. `rankCols` counts the PIVOT COLUMNS over `[0, cols)`.
`countRange_bij` equates two such counts given an injective σ, an inverse τ,
two `MapsInto` facts and two round-trip equations. There are two ways to point
it, and both previous ADRs described the bijection in the ROWS-first direction:
*"`r ↦ leadingIndex E r cols`, injective on the nonzero rows because the
leading indices strictly increase, and onto the pivot columns by definition"*
(ADR-1558 §3). That description is correct and it is the expensive direction.

## Decision

### 1. Point the counting law at the COLUMNS, and injectivity becomes free

Take `p := isPivotColB E rows cols` over `[0, cols)`, `q := nonzeroRowB E cols`
over `[0, rows)`, and therefore

```text
σ = Rat.pivotRowOfCol E rows cols   -- the first row < rows whose leading index is j
τ = Rat.pivotColOfRow E cols        -- fun r => leadingIndex E r cols
```

The conclusion is then `countRange p cols = countRange q rows`, i.e.
`rankCols = rank`, and one `Eq.symm` gives the stated orientation.

The injectivity hypothesis is now *σ injective on the pivot columns*: from
`σ c₁ = σ c₂`, apply `leadingIndex E · cols` to both sides and use
`Rat.leadingIndex_pivotRowOfCol` on each, which says the leading index of the
row `σ` found for column `c` is `c`. So `c₁ = c₂`, in three `Eq` steps and one
congruence.

In the rows-first direction the same hypothesis reads *the leading index is
injective on the nonzero rows*, which is the strictly-increasing property —
obligation 4 itself, the piece ADR-1554 sized as *"at least a lane on its own
and probably two"*. **The direction the counting law is pointed decides whether
its hardest hypothesis is a three-line lemma or the largest open obligation in
the family.** Nothing about the two definitions changed to make this true; only
which one was called `p`.

The general lesson, which is not about matrices: `countRange_bij`'s hypotheses
are not symmetric in strength. Injectivity of σ is demanded and injectivity of
τ is not, so **the side whose map has a cheap left inverse belongs on the
LEFT.** Here `pivotRowOfCol` is a section of the leading index by construction —
it searches for a row *with that leading index* — while the leading index has
no such property without echelon form.

### 2. The residue is one equation, and it is weaker than `isEchelon`

With the orientation fixed, the five hypotheses land as:

| hypothesis | discharged by | needs echelon form? |
|---|---|---|
| σ injective on pivot columns | `Rat.leadingIndex_pivotRowOfCol` | no |
| σ maps pivot columns to nonzero rows | `Rat.pivotRowOfCol_lt_rows` + the same | no |
| τ's range half (`Lt (τ r) cols`) | `Rat.nonzeroRowB_eq_ble` + `le_of_ble_eq_true` | no |
| τ (σ c) = c | `Rat.leadingIndex_pivotRowOfCol`, verbatim | no |
| σ (τ r) = r | **the section hypothesis** | YES |
| τ's selected half (`p (τ r) = true`) | the section hypothesis + `Rat.isPivotColB_eq_ble` | YES |

so the whole of obligation 4, as the bridge consumes it, is

```text
∀ r, Lt r rows → Eq Bool (nonzeroRowB E cols r) true →
  Eq Nat (pivotRowOfCol E rows cols (pivotColOfRow E cols r)) r
```

*The first row whose leading index equals row `r`'s leading index is `r`
itself.* This is **strictly weaker than `isEchelon E rows cols = true`**. The
echelon predicate also asserts that zero rows sit below nonzero ones
(`echelonStepOk`'s second clause, whose two conjuncts ADR-1554 explains are both
load-bearing); the section equation asserts nothing about zero rows at all. A
future `rowEchelon_isEchelon` implies it; so would a weaker lemma that only
proves the nonzero rows' leading indices distinct and increasing.

It is stated inline as a Pi, never as a named `Definition`. A named `Prop` could
be well-typed and mean something else; an inline Pi in the theorem's own type
cannot.

**The hypothesis is a real constraint, and this is checked rather than
asserted.** At `[[1,0],[1,0]]` — two nonzero rows sharing leading index `0`,
which is exactly the shape echelon form forbids — the section equation is FALSE
at row `1` by reduction, with a positive control showing it still holds at row
`0`. A conditional theorem whose hypothesis every matrix satisfies is an
unconditional theorem with a decoration, and that is the first thing to rule
out.

### 3. The `Bool` test and the `Nat` map are the same scan, proved once

ADR-1558's `isPivotColB` scans the rows for a leading index equal to `j` and
answers `Bool`. `Rat.pivotRowOfCol` scans the same rows in the same order with
the same fuel and answers the row index, `rows` when there is none. Rather than
re-deriving anything about `isPivotColB`, one fuel induction proves

```text
Rat.pivotColSearchAux_eq_ble : pivotColSearchAux E rows cols j fuel r
                                 = Nat.ble (succ (pivotRowSearchAux E rows cols j fuel r)) rows
```

and every `isPivotColB` fact in the bridge goes through its wrapper
`Rat.isPivotColB_eq_ble`. Two things about that induction are worth carrying
forward.

**The base case is not `Eq.refl`.** With no fuel the two scans answer `false`
and `rows`, and they agree only because `Nat.ble (succ rows) rows` is `false` —
an equation `Nat` does not carry, built here from `Nat.lt_irrefl` through a
two-way split on the `Bool` itself.

**The two splits in the step are not the same shape**, which is the observation
`pivot_bound.rs` recorded (ADR-1558 §4) and which held again. The inner split on
`Nat.beq (leadingIndex E r cols) j` is a bare `Bool.rec` at a `Prop` motive —
free, because both branch proofs exist without knowing which way the test went.
The outer split on `Nat.ble rows r` needs its hypothesis, because its `false`
branch is the only place a row index is known to be in range. In the sibling
induction `Rat.pivotRowSearchAux_leadingIndex` BOTH splits need theirs, because
there the inner `true` branch carries the entire conclusion
(`Nat.eq_of_beq_eq_true`). Recognising which splits are free is most of what
makes a fuel induction cheap, and it is not decidable from the shape of the
definition alone — it depends on what the motive says.

### 4. `Nat.le_of_ble_eq_false` is wanted by a third consumer, in a STRICTER form

ADR-1558 §4 recorded that `Nat` has `le_of_ble_eq_true` and not its false-side
twin, that `ipc` declared the statement under a non-`Nat` name, and that
`pivot_bound.rs` inlined it. This file is the third consumer — and it needed a
different statement. `pivot_bound.rs` splits on `Nat.le_total` and the surviving
disjunct is `Le b a`; the scans here need the STRICT `Lt b a`, because
`Nat.ble rows r = false` is the only place a row index is known to be in range
and the counting law's `MapsInto` demands `Lt`. Splitting on `Nat.lt_or_ge`
instead yields the strict form directly.

So the promotion `nat_prelude` is owed is `ble a b = false → Lt b a`, from which
the non-strict form follows and not conversely.

## Consequences

- **`rank ≤ cols` is no longer open.** ADR-1555 left it open and explained
  exactly why: it is a claim about the echelon form, where the column-form
  `rankCols ≤ cols` is one `Nat.countRange_le`. It is now one transport across
  the bridge. The same holds for **rank-nullity in the row form**, which is
  ADR-1558's column-form theorem with `rankCols` rewritten to `rank` — the
  receipt for that ADR's claim that the obligation was *relocated, entirely,
  into one bridge*.
- **The remaining work on this family is one statement, not four obligations.**
  Obligation 1 landed with ADR-1554; obligation 2's range half with ADR-1558;
  the cross-bound counting law on 2026-09-02. What is left for an unconditional
  `Rat.rank = Rat.rankCols` is the section equation, and the cheapest route to
  it is *not* the full `rowEchelon_isEchelon`: it is the loop invariant
  restricted to the nonzero rows' leading indices being distinct.
- **Obligation 2's content half and obligation 3 remain untouched by this
  lane**, and they are the prerequisites for that invariant rather than for the
  bridge. Sizing them as "on the bridge's critical path" would now be wrong.
- ADR-0603 grading for this family: row 1 is the general constructive form (the
  six facts); row 2 is **empty by proof**, as for ADR-1554, ADR-1555 and
  ADR-1558 — the order on the constructed rationals is decidable and every
  predicate here is total and `Bool`-valued, so there is no Markov-style
  boundary to refute; row 3 is `rat_prelude/rank_bridge_tests.rs`, which reduces
  both maps at the six matrices the rank and nullity lanes used and derives
  `pivotRowOfCol`'s expected answer FROM the leading indices the sibling test
  verified, so the two tables cannot agree while both being wrong; row 4 is
  empty — no import.
- The `rat` prelude builds in **1.63–1.64 s** with all thirteen declarations
  (`prelude_build_timing`, three consecutive runs on the dev box), which is at
  or under the ~1.7 s this family was told to watch. **No before-measurement was
  taken on this host, so this is a level and not a delta** — do not quote it as
  "the additions cost nothing". What can be said is that two fuel inductions
  over a matrix are cheap here for a structural reason: the fuel is symbolic and
  the matrix is never evaluated, so no `Rat` arithmetic runs during the build.

## Alternatives rejected

- **Pointing `countRange_bij` at the rows.** Rejected in §1: it is the direction
  both previous ADRs described, and it makes the injectivity hypothesis equal to
  obligation 4. This is the decision the ADR exists to record.
- **Assuming `Rat.isEchelon E rows cols = true` as the hypothesis.** It is the
  obvious hypothesis and it is stronger than necessary. Taking the section
  equation instead means a future obligation-4 lane may discharge the bridge
  without proving the zero-rows-last half of the echelon predicate, and it makes
  the statement pin (`the_bridge_statements_say_what_they_claim`) able to assert
  that `Rat.isEchelon` does NOT occur in the bridge's type.
- **Redefining `pivotRowOfCol` on top of `pivotColSearchAux`** so the two scans
  are the same declaration by construction, making `isPivotColB_eq_ble`
  unnecessary. Rejected because `pivotColSearchAux` returns a `Bool`, so
  recovering the row would need a second scan anyway; and because the identity
  as a THEOREM is checkable evidence that the two agree, where a shared
  definition would make the agreement true by fiat and unobservable.
- **Naming the section hypothesis as a `Definition`.** Rejected in §2: a named
  `Prop` can be well-typed and mean something else, and the whole family's
  discipline is that nothing here should be able to.
