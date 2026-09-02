# Lane: rank-bridge — the `Rat.rank = Rat.rankCols` bridge (ADR-1554 obligation 4)

<!-- plan-section: lane-status -->

**DONE (`rank-bridge`, 2026-09-02).** The bridge ADR-1558 left open now closes
**modulo one statement**, and the two theorems that were waiting behind it fall
out of it: `Rat.rank_le_cols_of_pivotSection` (the bound ADR-1555 explicitly
left open) and `Rat.rank_nullity_rows_of_pivotSection` (rank-nullity in the ROW
form). **Thirteen new declarations, all axiom-free**, in
`crates/axeyum-lean-kernel/src/rat_prelude/rank_bridge.rs`. `rat_prelude::`
**207 passed, 0 failed** (203 baseline + 8 new − the 4 already counted). Clippy
clean on `axeyum-lean-kernel --all-targets`. ADR-1562. Six facts.

## The finding: the orientation is the whole cost

`Nat.countRange_bij` (landed the same day by lane 422) equates two counts over
two different bounds given an injective `σ`, an inverse `τ`, two `MapsInto`
facts and two round trips. There are **two ways to point it at the bridge**, and
ADR-1555 and ADR-1558 both described the expensive one.

Point it with the **COLUMNS on the left** — `p := isPivotColB E rows cols` over
`[0, cols)`, `q := nonzeroRowB E cols` over `[0, rows)`, so `σ := pivotRowOfCol`
and `τ := pivotColOfRow` — and the **injectivity hypothesis becomes free**:
`σ c₁ = σ c₂` gives `c₁ = c₂` by applying the leading index to both sides, since
each side is its own column. Point it the other way, with the rows on the left,
and injectivity reads *the leading index is injective on the nonzero rows*,
which is the strictly-increasing property — **ADR-1554 obligation 4 itself**.
Nothing about the definitions changed; only which one was called `p`.

The transferable rule: `countRange_bij` demands injectivity of `σ` and not of
`τ`, so **the side whose map has a cheap left inverse belongs on the LEFT**.

## What is left, exactly

After that choice, four and a half of the five hypotheses come from properties
of the two SEARCHES and use nothing about echelon form. All of obligation 4, as
the bridge consumes it, is:

```text
∀ r, Lt r rows → nonzeroRowB E cols r = true →
  pivotRowOfCol E rows cols (pivotColOfRow E cols r) = r
```

*"the first row whose leading index is row `r`'s leading index is `r` itself."*
This is **strictly weaker than `isEchelon E rows cols = true`** — it says nothing
about zero rows sitting last, only that no earlier nonzero row shares a nonzero
row's leading index. A future `rowEchelon_isEchelon` implies it; so would a
weaker lemma proving only that the nonzero rows' leading indices are distinct.

## What landed

```text
Rat.pivotColOfRow E cols r  := leadingIndex E r cols                    -- σ
Rat.pivotRowOfCol E rows cols j                                          -- τ
  := the first row < rows whose leading index is j, `rows` when none
Rat.pivotColSearchAux_eq_ble  : the Bool scan and the Nat scan are the same scan
Rat.isPivotColB_eq_ble        : isPivotColB … j = ble (succ (pivotRowOfCol … j)) rows
Rat.pivotRowOfCol_lt_rows     : a pivot column's row exists
Rat.pivotRowSearchAux_leadingIndex, Rat.leadingIndex_pivotRowOfCol
                              : the row found leads in the column asked for
Rat.rank_eq_rankCols_of_pivotSection    -- the bridge
Rat.rank_le_cols_of_pivotSection        -- ADR-1555's open bound
Rat.rank_nullity_rows_of_pivotSection   -- rank-nullity, ROW form
```

plus the two definitions' `Eq.refl` equations and the fuelled `pivotRowSearchAux`.

`Rat.leadingIndex_pivotRowOfCol` is the load-bearing one: it supplies THREE of
the counting law's five hypotheses at once (injectivity, the selected half of
`σ`'s `MapsInto`, and one round trip verbatim).

## Two things for whoever proves the residue

**The two splits in a fuel induction are not the same shape, and recognising
which is free is most of the cost.** `pivot_bound.rs` recorded this (ADR-1558
§4) and it held again, differently in each of this lane's two inductions. In
`pivotColSearchAux_eq_ble` the inner split on the leading-index test is a bare
`Bool.rec` at a `Prop` motive — free, because both branch proofs exist without
knowing the answer — while the outer split on `Nat.ble rows r` needs its
hypothesis, its `false` branch being the only place a row index is known to be
in range. In `pivotRowSearchAux_leadingIndex` BOTH need theirs, because the
inner `true` branch carries the whole conclusion. It is not decidable from the
shape of the definition; it depends on what the motive says.

**`Nat.le_of_ble_eq_false` is now wanted by a THIRD consumer, and this one
needed the STRICT form.** `ipc` declared it under a non-`Nat` name;
`pivot_bound.rs` inlined it from `Nat.le_total`, which yields only `Le b a`. The
scans here need `ble a b = false → Lt b a`, because the counting law's
`MapsInto` demands `Lt`; `Nat.lt_or_ge` gives it directly, and the non-strict
form follows from it and not conversely. That is the statement `nat_prelude`
is owed.

## Evidence, and what the negative control shows

- **The bridge's hypothesis is a real constraint, not a decoration.** At
  `[[1,0],[1,0]]` — two nonzero rows sharing leading index `0` — the section
  equation is FALSE at row `1` by reduction, with a positive control showing it
  still holds at row `0`. A conditional theorem whose hypothesis every matrix
  satisfies is an unconditional theorem with extra words, and that is the first
  thing this family had to rule out.
- **The evaluation table is derived, not typed twice.** `pivotRowOfCol`'s
  expected answer at each column is computed FROM the leading indices that the
  sibling test verified independently, so the two tables cannot agree while both
  being wrong. The read-back is a search over candidate answers, so a wrong
  definition is reported as the number it actually is.
- **The three headline statements are pinned by their rendered type from the
  environment, each with a FORBIDDEN substring**: the bridge must not mention
  `Rat.isEchelon` (its hypothesis is strictly weaker), the bound must be
  `≤ cols` and not `≤ rows` (which is already free), and the row form must not
  be the column form under a new name.
- The axiom-freedom tests ask the environment whether each name EXISTS before
  reading its footprint. `Kernel::axiom_footprint` of an undeclared name is
  empty, so without that question the test passes for declarations that do not
  exist.

## What is NOT done, precisely

**`Rat.rowEchelon_isEchelon` is not proved**, so nothing in this family is
unconditional. **ADR-1554 obligation 2's CONTENT half and obligation 3
(`clearBelow`'s postcondition) were not attempted by this lane** — and the
bridge shows they are prerequisites for the loop invariant, not for the bridge,
so sizing them as "on the bridge's critical path" would now be wrong. This lane
deviated from its brief's ordering deliberately: the brief put obligations 2 and
3 before the invariant, but once the orientation collapsed obligation 4 to one
equation, neither was on the path to anything this lane could land.

`prelude_build_timing`: `rat` at **1.63–1.64 s** over three consecutive runs.
**No before-measurement was taken on this host**, so that is a level and not a
delta — do not quote it as "the additions cost nothing".

<!-- plan-section: landed-changes -->

| 2026-09-02 | rank-bridge | `Rat.rank_eq_rankCols_of_pivotSection`: the bridge ADR-1558 left open, closed modulo ONE section equation instead of all of obligation 4 |
| 2026-09-02 | rank-bridge | the finding is the ORIENTATION — pointing `Nat.countRange_bij` at the columns makes its injectivity hypothesis free, where the rows-first direction ADR-1555/1558 described makes it obligation 4 |
| 2026-09-02 | rank-bridge | `Rat.rank_le_cols_of_pivotSection`: the bound ADR-1555 explicitly left open, now one transport from the free column-form bound |
| 2026-09-02 | rank-bridge | `Rat.rank_nullity_rows_of_pivotSection`: rank-nullity in the ROW form, the receipt for ADR-1558's claim that the obligation was relocated into one bridge |
| 2026-09-02 | rank-bridge | `Rat.pivotColOfRow` and `Rat.pivotRowOfCol` as computed `Definition`s, evaluated at the six matrices the rank and nullity lanes used |
| 2026-09-02 | rank-bridge | `Rat.isPivotColB_eq_ble`: ADR-1558's `Bool` pivot-column test and the `Nat` pivot-row map are the same scan, so nothing here re-derives a search |
| 2026-09-02 | rank-bridge | `Nat.le_of_ble_eq_false` is wanted by a THIRD consumer and this one needs the STRICT form (`ble a b = false → Lt b a`, via `lt_or_ge`); that is the statement `nat_prelude` is owed |
| 2026-09-02 | rank-bridge | six facts, all `proved` / `kernel-lean` / footprint `[]`, each checker pinning the rendered type and a row count of 4 or 8 across the preludes that build the rationals |
