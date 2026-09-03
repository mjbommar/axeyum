# Lane: echelon-invariant — ADR-1554's obligations 3 and 4 for the row-echelon form over ℚ

<!-- plan-section: lane-status -->

**echelon-invariant (`DONE, with one deliverable explicitly NOT landed`,
2026-09-02).** Sixteen axiom-free declarations (fifteen `Rat`, one `Nat`), five
commits, eight facts, ADR-1571.

**Landed.** `Nat.lt_of_ble_eq_false` — the STRICT false-side `ble` bridge three
consumers were owed (ADR-1558 §4, ADR-1562 §4), promoted into `nat_prelude` and
spent exactly once. **ADR-1554 obligation 3 CLOSED**: `Rat.clearBelow_off`,
`Rat.clearBelow_zero` and the arithmetic core `Rat.add_neg_div_mul_cancel`, with
the fuelled form of each. **Obligation 2 COMPLETE**: `Rat.pivotSearch_column_zero`
is the exhaustion disjunct ADR-1562 recorded open, and with the range half
(ADR-1558) and the value half (ADR-1562) that obligation is now the first of the
four to close outright. Three of obligation 4's four prerequisites:
`Rat.leadingIndex_eq_of_first_nonzero`, `Rat.leadingIndex_eq_cols_of_zero_row`
and `Rat.clearBelow_preserves_zero`.

**NOT landed, and this is the deliverable the brief led with.**
`Rat.rowEchelon_isEchelon` is not proved, the pivot section is not derived, and
therefore ADR-1562's bridge is still conditional: `Rat.rank_eq_rankCols`,
`Rat.rank_le_cols` and the row-form rank-nullity remain `_of_pivotSection`, and
rank invariance under the elementary row operations was not attempted. **The
next lane's exact starting point** is ADR-1571 §3's table: one prerequisite is
still missing (`Rat.rowSwap` preserving a zero range over `[pr, rows)`, which
the pivot step needs because the swap happens BEFORE the sweep and between two
rows both in that range), and after it the invariant `Prop` and two inductions —
the fuel induction that preserves it and the exit derivation over
`isEchelonAux`'s own fuel. The sizing correction worth carrying: ADR-1554 called
obligation 4 "the loop invariant", and the loop invariant is only the last two
rows of that table; the four rows above it are separate lemmas about three
different functions and none was visible in the original sizing.

**Two findings that generalise.** (1) A fuelled recursion's postcondition needs
a fuel bound **iff its conclusion is false of the recursion's exhaustion
answer**. `clearBelow_zero` and `clearBelow_preserves_zero` are the same
function one hypothesis apart, and which way the conclusion points is the only
difference — the first needs `Lt q (r + fuel)` and refutes its exhaustion
branches, the second needs nothing and closes them from the hypothesis. (2) The
lambda that BUILDS a `Not (…)` must bind its argument at the equation, not at
the negation; binding at `Not (…)` gives `Not (Not (…))` and the kernel answers
with a bare `TypeMismatch` between two consecutive `ExprId`s, naming nothing.
One `eprintln` per `declare_*` call found it in a single rebuild.

**The dominance document's "no `rank` function at all" row is corrected in
place** (`docs/formalized-math-2026-08/09-*.md` §4.3), following ADR-1543's
precedent for the determinant. Measured on a fresh index (2,201 declarations),
`shape_search --ns Rat --name-contains rank` returns 14. What a referee should
check is not an absence but "built, with one open equation between its two
forms".

**Cost.** `rat` prelude 1.683–1.705 s (`prelude_build_timing`, four runs)
against 1.653–1.660 s measured on the same host three commits earlier, so this
IS a delta and not merely a level: the sixteen declarations cost ~30–45 ms. The
family is now marginally above the ~1.65 s it was told to watch and inside the
~1.7 s band. `rat_prelude::` suite 217 passed before the last two commits;
`clear_below_tests` 9, `leading_index_tests` 4, `pivot_content_tests` 5.

**Did not run.** No workspace sweep, no `just check`, no `check.sh`, no push.
Clippy was run as `-p axeyum-lean-kernel --all-targets -- -D warnings` and is
clean; nothing wider was attempted, so this lane makes no claim about the
aggregate gate.

<!-- plan-section: landed-changes -->

| 2026-09-02 | echelon-invariant | `Nat.lt_of_ble_eq_false`: the strict false-side `ble` bridge, promoted into `nat_prelude` |
| 2026-09-02 | echelon-invariant | ADR-1554 obligation 3 closed — `Rat.clearBelow_off`/`_zero` + `Rat.add_neg_div_mul_cancel` |
| 2026-09-02 | echelon-invariant | Obligation 2 completed — `Rat.pivotSearch_column_zero`, the exhaustion disjunct |
| 2026-09-02 | echelon-invariant | `Rat.leadingIndex` characterized in both directions (first-nonzero, zero row) |
| 2026-09-02 | echelon-invariant | `Rat.clearBelow_preserves_zero` — a zero column survives the sweep, with no fuel bound |
| 2026-09-02 | echelon-invariant | ADR-1571; eight facts; the dominance document's "no `rank`" row corrected |
