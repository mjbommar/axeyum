# Lane: rat-rank-nullity — rank-nullity in COLUMN form, and what the bridge to the row form actually costs

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, rat-rank-nullity, 2026-09-02).** Eighteen
declarations landed across two new files — sixteen in
`crates/axeyum-lean-kernel/src/rat_prelude/nullity.rs` and two in
`crates/axeyum-lean-kernel/src/rat_prelude/pivot_bound.rs` — every one admitted
axiom-free (`Kernel::axiom_footprint` empty, read from the kernel by
`the_nullity_family_is_axiom_free` and `the_pivot_bound_family_is_axiom_free`).
ADR-1558 carries the design and one correction to ADR-1555's sizing of the
bridge. `rat_prelude::` is 199 passed / 0 failed in 166 s (rat-rank recorded
190 before this lane); `rat_prelude::nullity_tests` alone is 9. The `rat`
prelude builds in 1.65–1.77 s over five `prelude_build_timing` samples, against
a briefed baseline of ~1.6–1.85 s — no measurable change.

**The headline landed symbolically.**

```
Rat.rank_nullity : ∀ M rows cols, Nat.add (rankCols M rows cols) (nullity M rows cols) = cols
```

is ONE application of `Nat.countRange_compl`, symbolic in all three arguments.
Nothing in its proof uses any property of `Rat.rowEchelon` — it would hold
verbatim if the elimination were the identity. The definitions:

```
isPivotColB E rows cols j := some r < rows has leadingIndex E r cols = j   (bounded scan, pivotSearchAux shape)
rankCols M rows cols      := countRange (isPivotColB (rowEchelon M rows cols) rows cols) cols
nullity  M rows cols      := countRange (setCompl (isPivotColB …)) cols
```

`nullity := cols - rank` was refused, as briefed: truncated ℕ subtraction makes
`rank + (cols - rank) = cols` a theorem *about* `rank ≤ cols`, which is open.

Also landed: `rankCols_le_cols` and `nullity_le_cols`, both FREE (one
`Nat.countRange_le` each) where the row-form `rank ≤ cols` is not — the
column-form count runs over `[0, cols)` and the bound holds whatever the
predicate does. Both degenerate column counts by `Eq.refl`;
`rankCols_zero_rows` by an induction with the matrix generalised; and
`nullity_zero_rows : nullity M 0 cols = cols`, which is the discriminating one
— a `nullity` returning `0` identically satisfies the other three and fails
this. Its proof needs `Nat.zero_add`, because `Nat.add` recurses right and
`add 0 x` is not `x` by reduction.

**Evaluation table** (each reduced by `def_eq`, each with a control at
`want ± 1` that must FAIL):

| matrix | dims | `rankCols` | `nullity` | what only this row separates |
| --- | --- | --- | --- | --- |
| `[[1,2],[3,4]]` | 2×2 | 2 | 0 | kills "return `0`" on `rankCols` |
| `[[1,2],[2,4]]` | 2×2 | 1 | 1 | the zero ROW contributes no pivot column (its `leadingIndex` is `cols`, not a column index) |
| `[[0,0],[0,0]]` | 2×2 | 0 | 2 | kills "return `cols`" on `rankCols` |
| `[[1,2,3],[2,4,6],[1,1,1]]` | 3×3 | 2 | 1 | needs the ELIMINATION: the input's pivot columns would be `{0}` alone |
| 3×3 identity | 3×3 | 3 | 0 | separates "count pivot columns" from "count columns after the first" |
| `[[1,0,2],[0,1,3]]` | **2×3** | 2 | 1 | the only RECTANGULAR row, so the only one that can catch a rows/cols confusion |

The rectangular case is the one addition to the rank lane's six. Every square
matrix is blind to a rows/cols swap by construction, and this family has four
index arguments.

**`rank_nullity` was also instantiated, not only proved.**
`rank_nullity_holds_by_reduction_at_every_concrete_matrix` reduces both sides
at all six and checks the sum is `cols` and NOT `cols + 1`. That is the guard
against a definition pair satisfying the theorem vacuously.

**The bridge did not land, and ADR-1555's sizing of it was one theorem short.**
ADR-1555 says the content concentrates into `rank = rankCols`, "where
`rowEchelon_isEchelon` is genuinely required". True, and not the whole cost.
Measured here:

```
whnf(rank     M rows cols) : head=Nat.rec  spine=4  major premise = FVAR 1002 (rows) -- STUCK
whnf(rankCols M rows cols) : head=Nat.rec  spine=4  major premise = FVAR 1003 (cols) -- STUCK
def_eq(rank, rankCols) at symbolic arguments = false
declaring the bridge by Eq.refl -> Err(DeclarationValueMismatch { declared: ExprId(3590301), inferred: ExprId(3590332) })
```

**Both sides are stuck on a DIFFERENT free variable.** They are counts over two
different ranges, and every one of the 23 `Nat.countRange_*` declarations in the
tree keeps the SAME bound on both sides of its equation —
`countRange_permute` permutes within `[0, n)` and does not relate two bounds;
`countRange_split` and `countRange_product` relate `n + m` and `n * m` to their
parts, not two independent bounds under a bijection. So the bridge needs a
**cross-bound counting law that does not exist in this tree**, in addition to
obligation 4 supplying the bijection `r ↦ leadingIndex E r cols`. The bridge
was NOT faked by redefining `rank`; it is checked where it is decidable
(`rank` and `rankCols` reduce to the same number at all six matrices,
`rank_equals_rank_cols_at_every_concrete_matrix`), which is ADR-0603 row 3.

**Obligation 2's range half landed as its own commit, and turned up a second
gap.** `Rat.pivotSearchAux_le_rows` and `Rat.pivotSearch_le_rows` — the pivot
scan never returns an index past the row count. ADR-1554's obligation 2 is a
disjunction and both disjuncts assert `result ≤ rows`, which needs neither the
`Or` nor the bounded `∀`, so the range half is self-contained. Two findings
worth carrying:

1. The step splits twice and **the two splits are not the same shape.** The
   inner split on `isZeroB (M r c)` needs no hypothesis at all — one branch is
   the induction hypothesis at `succ r`, the other is `r`, both already bounded
   — so it is a bare `Bool.rec` at a `Prop` motive, not a case analysis. Only
   the outer split on `Nat.ble rows r` needs its hypothesis. Recognising which
   splits are free is most of what made this cheap.
2. **`Nat` has `le_of_ble_eq_true` and NOT its false-side twin.** The `ipc`
   prelude has exactly the statement (`ipc_le_of_ble_eq_false`) and the `rat`
   build does not carry it. It is rebuilt as an INLINE step from `Nat.le_total`
   and `Nat.ble_eq_true_of_le` with the contradicting disjunct discharged
   through `Bool.true_ne_false` — inline on purpose, because a
   `Rat`-namespaced declaration of a ℕ fact is the naming hazard CLAUDE.md
   warns about. Two preludes have now needed it. A third consumer should move
   it into `nat_prelude`.

The bound is checked for NON-VACUITY, not merely stated: at `[[0,1],[1,0]]` the
search is strictly under the bound from row 0 (it finds row 1) and attains it
from row 2. A `pivotSearch` that always returned `rows` satisfies the theorem
and fails that test.

**Step 0, and one thing it corrects.** `shape_search` was rebuilt through
`scripts/cargo-serialized.sh` before any query (`declarations=2142`, against
the echelon lane's stale-binary 2092 — the freshness trap that lane recorded).
`Nat.countRange_compl` and `Nat.setCompl` both `FOUND 1`; positive control
`Rat.rank` `FOUND 1`; `isPivotColB`, `rankCols`, `nullity`, `rank_nullity` and
`rowEchelon_isEchelon` all `ABSENT` with a live positive control. `--const
Rat.leadingIndex` returned exactly one declaration
(`Rat.nonzeroRowB_eq_ble`), which is how the "does the pivot-column step
already exist inline" question was answered.

**Facts.** `F:rat-rank-nullity`, `F:rat-rank-cols-le-cols`,
`F:rat-nullity-zero-rows`, `F:rat-pivot-search-le-rows`. Each checker greps the
RENDERED TYPE from `kernel_declaration_projection` and not only the name, so it
fails on the statement drifting while the name survives — the `nullity_zero_rows`
checker pins the literal `AxNat.zero` in argument position, so a version stated
at a symbolic row count (which would be false) does not match. The refl equation
lemmas, `isPivotColB_zero_rows`, `countRange_isPivotColB_zeroRows`,
`rankCols_zero_rows`, `rankCols_zero_cols` and `nullity_zero_cols` carry no fact
of their own — they are checked by the environment-derived inventory assertion,
which is the convention `rat-echelon` set.

**The next lane's starting point, and it is a ℕ lane not a ℚ one.** The cheapest
step toward the bridge is the cross-bound counting law, and it is independent of
everything about matrices: build and test it in `nat_prelude` against
`countRange` alone. Informally, "a bijection between the `p`-true part of
`[0, n)` and the `q`-true part of `[0, m)` makes the two counts equal";
`Nat.countRange_permute`'s `InjectiveOn`/`MapsInto` hypotheses are the right
shape to copy, and `count_range_permute.rs`'s `countRange_point_change` is the
device that made the same-bound version short. With that in hand the bridge is
"supply the bijection", which is obligation 4 and nothing else. `Nat.le_of_ble_eq_false`
is a second, much smaller ℕ gap on the same trip.

<!-- plan-section: landed-changes -->

| 2026-09-02 | rat-rank-nullity | `rat_prelude/nullity.rs`: 16 axiom-free declarations — `Rat.rank_nullity` as one `Nat.countRange_compl`, with `isPivotColB`/`rankCols`/`nullity` computed, both free dimension bounds, and all four degenerate cases |
| 2026-09-02 | rat-rank-nullity | `rat_prelude/pivot_bound.rs`: the RANGE half of ADR-1554 obligation 2 (`pivotSearchAux_le_rows`, `pivotSearch_le_rows`), checked non-vacuous; the content half stays open |
| 2026-09-02 | rat-rank-nullity | ADR-1558 and four facts; the bridge `rank = rankCols` measured rather than sized by argument — both sides stuck on a different `Nat.rec` major premise |
| 2026-09-02 | rat-rank-nullity | ADR-1555's sizing corrected: the bridge needs a CROSS-BOUND counting law (none of the 23 `Nat.countRange_*` lemmas relates two different bounds) in addition to `rowEchelon_isEchelon` |
| 2026-09-02 | rat-rank-nullity | second gap recorded: `Nat` has `le_of_ble_eq_true` and not its false-side twin; `ipc` declared it under a non-`Nat` name, and it is inlined here rather than misnamed a third time |
