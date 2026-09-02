# Lane: rat-rank — `Rat.rank` over the row-echelon form, and what the inverse laws do NOT give

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, rat-rank, 2026-09-02).** Nine declarations landed
in a new `crates/axeyum-lean-kernel/src/rat_prelude/rank.rs`, every one admitted
axiom-free (`Kernel::axiom_footprint` empty, read from the kernel by
`the_rank_family_is_axiom_free`). ADR-1555 carries the design and one
correction to ADR-1554's handoff. `rat_prelude::` is 190 passed / 0 failed in
145 s (measured on the final tree; `rat-echelon` recorded 183 before this
lane); `rat_prelude::rank_tests` alone is 7. The `rat` prelude builds in
1.61–1.85 s over fifteen `prelude_build_timing` samples in three runs, against
a briefed baseline of ~1.6 s — no measurable change, and the run-to-run spread
covers any effect. Clippy `-D warnings` clean on `axeyum-lean-kernel` and
`axeyum-py`; `RUSTDOCFLAGS="-D warnings" cargo doc` clean on the kernel crate.

**What landed.**

```
Rat.nonzeroRowB E cols r    := Nat.ble (Nat.succ (Rat.leadingIndex E r cols)) cols
Rat.rank        M rows cols := Nat.countRange (Rat.nonzeroRowB (Rat.rowEchelon M rows cols) cols) rows
```

with `Rat.nonzeroRowB_eq_ble` and `Rat.rank_eq_countRange` (both `Eq.refl`, and
the only route the ℕ counting laws have to `rank`), `Rat.nonzeroRowB_zero_cols`
(`Eq.refl` at a SYMBOLIC matrix — `Nat.ble (succ _) zero` is `false` by ι),
`Rat.rank_le_rows` (one `Nat.countRange_le`), `Rat.rank_zero_rows` (`Eq.refl`),
`Rat.countRange_nonzeroRowB_zero` (induction on `n`, matrix generalised) and
`Rat.rank_zero_cols`.

**Evaluation table** (each reduced by `def_eq`, each with a control at
`want ± 1` that must FAIL):

| matrix | echelon form | `rank` | what only this row separates |
| --- | --- | --- | --- |
| `[[1,2],[3,4]]` | `[[1,2],[0,-2]]` | 2 | kills "return `0`" |
| `[[1,2],[2,4]]` | `[[1,2],[0,0]]` | 1 | kills "return `rows`" — the zero row must be EXCLUDED |
| `[[0,0],[0,0]]` | itself | 0 | kills "return `rows`" a second way, at every row |
| `[[1,2,3],[2,4,6],[1,1,1]]` | `[[1,2,3],[0,-1,-2],[0,0,0]]` | 2 | needs the ECHELON form: the input has three nonzero rows |
| 3×3 identity | itself | 3 | separates "count nonzero rows" from "count rows below the last pivot" |
| `rowScale 0 0` of `[[1,2],[3,4]]` | `[[3,4],[0,0]]` | 1 | the `k ≠ 0` side condition showing up as a number |

**Invariance: two of three deliverables did not land, and the handoff that
sized them was wrong.** ADR-1554's status block says rank invariance "needs
only the three inverse laws" and does NOT depend on obligation 4. That is
false, for two independent reasons, either fatal on its own.

1. **No `funext`.** Every law in `echelon.rs` is POINTWISE
   (`rowSwap i j (rowSwap i j M) r c = M r c`). `rank` takes the matrix as an
   ARGUMENT, so rewriting under it needs an `Eq` between two terms of type
   `Nat → Nat → Rat`, which this kernel does not have. The inverse laws cannot
   be *applied* under `rank` at all — there is no stuck term to report, because
   no proof term of the required shape can be built. This is the same wall
   `Rat.det_congr` was built to climb.
2. **Wrong statement even with `funext`.** The inverse laws give
   `rank (op⁻¹ (op A)) = rank A`, i.e. `rank A = rank A` with extra steps. What
   invariance asserts is `rank (op A) = rank A`, relating the elimination of two
   DIFFERENT matrices. The "bounded both ways" trick is real and does reduce
   two directions to one, but the surviving direction `rank (op A) ≤ rank A` is
   a statement about what Gaussian elimination produces, and every route to it
   goes through `rowEchelon_isEchelon`.

`rank_le_cols` is blocked by the same obligation: it asserts the echelon form
has at most one pivot per column. **Neither was rejected by the kernel — no
declaration was attempted, because the statement has no route, and reporting
that is more useful than a partial attempt.** Invariance is checked where it IS
decidable: by reduction at 2×2, for each of `rowSwap 0 1`, `rowScale 0 3` and
`rowAddMul 1 0 2`, on a rank-2 and a rank-1 matrix, each with a control that
the operation genuinely changed the matrix (ADR-0603 row 3).

**The cap was available and was refused.** `Nat.min (countRange …) cols` makes
`rank_le_cols` free and is mathematically harmless. It also makes a broken
elimination unobservable — four nonzero rows in three columns would be reported
as `3` and no evaluation test could see it. A bound that holds because the
definition truncates is not a theorem about rank.

**The tests were mutation-checked, and the first two mutants did not prove what
they looked like they proved.** Three mutants, in this lane's isolated
worktree:

| mutant | result | what it actually showed |
| --- | --- | --- |
| strict `ble (succ l) cols` → non-strict `ble l cols` | 7/7 tests fail | all seven at `built()`: the **prelude build** broke, because `nonzeroRowB_zero_cols` stopped being `refl`. The evaluation table never ran. |
| `leadingIndex E cols r` (arguments swapped) in the definition only | 7/7 fail | again a build failure — `DeclarationValueMismatch` on `nonzeroRowB_eq_ble`. Still not the evaluation table. |
| the same swap in the definition **and** its equation lemma | 4 fail, 3 pass | the prelude BUILDS and the values are wrong: `rank must be 1` and `row 1 of [[1,2],[0,0]] is zero` fail. The three survivors are the degenerate-dimension and axiom-freedom tests, which do not depend on the mutated behaviour. |

The lesson is the one worth carrying: a refl equation lemma next to a
`Definition` turns a value mutation into a **build** failure, so a mutation run
that kills every test may be telling you the trusted gate caught it and your
evaluation tests are still unmeasured. Only the third mutant measured them.

**The next lane's starting point — rank-nullity, and it is cheaper than it
looks.** Do NOT define `nullity := cols - rank`; that makes rank-nullity depend
on `rank ≤ cols` and inherits every obligation above. Count COLUMNS instead.
Add a computed `Rat.isPivotColB E rows cols j` ("some row below `rows` has
leading index exactly `j`", a bounded search of the shape `pivotSearchAux`
already demonstrates), then

```
rankCols E rows cols := Nat.countRange (isPivotColB E rows cols) cols
nullity  E rows cols := Nat.countRange (setCompl (isPivotColB E rows cols)) cols
```

and `rankCols + nullity = cols` is `Nat.countRange_compl`
(`∀ p n, countRange p n + countRange (setCompl p) n = n`), which **already
exists** in the ℕ prelude and needs nothing whatever about echelon form. The
entire content of rank-nullity then concentrates into one bridge,
`rank = rankCols` — the number of nonzero ROWS equals the number of pivot
COLUMNS — which is where `rowEchelon_isEchelon` is genuinely required and where
it should be spent. That turns one open theorem into one free theorem plus one
honest obligation.

Facts are `F:rat-rank-le-rows` and `F:rat-rank-zero-cols`. The four refl
equation lemmas and `Rat.countRange_nonzeroRowB_zero` carry no fact of their
own — they are checked by the environment-derived inventory assertion, not by
the ledger, which is the convention `rat-echelon` set.

<!-- plan-section: landed-changes -->

| 2026-09-02 | rat-rank | `rat_prelude/rank.rs`: 9 axiom-free declarations — `Rat.rank` as a computed `Nat.countRange` over the row-echelon form, `Rat.nonzeroRowB`, `rank_le_rows`, and both degenerate dimensions |
| 2026-09-02 | rat-rank | ADR-1555 and two facts; the cap at `cols` refused on purpose, so `rank_le_cols` is OPEN rather than bought by truncation |
| 2026-09-02 | rat-rank | ADR-1554's handoff corrected: rank invariance does NOT follow from the three inverse laws (no `funext`; and they prove `rank (op⁻¹ (op A)) = rank A`, not `rank (op A) = rank A`) |
| 2026-09-02 | rat-rank | rank-nullity re-sized downward: count pivot COLUMNS and their complement, and `Nat.countRange_compl` gives `rank + nullity = cols` for free |
