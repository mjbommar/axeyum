# Lane: rat-echelon — row-echelon form over ℚ, the computed definition `rank` reads off

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, rat-echelon, 2026-09-02).** Twenty-nine
declarations landed in a new `crates/axeyum-lean-kernel/src/rat_prelude/echelon.rs`,
every one admitted axiom-free (`Kernel::axiom_footprint` empty, read from the
kernel by `the_echelon_family_is_axiom_free`). ADR-1554 carries the design.
`rat_prelude::` is 183 passed / 0 failed in 121 s, up from 169 tests. The `rat`
prelude builds in 1.61–1.66 s over three `prelude_build_timing` runs, against a
briefed baseline of ~1.65 s — no measurable change, and the run-to-run spread
exceeds any effect. Clippy `-D warnings` clean on `axeyum-lean-kernel` and
`axeyum-py`.

**What landed.** `Rat.isZeroB`, the decided zero test, with four bridge theorems
to the propositional `Eq x 0`. The three elementary row operations
`Rat.rowSwap` / `Rat.rowScale` / `Rat.rowAddMul`, each ONE `Rat.matSetRow`
write, with their `_at`/`_off` equations. `Rat.pivotSearch`, `Rat.clearBelow`,
`Rat.echelonAux` and `Rat.rowEchelon` — Gaussian elimination as a `Definition`
the kernel reduces. `Rat.leadingIndex`, `Rat.echelonStepOk` and
`Rat.isEchelon`, the decidable predicate. And the three inverse laws
`Rat.rowSwap_involutive` (unconditional, `i = j` included),
`Rat.rowAddMul_inverse` (`j ≠ i` required — at `i = j` the operation scales row
`i` by `1 + k`) and `Rat.rowScale_inverse` (`k ≠ 0`, not `0 < k`, so it covers
the negative pivots elimination produces).

**Evaluation table** (each row reduced by `def_eq` at concrete arguments, each
with a control that must FAIL to be defeq):

| input | `rowEchelon … 2 2` / `… 3 3` | `isEchelon` before | after | what only this input separates |
| --- | --- | --- | --- | --- |
| `[[1,2],[3,4]]` | `[[1,2],[0,-2]]` | `false` | `true` | ordinary elimination; `(1,0)` was 3 |
| `[[1,2],[2,4]]` | `[[1,2],[0,0]]` | `false` | `true` | dependent pair; `leadingIndex` row 1 = `cols` = 2 |
| `[[0,1],[1,0]]` | `[[1,0],[0,1]]` | `false` | `true` | zero pivot forces a SWAP; `(0,0)` was 0 |
| `[[1,2,3],[2,4,6],[1,1,1]]` | `[[1,2,3],[0,-1,-2],[0,0,0]]` | `false` | `true` | zero row created in the MIDDLE, so the second pivot column re-pivots |
| `[[0,0],[1,0]]` | — | `false` | — | zero row ABOVE a nonzero one; the clause `echelonStepOk`'s second conjunct exists for |
| `isZeroB` at `0 / 1 / -1 / 2` | `true / false / false / false` | — | — | the NEGATIVE case, where a one-sided `ble x 0` is wrong |
| `pivotSearch [[0,1],[1,0]]` col 0 from 0 | `1` | — | — | not the start index |
| `pivotSearch [[0,1],[1,0]]` col 1 from 1 | `2` (= `rows`, absent) | — | — | not the start index either |

**Two things worth carrying forward, neither of them about the mathematics.**

The coordinator's step 0 was run against a STALE prebuilt `shape_search`. Its
`matSetRow` and `matSubstRows` ABSENT verdicts were wrong — both exist in
`rat_prelude/det_mul.rs` and landed the same day. The stale binary reported a
bare-index positive control of 1,963 against a current 2,092 (and 2,835
`--include-constructed` against 2,092 fresh), and the freshness probe passed
because the control used, `Rat.det_matMul_2`, PREDATES the merge that landed
`matSetRow`. A 73-second rebuild turned both ABSENTs into `FOUND 3`. The lesson
is narrower than "rebuild before trusting ABSENT": **the freshness control has
to be newer than the change you are asking about**, and `Rat.det_matMul_2` is
not `Rat.det_matMul`.

`rat_prelude_tests::every_rat_declaration_is_checked_and_axiom_free` fired on
its first run after the module landed and named all 25 declarations nothing was
checking. It derives its subject from `kernel.environment()` rather than from a
literal, which is exactly why it could. Registering them in the two inventory
lists is a mechanical fix and the test earned its keep.

**What did NOT land, and what it would cost.**
`rowEchelon_isEchelon : ∀ A r c, isEchelon (rowEchelon A r c) r c = true` was
not attempted. It is a full correctness proof of Gaussian elimination at
symbolic dimension. ADR-1554 sizes its four obligations; the short version is
that obligation 1 (the `isZeroB` ↔ `Eq 0` bridge) was the only cheap one and it
landed here, obligations 2 (`pivotSearch`'s postcondition) and 3
(`clearBelow`'s postcondition) are a lane each, and obligation 4 (the loop
invariant, a fuel induction with the invariant as an explicit `Prop` in the
motive) is at least one lane and probably two. **Nothing is stuck** — no term
was rejected, no defeq failed; the work was simply not attempted, and reporting
it as "did not run" is more useful than a partial attempt.

**The next lane's starting point.** `rank` needs three things from this module
and no more: `Rat.leadingIndex` over the rows of `Rat.rowEchelon`, a count of
the rows whose leading index is strictly below `cols`, and
`Rat.eq_zero_of_isZeroB` / `Rat.ne_zero_of_isZeroB_false` to say anything about
an ENTRY from a statement about where the scan stopped. Rank INVARIANCE needs
only the three inverse laws — it does **not** depend on obligation 4 above, and
sizing it as blocked on `rowEchelon_isEchelon` would be wrong. Facts are
`F:rat-row-swap-involutive`, `F:rat-row-add-mul-inverse`,
`F:rat-row-scale-inverse`, `F:rat-eq-zero-of-is-zero-b`,
`F:rat-ne-zero-of-is-zero-b-false`. The seven `_at`/`_off` equation lemmas and
`Rat.isZeroB_zero` / `Rat.isZeroB_of_eq_zero` carry no fact of their own —
they are checked by the environment-derived inventory assertion, not by the
ledger.

<!-- plan-section: landed-changes -->

| 2026-09-02 | rat-echelon | `rat_prelude/echelon.rs`: 29 axiom-free declarations — the three elementary row operations with their equations and inverses, `Rat.rowEchelon` as a computed Gaussian elimination, and the decidable `Rat.isEchelon` |
| 2026-09-02 | rat-echelon | `Rat.isZeroB` and four bridges to the propositional `Eq x 0`; the one place ℚ's decidable order is spent, and obligation 1 of `rowEchelon_isEchelon` |
| 2026-09-02 | rat-echelon | ADR-1554 (computed pivot search, exact `cols` fuel, `leadingIndex = cols` for a zero row; ADR-0603 row 2 empty by proof) and five facts |
