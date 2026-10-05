# Lane: echelon-invariant-2 — ADR-1554 obligation 4 closed, and the ADR-1562 rank bridge unconditional

<!-- plan-section: lane-status -->

**echelon-invariant-2 (`DONE`, 2026-09-02).** Twenty-two axiom-free `Rat`
declarations, fifteen facts, six commits, ADR-1574. **ADR-1554's obligation 4 is
closed and all four of its obligations are now complete**, and the ADR-1562
bridge is unconditional.

**The headline.**
`Rat.rowEchelon_isEchelon : ∀ M rows cols, isEchelon (rowEchelon M rows cols)
rows cols = true` — axiom-free, no hypothesis on `M` or the dimensions. ADR-1554
sized this as *"at least a lane on its own and probably two"*. Behind it:
`Rat.rank_eq_rankCols`, `Rat.rank_le_cols` and `Rat.rank_nullity_rows`
(rank-nullity in the ROW form) now hold for every matrix with **no hypothesis**,
where they were `_of_pivotSection` before.

**The sizing correction, which is the finding.** ADR-1571 §3 listed the
invariant's preservation and the exit derivation as two inductions. They are
**one**: carrying `isEchelon … = true` ITSELF as the conclusion at every fuel
level means each of the three leaves that stop the loop discharges it on the
spot, and nothing in the proof ever names the cursors the loop stopped at. The
rule, which is not about matrices: *a loop lemma whose conclusion is the
INVARIANT needs a separate exit derivation; one whose conclusion is the
POSTCONDITION does not, provided the postcondition does not mention the loop's
own cursors.*

**Four more things measured.** (1) The invariant has FIVE clauses, not the three
ADR-1571 described: `Le pc cols` is a real fifth, because the fuel clause bounds
`pc` from BELOW and the exit needs the other side. (2) Writing the fuel clause
as `pc + fuel` rather than `fuel + pc` makes two of the three exit leaves
literally the same derivation, since `Nat.add` recurses on its right argument
and `Le cols (Nat.add pc 0)` IS `Le cols pc`. (3) The invariant's clause about
the already-placed prefix looks like it needs `funext` — ADR-1555 measured that
the ROW form of rank invariance does — and does not:
`Rat.leadingIndex_congr_row` is pointwise in, pointwise out. (4) The chain from
`isEchelon`'s ADJACENT pairs to distinctness at a distance inducts on the UPPER
ROW, not on the distance, which keeps `Nat.add` and `Nat.sub` out of the family
entirely.

**Three prerequisites ADR-1571's table did not predict** were needed and landed:
`Rat.leadingIndex_congr_row`, `Rat.clearBelow_rowSwap_off` and
`Rat.pivotSearch_ge_start` (ADR-1558 had landed only the other side of that
bound). The one it did predict, `Rat.rowSwap_preserves_zero_range`, landed
first.

**Not attempted.** Rank invariance under the elementary row operations
(deliverable 5) was NOT started — the budget went to the bridge, which the brief
ordered ahead of it. ADR-1555's finding stands unexamined by this lane: the row
form needs `funext` and the column form is the one to prove. Nobody has checked
whether `Rat.rank_eq_rankCols` makes the column form reachable, and that is the
next lane's first question.

**Cost, bisected rather than attributed.** `rat` builds in **1.786–1.824 s**
over four runs, against 1.683–1.705 s at the lane's start. Bisected mid-lane by
removing the two large declarations: 1.720–1.746 s without them and 1.748–1.779 s
with, so the obligation-4 induction costs ~30 ms, its ten supporting lemmas
~40 ms, and the ten section declarations ~40 ms. Proportionate; no pathology.
Final sweep `rat_prelude::` **239 passed** (225 at the lane's start), `--release`,
`--test-threads=4`; of those, `echelon_invariant_tests` 10 and
`echelon_section_tests` 4.

**Did not run.** No workspace sweep, no `just check`, no `check.sh`, no push.
Clippy was run as `-p axeyum-lean-kernel --all-targets -- -D warnings` and is
clean; nothing wider was attempted, so this lane makes no claim about the
aggregate gate.

<!-- plan-section: landed-changes -->

| 2026-09-02 | echelon-invariant-2 | `Rat.rowSwap_preserves_zero_range` — ADR-1571 §3's one missing prerequisite |
| 2026-09-02 | echelon-invariant-2 | `Rat.leadingIndex_congr_row` + `Rat.clearBelow_rowSwap_off` — the placed prefix survives a step without `funext` |
| 2026-09-02 | echelon-invariant-2 | **ADR-1554 obligation 4 CLOSED** — `Rat.rowEchelon_isEchelon`, axiom-free |
| 2026-09-02 | echelon-invariant-2 | `Rat.pivotSection_of_isEchelon` — echelon form implies ADR-1562's section equation |
| 2026-09-02 | echelon-invariant-2 | `Rat.rank_eq_rankCols`, `Rat.rank_le_cols`, `Rat.rank_nullity_rows` — the bridge, unconditional |
| 2026-09-02 | echelon-invariant-2 | ADR-1574; fifteen facts; `prelude_fields.rs` regenerated |
