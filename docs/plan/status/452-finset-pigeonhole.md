# Lane: finset-pigeonhole — cardinality of an injection, and the `Nat.Finset` pigeonhole

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, finset-pigeonhole, 2026-09-03).** ADR-1577 named
the one missing piece and it is closed: **seven theorems, every one admitted on
the FIRST attempt, every one with `Kernel::axiom_footprint = []`** read from
`kernel_declaration_projection`. `Nat.countRange_le_of_injOn` (the cross-bound
counting INEQUALITY), `Nat.Finset.lt_bound_of_memB`,
`Nat.Finset.card_le_of_injOn`, `Nat.Finset.pigeonhole` (refutation form),
`Nat.Finset.allBelow_false_witness` (the search direction of `allBelow`),
`Nat.Finset.exists_collision` (the explicit colliding pair) and the consumer
`Rat.rankCols_le_rank`. ADR-1593; seven facts; `validate-facts.py` 2754 facts,
0 errors (2747 before).

**The route, and the one rejected with its cost.** The chosen route is
`Nat.countRange_bij`'s OWN induction with the inverse `τ` and the two
round-trip equations DELETED, so it reuses `count_range_bij.rs`'s single-point
removal apparatus (`drop_pred` and its three equations, `weaken_inj`, `sel`,
`lift_lt`) and pays for the removal with the same
`Nat.countRange_point_change`. Exactly two branches change and both get
SIMPLER: `n = 0` becomes `Nat.zero_le` (the bijection's base case had to refute
every selected `j < m` through `τ`), and the selected successor branch closes
through `Nat.succ_le_succ` instead of at an equality. No arithmetic lemma was
needed to line the spellings up — `add x (sel true) ≡ succ x` and
`add x (sel false) ≡ x` by ιδ, because `Nat.add` recurses on its RIGHT
argument.

The rejected route is the one the brief named: the RANGE pigeonhole in
`finite.rs` plus a rank/enumeration of a Finset's members as `[0, card s)`.
Measured, not guessed — `--name-like` for `nthtrue`, `enumerate`, `rankof`,
`selectIndex`, `indexOfNth`, `nthMember` all ABSENT — so that route pays for a
new `Definition` (with the evaluation tests every `Definition` here needs),
plus an injectivity induction, plus a surjectivity induction which is the SAME
"remove one point and recount" argument the chosen route uses directly, and
then arrives at the weaker range statement. **The generalisable form: when a
bijection law exists and an inequality is wanted, check whether the inequality
is the same induction with the surjectivity half struck out before building
anything.**

**Two strengths of the pigeonhole landed, and the distinction is the finding.**
`Nat.Finset.pigeonhole` REFUTES injectivity. `Nat.Finset.exists_collision`
produces the pair — and it cannot be derived from the refutation, because
nothing turns `¬P` into `∃ w` by logic in a kernel with no `funext`, no
`propext` and no classical choice. What does turn it is a DECISION PROCEDURE,
and injectivity on the members of a `Nat.Finset` has one (bounded domain,
decidable equality). So the pair is COMPUTED by a bounded double search whose
`true` branch reflects back to injectivity through ADR-1577's
`allBelow_true_at` (refuted by `pigeonhole`) and whose `false` branch yields the
witnesses through the new `allBelow_false_witness`. The search loop is written
INLINE, not as a named `Definition`: nothing in either statement mentions it,
and a named one could be well-typed and mean something else.

**The consumer is `Rat.rankCols_le_rank`, and it is a new fact rather than a
shorter proof.** `rank_bridge.rs` gets `rank = rankCols` from
`Nat.countRange_bij` and pays the SECTION HYPOTHESIS for the inverse's round
trip; every statement downstream of it inherits that hypothesis.
`Nat.countRange_le_of_injOn` takes exactly the bridge's `H1` and `H2`, which
that file's own table records as discharged from the two SEARCHES alone, so
`rankCols ≤ rank` holds with NO hypothesis at all. The asymmetry is real and is
pinned by the test: the reverse direction, `rank ≤ rankCols` — the one that
bounds `rank` by `cols` — still needs the section, because there the
injectivity obligation IS ADR-1554 obligation 4.

**Step 0, on a freshly built binary.** `declarations=2622` nat-only,
`3496` with `--include-constructed`; freshness controls `AlgS.mul_zero` FOUND 1
and `CReal.commRingS` FOUND 2, both landed 2026-09-03 AFTER this lane's merge
base. `--hyp Nat.injectiveOn --concl Nat.le` ABSENT;
`--const Nat.countRange --concl Nat.le` FOUND 4, and all four move ONE argument
(bound with predicate fixed, or predicate with bound fixed) — which is exactly
what was missing; `--const Nat.Finset.memB --concl Nat.lt` ABSENT;
`--const Nat.Finset.allBelow --concl Exists` ABSENT.

**One check the tree was not doing.** `finset_tests.rs`'s
`every_finset_declaration_is_present_and_axiom_free` enumerates a hand-written
array of 28 names, which measures the maintainer's memory. The new
`every_finset_declaration_in_the_environment_is_axiom_free` derives the
population from `Kernel::environment()` and then asserts the five new names are
AMONG them, so an empty derivation cannot pass. Both are kept; the old one is a
subset check now.

**Two gates caught real defects in this lane's own work, and both are worth
recording because a narrower check was green over each.**
`every_nat_declaration_is_checked_and_axiom_free` derives its population from
the live prelude, and it named all six new `Nat` declarations as live and
watched by nothing — while `nat_prelude::finset` was 21 green with the gap
open. A filter cannot catch a MISSING registration by construction. And the
ledger's own checker table found that **five of the seven `kernel-term` rows
did not pass as written**: a `grep -F` pattern that BEGINS with `-` is parsed
as an option, and five of the seven distinguishing substrings start with the
arrow before a conclusion. Fixed with `grep -cF -e`; the re-run is 28 for 28
(every row passes, every perturbed row fails). The defect ran in the safe
direction — the rows failed rather than passing vacuously — but it was still a
checker that had never examined its subject.

**Gates.** `nat_prelude::` 441 passed / 0 failed; `rat_prelude::` 266 passed /
0 failed; `nat_prelude::finset` 21 passed / 0 failed (14 pre-existing + 7 new);
`rat_prelude::rank_bridge` 9 passed / 0 failed (8 + 1 new);
`clippy -p axeyum-lean-kernel --all-targets -D warnings` clean;
`rustfmt --edition 2024` on every touched file;
`validate-facts.py` 2754 facts / 0 errors; `cargo check --workspace
--all-targets` clean (the regenerated `axeyum-py` prelude field table is the
reason to run it); `check-merge-hygiene.sh` PASS.

**Two things did NOT run, and neither is a pass.** The `finite::` filter the
brief asked for runs **ZERO tests** — there is no `nat_prelude::finite` test
module; `finite.rs`'s coverage lives in `nat_prelude_tests.rs`, which the full
`nat_prelude::` sweep above does run, and this lane changed no line of
`finite.rs`. And `check-theorem-inventory-completeness.py` is RED, on the
`list` prelude group being absent from `cross_prelude_collision_tests`'s
`build_groups`. That is pre-existing and not this lane's: the file is
byte-identical to the merge base and this lane's diff does not touch any
`build_groups`. It belongs to whoever landed the `list` prelude.

<!-- plan-section: landed-changes -->

| 2026-09-03 | finset-pigeonhole | open the lane (`a4cadf61d`) |
| 2026-09-03 | finset-pigeonhole | `countRange_le_of_injOn` + `card_le_of_injOn` + `pigeonhole` (`f91ded0c2`) |
| 2026-09-03 | finset-pigeonhole | `exists_collision`, `allBelow_false_witness`, `Rat.rankCols_le_rank`, tests (`164e4d329`) |
| 2026-09-03 | finset-pigeonhole | ADR-1593 and seven facts (`dfc9c1c1a`) |
| 2026-09-03 | finset-pigeonhole | register the seven with both authority lists (`b04b5d1f9`) |
| 2026-09-03 | finset-pigeonhole | fix five ledger checkers that never matched |
