# Lane: hall-assembly — Hall's marriage theorem is a kernel theorem

<!-- plan-section: lane-status -->

**Hall's marriage theorem is proved in the kernel, axiom-free, in both
directions** (`DONE`, hall-assembly, 2026-09-05, ADR-1645).

```text
Nat.Hall.sufficient   : ∀ s nb, HallCondition s nb → ∃ f, IsMatching s nb f
Nat.Hall.marriage_iff : ∀ s nb, HallCondition s nb ↔ ∃ f, IsMatching s nb f
```

Eleven declarations landed, all admitted axiom-free, all registered in
`nat_prelude_tests::definition_names`/`theorem_names`, and that sweep was RUN
(`every_nat_declaration_is_checked_and_axiom_free`,
`every_promised_name_is_admitted_with_the_expected_kind`, 3 passed). Kernel
inventory 3,236 → 3,247 declarations (theorems 2,150 → 2,160, definitions
866 → 867), read from a `shape_search` rebuilt at this lane's HEAD.

This closes the six-slice sequence ADR-1608 → 1614 → 1623 → 1630 → 1644 → 1645.

ADR-1644 sized the remainder as "assembly, and nothing that has been shown to
need a new idea", and named the two descent steps as the one place a surprise
was still possible. The descent was the cheap part. **Three other things were
not, and none appears in any prior slice's sizing.**

**1. The descent needs an EQUATION, and the nearest existing name is the wrong
statement.** `Nat.Finset.card_le_card_sdiff_add` already existed and reads like
the lemma you want; it is `card s ≤ card (sdiff s t) + card t`, holds without
the subset hypothesis, and bounds `card s` from ABOVE — the useless direction
for a descent. The lemma actually needed is
`Nat.Finset.card_add_card_sdiff`, a composition of `memB_union_sdiff_self` +
`card_congr_of_memB` + `card_union_of_disjoint`, none of whose names mentions
counting a complement. Same retrieval failure ADR-1644 recorded for
`sum_union_disjoint`, one slice later.

**2. `criticalB s nb t = true` does NOT imply `t ⊆ s`.** `subsetFixed` loops to
`bound s`, so `Nat.Hall.criticalB (range 3) nb (singleton 5)` is `true` and
`5 ∉ range 3`. The proof never assumes otherwise:
`Nat.Finset.existsSubset_of_search` returns `bound t = bound s` ALONGSIDE the
verdict, and it is that equation — fed to the new
`Nat.Finset.memB_of_subsetFixed_of_bound_le` — that upgrades a decision to a real
inclusion. Without it the critical branch would recurse on a non-subset. The
committed test asserts BOTH halves (the predicate accepts `singleton 5`; the
search cannot return it, because the bounds differ) rather than picking an
instance where the predicate happened to say `false` and hiding the hazard
behind a green assertion.

**3. The search predicate carries TWO positivity conjuncts, and neither implies
the other.** They sit on opposite sides of the split and each is exactly one
descent lemma's hypothesis. Drop `ble 1 (card t)` and the branch fires at
`t = empty` — whose COMPLEMENT is nonempty — and recurses on `sdiff s empty` at
the same count. Drop `ble 1 (card (sdiff s t))` and it fires at `t = s` — which
IS nonempty — and recurses on `t` at the same count.
`neither_positivity_conjunct_subsumes_the_other` asserts the four counts that
make that so instead of asserting it in prose.

A fourth thing, smaller: `forallSubset_of_search` yields
`criticalB s nb w' = false` and the branch needs
`card w < card (unionOver nb w)`. Going directly needs `ble a b = false → Lt b a`,
and this tree carries only `ble_eq_false_of_lt`, the other way — ADR-1644's
corrected blocker list missed the asymmetry because it checked only that a
reflection PAIR existed. No new lemma was written: the branch decides with
`lt_or_ge` and on the weak side BUILDS `criticalB = true` from the four
conjuncts with `andB_intro`, clashing it against the search's `false`.

**One earlier deliverable turned out unusable by the induction it was landed
for.** `Nat.Hall.exists_isMatching_singleton` (ADR-1630) is stated at a LITERAL
`Nat.Finset.singleton a`, and an arbitrary `s` with `card s = 1` is not
definitionally one — there is no route from the count to the spelling without
set extensionality. It is not needed: the non-critical branch commits one index
and recurses on `sdiff s (singleton x)`, which the empty case answers. Recorded
in ADR-1645 rather than dropped, so a later reader finding it unreferenced knows
it was measured as unusable here, not forgotten.

Three mutants RUN, none predicted, registered as
`SUITES["hall-marriage-in-kernel"]` so they are re-runnable: descent measure
weakened `<` → `≤`, the two branches exchanged, the two positivity conjuncts
collapsed. Baseline green 44 tests; all three `killed 44`, harness exit 0. That
number is ONE kill mechanism, not 44 guards — each mutant produces a declaration
the trusted gate rejects, so the prelude fails to build and every test in the
filter dies together. The first mutant has a second, independent killer that does
not go through the prelude build:
`hall_descent_tests::the_subset_measure_conclusion_is_strict` applies the lemma
at a closed instance, infers the type, and requires it to be `Lt 1 3` and not
def-eq to `Le 1 3` — a rendered-string check cannot separate them, since
`Nat.lt a b` unfolds to `Nat.le (succ a) b`.

Detail in
[ADR-1645](../../research/09-decisions/adr-1645-halls-marriage-theorem-lands-and-the-search-predicate-carries-two-positivity-tests.md).

<!-- plan-section: landed-changes -->

| 2026-09-05 | `bc6948454` | The descent measure: `Nat.Finset.card_add_card_sdiff` (the exact split of a count at a subset), the two strict inequalities over `subsetFixed`, and `memB_of_subsetFixed_of_bound_le`, the bridge from the search's output to the counting shelf's input. Five tests. The two measure tests APPLY the lemma at a closed instance and compare the INFERRED type against `Lt 1 3` / `Lt 2 3`, asserting it is not def-eq to the weak `Le`; a rendered-string check cannot separate them. |
| 2026-09-05 | `319bdec75` | `Nat.Hall.sufficient` and `Nat.Hall.marriage_iff`, plus `criticalB` and its congruence, the two family-weakening lemmas, and `Nat.Finset.memB_sdiff_congr`. Five tests, including the instance that pins the truncation hazard: the predicate accepts a set that is not a subset, and the search's bound equation is why that is sound. |
| 2026-09-05 | `7887bc69e` | Registered the three mutants as `SUITES["hall-marriage-in-kernel"]` so the guards cannot rot back to survivable in a commit message. All three RUN, `killed 44` of a 44-test baseline, harness exit 0, 21m06s. |
| 2026-09-05 | `e57f53593` | Sorted the new `mod`/`use` lines and regenerated the `axeyum-py` prelude-field mirror; `cargo check --workspace --all-targets` because a `NatPrelude` change reaches a generated consumer a kernel-only check never compiles. |
