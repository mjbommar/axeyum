# Lane: hall-singleton — the empty/singleton shelf and Hall's base case (W2-12)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, hall-singleton, 2026-09-05).** **The empty set and
the singleton are closed; Hall's sufficiency has a base case and an empty case
and still did not land in general.** Thirteen declarations (one definition,
twelve theorems), all axiom-free, `declarations 3,093 → 3,106`.
`nat_prelude/finset_singleton.rs` is new and carries `Nat.Finset.empty` (which
did not exist), the singleton's full membership equation plus its intro/elim
rules, `card_singleton`, `card_empty`, `memB_empty`,
`card_eq_zero_of_no_memB`, and **both directions between a count and a
member** — `card_pos_of_memB` and the search-based
`exists_memB_of_card_pos`, the direction ADR-1623 named as missing.
`nat_prelude/hall_sufficiency.rs` is new and carries `isMatching_congr`,
`exists_isMatching_of_card_le_zero` and `exists_isMatching_singleton`, all in
necessity's vocabulary (`IsMatching`/`HallCondition`/`unionOver`) so the
eventual `Iff` is a composition; a test asserts that against the rendered types
read out of the kernel, and asserts the base case is not phrased over
`Nat.Finset.range`. ADR-1630.

**Where the next lane starts, measured at `declarations=3106` with a
`shape_search` binary rebuilt at this lane's HEAD.** The obstruction has moved a
fourth time, and for the first time it is **one named lemma** rather than a new
primitive. The critical-subset split has to be a bounded search, and
`Nat.Finset.forallSubset_of_search` demands its predicate be congruent under
pointwise membership. `card` and `card (unionOver nb ·)` are congruent already
(`card_congr_of_memB`, `card_unionOver_congr`); the conjunct spelling `t ⊆ s`
is not, and every spelling is missing its lemma —
`--const Nat.Finset.subsetB` is **FOUND 1** (`card_le_of_subsetB`, so no
reflection and no congruence, and it loops over `bound t`, which is exactly what
the congruence premise forbids), `--const Nat.Finset.inter` is **FOUND 1**
(`card_union_add_card_inter`, so no `memB_inter`), and
`--const Nat.Finset.allBelow` is **FOUND 3** (its three original laws, no
congruence). **Spell inclusion over the FIXED bound `bound s` —
`allBelow (fun i => notB (memB t i) || memB s i) (bound s)` — which is
congruent in `t` because the loop bound does not depend on `t`, and is a genuine
inclusion for the sets the search produces (`existsSubset_of_search` returns
`t` with `bound t = bound s`). That needs exactly one new lemma,
`Nat.Finset.allBelow_congr : ∀ f g n, (∀ i, f i = g i) →
Eq Bool (allBelow f n) (allBelow g n)`, a decision on the loop with
`allBelow_true_at`/`allBelow_of_all_true` on one side and
`allBelow_false_witness` on the other.** After that the step is bookkeeping over
lemmas that all exist (`card_le_card_unionOver_sdiff_add`,
`card_le_card_sdiff_add`, `memB_sdiff_elim`, `isMatching_union`, and this
lane's `isMatching_congr`), but it is several hundred lines of kernel term per
branch and is NOT one lemma.

**What did not run in this lane.** `just check` and `./scripts/check.sh` were
not run — this lane's verification was the per-module release test filters, the
crate-wide `cargo check --all-targets`, clippy on `-p axeyum-lean-kernel
--all-targets -D warnings`, `cargo fmt --all --check`, the fact validators, and
`scripts/check-merge-hygiene.sh`. The autogenesis kernel-dependency projection
(`gen-autogenesis-kernel-dependency-projection.py --check`) was NOT run and is
NOT fixed here; ADR-1623's lane recorded it as failing on main before that lane
started, for reasons that predate both lanes, and it needs its own.

<!-- plan-section: landed-changes -->

| 2026-09-05 | hall-singleton | the empty/singleton shelf and the count-to-member direction: 9 declarations in the new `nat_prelude/finset_singleton.rs` (5cc0ab0ae) |
| 2026-09-05 | hall-singleton | Hall's base case, empty case and `isMatching_congr`, plus `card_pos_of_memB`: 4 theorems in the new `nat_prelude/hall_sufficiency.rs` (a7d5f071d) |
| 2026-09-05 | hall-singleton | ADR-1630 and two facts; Hall sufficiency re-sized at one missing lemma, `Nat.Finset.allBelow_congr` |
