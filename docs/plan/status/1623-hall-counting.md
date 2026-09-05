# Lane: hall-counting — the counting half of Hall's marriage theorem (W2-12)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, hall-counting, 2026-09-05).** **All three of
ADR-1614 §4's obstructions on Hall's sufficiency are closed, and sufficiency
still did not land.** Seventeen declarations (one definition, sixteen theorems),
all axiom-free: `unionOver` now has an elimination rule and so a two-sided
characterisation (`anyBelow_witness`, `memB_unionOver_elim`), which gives both
index-set congruences; deleting commutes with the union POINTWISE
(`memB_unionOver_sdiff`), which was NOT the counting argument ADR-1614 predicted
— the only real counting is one `Nat.Finset` law, `card_le_card_sdiff_add`; and
two matchings with disjoint IMAGES glue (`isMatching_union`), with no
disjointness needed of the index sets. `finset.rs` gains the membership calculus
for `sdiff` and `union` that it did not have — before this lane nothing in the
tree had a type mentioning `Nat.Finset.sdiff`.

**Where the next lane starts, measured at `declarations=3017` with a freshness
control that postdates every commit here.** The obstruction has moved to the
EMPTY SET. `--const Nat.Finset.singleton` is ABSENT: the singleton has no lemmas
at all, and Hall's base case is a singleton index set. Nothing turns a positive
`card` into a member (`countRange_eq_zero_of_all_false` exists and is the wrong
direction); `card_pos`, `card_eq_zero`, `exists_memB`, `card_union_disjoint` and
`card_sdiff_lt` are all ABSENT. **Build the empty-set bridge first and expect
the rest to be assembly** — the skeleton is unobstructed: `Nat.strongInduction`
takes the motive, `existsSubset_of_search` splits, `card_unionOver_congr`
discharges the congruence premise ADR-1614 left undischarged,
`card_le_card_unionOver_sdiff_add` re-establishes the deleted family's Hall
condition, and `isMatching_union` combines the two sub-matchings. ADR-1623.

**A gate this lane did NOT break and did not fix.**
`scripts/gen-autogenesis-kernel-dependency-projection.py --check` fails on main
and failed before this lane started. The committed
`artifacts/autogenesis/kernel-dependency-projection-v1.json` indexes 1,644
declarations against a live 3,000 at this lane's base commit, and 414 `Nat.*`
against a live 1,258. It contains **zero** `Nat.Finset.*` and **zero**
`Nat.Hall.*` entries, though both namespaces landed on main weeks earlier
(ADR-1577, ADR-1608) — so this is not the seventeen declarations added here. It
was last regenerated on 2026-08-26 (`d2d6fc0d0`) and 385 commits touched
`nat_prelude.rs` between then and this lane's base. `check-merge-hygiene.sh`
does NOT cover this artifact — it reports `generated=current` and PASSes — so
nothing catches the drift at merge time; only `just check`'s
`autogenesis-kernel-projection` step does. Regenerating it was started here and
DELIBERATELY ABANDONED: the diff would sweep 1,373 declarations belonging to
385 other commits into this lane's history, which is the shared-append-point
failure `CLAUDE.md` names. It needs its own lane. The run is slow — `--check`
alone takes ~35 min because it spawns a kernel binary per declaration.

<!-- plan-section: landed-changes -->

| 2026-09-05 | hall-counting | `unionOver`'s congruence and the family-modification transports: 11 theorems, `nat_prelude::` 580 → 591 (46a61c2ac) |
| 2026-09-05 | hall-counting | the matching union on disjoint images, plus the union's membership calculus: 5 theorems + 1 definition, `nat_prelude::` 595 (b4cda2323) |
| 2026-09-05 | hall-counting | ADR-1623 and two facts; all three ADR-1614 obstructions closed, Hall sufficiency sized at the empty set |
