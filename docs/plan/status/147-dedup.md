# Lane: dedup — adjudicating `shape_search --duplicates`' 10 groups

<!-- plan-section: lane-status -->

**Done for this pass (`WIP`, dedup, 2026-08-27).** Adjudicated all 10 groups
`shape_search --duplicates` reports (ADR-0608). Full evidence — actual
statements and proof terms, not names or shape — in
[`docs/research/11-design-review/2026-08-27-shape-search-duplicates-adjudicated.md`](../../research/11-design-review/2026-08-27-shape-search-duplicates-adjudicated.md).

Verdicts: **6 of 10 are deliberate zero-cost restatements (b)** —
`characterization.rs`'s four Peano/order-pinning entries, `rat_prelude`'s
`weak_law_of_large_numbers` alias, and `nat_prelude/order_extra.rs`'s
`succ_le_succ` — each reuses the *same proof term* under a second name, so
there is exactly one proof per fact despite two declarations. **4 of 10 are
genuine duplicate propositions (a)**: Apollonius'
`apollonius_from_stewart`/`apollonius_median` (intentional, documented as a
deliberate cross-check between two independent proof routes — left alone);
`CReal.rat_approx_{upper,lower}`/`sample{Upper,Lower}Bound` (accidental —
confirmed the brief's prediction: a 2026-08-26 lane could not find the
four-day-older `rat_approx_*` and built an independent proof of the same
statement; both sides load-bearing in different modules; `creal/` is out of
this lane's scope, so reported with a sketched-but-unverified fix rather than
applied); and `Nat.succ_sub_succ`/`succ_sub_succ_eq_sub` (accidental,
**fixed this pass** — see below). **0 of 10 are shape-only false positives
(c)** — every shape-matched pair turned out to state the actual same
proposition, including the Chebyshev/WLLN pair the brief flagged as the
likeliest (c) candidate by name.

Detail moved to [`../notes/147-dedup.md`](../notes/147-dedup.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | (pending commit) | Fix `Nat.succ_sub_succ_eq_sub` (`nat_prelude/order_extra.rs`) to reuse `succ_sub_succ`'s proof term instead of an independent re-derivation, matching the file's own alias pattern; adjudicate all 10 `shape_search --duplicates` groups in `docs/research/11-design-review/2026-08-27-shape-search-duplicates-adjudicated.md`. |
