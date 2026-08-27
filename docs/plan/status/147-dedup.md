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

**One kernel fix landed**, in scope (`nat_prelude/`, not on the
creal*/rat_prelude/characterization.rs/complex* do-not-edit list):
`crates/axeyum-lean-kernel/src/nat_prelude/order_extra.rs`'s
`succ_sub_succ_eq_sub` was an independent re-derivation (copy of
`algebra.rs`'s `succ_sub_succ` induction) with zero downstream consumers,
inside the very file whose established pattern (three other lemmas in the
same file) is to alias rather than re-derive. Changed it to
`d.lemma(p.succ_sub_succ, &[n, m])`, matching the file's own pattern.
Verified: `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 95 passed,
0 failed (including `every_nat_declaration_is_checked_and_axiom_free`);
`creal::creal_tests::creal_prelude_builds` — 33.5s, within the 36-41s recent
reference range (smoke check only — the fix is outside `creal`);
`shape_search --duplicates` still reports 10 groups after the fix, as
expected — the tool compares admitted types, not proof terms, so an alias
and a re-derivation of the same type are indistinguishable to it. That
distinction (real proof-duplication vs. safe aliasing) is not something
`--duplicates` can currently see; described as a possible refinement in the
findings doc, not built (`shape_index.rs` has 18 mutation-verified guards and
is out of this lane's scope).

**Not applied, described only:** the `rat_approx_*`/`sample*Bound` thin-alias
fix (creal/* is out of scope — six kernel lanes are live there) and the
shape-vs-proof-term refinement to `--duplicates` (shape_index.rs is out of
scope). Both are concrete next steps for whichever lane owns `creal/` or
`shape_index.rs` next.

**On the framing in ADR-0608 / the design-review appendix:** "ten theorem
pairs stating literally the same proposition under two names" is accurate
about the *proposition* (verified all 10) but risks reading as "ten
maintenance hazards." It is closer to six safe aliases plus four genuine
duplicates (one by design, three by accident, one now fixed) — see the
findings doc's closing section for the full argument.

<!-- plan-section: landed-changes -->

| 2026-08-27 | (pending commit) | Fix `Nat.succ_sub_succ_eq_sub` (`nat_prelude/order_extra.rs`) to reuse `succ_sub_succ`'s proof term instead of an independent re-derivation, matching the file's own alias pattern; adjudicate all 10 `shape_search --duplicates` groups in `docs/research/11-design-review/2026-08-27-shape-search-duplicates-adjudicated.md`. |
