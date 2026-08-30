# Notes: 147-dedup

Detail moved out of [`../status/147-dedup.md`](../status/147-dedup.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
