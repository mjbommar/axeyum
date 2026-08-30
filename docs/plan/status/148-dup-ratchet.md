# Lane: dup-ratchet — fix the `rat_approx`/`sampleBound` duplicate, gate the class

<!-- plan-section: lane-status -->

**Done (`WIP`, dup-ratchet, 2026-08-27).** Follow-on to the `dedup` lane's
adjudication of `shape_search --duplicates`' 10 groups
(`docs/research/11-design-review/2026-08-27-shape-search-duplicates-adjudicated.md`,
`docs/plan/status/147-dedup.md`). That pass found two accidental groups: one
fixed (`Nat.succ_sub_succ_eq_sub`), one described but not applied because
`creal/` was out of that lane's scope
(`CReal.rat_approx_{upper,lower}`/`sample{Upper,Lower}Bound`). This lane's
task: fix the second, and build a gate so a new accidental duplicate cannot
land silently.

**Task 1 — the alias, and which side survived.** `CReal.rat_approx_upper`
(`creal/density.rs`, landed 2026-08-22) and `CReal.sampleUpperBound`
(`creal/uniform_continuity.rs`, landed 2026-08-26) prove the identical
statement — confirmed by reading both proof terms, not just the shape — via
two genuinely independent derivations. Both are load-bearing: `rat_approx_upper`
in `ivt.rs` and `density.rs` itself (2 consuming declarations, 2 files);
`sampleUpperBound` in `uniform_continuity.rs` itself (bucket-clamp),
`uniform_convergence.rs`, and `integral.rs` (3 consuming declarations, 3
files) — **more consumers than `rat_approx_upper`**, contrary to the prior
pass's "the older name is load-bearing elsewhere" read (which had only
checked `completeness.rs`'s doc-comment mention, not an actual proof
consumption — there is none).

Detail moved to [`../notes/148-dup-ratchet.md`](../notes/148-dup-ratchet.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | (pending commit) | Fix the `rat_approx_{upper,lower}`/`sample{Upper,Lower}Bound` accidental duplicate: `sample_upper_bound`/`sample_lower_bound` (`creal/uniform_continuity.rs`) now forward to `rat_approx_upper`/`rat_approx_lower`'s proof term instead of re-deriving; direction chosen by build order, not consumer count. Add `scripts/check-shape-duplicates.py` + `scripts/shape-duplicates-allowlist.json`, a mutation-verified gate (8/8 guards killed) so a new `shape_search --duplicates` group must be read and either fixed or allowlisted with a reason. |
