# Lane: supon6 — `CReal.supOn` rung 6, re-verifying the telescope plan

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, supon6, 2026-08-27).** No new kernel
declarations landed this pass. What landed is a corrected module-doc map of
`creal/supremum.rs`'s rung 6 — the coordinator's brief flagged the existing
sketch as written by a lane that "did not attempt it" and asked to treat it
as a hypothesis; it does not hold up, and the doc now says precisely why,
with two named candidate routes for whoever attempts rung 6 next.

**The "constant-multiple corollary" the old sketch names as the one open
piece is not the bottleneck.** It already exists in substance:
`geometric.rs`/`exponential.rs`/`trig.rs`'s `pub(super)`
`mul_ordered_half_body` + `promote_ordered_half_to_full` +
`telescope_cauchy_pad2` already scale an ordered-half Cauchy bound by a
fixed positive `CReal` constant and promote it past `Nat.le_total`, and
`CReal.cauchy_of_abs_diff_le` (`creal/ivt.rs`) already supplies the general
real-bound-to-canonical-sample bridge `regular_of_scaled_cauchy` needs, with
a RAW `(K, proof)` pair available from its own construction (the body,
before the final `cexists_intro`) — this development's standing convention
is to reproduce a sibling's private helper rather than widen its visibility
for one caller, so this is a reproduction task, not a derivation.

Detail moved to [`../notes/170-supon6.md`](../notes/170-supon6.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | supon6 | `creal/supremum.rs` module doc: corrected rung 6's plan — the "constant-multiple corollary" already exists (`mul_ordered_half_body`/`promote_ordered_half_to_full`/`cauchy_of_abs_diff_le`); the real blocker is an unattempted multi-level nearest-mesh-point gap bound, documented with two candidate routes. No new kernel declarations. |
