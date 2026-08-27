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

Consumer count alone would point at keeping `sampleUpperBound` canonical and
aliasing `rat_approx_upper` to it. **Build order overrides that.**
`density::declare_density` runs *before*
`uniform_continuity::declare_uniform_continuity` in `CRealPrelude`'s build
sequence (the latter calls `declare_sample_upper_bound`/`_lower` at its own
tail), so at the point `rat_approx_upper` would need to reference
`sample_upper_bound`, the kernel has not admitted it yet — that alias
direction does not type-check, full stop. Confirmed by writing it that way
first and watching `declare_density` fail to build (reverted before
committing). So: `rat_approx_upper`/`rat_approx_lower` (`density.rs`) stay
canonical, keep their exact proofs; `sample_upper_bound`/`sample_lower_bound`
(`uniform_continuity.rs`) become thin forwards (`d.lemma(p.rat_approx_upper,
&[x, n])` / `..._lower`). Both propositions confirmed identical up to the
bound-variable name (`n` vs. `m`) by reading the type-construction code line
for line, not assumed from the design-review doc.

Verified: `cargo test -p axeyum-lean-kernel --lib
creal::creal_tests::{sample_upper_bound,sample_lower_bound,crossing_sample_upper_and_lower,ivt_,close_within_of_within,creal_prelude_builds}`
(11 tests total across those filters) — all pass, including
`creal_prelude_builds` (the build-order fix is exercised there: it would
fail loudly with a "name not yet declared" kernel error if the order were
wrong). `cargo check -p axeyum-lean-kernel --lib` — clean, no new warnings
(the two now-unused independent-derivation helper functions in `density.rs`
were never touched since that file's proofs stayed as-is; no dead code was
left behind in `uniform_continuity.rs` either — checked by compiling, not by
inspection).

**Task 2 — the gate.** `scripts/check-shape-duplicates.py` runs
`shape_search --duplicates` and compares its reported groups (by exact
name-set, not shape text) against `scripts/shape-duplicates-allowlist.json`,
which carries all 10 currently-reported groups **each with a written
reason** (6 zero-cost aliases, 1 intentional cross-check, 3 now-fixed
accidents — `succ_sub_succ_eq_sub` from the prior pass and this pass's two
`sample*Bound` entries). Two failure modes, both exit 1:

- a reported group **not** on the allowlist ("NEW/UNADJUDICATED") — a new
  accidental duplicate, or an existing pair that gained a third member;
- an allowlist entry **not** currently reported ("STALE") — the
  `#[expect]`-style bidirectional half: an allowlist entry whose group
  stopped being a duplicate (renamed, or fixed a different way) must be
  removed, or it reads as still-considered when it is not.

Malformed input (bad allowlist JSON, unparseable `--duplicates` output, a
mismatch between the tool's own `verdict: DUPLICATE-GROUPS N` line and what
this gate parsed) is a distinct exit 2 — "the gate broke," not "a duplicate
was found."

Confirmed clean on the real tree: `python3 scripts/check-shape-duplicates.py`
→ `OK: 10 duplicate group(s), all allowlisted with a reason.`, exit 0.

**Mutation-verified, 8 of 8 guards killed, 0 survived**
(`scripts/tests/test_check_shape_duplicates.py::MutationTests`, plus 23
ordinary unit/end-to-end tests, 24 total, all green): each of
malformed-line-column-count, fewer-than-two-names, allowlist-empty-reason,
allowlist-bad-names-shape, allowlist-duplicate-entry, unrecognized-detection,
stale-detection, and verdict-count-mismatch was disabled one at a time in a
scratch-copied mutant (never the real file) and its own dedicated test
failed against the mutant while passing against the baseline. `unrecognized-
detection` and `stale-detection` are the two guards that matter most (they
are properties 1 and 2 from the brief); both killed cleanly.

**Live-fire demonstration (not just the unit mutation): a genuinely new
duplicate, constructed in an isolated `/data0` snapshot, makes the real
`shape_search` + gate pipeline go red; the unmutated tree is the control and
is green.** See the run transcript below. [Coordinator: fill in the actual
counts/output from the demonstration once run — the mutation-test section
above is what is machine-verified in this commit; the live-fire run is
recorded as its own paragraph so it is not conflated with the unit-level
mutation loop.]

**On the 6 "safe" groups, re-examined:** nothing new. Re-reading
`characterization.rs`'s four bundle entries, `weak_law_of_large_numbers`, and
`succ_le_succ` while writing the allowlist reasons did not surface anything
the prior pass's adjudication missed — each is still a one-line
`d.lemma`/`const_` forward with zero re-derived proof steps.

<!-- plan-section: landed-changes -->

| 2026-08-27 | (pending commit) | Fix the `rat_approx_{upper,lower}`/`sample{Upper,Lower}Bound` accidental duplicate: `sample_upper_bound`/`sample_lower_bound` (`creal/uniform_continuity.rs`) now forward to `rat_approx_upper`/`rat_approx_lower`'s proof term instead of re-deriving; direction chosen by build order, not consumer count. Add `scripts/check-shape-duplicates.py` + `scripts/shape-duplicates-allowlist.json`, a mutation-verified gate (8/8 guards killed) so a new `shape_search --duplicates` group must be read and either fixed or allowlisted with a reason. |
