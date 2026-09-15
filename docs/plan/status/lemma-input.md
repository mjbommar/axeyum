# Lane: lemma-input — the refresh rereads the atom set a quarter-million times

<!-- plan-section: lane-status -->

**The handoff named the right function and the wrong loop** (`DONE`,
lemma-input, 2026-09-15, [ADR-2080]). [ADR-2075] §7(B) handed over
`refresh_initial_lemmas` at 95.98 % of a row z3 refutes in 107 ms, with the
mechanism given as a cap that bounds its OUTPUT where its sibling bounds its
INPUT. An attribution build over the whole committed 208-row census says the
site is right and the loop is not: on `havoc-bench_sum` the refresh runs
**293,304 times** (once per assertion, rebuilding from scratch) over an atom set
that reaches **7,272**, and `extract_ms=21,395` of `mutex_ms=21,822` is the
**linear** per-atom rescan. The quadratic loop everyone looks at is quadratic in
the BOUNDS — **90** of them — and is 427 ms of the 21.8 s.

**The cap in the handoff has never fired.** `MAX_INITIAL_BOUND_MUTEX_LEMMAS`
truncated nothing: `cap_hits=0` on **153 of 153** rows with a reading. Both it
and the sibling input cap were added in **one hunk of one commit**
(`c093fa911`, 2026-06-25) on adjacent lines — one commit applying two
disciplines, not two authors across time. The 2026-09-08 registry sweep
registered the output cap and could not have seen the missing input cap:
`config_registry_scan.py` derives its population from `const` declarations, so
**a coverage checker over declarations is structurally blind to an absent one**.

**The population is 5 of 153, and 3 of the 5 are outside the bucket handed
over** (Wilson `[1.4 %, 7.4 %]`); P1 and P5 right.

**Built, `Off`, and NOT recommended `On`.** `AXEYUM_LIA_INITIAL_BOUND_INDEX=1`
makes the refresh incremental in three output-preserving steps (early return on
an unchanged atom count, cached extraction over the append-only atom vector,
pair loop indexed by the `expr` that `conflicting_bounds` already requires). The
A/B over all 208 census rows: **0 gains, 0 losses, 0 flips, 0 exit-status
moves**; 3 passes over 58 rows: **0 unstable**. D2 was pre-registered — gains = 0
ships `Off` — and it is what decides this against the lane's own preference.

The speedup is real and reported as speed only: the five profiled rows are the
**five largest speedups on the whole 208-row census** (0.552-0.644) against
per-row base bands of 1.000-1.275, while the three largest apparent SLOWDOWNS
(1.948, 1.460, 1.218) each sit **inside** their own row's base band and are not
slowdowns at all. Mechanism, both paths instrumented: `extract_ms` 22,199 → **5**,
and on `havoc-bench_036` the pair loop goes **69.1 billion → 327 million
iterations at an identical `max_bounds=1,756`** (582x per call; P3 predicted
≥ 100x).

**Three of the five leave [ADR-2075]'s bucket**: `Watchdog` + `; partial route `
+ 8 attempts becomes `ResourceLimit` + a complete `; route ` + **20** attempts,
with a named next blocker (`bound_by=q:mbqi`, e-matching budget exhausted
mid-round). That is ADR-2075 §12.5's structural recommendation reached by
removing the un-deadlined work rather than by adding a clock — and it is **not**
counted as a verdict.

**The input cap the brief asked for exists, ships `Off`, and its zero is nearly
vacuous.** Enforcing it cost 0 of 58 rows — but of the 53 decided control rows
**exactly one** is a measured crosser, Wilson `[0 %, 79.4 %]`, and 34 have
unknown exposure. It would fire on **103 of 153** rows and buys exactly what the
output-preserving route buys. P6 (the cap costs ≥ 1 decided row) is **wrong**,
and P2 (the atom count is below 512) is **wrong** — 7,272.

**A mutation battery found a real gap and it is why there are four tests.**
Making the cache re-read from zero, so it doubles on every refresh, killed
**nothing**: the duplicates land after the originals and `seen` dedups the
repeated pairs, so the lemma output stays byte-identical. Final table: M1 → 3,
M2 → 2, **M3 → exactly 1**, M4 → **0 and cannot be killed** (deleting the early
return cannot change output by construction; that impossibility is the finding).

**The sharpest open question is not answered here**: switching the whole pass
off changed no verdict on 58 rows and its output cap has never fired on 153, so
the pass's cost is measured and its **benefit is measured by nobody**.

Gates on this branch: clippy **890/890 targets, 27/27 crates, 0 diagnostics**;
solver lib sweep **1789 passed** (1,785 baseline plus this lane's four);
`corpus_regression` 2 passed; `cargo doc -D warnings` 41 crates;
`progress_frontier` 12 passed (its five `bench-results/frontier/*.json`
reverted, not committed); all **19** `dispatch/reason` fixture suites green with
nonzero counts. `check-config-registry-staleness.py` is **red with 11 stale
entries and was red without this branch** — none is this lane's, both entries it
adds are `undated`, and it is not in `hooks/pre-push`; reported rather than
omitted.

Artifacts: [`bench-results/lemma-input-20260915/`](../../../bench-results/lemma-input-20260915/).

[ADR-2075]: ../../research/09-decisions/adr-2075-the-silent-hang-is-not-silent-it-is-the-inventory-of-code-that-polls-no-deadline.md
[ADR-2080]: ../../research/09-decisions/adr-2080-the-refresh-rereads-the-atom-set-a-quarter-million-times-and-the-output-cap-has-never-fired.md
