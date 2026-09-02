# Lane: unowned-red-gates — diagnose the two red aggregate-gate steps and close the pre-push partition-gate hole

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, unowned-red-gates, 2026-09-02).**

**The two named red steps.**

- `autogenesis-nursery-dispatch-baseline --check` (classification: **(a) stale
  generated artifact**). Commit `d46e578bc` (ADR-1564) regenerated
  `nursery-v1.json` — dropping three now-empty
  `component_split_exemptions` and landing the `natural-bit-decode`
  amendment — which changed its content digest with "no row moved
  partition" (that commit's own claim, confirmed: regenerating the baseline
  changed only the `nursery_sha256`/`baseline_sha256` fields, dispatchable
  stayed 0/22/176). Regenerated with
  `python3 scripts/create-autogenesis-nursery-dispatch-baseline.py`.
  **Before: exit 1. After: exit 0.**
- `propose-nursery-refill` / `propose-nursery-refill-tests` (two
  classifications). R2 staleness was **(a)**: the tracked headroom snapshot
  predated the same `d46e578bc` re-record; `--remeasure` (needs `/nas3`,
  mounted here) refreshed it with no row moving partition. But the freshly
  remeasured snapshot still fails **R3 "cannot-refill"** — 1 ready family
  yields 0 dispatchable rows against a floor that needs 2 — which is
  **(c) a real, standing finding**, not a checker defect: the script's own
  docstring names this exact condition as R3's job, and `sole_blocker_note`
  in the snapshot explains why (growing the pool needs a settled-mirror
  witness the catalog does not have). Left red on purpose; the reason is in
  its own stderr. Separately, `test-propose-nursery-refill.sh` itself was
  **(b) the checker's own query wrong about a moved subject**: its case 0
  demanded exit 0 from the real tree (a control over queue SIZE, not false
  positives — the identical shape `test-dispatchable-frontier.sh` fixed for
  its own G7 on 2026-08-30), and 11 of its 19 mutation fixtures built from
  the live snapshot lost guard isolation once that snapshot's only
  ready-family count dropped to 1. Fixed by porting the sibling suite's
  `ARTIFACT_GUARDS` pattern and adding one synthetic ready-family entry to
  the mutation-case base. Mutation-verified: deleting R3's fire condition
  kills exactly its two dedicated cases; deleting the R2 block kills exactly
  its six.
  **Before: propose-nursery-refill-tests exit 1 (11/19 FAIL); propose-nursery-refill
  exit 1, R2 (spurious). After: propose-nursery-refill-tests exit 0 (19/19);
  propose-nursery-refill exit 1, R3 only (real, left red intentionally).**

**Pre-push coverage.** `hooks/pre-push`'s L0 block ran 4 gates (~1.3s):
`check-settled-fact-statements`, `check-holdout-closed-evaluation`,
`check-semantic-control-fixtures --check`, `check-partition-edges --baseline`
(the last joined by another lane earlier today, ADR-1546/1550). The four
gates this brief named were each measured and added:

| gate | measured | in L0 before |
| --- | ---: | :---: |
| `check-development-partition.py` | 0.13s | no (check.sh/justfile only) |
| `check-autogenesis-holdout-isolation.py` | 0.80s | no (check.sh/justfile only) |
| `check-holdout-adjacency.py` | 0.43s | no (check.sh/justfile only) |
| `check-draw7-frozen-families.py` | 0.04s | **no — invoked by NOTHING at all** |

`check-draw7-frozen-families.py` was a true orphan: not in `check.sh`,
`justfile`, or any hook, and invisible to
`check-control-registration.sh` because that registry is derived from
`scripts/tests/*`, not top-level `scripts/check-*.py`. Registered it as a
real step in both `scripts/check.sh` and `justfile` (mirroring the other
three's placement), so it now runs in `just check`/`check.sh` too, not only
the hook. It is a DIFF gate (`--before <ref>`, default `HEAD~1`), so
`hooks/pre-push` now captures `L0_BEFORE`/`L0_TIP` unconditionally in the
existing ref-parsing loop (previously `PREPUSH_BASE`/`PREPUSH_TIP` were set
only when a ref's diff touched `*.rs`/`*.toml`/`Cargo.lock`) and passes
`--before "$L0_BEFORE"`, so a batched multi-commit push is covered, not just
its tip commit.

`scripts/tests/test-prepush-l0-gates.sh` (arms A-C already existed for the
loop shape, script existence, and `check-partition-edges --baseline`'s
flag): added arm D-F (bare match on the three state-check gates) and arm G
(flag-aware match on `check-draw7-frozen-families.py --before`, since a bare
match would let the hook silently revert to the wrong single-commit
default). Drove all four new arms to failure against scratch `PREPUSH_L0_HOOK`
copies — removing any one gate's line, and separately stripping arm G's
`--before` flag — each produced exactly its own `FAIL` and nothing else;
scratch copies were never committed.

**L0 total: ~1.3s -> ~2.7s (measured warm on this host).**
`check-control-registration.sh`: unchanged, `controls=52 orphans=0`.

**The skip-list census.** Every `docs/plan/status/*.md` touched by a commit
since 2026-09-01 (61 files, via `git log --since`), grepped for
"pre-existing"/"not mine" (112 raw hits, 19 files after intersecting with
the date filter, one of which is this file). Filtered to hits that actually
name a GATE a lane treated as out of scope (excluding mutation-kill counts,
fact-row provenance, and baselines a lane itself closed), then each named
gate was re-run on this tree to see whether it is still red:

| gate | files (2026-09-01+) declaring it pre-existing | status now |
| --- | ---: | --- |
| `check-autogenesis-nursery.py` | 3 (`400-nursery-draw-17`, `nursery-draw-19`, `nursery-draw-author`) | **green** (fixed by `431-partition-gates-green`/`432-train-is-not-evaluation`, ADR-1563/1564) |
| `check-development-partition.py` | 1 (`nursery-draw-19`) | **green** (same fix) |
| `mathlib-nursery-split --check` | 1 (`431-partition-gates-green`) | **green** (fixed by `d46e578bc`, ADR-1564) |
| `tests/test_check_autogenesis_nursery` | 2 (`431`, `432`) | **green** (31 tests OK) |
| `check-dispatchable-frontier.py` (G7) | 1 (`405-divergence-bitwise`) | **green** (dispatchable set non-empty) |
| `gen-autogenesis-nursery-refill.py --check` | 1 (`queue-unblock-four-families`) | **green** |
| `check-absence-claims.py` (budget ratchet) | 1 (`eisenstein-lattice`) | **green** |
| `check-settled-fact-statements.py` | 1 (`eisenstein-2`, fixed by that lane itself) | **green** |
| `nursery-dispatch-baseline --check` | 2 (`431`, `432`) | **green — this lane** |
| `propose-nursery-refill` | 2 (`431`, `432`) | **red — this lane's R2 fix landed, R3 is real (see above)** |
| `tests/test_check_autogenesis_holdout_isolation` | 2 (`431`, `432`; `406` names the bare script separately) | **RED — still unowned** |
| `check-aggregate-scope.sh` | 1 (`406-nursery-repartition`) | **RED — still unowned** |
| `attest-nursery-surface.py` | 1 (`431`) | **unverifiable on this host** — needs a built Mathlib, pinned to s5 |
| `cargo doc --workspace --all-features --no-deps` (rustdoc links) | 2 (`creal-split`, `creal-split-2`) | **not re-run this session** (no cargo per this lane's scope) |
| `scripts/tests/test_fact_frontier.py` | 2 (`frontier-holdout-screen`: found not fixed; `frontier-test-drift`: claims DONE) | **RED — down from 10 failures to 1** (`test_exact_gate_review_allows_kernel_b_and_new_mention_rejects`), confirmed by direct run this session |

Three gates are still red on main after this lane's fixes and are named here
because no lane above claimed to fix them and none is a one-hour job:

- **`propose-nursery-refill` (R3 cannot-refill)** — real: growing the pool
  needs proof work (a settled mirror witnessing a new bridge constant, or
  declaring `instSubNat`/similar per `sole_blocker_note`). Owner: whichever
  lane next authors a nursery draw / grows the fact catalog.
- **`tests/test_check_autogenesis_holdout_isolation`** — the `held_out=206`
  pin is stale against the live `held_out=226`; this is the SECOND
  recorded drift of this exact pin (`402-score-the-blind-population.md`
  already moved it 186 -> 206 once). Needs the manual review the test's own
  failure message demands (establish rise-vs-fall, verify new rows are
  unspent, extend the audit trail) before re-pinning — not a mechanical
  bump. Owner: whoever runs the next nursery draw / holdout audit.
- **`check-aggregate-scope.sh`** — 81 one-sided steps total, 17 unrecorded
  (`check.sh`-only: 4; `just`-only: 13, largely the checked-interchange /
  lean-adapter / structural-index / module-baseline / proof-plan family).
  Also named pre-existing by `406-nursery-repartition.md` the same day.
  Currently unowned; needs either the missing steps added to both files or
  `--update` to record them deliberately.

Not independently reconfirmed this session (reported fixed by
`420-baseline-holdout-leak.md`, but its own gate,
`check-generated-artifact-ownership.py`, runs sandboxed copies of 17
producers and did not finish inside this session's time budget): treat as
"reported fixed, unverified" rather than confirmed green.

<!-- plan-section: landed-changes -->

| 2026-09-02 | `ffb84983c` | regenerate the stale `mathlib-nursery-dispatch-baseline-v1.json` (`d46e578bc` re-recorded the nursery, no row moved partition); `--check` 1 -> 0 |
| 2026-09-02 | `f9f289d35` | remeasure `refill-headroom-v1.json` (R2 fixed, R3 is a real standing finding, left red); rebuilt `test-propose-nursery-refill.sh`'s case 0 and guard-isolation base so 11 spuriously-failing cases pass again; mutation-verified |
| 2026-09-02 | `92b591bfc` | add `check-development-partition`/`check-autogenesis-holdout-isolation`/`check-holdout-adjacency`/`check-draw7-frozen-families` to `hooks/pre-push`'s L0 block (~1.3s -> ~2.7s), register the orphaned `check-draw7-frozen-families.py` in `check.sh`/`justfile`, add and mutation-drive 4 new arms in `test-prepush-l0-gates.sh` |
