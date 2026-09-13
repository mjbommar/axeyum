# Lane: anchor-repair — the stale mutation anchors blocking the aggregate gate

<!-- plan-section: lane-status -->

**Lane anchor-repair (`DONE`, anchor-repair, 2026-09-13).**
`scripts/check.sh` step `mutation-anchors-are-fresh` was RED on `main`, blocking
the fullest aggregate gate. It is green: `MUTATION_ANCHORS|suites=124|anchors=1030|stale=0`,
exit 0. ADR: [ADR-1990](../../research/09-decisions/adr-1990-the-anchor-gate-could-not-count-and-a-fresh-anchor-is-not-a-live-mutation.md).

**The budget question, answered plainly: no capability regression.** The granted
work budget still reaches subsumption and BVE. `run_subsume`/`run_bve` still take
`grant`, still build `SubsumeOptions { work_budget: Some(work_budget) }` /
`BveOptions { work_budget: Some(work_budget), .. }`, and still treat `None` as
"do not run the pass" rather than "run it with zero". They moved from
`crates/axeyum-solver/src/sat_bv_backend.rs` to
`crates/axeyum-cnf/src/inprocess.rs` in `a083163f1`. That is the whole change,
and it was verified by reading both functions rather than by an anchor matching
again.

**What drifted.** Three unrelated causes, each attributed to a commit by walking
the anchor back through the history of the file it points into:

| anchor | broke at | date | cause |
|---|---|---|---|
| `dt-capability-1935` exactness | `47f3d61d8` | 09-12 | a SECOND exactness check at the same indentation → AMBIGUOUS |
| `dt-capability-1935` UF result | `47f3d61d8` | 09-12 | the guard was DELETED — that was ADR-1946's point |
| `dt-capability-1935` Ackermann shape | `47f3d61d8` | 09-12 | a third conjunct added to the arm |
| `dt-capability-1935` array field | `c3891327d` | 09-13 | `sort_mentions_datatype` gained an `arena` parameter |
| `dt-valued-result-1946` array result | `c3891327d` | 09-13 | same `arena` parameter |
| `solver-occurrence` subsume budget | `30785cf33` | **09-08** | option literal duplicated, then moved crates |
| `solver-occurrence` BVE budget | `30785cf33` | **09-08** | same |

The two budget anchors had been stale for **five days**, not one.

**One mutation is removed, not re-anchored.** `dt-capability-1935`'s "a
datatype-valued UF result is refused rather than Ackermannized" pinned a refusal
ADR-1946 deliberately removed — admitting that result was the whole content of
the ADR. There is nothing to anchor to, and anchoring to adjacent text would have
made the suite green over a distinction the code stopped making. Both successors
are controlled in `dt-valued-result-1946`, so coverage moved suites rather than
being lost. ADR-1935's own mutation table is stale on that row.

**The measurement that overturned the obvious fix, and is the reason to run
these rather than trust them.** The tidy move — put the two wiring mutations in
the crate their code now lives in — was measured and is WRONG:

```
cnf-occurrence-pass-wiring: baseline green, 9 tests
  the granted budget reaches subsumption SURVIVED — 9 tests ran, none depend on this guard
  the granted budget reaches BVE        SURVIVED — 9 tests ran, none depend on this guard
```

Every grant in `inprocess.rs`'s own tests is `u64::MAX`, and the mutation does
not starve the pass, it UNCAPS it — so "budgeted with infinity" and "unbudgeted"
are the same run and no test in that crate can tell them apart. The tests that
can never moved: `the_granted_budget_reaches_the_pass` and
`the_granted_subsume_budget_reaches_the_pass` are still in `sat_bv_backend`'s
test module. Both mutations therefore keep the solver runner and carry an
explicit per-mutation target; the suite spans two crates and its banner records
this measurement so the next person finds the reason it was rejected.

**The gate could not count.** `check_anchors()` assigned `failed = 1` per problem
instead of accumulating: seven problem lines, `stale=1`. Somebody repairing six
of seven would have watched the number not move. Two status docs in-tree already
quote `stale=1` beside "the same 4 pre-existing complaints". Fixed, and the exit
status is now clamped to a boolean — `SystemExit` takes its status mod 256, so
returning the raw count was a gate that could not fail at exactly 256 stale
anchors.

**Hand-merge damage, found while there.** `scripts/tests/mutation_controls.py`
held the whole self-demo block **three times** — seven top-level bindings plus a
duplicated `SUITES` key, all byte-identical (`ast` + sha256). A `FunctionDef`
scan finds three of the seven; the other four are `Assign` nodes, and the
duplicate `SUITES` key is the dangerous one because it silently overwrites a
whole suite without moving any count the gate prints. Deduplicated to one each,
proven by AST, and the harness re-run to confirm identical output — a parse is
not a run.

**`check_anchors` had no control of its own** among the harness's 25
self-mutations, and its two freshness controls inject exactly ONE fault each,
where `= 1` and `+= 1` agree. A guard that can only observe a count of one cannot
check that counting happens. Closed: `test_two_stale_anchors_are_counted_as_two`
plus mutation 26, isolated to show it discriminates the arithmetic rather than
merely dying because mutating the harness breaks the harness's own anchor.

**NOT fixed, and the next lane should take it.** The gate costs **0.14 s and
builds nothing**, yet runs only in `just check`/`check.sh` — the aggregate gate
CLAUDE.md steers lanes away from. The 840-line `hooks/pre-push` battery lanes DO
pay ten minutes for runs **no Python suite at all**, so the lane whose Rust
refactor breaks an anchor never sees it, and the lane that does see it correctly
reports "none this lane's". Adding one 0.14 s read-only step to pre-push is the
obvious candidate, deliberately left to a lane that can watch the effect of
tightening a shared hook. Deeper and also untouched: `--check-anchors` verifies
a mutation POINTS at real code, never that it KILLS anything, and no gate runs a
real mutation suite — so a perfectly fresh suite can measure nothing, which is
exactly what the `cnf-occurrence-pass-wiring` measurement above caught live.

<!-- plan-section: landed-changes -->

| 2026-09-13 | `f4445e844` | `mutation-controls`: the anchor gate could not count (`failed = 1`, seven problems reported as `stale=1`), and the file held three byte-identical copies of seven top-level bindings plus a duplicate `SUITES` key. |
| 2026-09-13 | `ec2116d8a` | Re-anchor five stale mutations against the three commits that drifted them; delete the one whose guard ADR-1946 removed rather than inventing an anchor for it. |
| 2026-09-13 | `6a6ae456c` | The budget-wiring mutations keep the SOLVER runner with a per-mutation target — measured SURVIVING 2 of 2 under the tidier cnf runner — and `check_anchors` gets the mutation control it never had. |
| 2026-09-13 | `d76a70e85` | ADR-1990: what drifted, the budget answer, and the four mechanisms that let anchors go stale under a green-ish gate — two closed here, two named and left. |
