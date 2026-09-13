# ADR-1990: the anchor gate could not count, and a fresh anchor is not a live mutation

Status: accepted
Index-summary: `scripts/check.sh`'s `mutation-anchors-are-fresh` step was RED on `main` for five days, blocking the full aggregate gate. It printed **seven problem lines and reported `stale=1`**, because `check_anchors()` assigned `failed = 1` per problem instead of adding — so a lane repairing six of seven would have watched the number not move, and one lane status doc in-tree already says `stale=1` and "the same 4 pre-existing complaints" **in the same table cell** — the author counted the problem lines, got four, and recorded the gate's one beside it. Three unrelated causes, each attributed to its commit rather than inferred: [ADR-1946] (`47f3d61d8`) added a SECOND exactness check at the same indentation, making a one-line anchor AMBIGUOUS, and widened the Ackermann shape arm with a third conjunct; [ADR-1955] (`c3891327d`) gave `sort_mentions_datatype` an `arena` parameter; and `30785cf33` (2026-09-08) duplicated the two budget-option literals before `a083163f1` moved `run_bve`/`run_subsume` into `axeyum-cnf`. **The budget still reaches subsumption and BVE** — a file move, not a capability regression, verified by reading both functions. One mutation is REMOVED rather than re-anchored: ADR-1946 ADMITTED the datatype-valued UF result its guard refused, so the distinction no longer exists and anchoring to adjacent text would have made the suite green over it. The lane's own tidier first attempt — move the two wiring mutations to the crate their code now lives in — **was measured SURVIVING, 2 of 2**: every grant in `inprocess.rs`'s tests is `u64::MAX`, and the mutation UNCAPS rather than starves, so no test in that crate can see it; the tests that kill it never moved out of `sat_bv_backend`. Structurally: the gate costs **0.14 s and builds nothing**, yet runs only in `just check`/`check.sh` — the aggregate gate CLAUDE.md steers lanes away from — and the 840-line pre-push hook runs **no Python suite at all**, so the lane whose Rust refactor breaks an anchor never sees it and the lane that does see it correctly reports "none this lane's". `check_anchors` was also the one function with **no mutation of its own** among the harness's 25, and its two freshness controls inject exactly ONE fault each, where `= 1` and `+= 1` agree. Both closed here (26 mutations, 36 controls). The deeper limit is stated and NOT closed: `--check-anchors` verifies that a mutation POINTS at real code, never that it KILLS anything, and no gate runs a real mutation suite — so a perfectly fresh suite can measure nothing.
Index-status: accepted
Date: 2026-09-13

## Context

`scripts/check.sh` step `mutation-anchors-are-fresh` was red on `main`, and had
been for days, blocking the fullest aggregate gate. It printed this:

```
AMBIGUOUS ANCHOR dt-capability-1935: 'congruence needs an EXACT expansion of its datatype argument' matches 2 places
NOT APPLIED dt-capability-1935: 'an array field whose element sort mentions a datatype gets no variable' matches 0 places
NOT APPLIED dt-capability-1935: 'a datatype-valued UF result is refused rather than Ackermannized' matches 0 places
NOT APPLIED dt-capability-1935: 'an Ackermannized datatype argument must be a variable or a constructor' matches 0 places
NOT APPLIED dt-valued-result-1946: 'an array-over-a-datatype result is refused rather than fallen through' matches 0 places
NOT APPLIED solver-occurrence-pass-admission: 'the granted budget reaches subsumption' matches 0 places
NOT APPLIED solver-occurrence-pass-admission: 'the granted budget reaches BVE' matches 0 places
MUTATION_ANCHORS|suites=124|anchors=1030|stale=1
```

Seven problem lines. `stale=1`.

## What drifted, and when

Attributed by walking each anchor back through the history of the file it points
into, not by reading commit messages:

| anchor | broke at | date | cause |
|---|---|---|---|
| `dt-capability-1935` exactness | `47f3d61d8` | 09-12 | a SECOND exactness check at the same indentation |
| `dt-capability-1935` UF result | `47f3d61d8` | 09-12 | the guard was DELETED (that was the ADR's point) |
| `dt-capability-1935` Ackermann shape | `47f3d61d8` | 09-12 | a third conjunct added to the arm |
| `dt-capability-1935` array field | `c3891327d` | 09-13 | `sort_mentions_datatype` gained `arena` |
| `dt-valued-result-1946` array result | `c3891327d` | 09-13 | same `arena` parameter |
| `solver-occurrence` subsume budget | `30785cf33` | **09-08** | option literal duplicated, then moved crates |
| `solver-occurrence` BVE budget | `30785cf33` | **09-08** | same |

The two budget anchors had been stale for **five days**, not one. From
`30785cf33` they matched twice (AMBIGUOUS) or zero times in
`sat_bv_backend.rs`; `a083163f1` then moved the code into
`axeyum-cnf::inprocess`, where the anchor text is byte-identical and matches
exactly once — pointing at the wrong file, not at vanished code.

### The one that is removed rather than repaired

`dt-capability-1935`'s "a datatype-valued UF result is refused rather than
Ackermannized" pinned a refusal that [ADR-1946] **deliberately removed**;
admitting that result was the entire content of the ADR. The blanket
`if sort_mentions_datatype(result) { refuse }` became a `match` that takes
`Sort::Datatype(dt)` subject to exactness.

So there is nothing to re-anchor to. Anchoring to adjacent text that still
mentions the result sort would have turned the gate green over a distinction the
code stopped making, which is the failure mode this whole harness exists to
prevent. It is deleted, with the reasoning in place of the tuple. Both
successors are controlled in `dt-valued-result-1946` — the admission itself, and
the surviving array-over-a-datatype half of the old refusal — so coverage moved
suites rather than being lost. [ADR-1935]'s own mutation table is stale on this
row and is left as the historical record it is.

## The budget question, answered

The most important question was not "where do I re-anchor" but "does the granted
work budget still reach subsumption and BVE at all?" A capability regression
there would have outranked the entire repair.

**It does.** `run_subsume` and `run_bve` still exist, still take `grant`, still
build `SubsumeOptions { work_budget: Some(work_budget) }` and
`BveOptions { work_budget: Some(work_budget), .. }`, and still treat `None` as
"do not run the pass" rather than "run it with a budget of zero" — the
distinction their doc comments are careful about, because a zero-budget call
still pays the `O(|F|)` occurrence-list setup the admission test declined. They
live in `crates/axeyum-cnf/src/inprocess.rs` now instead of
`crates/axeyum-solver/src/sat_bv_backend.rs`. That is the whole change.

Verified by reading both functions, not by observing that an anchor matched
again.

## The measurement that overturned the obvious fix

The code moved to `axeyum-cnf`, so the mutations should move with it. That is
wrong, and the harness said so:

```
cnf-occurrence-pass-wiring: baseline green, 9 tests
  the granted budget reaches subsumption SURVIVED - 9 tests ran, none depend on this guard
  the granted budget reaches BVE        SURVIVED - 9 tests ran, none depend on this guard
```

Every grant in `inprocess.rs`'s own tests is `u64::MAX`, and the mutation does
not starve the pass — it UNCAPS it. **"Budgeted with infinity" and "unbudgeted"
are the same run**, so no quantity of tests in that crate can distinguish them.
The two tests that can, `the_granted_budget_reaches_the_pass` and
`the_granted_subsume_budget_reaches_the_pass`, never left `sat_bv_backend`'s
test module, where they grant a finite budget through the shipping schedule and
assert on the DIFFERENCE in `work_spent` rather than on an invariant that holds
either way.

So the suite keeps its runner and the two mutations carry an explicit
per-mutation target. `solver-occurrence-pass-admission` now spans two crates,
and its banner says so together with this measurement, so that the next person
to find the tidier arrangement finds the reason it was rejected.

A re-anchored mutation that no longer kills anything is worse than the stale
anchor it replaced, because the stale one at least announces itself.

## The gate could not count

`check_anchors()` assigned `failed = 1` on each problem instead of accumulating.
Seven problems, `stale=1`.

The cost is not cosmetic. Somebody repairing six of the seven would have watched
the number not move and concluded they had fixed nothing — and the number has
already been misread in practice. One lane status doc
(`docs/plan/status/playfair-2026-09-05.md`) records, **in a single table cell**,
both `MUTATION_ANCHORS|suites=99|anchors=917|stale=1` and *"the same 4
pre-existing complaints in `cas-summation-and-gaussian` and
`creal-migrate-consumers`"*. That is the sharpest evidence available: the author
counted the printed problem lines, got four, wrote four — and copied the gate's
`stale=1` down beside it without the contradiction registering. A gate whose
summary disagrees with its own output trains readers to ignore the summary.

(Two other status docs quote `stale=1` as well — `chebyshev-pi-2026-09-05.md`
and `lean-import-composition.md` — but each describes a single stale row, so for
those the number was right. The claim here is about the one cell that contradicts
itself, not about every citation of the field.)

The exit status is now clamped to a boolean rather than returned raw.
`SystemExit` takes its status mod 256, so `return failed` was a gate that could
not fail at exactly 256 stale anchors. `stale=` still carries the count.

## Three copies of the file's own gate

`scripts/tests/mutation_controls.py` contained the whole self-demo block **three
times**: `DEMO_SUBJECT`, `DEMO_CONTROL`, `SUITES["self-demo"]`, `DEMO_EXPECTED`,
`DEMOS`, `run_demo`, `check_anchors` and `main` — seven top-level bindings and a
duplicated `SUITES` key. All copies byte-identical (`ast` + sha256), so today's
behaviour was whatever landed last, which happened to agree. It would not have
stayed that way: the next lane to fix a bug in `check_anchors` would have fixed
one of three, and the last definition wins.

This is hand-merge damage at the repository's most-merged shared append point,
and it is the second distinct failure mode found in this one file in one day.

Note the search that finds it: an AST scan over `FunctionDef` alone reports
three duplicated functions. Four of the seven duplicated bindings are `Assign`
nodes, and the duplicated `SUITES` key is a `Subscript` target. **A duplicate
`SUITES` key is the dangerous one** — it silently overwrites a whole suite
without changing any count the gate prints.

## What structurally allows this, which is the part that matters

Four mechanisms, in increasing order of how much they should worry us.

**1. The gate is not where lanes look.** `--check-anchors` runs in
`scripts/check.sh` and the `justfile` — the aggregate gate CLAUDE.md explicitly
steers lanes away from on cost grounds. The 840-line `hooks/pre-push` battery
that lanes DO pay for, at roughly ten minutes, runs **no Python test suite at
all**. So the only gate that sees anchor drift is the one no lane runs.

The gate costs **0.14 s** (three runs: 0.16 / 0.14 / 0.13) and builds nothing.

**2. Nobody owns a gate that fires on someone else's file.** Anchor drift is
caused by lane A editing Rust and observed as a failure naming lane B's suite.
Lane A, reading a red step about a file it did not touch, correctly concludes
the breakage is not its own and records exactly that. The in-tree evidence is
verbatim: *"the same 4 pre-existing complaints ... **none this lane's**"*. Every
lane is individually right and the anchor stays stale. The counting bug made
this worse by rendering a growing problem as a constant `1`.

**3. The watcher was unwatched.** The harness carries 25 mutations of itself and
not one touched `check_anchors`, the single function that watches the other
1029 anchors. Its two freshness controls each inject exactly **one** stale
anchor — and `= 1` and `+= 1` agree at one. A guard that can only ever observe
a count of one cannot check that counting happens. This is the repository's own
rule about deriving an "every X" test from the authority, in a new dress.

**4. A fresh anchor is not a live mutation, and nothing checks the second.**
This is the limit that is stated here and NOT closed. `--check-anchors` verifies
that every mutation POINTS at code that exists, exactly once. It says nothing
about whether the mutation still KILLS anything, and by the harness's own
docstring *no gate runs any real mutation suite*: each subject is
mutation-checked once, by hand, at commit time, and then nothing looks again.

The `cnf-occurrence-pass-wiring` measurement above is precisely this hazard made
concrete. Those two mutations had fresh anchors matching exactly once in real
shipping code, and killed nothing. A green `--check-anchors` would have reported
them as healthy forever.

## Decision

1. Re-anchor the five repairable mutations; delete the one whose guard [ADR-1946]
   removed, recording why in place of the tuple.
2. Keep the two budget mutations in `solver-occurrence-pass-admission` with an
   explicit per-mutation target, because that is where the tests that kill them
   are. Record the survival measurement in the suite banner.
3. Make `check_anchors` accumulate, and clamp its exit status to a boolean.
4. Delete the duplicated blocks, keeping one of each binding.
5. Give `check_anchors` the mutation it never had
   (`test_two_stale_anchors_are_counted_as_two`, and mutation 26 in
   `mutation_controls_self.py`), isolated to show it discriminates the
   arithmetic rather than merely dying because mutating the harness breaks the
   harness's own anchor:

   | assertion | passes on `failed += 1` | passes on `failed = 1` | |
   |---|---|---|---|
   | `assertEqual(status, 1)` | yes | yes | blind |
   | `assertIn("NOT APPLIED", out)` | yes | yes | blind |
   | `assertIn("\|stale=2", out)` | yes | **no** | discriminates |

## What this does not fix

The gate still is not in `hooks/pre-push`, so the next Rust refactor will break
an anchor and the lane that breaks it still will not see it until somebody runs
the aggregate gate. Adding one 0.14-second read-only step to the pre-push
battery is the obvious candidate and is deliberately left to a lane that can
watch the fleet-wide effect of tightening a shared hook; it is not a change to
make invisibly at the end of an unrelated repair.

And mechanism 4 is untouched. Closing it means a gate that actually runs
mutation suites, which is a real cost decision — 124 suites, most of them cargo
— and belongs in its own ADR rather than being smuggled in here.

[ADR-1935]: adr-1935-the-congruence-precondition-is-exactness-not-scalarity.md
[ADR-1946]: adr-1946-a-datatype-valued-uf-result-the-witness-is-a-variable-and-the-scan-has-not-run-yet.md
[ADR-1955]: adr-1955-the-nested-array-sort-is-the-first-of-three-gates-and-the-only-one-the-ir-owns.md
