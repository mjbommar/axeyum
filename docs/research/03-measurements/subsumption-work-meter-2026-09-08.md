# Subsumption had no waste to reclaim, and the dead ids were never the constant

**Date:** 2026-09-08 · **Lane:** `subsume-meter-compact` · **Host:** s4 (12th Gen
Intel i5-12600K, 6 P-cores / 4 E-cores, 16 threads, 123 GB) ·
**Corpus:** the pinned `bench-results/parity-lists/QF_BV.txt` (200 files,
sha256 `6f873e15b191`) · **Rows:**
`bench-results/subsumption-meter-2026-09-08/`

This acts on the two items
[the admission measurement](inprocessing-admission-2026-09-08.md) §6 listed as
not done: subsumption had no work meter at all, and occurrence lists are never
compacted, with "whether compaction beats budgeting, or the two compose"
explicitly unmeasured.

Three results, and two of them are refutations.

1. **Compaction does not beat budgeting and cannot.** The lazy-removal constant
   it exists to delete is **0.10 %** of what BVE spends; budgeting removes
   52.9 %. Even a free, perfect compactor is 520 x short.
2. **Subsumption has almost no waste to reclaim.** The mechanism that made BVE's
   budget worth 217 s — a pass spending most of its work after its last useful
   action — is 1.5–2.2 % here. Its spend spans 131 x to 193 x setup across the
   corpus, against BVE's 474 x to 39,654 x.
3. **A subsumption budget still pays, for a different reason, and it recovers
   `div3.c.50`.** Not by declining waste but by declining *real* work that is
   worth less than the search time it costs. At `K = 50 x setup`: 44.5 s of
   subsumption not spent, the best inprocessing arm measured (186 decided,
   PAR-2 960.5 against an unbudgeted 185 / 1003.7), and the one file the
   admission lane's gated arm lost comes back — decided `sat` in 22.4 s where
   the baseline timed out.

The instrumentation is what makes all three checkable, and it is the part worth
keeping.

---

## 1. One meter, two passes

`crates/axeyum-cnf/src/pass_work.rs` is now the meter/budget pair both
occurrence-list passes use: setup charged up front, a one-comparison stop that
**latches its own reason**, the last-progress reading that prices every
candidate budget from a single unbudgeted sweep, and a dead-entry counter. BVE
moved onto it with no behaviour change; subsumption gained it.

Two copies would have been the easier diff and the wrong one. The whole value of
"BVE spends 95 billion steps and subsumption spends 4 billion" is that the two
numbers are in the same unit, and two independently maintained meters drift in
what they charge on the first change to either.

It does **not** use `axeyum_ir::budget::WorkMeter`, deliberately: `axeyum-cnf`
does not depend on `axeyum-ir`, and pulling the term IR into the CNF layer to
hold a `u64` would be a layering change made for a struct (ADR-0001). The split
matches where the decisions live — a pass **meters itself** in its own crate,
and `axeyum_ir::budget`'s `EffortPolicy` / `EffortAccount` / `Grant` turn a
formula into a budget from `axeyum-solver`. `PassWork::must_stop` is the same
`spent >= limit` test as `Budget::exhausted`, so a limit computed there is
consumed unchanged here.

On the solver side, `bve_admission` became `admit_occurrence_pass` plus a table
of constants, and `subsume_admission` is the second caller. A test asserts the
two grants stay in the ratio of their multiples on the same formula, so a fork
of the shared function fails rather than diverging quietly.

### What the meter charges

One step per occurrence-list entry **examined** (not per entry that survives the
filters), per literal walked by a subset test, per literal marked and unmarked,
per occurrence entry written, plus each round's `O(|F|)` setup. It is the same
unit `crate::bve` charges in.

The counter that was already there — `checks`, the candidates surviving the
length and signature pre-filters — is to subsumption exactly what `resolutions`
was to BVE: a bound on a component. On the file that costs the most it is never
reached.

---

## 2. Subsumption is not a runaway pass, and that is the finding

Calibration arm: `inproc-vivify` at the parity protocol's 24 s / 8 GiB, BVE
budgeted at its shipped `2000 x setup`, subsumption unbudgeted. 200 of 200 rows;
141 files ran subsumption and recorded the counters.

| quantity | subsumption | BVE (2026-09-08) |
|---|---:|---:|
| last progress, p50, in units of the pass's own setup | **131 x** | 474 x |
| p90 | **179 x** | 12,723 x |
| max | **193 x** | 39,654 x |
| spread, p50 to max | **1.5 x** | **84 x** |
| spend after the last useful action | **2.2 %** | 22.9 % |
| throughput, steps/ms (median) | **127,599** | 460,365 |

**The distribution has a typical member, and BVE's did not.** Where BVE's last
elimination spanned five orders of magnitude in units of its own setup cost —
so that no single multiple could be both generous and frugal — subsumption's
spend sits between 131 x and 193 x setup across the whole corpus. It does work
proportional to the formula and then stops.

The consequence is the one that matters for a budget: **there is almost nothing
to reclaim.** BVE's budget bought 217 seconds mostly by declining work that had
already stopped paying off; subsumption's 2.2 % of spend after its last useful
action is 1.7 s of the corpus's 77.6 s. Every second a subsumption budget saves
beyond that is a second of work that was still subsuming clauses.

### Pricing a budget, from the one calibration sweep

Derived from the calibration rows, so no extra sweep per candidate. "sec saved"
charges each file at its own measured rate; "files keeping 100 %" is files whose
last progress still fits the budget.

| K (x setup) | files cut | sec saved | files keeping 100 % |
|---:|---:|---:|---:|
| 10 | 127 | 72.5 s | 22 |
| 25 | 109 | 64.9 s | 34 |
| 50 | 98 | 52.3 s | 46 |
| 100 | 82 | 28.5 s | 60 |
| 200 | **0** | **0.0 s** | 141 |
| 500+ | 0 | 0.0 s | 141 |

Read this against BVE's table and the difference is the whole story. BVE at
`K = 2000` declined 200 s of 307 s while 98 of 143 files still reached their
last elimination. There is no such row here: **every second is bought by giving
up subsumptions**, and the only choice is how many.

Which makes the constant a decision about the *solve*, not about the pass — so
it was measured that way rather than read off the table.

### Confirmation: three budgets against the baseline

Four arms, run **concurrently and pinned to distinct physical P-cores**, 200 of
200 rows each, `bench-results/subsumption-meter-2026-09-08/b2-*.jsonl`. Verdicts
were checked before any timing was read: **0 cross-arm conflicts.**

| arm | decided | PAR-2 | inproc s | subsume s | vivify s | bve s | work-cut files |
|---|---:|---:|---:|---:|---:|---:|---:|
| inprocessing off | 184 | **926.8** | — | — | — | — | — |
| subsumption unbudgeted | 185 | 1003.7 | 160.2 | 74.4 | 2.9 | 79.1 | 53 |
| `K = 100` | 184 | 1020.5 | 120.9 | 37.4 | 2.6 | 77.8 | 135 |
| **`K = 50`** | **186** | **960.5** | 149.4 | **29.9** | 3.5 | 111.1 | 152 |

`K = 50` is shipped. Three things in that row are worth naming separately.

**It recovers the file this lane was handed.** `div3.c.50` — where subsumption
spends a 10.8 s slice by itself while BVE spends 73 ms, and which the admission
lane's gated arm lost — comes back:

| arm | verdict | wall | subsume | bve | subsumption work |
|---|---|---:|---:|---:|---:|
| off | unknown (watchdog) | 25,000 ms | — | — | — |
| unbudgeted | unknown (watchdog) | 24,439 ms | 10,764 ms | 73 ms | 1,245,284,660 |
| `K = 100` | unknown (watchdog) | 25,000 ms | — | — | — |
| **`K = 50`** | **sat** | **22,402 ms** | 4,221 ms | 4,501 ms | **452,526,023** |

452,526,023 is exactly `50 x` that file's setup cost of 9,050,520 — the budget
binding to the step, which is what "deterministic" means here. Note that the
**baseline also times out** on this run: at this host load `div3.c.50` sits
inside the boundary population the cost decomposition documented, so the
comparison that matters is against the unbudgeted arm, not against `off`.

**BVE's time goes up, not down.** 79.1 s to 111.1 s. Cutting subsumption short
leaves more clauses for BVE to eliminate and more of the slice to do it in, so
the passes trade rather than compose. Net inprocessing still falls, 160.2 s to
149.4 s, and the trade is favourable — but a note claiming "44.5 s saved" as a
bottom line would be wrong by two thirds.

**`K = 100` is worse than doing nothing on PAR-2**, and that is not a monotone
story. The identical-arm spread measured on this host between two `off` runs
was **1 file and 17.6 PAR-2 points** (185 / 944.4 against 184 / 926.8). The
43-point gap from unbudgeted to `K = 50` exceeds that; the one-file differences
in decided counts do not. So: the seconds are measured, the ordering of adjacent
arms is provisional, and `K = 100` is reported rather than dropped because
dropping it would have made the ranking look cleaner than it is.

---

## 3. Compaction against budgeting: not close

The hypothesis was that lazily-removed clause ids are "a large constant on
exactly the files being budgeted", so a budget hides the cost while compaction
removes it. `dead_occurrence_entries` — occurrence entries examined whose clause
had already been removed — measures that constant instead of arguing about it.
It is a **subset** of the spend, so `dead / spent` is the fraction a *perfect*
compactor could delete.

Unbudgeted BVE over the 200-file list:

| | value |
|---|---:|
| occurrence-list steps spent | 94,971,266,676 |
| of which examined a dead entry | **96,305,989** |
| **share** | **0.10 %** |
| per file: p50 | 0.06 % |
| p90 | 0.68 % |
| max | 12.50 % |

**The ceiling on compaction is 0.10 % of BVE's scan.** Against that:

| fix | BVE work steps | change |
|---|---:|---:|
| neither | 94,971,266,676 | — |
| **budget only** (2000 x setup) | 44,749,287,705 | **−52.9 %** |
| compaction only | 94,542,807,315 | −0.45 % |

Budgeting removes 50.2 billion steps. Removing *every* dead entry for free would
remove 0.096 billion — **520 times less**. The two do not compose in any
interesting way either: there is nothing meaningful for compaction to add to a
budget that has already declined half the work.

Compaction does do what it says: it cut dead entries from 96.3 M to 59.6 M
(−38 %, the rest being lists that never reach the half-dead threshold). It is
simply that the quantity it halves is not the cost.

**Why `live_ids` is the hot spot without dead ids being the reason.** The
decomposition was right that the occurrence-list scan dominates and wrong about
why. The scan is expensive because the lists are long and are walked many times
— twice per variable popped, and a variable is re-queued once per neighbour of
every later elimination — not because they are full of corpses. Removal is lazy,
but an eliminated variable's own lists are never scanned again, and a neighbour's
list is mostly live when it is next visited.

**Wall-clock is not usable here and is not quoted.** Both compaction arms ran
BVE unbudgeted, so both were cut off by the wall clock at different points
(1,875,684 against 1,849,115 variables eliminated) — the runs diverge, so their
seconds are not comparable in kind. The host also carried load 15–20 from
concurrent lanes. The step counters are deterministic and unaffected, which is
exactly why the claim above is stated in steps.

### The knob that was removed rather than shipped

Subsumption **cannot produce a dead occurrence entry at all**, and it reports
`dead_occurrence_entries = 0` on every file. That is a property of its schedule:
occurrence lists are rebuilt from the live clauses at the top of every round, and
the only clause a round ever removes is the candidate it is currently examining
— which is connected on the `Keep` arm, i.e. only when it is *not* removed.

So `SubsumeOptions` has no compaction knob. An option that cannot fire is a
safety mechanism that cannot fail, which is worse than not having one; the
counter measures the zero instead, and
`this_pass_cannot_produce_a_dead_occurrence_entry` fails if the schedule ever
changes such that the invariant stops holding.

---

## 4. Mutation controls

Every guard here was deleted once and the resulting failure **recorded, not
predicted**. Four suites, 21 mutations, registered in
`scripts/tests/mutation_controls.py` as `cnf-pass-work-meter`,
`cnf-subsume-work-meter`, `cnf-bve-compaction` and
`solver-occurrence-pass-admission`, so they can be re-run rather than believed.

| deleted | tests that died |
|---|---|
| `with_setup`'s `spent: setup` | 2 — `setup_is_charged_before_the_pass_does_anything`, `last_progress_brackets_the_free_budget` |
| `must_stop`'s `self.exhausted = true` | 2 — `must_stop_fires_at_the_limit_and_never_without_one`, `the_stop_reason_survives_further_charging` |
| compaction's `live_count * 2 > before` threshold | 1 — `compaction_waits_for_half_the_list_to_die` |
| the compaction rewrite's `work.charge` | 1 — same test |
| making `charge_dead` also move `spent` | 1 — `dead_entries_are_counted_inside_the_spend_not_beside_it` |
| the per-entry scan charge in `try_subsume` | 1 — `every_occurrence_step_is_charged_exactly_once` |
| the subset test's literal charge | 1 — same test |
| the mark/unmark charge | 2 — same test, plus `the_budget_binds_within_a_round_and_not_only_between_rounds` |
| each round's occurrence-list rebuild charge | 1 — `every_occurrence_step_is_charged_exactly_once` |
| `work.must_stop()` in the candidate loop | 1 — `the_budget_binds_within_a_round_and_not_only_between_rounds` |
| `work.note_progress()` in the `Subsumed` arm | 1 — `a_budget_at_the_last_progress_reading_loses_nothing` |
| subsumption's `work.charge_dead(1)` | 1 — `a_dead_occurrence_entry_is_counted_when_one_is_reachable` |
| BVE's `charge_dead` in `live_ids` | 1 — `eliminations_leave_dead_ids_behind_for_later_scans_to_pay_for` |
| BVE's `if self.compact` block | 1 — `compaction_changes_the_cost_and_not_the_result` |
| BVE's occurrence-scan charge | 2 — `the_occurrence_scan_is_charged_even_when_the_variable_is_rejected`, `work_at_last_elimination_brackets_the_free_budget` |
| BVE's `work.must_stop()` in the queue | 1 — `work_budget_stops_the_pass_early_and_keeps_the_result_sound` |
| compute the budget, hand subsumption `SubsumeOptions::DEFAULT` | 1 — `the_granted_subsume_budget_reaches_the_pass` |
| compute the budget, hand BVE `work_budget: None` | 1 — `the_granted_budget_reaches_the_pass` |
| `.with_init_cost` in the shared admission | 2 — both `a_spent_slice_delays_*` tests |
| the slice cap on the reference window | 2 — both `a_spent_slice_delays_*` tests |
| the lever's "an unparseable value keeps the default" | 1 — `the_measurement_levers_default_to_the_shipped_constants` |

### Two of these SURVIVED on the first run, and both were real

The table above is the second run. The first found two guards that nothing
tested, and neither was obvious from reading the code.

**"the work budget stops the candidate loop" survived.** Deleting the
`must_stop()` check inside `subsume_round`'s candidate loop left all 14 tests
green, because the *round* loop checks too — so the budget still appeared to
bind and `work_exhausted` was still set. It does not bind: the first round
always starts, so with only the round-level check one round overruns the budget
by whatever that round costs, which on a large formula is unbounded — exactly
the population a budget exists for. The new guard uses a fixture that reaches
its fixpoint in **one** round, which makes the round-level check unable to stop
anything, so only the candidate-loop check can.

**"the dead-entry counter reaches the stats" survived**, and could not be fixed.
Replacing `stats.dead_occurrence_entries = work.dead_entries()` with `= 0`
killed nothing, because the only test asserts the value **is** zero — the
vacuity the invariant is made of. There is no input for which this pass produces
a nonzero value, so no test can distinguish the assignment from the constant,
and that impossibility is the finding rather than a gap to paper over. What is
testable is the counting *path*, so
`a_dead_occurrence_entry_is_counted_when_one_is_reachable` plants a dead id
directly into a `try_subsume` call and requires the counter to see it. The pair
then says both halves: the instrument works, and the pass never trips it.
Without it, "subsumption reports zero dead entries" would have been a statement
about the instrument.

### Three guards that exist because of how they nearly failed

**The charge test asserts an exact equality, not an inequality.** The sibling
lane's first scan-charge guard asserted `work_spent > setup` and its mutant
*survived*, because unrelated charges satisfied it. Here the fixture is two
clauses and the expectation is a sum of named terms — one line per place the
pass touches memory — so deleting any single charge moves the number. Four
separate mutations are killed by that one test, which is what "exact" buys.

**The compaction test does not assert that compaction is cheaper.** On its
fixture compaction costs *more* (8,982 steps against 7,386): every variable
there is eliminated on its first visit, so a compacted list is never scanned
again and the rewrite buys nothing. Asserting a saving would have meant tuning
the fixture until it agreed with the hypothesis the corpus then refuted. It
asserts what compaction actually guarantees — the reduced formula and the
elimination count are unchanged, and the cost is not.

**The lever test consumes the shipped parsing function.** `parse_multiple_lever`
is separated from the environment read so a test can call it: a test that sets a
process-wide variable is a gate on one shell and races a threaded suite, and a
test that re-derives the parsing rules inline passes while the artifact is wrong.

## 5. What was not done

* **Inprocessing is still not a net win at 24 s, and this does not make it
  one.** `K = 50` is 960.5 PAR-2 against the baseline's 926.8. It closes most of
  the gap the unbudgeted arm had (1003.7) and does not close it. Nothing here is
  enabled by default: `SolverConfig::cnf_inprocessing` is still `false`, the
  compaction knob is off, and `SubsumeOptions::DEFAULT` is exactly the behaviour
  every caller had before the meter existed.
* **Two runs, not two hosts, and both under other lanes' load.** Batch 1 ran at
  load 15–20 and batch 2 at 8–12; every arm within a batch ran concurrently and
  pinned to distinct physical P-cores, so arms are comparable to each other and
  the batches are not comparable to the 2026-09-08 admission note's absolute
  seconds. Every claim about *work* is stated in the deterministic step counters
  for that reason, and the run-to-run spread on an identical arm is quoted above
  rather than left for the reader to assume away.
* **A quiet-host repeat, and a `K` between 50 and 100.** The pricing table says
  `K = 25` would decline another 12 s; whether that is bought or given away was
  not measured, and the `K = 100` row says the curve is not smooth enough to
  interpolate.
* **Compaction is implemented, off, and kept.** `BveOptions::compact_occurrences`
  costs nothing when unset and is the only way to re-measure the 0.10 % ceiling
  if the elimination schedule ever changes. It is not a recommendation.
* **The `unsat` certificate gap is untouched.** Per ADR-1750 the proof is checked
  against the reduced formula, so the BVE link is trusted rather than checked;
  subsumption is model-preserving and emits ordinary `RUP`, which this lane did
  not change.
