# The integer routes get counters, and the counters move the target

Lane `lia-counters-incremental`, 2026-09-08. Working record: the
instrumentation, the measurement it produced, and the two hypotheses the
measurement killed.

## Why this lane existed

`QF_LRA` got engine counters and the first thing they did was refute the plan's
stated cause ([the LRA lane's diary](lra-theory-side-2026-09-07.md)). The
integer routes had **nothing**: `LiaTheory` implements no `engine_counters`, and
the offline `lia-simplex` decider is not a `TheorySolver` at all, so neither
could ever appear on the `; theory-layer` line. A lane measuring `QF_LIA` or
`QF_UFLIA` was blind exactly as the `QF_LRA` lane had been.

The brief carried two source-level hypotheses to test:

1. **the per-assert `TermArena` clone** — `LiaTheory::assert` clones the whole
   arena and calls the *offline* branch-and-bound, per asserted literal;
2. **core minimisation** — it then re-calls the offline decider once per literal
   to minimise the conflict core.

One is confirmed and one is refuted, and neither is the largest term.

## The instrument, and the one rule it is built around

`crate::lia_counters`. Opt-in, clock-free, thread-local, restoring on drop —
the same shape as `DlOnlineStatsGuard` / `FrontDoorStatsGuard` /
`RouteAttributionGuard`, which `--trace` already composes. It prints one
`; lia …` line.

The hazard in doing this at all is that the fields are `u64`, so **`0` reads as
measured**. Wiring a struct in without wiring the sites is worse than leaving it
unwired: it manufactures confident zeros at full speed. Three things stop that:

- `last_lia_counters()` returns `Option`. `None` means *never enabled on this
  thread*.
- Every group carries an **entry counter** (`offline_calls`, `bnb_roots`,
  `simplex_solves`, `theory_asserts`, `propagate_calls`), so a zero inside a
  group is readable against whether the group ran.
- `LiaCounters::group_reading` returns `NotCollected` / `NotReached` /
  `Measured`, and the trace line prints that word in front of each group.

That third distinction earned itself immediately: on the 58 committed
`QF_UFLIA` losses the theory group reads `not-reached` on **all 58** — every
`theory_*` field is zero, and it is a zero that means "this code never ran", not
"it ran and found nothing". A struct without the reading would have reported the
same zeros as a measurement.

`LiaCounterPolicy` is a policy object rather than constants inlined at the
sites, and it is carried into the snapshot, so a number can say which policy
produced it.

**Cost when armed is not paid per event at the two hot sites.** The simplex
accumulates pivots in a local and records once per solve; branch-and-bound's
node count is recovered from the node-budget delta. Arming the guard cannot
change the shape of the profile it is being used to read, and
`arming_the_counters_does_not_change_a_verdict` is the control for the rest.

## Method

`scripts/lia-counter-sweep.sh <list> <out-dir> [budget_s] [jobs]` runs
`smtcomp_cli --trace` over a committed list at the parity budget (24 s, 8 GiB
`ulimit -v`) and keeps one log per file;
`scripts/lia-counter-report.py` aggregates, and **never averages a group that
did not run** — every total states the number of files in which its group read
`measured`.

Populations: the committed loss lists
`bench-results/parity-losses-20260905/QF_LIA.txt` (27 files) and
`QF_UFLIA.txt` (58). The miss population, not the parity list: improving files
we already win proves nothing.

Timings below are from **serial** runs (`jobs 1`). A parallel run inflates the
arena-clone share specifically, because it is memory-bandwidth bound where the
exact-rational arithmetic is not: the same file measured 11.5% clone share idle
and 27% under six-way load. Counts are load-insensitive and were taken either
way.

## Finding 1 — the whole budget is in `assert`, and `final_check` gets none of it

The existing `; theory-layer` stage timings, on the twelve `QF_LIA` losses that
produce one:

| | |
|---|---|
| `theory_assert_ms` | 8,057–10,034 of a ~10,050 ms route |
| `theory_final_check_ms` | **0 on every file** |
| `theory_propagate_ms` | 0 on eight, 1,163–7,758 on four |

This is the CDCL(T) anti-pattern stated as a measurement rather than an
inference. The integer theory is complete **per assert**, so the search never
reaches a final check with anything left to decide; every literal the Boolean
search puts on the trail triggers a full conjunctive integer decision.

## Finding 2 — the blind spot is the hardest 37% of the population

**10 of the 27 `QF_LIA` losses print no counters at all.** The watchdog fires
before the worker thread returns, and every thread-local diagnostic in this
binary is unreadable on that path — `; theory-layer` and `; route` already said
so explicitly; `; lia` now does too. Without that line the absence would be
indistinguishable from a run that never armed the guard.

Any aggregate over this division is therefore over the 63% that finished. That
is stated, not worked around.

## Finding 3 — `QF_UFLIA` never touches the online integer theory

| | |
|---|---|
| theory group reading | `not-reached` on **58 of 58** |
| binding routes | `uf-arith-lazy-overbound` 36, `…-pre-lia` 8, `dl-online` 8, `fd:parse` 6 |
| offline decider calls | **296,029** over the 52 files where the offline group ran |
| arena clones | **0** |

So hypothesis 1 is **irrelevant to `QF_UFLIA` entirely**. The lazy-overbound
routes call the offline conjunctive decider directly and never build a
`LiaTheory`. Any plan that reads "make the LIA theory incremental" as a UFLIA
lever is aimed at code that division does not execute.

## Finding 4 — core minimisation never runs. Zero of 363,062 offline calls

`core_minimizations = 0` and `core_minimization_probes = 0` across **both**
divisions, against 67,033 (`QF_LIA`) + 296,029 (`QF_UFLIA`) offline decider
calls.

Hypothesis 2 is refuted. `minimize_core` is only reached from a
`Feasibility::Unsat` returned by the *offline* branch of
`feasibility_with_core_minimization`, and on this population that branch is
never taken inside the budget — the searches run out of time before the offline
decider refutes a live set. The per-literal re-decision that the source reading
predicted would dominate does not happen once.

Two related zeros, both real and both worth having:

- `bnb_budget_exhausted = 0` on both divisions. The branch-and-bound node cap is
  **not** the incompleteness the loss census attributes files to, at this
  budget on this population.
- `filter_refuted = 0`. The warm rational filter in front of the offline decider
  refutes **nothing** in 17,950 `QF_LIA` checks and confirms an integral point
  in 400 (2.2%). It is close to pure overhead here.

## Finding 5 — the counter that was missing was the one doing the work

The first version counted `simplex_pivots` (the `simplex_feasible` engine) and
not the Gomory tableau's own pivots. On `BART-PT-020/RF-13.smt2` that reported
`simplex_pivots=0` against **10,102 Gomory calls** — which reads as "no pivoting
happened", when in fact every pivot had moved into an engine nothing was
watching. `gomory_pivots` / `gomory_rows` / `gomory_columns` now exist. On the
`QF_UFLIA` losses they total 2,840,232 pivots, which no earlier number showed.

This is the module's own rule catching the module: a counter that is silent
about the engine actually doing the work is the confident zero in its most
expensive form.

## Finding 6 — where the time actually goes, priced

`perf` is unavailable on this host (`perf_event_paranoid = 4`), so the split
inside `assert` was taken with a temporary in-situ timer (removed before
commit), one file at a time, uncontended:

| file | route ms | arena clone ms | offline decider ms | clone share |
|---|---:|---:|---:|---:|
| `BART-PT-020/RF-13` | 10,048 | **4,946** | 1,692 | 49% |
| `bofill ex13800_2600_100` | 10,051 | 2,333 | 6,053 | 23% |
| `bofill ex20400_2600_100` | 10,066 | 2,420 | 5,944 | 24% |
| `bofill ex5640_2400_100` | 10,102 | 1,591 | 6,244 | 16% |
| `bofill ex8280_2400_100` | 10,056 | 1,544 | 5,245 | 15% |
| `convert-jpg2gif-query-1423` | 10,028 | 1,012 | 8,274 | 10% |

**Hypothesis 1 is confirmed as a real cost and refuted as the dominant one.**
The clone is 10–49% of the budget (median ~21%) on the `QF_LIA` files where the
online theory runs, and 0% everywhere else. The offline conjunctive decider is
the larger half on nine files of ten.

The counted quantity behind that share: **13,270 clones copying 352,311,472
term nodes**, 11,365 nodes per assert. A clone is not a memcpy — `TermArena`
carries an `intern` map with one entry per node and four `String`-keyed name
tables — and `crates/axeyum-bench/examples/arena_clone_cost.rs` prices it on
real benchmark arenas at 27 ns/node at 6k nodes rising to 323 ns/node at 98k.
The per-node cost is superlinear in arena size, which is why an
"it's only 20k nodes" argument gets this wrong.

## What was changed, and what it measured

The clone existed for one reason: `live_terms` had to *add* a `BoolNot` node for
a false-polarity literal, and a `&self` method cannot grow `self.arena`. So
every atom's negation is now built **once**, at construction, in the theory's
own arena, and the live conjunction is assembled by lookup against
`&self.arena`. At most one new node per registered atom, once, against a copy of
the whole arena on every check. Work proportional to the delta rather than the
state.

Nothing about the decider's input changes — same registered atom, same interned
`BoolNot` — and `live_terms_in_place` returns `None` in exactly the places
`arena.not(atom).ok()?` did, so an unbuildable negation still degrades to
`Unknown`. The owning-arena builder stays for the equality-branch probe, which
genuinely must build a term that is not a registered atom.

**A/B on the 27-file loss list, both runs serial, same host, same budget:**

| | before | after |
|---|---:|---:|
| arena clones | 14,424 | **583** (−96%) |
| term nodes copied | 352,311,472 | 13,343,121 (−96%) |
| feasibility checks completed | 14,666 | **18,350** (+25%) |
| files decided | 1 of 27 | **1 of 27** |

Per file, the cleanest cases are the four `bofill/SMT_real_LIA` files, where the
counters are byte-identical before and after (1,268 feasibility checks, 4,685
offline calls, 1,023 decisions) and only the time moved:

| file | `theory_assert_ms` before | after |
|---|---:|---:|
| `ex5640_2400_100` | 8,915 | **5,665** |
| `ex6960_2400_100` | 8,296 | 4,996 |
| `ex8280_2400_100` | 7,737 | 4,801 |
| `ex9600_2400_100` | 8,057 | 4,655 |

Identical work, 36–42% less time. On `RF-13` the same budget now fits 5,508
feasibility checks where it fit 2,242 (2.46x). On the `ex*_2600_100` family,
+5–7%.

**No file changed verdict.** The parity number does not move from this change,
and saying otherwise would be the story rather than the measurement.

## What this leaves for whoever takes it next

The measurement relocates the target. Across both divisions the one common,
dominant cost is now unambiguous and it is **not** in the online theory:

> the offline conjunctive decider is entered **363,062 times** across 79 lost
> files, and every entry re-collects the whole constraint system with a fresh
> `IntCollector` walk, re-runs the gcd tightening over all of it, rebuilds the
> Gomory standard form from scratch, and re-solves — for a system that differs
> from the previous call by one literal.

The supporting figures, from the `measured` files only:

| | `QF_LIA` (16 files) | `QF_UFLIA` (52 files) |
|---|---:|---:|
| offline calls | 67,033 | 296,029 |
| constraints collected | 25,051,097 | 28,618,397 |
| constraints per call | 374 | 97 |
| Gomory calls / decided | 50,788 / 50,769 | 249,857 / 249,854 |
| Gomory cuts emitted | 398 | 2,663 |
| Gomory pivots | 11,676 | 2,840,232 |
| simplex solves / pivots | 29,444 / 2,022,671 | 265,948 / 9,512,714 |

Two things in that table are worth reading twice. **The cut engine decides
99.99% of the calls it is given** (50,769/50,788 and 249,854/249,857) while
emitting almost no cuts — it is functioning as the primary LP oracle, not as a
cut generator, and branch-and-bound is the rare path. And the whole of it is
cold every time.

That is the same "work proportional to the state, not the delta" shape this
lane removed one instance of, at roughly five times the size. It is also
consistent with what the references do — cvc5 and Yices both keep a warm
tableau across theory calls rather than a cold conjunctive oracle — and it is a
larger piece of work than one slice.

Two smaller things this lane did not spend:

- the warm rational filter refutes nothing on this population (`filter_refuted =
  0`, `filter_integral` 2.2%). Either it needs to be cheaper or it needs to be
  skipped when it has not paid recently; it currently runs before every check.
- 10 of 27 `QF_LIA` losses are invisible to every thread-local diagnostic
  because the watchdog outlives the worker. Nothing can profile them until that
  changes.
