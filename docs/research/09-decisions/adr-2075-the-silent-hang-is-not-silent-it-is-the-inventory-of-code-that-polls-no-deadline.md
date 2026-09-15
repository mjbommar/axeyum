# ADR-2075: the silent hang is not silent — the census grepped a prefix the watchdog deliberately does not use, and what is left is the inventory of code that polls no deadline

Status: accepted
Index-summary: [ADR-2040] §8 and [ADR-2050] §4(C) both named "undecided rows with NO ROUTE LINE AT ALL" as the second-largest unexplained bucket and both left it alone. **There was never an absence.** `skeleton-reach`'s `fd-census.sh` greps `^; route `; the watchdog path prints `; partial route `. The `; partial ` prefix is DELIBERATE — `smtcomp_cli.rs`'s `partial_line` adds it so a consumer grepping for COMPLETE lines cannot sweep a mid-search reading into a total — and the census implemented only that half of the contract, so a deliberate relabel was recorded as nothing and carried into two ADRs. Each of these rows prints **fourteen** lines, including a full route trail with `bound_by=`, an open-segment line saying where the budget went, and a live phase breadcrumb. **R1 first: 4 of the 13 inherited rows are not in the bucket at all** on current `main` (P5 predicted at most 2 — **wrong**); the population is **9**, all `UFNIA`. Read with the line the census skipped, the 9 split **four ways by mechanism**: 3 `in=none`, 2 `euf:fc-pair-scan`, 2 `euf:offline`, 2 `euf:round-incremental-arith` — and `enters=` splits one label into two regimes nothing else could tell apart, `dpll-lia:abstract` entered **163,583** times on one row and **5** on another. **R6 is answered by measurement, not argument**: every profiled row is `R` at every one-second sample with `utime` climbing ~101 ticks/s (100 % of one core) and RSS **flat** — 395,524 KB unchanged across 48 s — with a whole-population peak of **527 MB**, so "thrashing" is refuted for all 9 (P3 predicted >4 GB — **wrong**) and "blocked" with it. Raising the budget 24 s → 120 s decides **0 of 9**. Five `perf` profiles name five different answers, one of them reproduced across two independently built binaries at 95.98 %/95.98 %. **The unifying finding is not any one of them**: the solver's own soft deadline normally wins the race against the watchdog, and **53 of 53 decided control rows returned gracefully while 9 of 9 bucket rows did not** — so this bucket is precisely the inventory of code paths that poll no deadline, which is also exactly why no route line exists (a graceful decline records a route; a kill does not). Four bounded sites are named with profiles. **One lever is built and ships `Off`**: `collect_eq_atoms` lacks the visited check its two siblings in the same file have, so it walks a DAG as a tree — 22.6 % of samples plus 44 % allocator on the row whose `euf:offline` phase had been inside that single call for **49,442 ms**. Its two tests were **both vacuous on the first mutation run** because the fixture put the shared atom where one path reached it; fixed, the mutation kills **exactly one**. The A/B moved **0 rows** and the lever is therefore NOT recommended `On` on this evidence.
Index-status: accepted
Date: 2026-09-15

## Context

Two merged ADRs name the same thing and both explicitly declined it:

> **[ADR-2040] §8**: **The 12 undecided `UFNIA` rows with `bound_by=NONE`** — no
> route line at all, because the watchdog fired before the worker thread
> returned — are **unsplit**. That is the second-largest unexplained bucket in
> §1 and nothing here touches it.

> **[ADR-2050] §4(C) SILENT HANG — two rows**: the watchdog fires with **no
> route line at all**, at 24 s and at 120 s, **even on the minimal core**.

A row with no route line is a row where our own instrumentation produced
nothing. Every other census in this repository works by reading what a route
reported, so the usual method does not apply — which is why the bucket was
skipped four times.

Branch base: `git merge-base main HEAD` is
`33c23a2fb0461fe71bf8f130289e597290e36d02`, which **is** local `main`'s HEAD.
Rules and predictions were
[pre-registered](../../../bench-results/silent-hang-20260915/PREREGISTRATION.md)
before the lane's binary finished compiling.

## 1. There was never an absence

The population is derived from the committed census by script, never typed
(`derive-population.sh`, which carries its own positive control: the same `awk`
over the same columns asking for the complement must be non-empty, and prints
142). It is **13** rows — 12 `UFNIA` and 1 `UFLIA`.

Here is what one of them actually prints, verbatim, on the stdout the earlier
census read (`UFNIA/sledgehammer/Hoare/z3.850818.smt2`, `--trace`, 24 s):

    ; give-up kind=Watchdog detail=watchdog fired before the worker thread returned
    ; partial at=watchdog-kill recovered=12 sampled=config:in-flight,front-door:complete,…
    ; partial front-door parse_ms=18
    ; partial theory-layer … theory_propagations=3454 …
    ; partial lia offline=measured offline_calls=162 offline_constraints=1676 …
    ; partial route decided_by=none bound_by=q:mbqi-quick last=q:mbqi-quick bound_ms=1561 total_ms=1676 attempts=8
    ; partial route-trail {"schema_version":1,"attempts":[{"route":"fd:parse",…8 attempts…}]}
    ; partial route-open ms=23323 after=q:mbqi-quick attributed_ms=1676 note: bound_by is NOT the answer: most of the budget is in the open segment
    ; partial phase stack=none depth=0 in=none in_ms=na deepest=euf:lazy-arith-overbound>euf:uf-arith-lazy>euf:fc-loop>euf:fc-round-solve>euf:round-incremental-arith>dpll-lia:new>dpll-lia:assert-all>dpll-lia:abstract enters=…

**Fourteen lines.** It has a `bound_by`. It has an eight-attempt route trail. It
has a line that says 23,323 ms of the 24,000 ms budget is in the open segment,
and another naming the deepest phase chain the run ever reached.

`fd-census.sh` does:

    rl=$(printf '%s\n' "$raw" | grep -m1 '^; route ' || true)

and every line above begins `; partial route ` or `; partial phase `. The
`; partial ` prefix is not an accident — `smtcomp_cli.rs`'s `partial_line` says
why it exists:

> The leading token changes rather than a field being appended, and that is the
> whole point: a consumer that greps `^; theory-layer ` keeps matching only
> COMPLETE lines, so a mid-search count can never be swept into an aggregate
> that thinks it has totals. A consumer that wants the partial data asks for
> `^; partial ` and takes on the obligation that comes with it.

That contract is right, and **only the first half of it was ever implemented**.
The census never asked for `^; partial `, so a deliberate relabel was recorded
as an absence, and the absence became "the second-largest unexplained bucket" in
two merged ADRs.

The general shape is worth more than the instance: **a producer that renames a
line to protect aggregates has changed a wire format, and every consumer that
greps for the old name now reports a silent zero.** The rename was documented in
the producer. Nothing checked that a consumer had been updated.

## 2. R1: four of thirteen are not in the bucket at all

Re-derived on this branch at 24 s, with `phase-census.sh`:

| row | now |
|---|---|
| `UFLIA/…/javafe.ast.StandardPrettyPrint.008` | `bound_by=q:mbqi-quick`, a real `; route ` line |
| `UFNIA/2019-Preiner/full/t3_rw432` | `bound_by=q:egraph` |
| `UFNIA/2019-Preiner/full/t3_rw737` | `bound_by=q:egraph` |
| `UFNIA/vcc-havoc/vccp-union1.c.6.reint2` | `bound_by=q:mbqi`, finished in **19.7 s** of 24 s |

Pre-registered **P5** said at most 2 would re-derive out. **P5 is wrong.** The
bucket is **9**, and the one `UFLIA` row is gone, so it is 9 of the 12 `UFNIA`
rows [ADR-2040] counted — Wilson 95 % on 9/12 is `[46.7 %, 90.7 %]`, which at
n = 12 is as wide as it should be and is quoted rather than hidden.

**Every one of the 13 exits 0** (R7). Not one is a process that died; all are
runs that printed a verdict.

## 3. The nine are four mechanisms, and one label is two regimes

`split.py` reads the phase line and splits by the innermost open frame — the
code that was *running* when the watchdog read the breadcrumb, not the last
thing that finished:

|  n | `in=` |
|---:|---|
| 3 | `none` — outside every instrumented phase |
| 2 | `euf:fc-pair-scan` |
| 2 | `euf:offline` |
| 2 | `euf:round-incremental-arith` |

Seven of the nine share one `deepest=` chain and two differ by one frame, so
**`deepest` alone would have said "one cause"**. The `enters=` counter is what
refuses that reading:

| `dpll-lia:abstract` entries | row |
|---:|---|
| 163,583 | `havoc-bench_sum.1.bar` |
| 50,400 | `havoc-bench_036.1.AddElement` |
| 24,911 | `int_check_bvslt_bvurem1_ltr_no_inv` |
| 17,628 | `int_check_bvsgt_bvadd_ltr_inv_r` |
| 150 | `z3.850818` |
| 8 | `mqueue_example_2_2_2_4` |
| 5 | `test14-DafnyAst.ssc.30` |

Same label, same chain, five entries against 163,583. A name scan reports one
bucket; the counter reports two regimes and it is already shipped.

## 4. R6: what the watchdog cannot say, taken rather than argued

The watchdog reports one bit — a deadline passed. The pre-registration named,
in advance, the observation separating *progress*, *stuck* and *thrash*, and
those observations were taken.

**Not blocked.** `/proc/<pid>/task/<worker>/stat` sampled every second: state
`R` at every sample, `utime` climbing ~101 ticks per second. 100 % of one core,
continuously, for the whole budget.

**Not thrashing.** RSS on `havoc-bench_sum` is **395,524 KB at t=6 s and
395,524 KB at t=54 s** — not drifting, identical. Peak RSS across the whole
9-row population is **527 MB**. Pre-registered **P3** predicted at least one row
above 4 GB. **P3 is wrong**, and it is wrong by a factor of eight in the safe
direction: there is no memory story in this bucket at all.

**Not a budget.** `budget-sweep.sh` at 120 s, one pinned core per row:
**0 of 9 decided** (`ref/budget-120s.tsv`). Three rows that were `partial` at
24 s reach a route boundary at 120 s and are still `unknown`. **P6 holds.**

So: spinning, on a fixed working set, and five times the budget does not help.

## 5. Five profiles, five answers, and the caller chain we could not get the easy way

**`gdb` cannot be used on this host**, and that is recorded rather than worked
around: `/proc/sys/kernel/yama/ptrace_scope` is `1`, which permits a ptrace
attach only from an ANCESTOR, and a sampler's gdb is a SIBLING of the solver.
All four attempts returned "Could not attach to process"
(`prof/havoc-sum/bt.txt` keeps the receipts) — because an empty `bt.txt` read as
"no stack available" is exactly the absence-as-finding this lane is about. A
second binary with frame pointers (`build-fp.sh`) and `perf --call-graph=fp`
needs no ptrace. **It is an attribution binary only and no time or verdict in
this ADR comes from it.**

| row | phase | profile |
|---|---|---|
| `havoc-bench_sum.1.bar` | `euf:round-incremental-arith` | **95.98 %** in `dpll_lia::simple_int_literal_bounds` + `simple_int_bounds_for_order` + `IncrementalArithDpll::refresh_initial_lemmas` |
| `mqueue_example_2_2_2_4` | `euf:offline` | 22.57 % `euf_egraph::collect_eq_atoms`, **44 %** allocator, 12 % SipHash |
| `test14-DafnyAst.ssc.30` | `none` | **54.29 %** `axeyum_rewrite::quantifiers::instantiate_with_triggers`, 26 % `RandomState`/`DefaultHasher` |
| `int_check_bvsgt_bvadd_ltr_inv_r` | `euf:fc-pair-scan` | 18.67 % `axeyum_ir::eval::eval_with_memo`, ~20 % allocator |
| `z3.850818` | `none` | 16.71 % `sat_bv_backend::handle_sat_result`, 8.53 % `egraph::check_congruence` |

`havoc-bench_sum` was profiled on two independently built binaries — the default
one at 56.56/27.36/13.48 and the frame-pointer one at 53.18/25.31/17.49. Same
three functions, same order. One profile is a sample; two agreeing across
binaries is a measurement.

**`test14-DafnyAst.ssc.30` settles P2 and it is a finding about the instrument.**
Its 54 % is in `axeyum-rewrite`, and there is no `phase_breadcrumb::enter`
anywhere in that crate: all **41** frames are in `axeyum-solver` theory routes,
none in ingest, none in rewriting, none in the quantifier ladder. So
`stack=none depth=0` never meant "nothing was running"; it meant "the running
code is in the one place the instrument does not reach", which is what
`phase_breadcrumb.rs:113-116` says such a reading means.

**Two instrument failures were caught rather than read as findings.** Two of the
first five `perf record`s wrote ZERO samples against `perf_event_mlock_kb`
("Permission error mapping pages", five recorders at once) and produced an
empty `profile.txt`; that was checked against `perf.log` instead of believed.
And the guard added to catch exactly that read `nr_samples` from
`perf report --header-only`, a field this perf does not emit, so it printed
"samples: 0" over a profile whose top frame was 54 %. A guard that cries wolf
is the same defect class as one that cannot fail; both are in the record.

## 6. The unifying finding: this is the inventory of code that polls no deadline

The most useful result here was produced by a *failed* control, twice.

To show the A/B's control was non-vacuous, each decided control row was re-run
at a budget below its own measured solve time, so the watchdog would fire and
the breadcrumb would print. It never fired — at a flat 1,200 ms, and again at
40 % of each row's own time. `phase_line_present` was `no` on **53 of 53**.

That is not a fact about the probe. `smtcomp_cli` gives the solver a **soft
deadline** equal to the budget and the watchdog a **hard** one at budget + 1 s
grace, and the design expects the soft one to win. On the control it always
does: 53 of 53 decided `UFNIA` rows return a graceful verdict before the
watchdog. On this bucket it never does: **9 of 9 are watchdog kills.**

So the bucket has a single crisp characterisation, and it is not a theory or a
route:

> **These are the rows whose running code checks no deadline.** Everything else
> in the corpus notices its own budget and declines in good order — recording a
> route as it goes, which is why it has a `; route ` line. These do not, so the
> process-level watchdog is the only thing that stops them, and a kill records
> no route because a route is recorded on the way OUT.

The missing route line and the hang are **the same fact**, not two. And it makes
the watchdog the right instrument for the wrong reason: it is a backstop, and
the population it backstops is an inventory of un-instrumented loops rather than
of hard problems.

The four sites below are each an instance, and none of them polls a deadline:
`collect_eq_atoms` is a bare recursive walk; `refresh_initial_lemmas` is called
per assertion with no budget test; `args_tuples_equal` is an O(n²) scan; and
`instantiate_with_triggers` is in a crate with no breadcrumb at all.

## 7. Four bounded sites, each with its profile

### (A) `collect_eq_atoms` walks a DAG as a tree — BUILT, ships `Off` (§8)

`euf_egraph.rs` has three sibling collectors. `collect_euf_atoms` and
`collect_bool_symbols` both open with `if !seen.insert(term) { return; }`.
`collect_eq_atoms` does not: its `seen.insert(term)` sits *inside* the `Op::Eq`
test, where it dedups the OUTPUT list. The recursion has no visited check, so
every non-`Eq` node is re-walked once per path that reaches it, and
`let args = args.clone()` allocates a `Vec` on each of those visits. The call is
the **first statement** of the `euf:offline` phase, which `mqueue`'s breadcrumb
says it had been inside for **49,442 ms** of a 60 s budget.

### (B) a cap that bounds its output but not its scan — NOT BUILT

`refresh_initial_lemmas` is called from `add_assertion` **once per assertion**,
and rebuilds `initial_int_bound_mutex_lemmas` from scratch: an O(atoms) rescan
via `simple_int_literal_bounds`, then an O(bounds²) pair loop.
`MAX_INITIAL_BOUND_MUTEX_LEMMAS = 8_192` is checked **inside** that loop and
caps the CONFLICTS FOUND, so a query with few conflicting pairs pays the whole
quadratic scan every time. Its sibling sixty lines below,
`initial_int_bound_implication_lemmas`, caps its **input** —
`MAX_INITIAL_BOUND_IMPLICATION_ATOMS = 512`, tested at function entry, with a
`note_crossed` record when it declines. One of the two passes knows the
difference between bounding what you produce and bounding what you read. This is
**95.98 %** of `havoc-bench_sum`, which z3 refutes in **107 ms**.

### (C) the twin with the fast path and the twin without — NOT BUILT

`euf.rs::args_tuples_equal_under_fixed_assignment` (`:1922`) opens its loop with
`if a == b { continue; }`. `args_tuples_equal` (`:1951`), thirty lines below and
otherwise the same function, does not — and `TermId` is a hash-consed handle, so
that test is one integer compare that would skip two full evaluations. It is
called for every argument of every pair in the O(n²) `euf:fc-pair-scan`, and
`axeyum_ir::eval` allocates a **fresh memo `HashMap` per call** (`eval.rs:331`).
That is the 18.67 % `eval_with_memo` plus ~20 % allocator on the two
`2019-Zohar-ic` rows.

### (D) SipHash in a hot term walk — NOT BUILT, and NOT a determinism bug

`axeyum-rewrite/src/quantifiers.rs` uses `std::collections::HashMap` with the
default `RandomState` at 20+ sites, where the rest of this codebase uses
`FxBuildHasher`. On `test14-DafnyAst.ssc.30` that is **26 %** of samples
(`RandomState::hash_one` 19.50 %, `DefaultHasher::write` 6.95 %) next to 54 % in
`instantiate_with_triggers` itself.

**It was checked for the worse defect and does not have it.** `RandomState` is
seeded per process, so an iterated map there would break the determinism promise
in `CLAUDE.md`. The file contains no `.keys()`, `.values()`, `.drain()` or
`.into_iter()` on any of those maps, and the one `for … in &matches` iterates a
`Vec`. **This is a speed finding only** and is stated that way rather than
upgraded.

## 8. The lever, the vacuous tests, and the A/B that did not pay

`AXEYUM_EQ_ATOM_DAG_WALK=1`, **off by default**, selects `collect_eq_atoms_dag`.
Both walks stay compiled in deliberately, which is what lets the A/B run **one
binary under two environment values** rather than comparing two builds.

The output is believed identical — an atom is pushed at its first reach either
way, and pruning repeat visits cannot change which node is reached FIRST — and
that belief is tested rather than argued.

**Both tests were vacuous on the first mutation run.** Deleting the visited
check, the exact mutation they exist to catch, left `2 passed; 0 failed`. The
assertions were fine; the **fixture** put the `Eq` atom at the ROOT of the
shared stack, where exactly one path reaches it, so a walk with no visited check
pushes it exactly once and the equivalence held. With the atom moved to the
BOTTOM, under the whole doubling stack and reachable by `2^depth` paths, the
same mutation gives `test result: FAILED. 1 passed; 1 failed` — `left` holding
2^20 copies of one `TermId` against `right`'s single entry. **Exactly one** test
dies; the survivor is the fixture-validity control, which deliberately does not
call the code under test, because two tests that die to one mutation are one
test with a spare.

**The A/B (§9) moved nothing, and the lever is therefore NOT recommended `On`
on this evidence.** Removing 22.6 % of samples plus its allocator traffic from a
run that needs a >100x speedup to fit its budget was never going to convert a
row by itself, and saying so after measuring is the point of measuring.

## 9. What the A/B measured

Polarity, stated in the runner's own header: BASE is the lever unset (the
shipped tree walk); ARM is `AXEYUM_EQ_ATOM_DAG_WALK=1`. One binary, two `env`
values, arms back to back on one pinned core, order alternating per row.

| | treatment (the 9, **3 passes each**) | control (53 decided `UFNIA`, 1 pass) |
|---|---:|---:|
| runs | 27 over 9 files | 53 over 53 files |
| gains | **0** | 0 |
| losses | **0** | **0** |
| FLIPS (`sat`↔`unsat`) | **0** | **0** |
| exit-status moves (R7) | **0** | **0** |
| UNSTABLE across passes | **0** | n/a |

**Zero gains.** The lever does not convert a single row, and three passes per
arm agree on every one of them.

The treatment's arm/base wall ratio is median **1.000**, min 0.968, max 1.029 —
which is not evidence of anything except that all nine rows burn the entire
budget under both arms, exactly as §4 said.

**The control's non-vacuity is NOT ESTABLISHED, and that is reported rather than
assumed.** The intended probe could not run for the reason in §6 — on a decided
row the soft deadline wins, so the breadcrumb never prints and the phase reading
that would show `euf:offline` executing is unavailable. The fallback read, per-row
wall time, cannot substitute: the control's ratio is median 0.994 with **min
0.514 and max 1.469**, so a run 49 % *slower* under the arm is inside the same
band as one 49 % faster, and the two runs that came in >20 % faster are not
distinguishable from that noise. A single-pass control cannot separate them, and
this lane did not re-run it three times because nothing moved.

So the control supports "**no verdict moved**" and **does not** support "the
changed code ran there". Establishing the second needs a counter on the walk
itself, which is new production surface this lane did not add.

## 10. Verdicts against independent authorities

`authority.sh`, on the 9. `z3 -T:24` is SECONDS, `cvc5 --tlimit=24000` is
MILLISECONDS; the two flags are deliberately not written to look alike.

| | n |
|---|---:|
| rows | 9 |
| z3 decided | 7 |
| cvc5 decided | 6 |
| **BOTH decided — the comparable denominator** | **5** |
| NEITHER decided (no-opinion) | 1 |

Every decision is `unsat`. Four of them are not close:

| row | z3 | cvc5 | us |
|---|---:|---:|---|
| `havoc-bench_sum.1.bar` | **107 ms** | 307 ms | 24 s, `unknown` |
| `test14-DafnyAst.ssc.30` | **107 ms** | 1,209 ms | 24 s, `unknown` |
| `havoc-bench_036.1.AddElement` | **307 ms** | 9,116 ms | 24 s, `unknown` |
| `test14-DafnyAst.ssc.91` | **408 ms** | no-opinion | 24 s, `unknown` |

**This bucket is not hard.** That is what makes it worth the next lane's time,
and it is the strongest argument in this ADR: a row z3 refutes in 107 ms, on
which we spend 96 % of a 24 s budget inside one quadratic pass, is a performance
defect wearing a capability label.

## 11. The rules, against what happened

| rule | pre-registered | outcome |
|---|---|---|
| R1 | the inherited population is re-derived before it is counted | §2 — **4 of 13 re-derived OUT**. It DID overstate |
| R2 | no "the instrument reports nothing" without a positive control | §1 — the control fired (`in=euf:offline in_ms=6953`) on the breadcrumb module's own documented example, a row the old census would also have filed `bound_by=NONE` |
| R3 | every bucket with its denominator; NOT-MEASURED separate | §3, §9, §10 |
| R4 | causes by MECHANISM; split a label that covers >1 site | §1 (`bound_by=NONE` was three program points), §3 (`enters=` splits one label into two regimes) |
| R5 | profiling, not reading, with sample counts | §5 — 18,188 / 16,647 / 17,204 / 18 K samples; two of five had to be re-run because they recorded ZERO |
| R6 | name the distinguishing observation IN ADVANCE, then take it | §4 — and the answer came out "neither (b) nor (c)", then §6 found the characterisation that does fit |
| R7 | exit status as its own channel | §2 — all 13 exit 0; no row is a dead process |
| R8 | Wilson 95 % on every proportion | §2 — 9/12 is `[46.7 %, 90.7 %]` |
| R9 | authorities with a comparable denominator beside any zero | §10 — 5 of 9 comparable, 1 no-opinion, both printed |
| R10 | no lever unless the profile names ONE bounded site | §7(A) — met; built; **and the A/B says do not ship it `On`** |
| R11 | the measurement is of THIS BRANCH; post-merge predicted | §12 |
| R12 | freshness by `find -newer`, not exit status | `build.sh` / `build-fp.sh`; binaries `453c1aae…`, `04fda832…`, `827b6404…` |
| R13 | no waiter greps for a process by a pattern its own command line contains | every waiter here watches an artifact |
| R14 | unfinished checks reported as "did not run" | §13 |
| R15 | peak RSS per row; a ceiling on anything that expands | §4 — 527 MB population peak; `MEM_LIMIT_GB=16 scripts/mem-run.sh` on the analysis scripts |
| R16 | fixture suites if a route changes; interleaved one-binary A/B, 3 passes, noise floor | §9 — all **19** `dispatch/reason` suites green with nonzero counts, the list parsed out of `hooks/pre-push` so it cannot drift; 3 passes per arm; the noise band is published and is what refuses the timing read |

**The predictions:**

| | predicted | measured |
|---|---|---|
| **P1** | not one cause | **right** — four mechanisms, and `enters=` splits one of the labels again |
| **P2** | ≥1 row shows `stack=none`, and it is a finding about the INSTRUMENT | **right** — 3 rows, and the profile names `axeyum-rewrite`, a crate with zero breadcrumb frames |
| **P3** | ≥1 row's peak RSS above 4 GB | **WRONG** — population peak 527 MB. No memory story at all |
| **P4** | the dominant frame is not in the CDCL SAT core | **right** — none of the five |
| **P5** | at most 2 re-derive out | **WRONG** — 4 did |
| **P6** | ≤3 decide at a raised budget | **right, and stronger** — 0 of 9 at 120 s |

Two wrong out of six, and both wrong in the same direction: **the bucket was
smaller and tamer than the pre-registration expected.** P3 and P5 were both
written expecting a dramatic cause, and a pre-registered prediction that
something will be dramatic is a standing invitation to find drama.

## 12. Decision

1. **The bucket is closed as an unexplained population.** It is 9 rows, four
   mechanisms, all spinning on CPU at a fixed working set, none helped by a
   bigger budget, with four named sites carrying profiles.
2. **`fd-census.sh` and any consumer of `smtcomp_cli --trace` must read
   `^; partial ` as well as `^; route `.** Not doing so is what created this
   bucket. This ADR does not edit `skeleton-reach`'s committed artifacts; a
   consumer written after it has no excuse.
3. **The lever ships `Off` and is NOT recommended `On`** — §8. It is committed
   with its tests because the site is real and the next lane should not have to
   re-find it, not because the A/B paid.
4. **The next lane's target is §7(B)**, not (A): `refresh_initial_lemmas` is
   95.98 % of a row z3 refutes in 107 ms, its sibling pass already demonstrates
   the input-cap-plus-crossing-record pattern to copy, and unlike (A) it has a
   plausible path to a converted verdict.
5. **The structural recommendation is §6**: give these walks a deadline poll, or
   at minimum a breadcrumb frame. A route that notices its own budget declines
   in good order and records itself; that is the difference between the 53 and
   the 9, and it is a property of the code rather than of the problem.

**Predicted post-merge value: no division total moves.** The lever ships `Off`;
the only `crates/` change is behind it plus two tests. R16's fixture suites are
run because a route's behaviour is selectable here even though the default path
is byte-identical.

Gates, with their counts, all on this branch:

| gate | result |
|---|---|
| `check-clippy-complete.sh` (under `cargo-serialized --batch`) | **890 of 890** workspace targets across **27 of 27** crates, **0 diagnostics** |
| `RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps` | finished; 41 crates generated |
| `cargo fmt --all --check` | exit 0 |
| `cargo check --workspace --all-targets` | finished |
| `cargo check -p axeyum-solver --all-targets` (**default features**) | finished; no diagnostic from `euf_egraph.rs` |
| `-p axeyum-solver --lib --features full -- --test-threads=4` | `test result: ok. 1785 passed; 0 failed` — the 1,783 baseline plus this lane's two |
| `corpus_regression` | `test result: ok. 2 passed; 0 failed` |
| `run-dispatch-reason-suites.sh` (R16) | **19 suites**, all green, every count nonzero |
| `progress_frontier --features full -- --test-threads=1` | `test result: ok. 12 passed; 0 failed` |

`progress_frontier` rewrites its own machine record; the five
`bench-results/frontier/*.json` it touched were **reverted, not committed**, so
no baseline is narrowed by this lane's host.

## 13. Not measured here, reported as "did not run"

- **The control's non-vacuity is not established** (§9). It needs a counter on
  the walk, which is new production surface.
- **§7(B), (C) and (D) are named and profiled, not built and not A/B'd.**
- **Nothing outside these 13 files was measured.** The corpus rate of any of
  these four mechanisms is unknown, and R1 forbids transferring it — the
  population is 9 rows drawn from one division's 147 undecided.
- **`euf_egraph.rs:878` (`prove_unsat_lazy`), `:2731` (`run_online_diag`) and
  `string_theory.rs:916` also call `collect_eq_atoms`** and were not profiled;
  only the `euf:offline` site at `:1472` was.
- **The `stack=none` rows were not traced past their top frame.** `perf`'s
  frame-pointer chain names the caller; the *reason* `instantiate_with_triggers`
  runs for 24 s on a file z3 refutes in 107 ms is not answered here.

[ADR-1957]: adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-2020]: adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
[ADR-2040]: adr-2040-the-reach-half-is-worth-two-and-the-whole-remaining-shape-is-the-ground-checker.md
[ADR-2050]: adr-2050-the-eleven-are-four-causes-and-the-largest-is-one-refused-atom.md
[ADR-2065]: adr-2065-the-real-collector-can-hold-a-term-and-the-sat-exits-close-by-type.md
