# Is there a route that would have decided this file, which we never reached?

Lane `parallel-portfolio`, 2026-09-08. Measurement note; the decision it
supports is at the end.

## The question, and the one it is not

The [route-attribution sweep](route-attribution-2026-09-07.md) concluded that a
parallel portfolio is not the largest available win, on two numbers:

- on the 754 files we decide, running the same routes concurrently recovers
  24.9% of in-dispatch time — a **1.33x** wall-clock speedup;
- on the 350 files we lose, the binding route already holds a **median 84%** of
  the trail, so there is no queue in front of it to remove.

Both numbers are sound and neither is disputed here. They answer *"if we ran the
same routes concurrently, how much waiting disappears?"*, and one dominant route
does mean little there.

They do not answer the question that decides whether to build a portfolio:
**is there a route that would have decided this file quickly, which we never
reached because a slower one ran first?** Those are different questions, and one
route holding most of the clock is consistent with a large answer to the second
one. The same repository already carries a direct counterexample: on four
`QF_ABV` files `abv-online-cdclt` spent 24.009 s of a 24 s budget, declined, and
`array-fast-path` then decided them in 0.191 s
([QF_ABV attribution](qf-abv-route-attribution-2026-09-08.md)).

The earlier sweep was explicit about why it could not answer the second
question, and it was right: *"A strict virtual best runs each route alone on
each file. `SolverConfig` has no route-selection knob, so that is not measurable
and is not claimed."* What a sequential trail gives per file is three-valued —
every route before the winner is a measured NO, the winner is a measured YES,
and **every route after it is UNKNOWN**. The prize lives entirely in that third
class, and no amount of re-reading the same trails recovers it.

## What can be measured without a route knob

The ladder is sequential, and every route's `config.timeout` is clamped to what
remains of one wall deadline (`auto.rs`'s `config_with_remaining_deadline`). So
**raising the wall budget has exactly the effect of letting the routes after the
binder take their turn.** That is the experiment:

- **control** — the file at the competition budget (24 s). A file that decides
  here is stale population, not a prize; it is reported and excluded.
- **probe** — the same file at 120 s with `--trace`. The `; route-trail` line
  (`RouteTrace::to_json_with_timing`) carries each attempt's own `elapsed_ns`,
  so the deciding route's own cost is read rather than the ladder's total.

A file is scored a **prize** when the probe decides it and

    shared_preamble + deciding_route_own_time  <=  24 s

because a portfolio arm starts at t = 0: it pays the preamble every arm pays,
its own time, and nothing for the routes queued in front of it. The preamble is
excluded from the recoverable part deliberately — counting it is the mistake
that inflated `QF_SLIA` from 63% to 84% in the first draft of the earlier
aggregate.

Harness: `scripts/portfolio-oracle.py`, `scripts/portfolio-oracle-slot.sh`,
`scripts/portfolio-oracle-aggregate.py`.

### Three things this cannot see, stated rather than absorbed

1. **Routes the ladder never admits stay invisible.** Raising the budget lets
   later routes run; it does not make an inadmissible route admissible. Every
   number below is a **lower bound** on the portfolio prize, never an upper one.
2. **The 120 s ladder is a different schedule, not the 24 s one with more room.**
   Several internal shares are *fractions* of the budget —
   `cegar_probe_budget` takes 3/4 of what remains, `dl_probe_budget`
   `min(timeout/4, 6 s)`. `--confirm` therefore checks reproducibility of the
   probe, not the budget.
3. **The harness's 1 s `WATCHDOG_GRACE` lets the control arm report a verdict a
   real external limit would kill.** `control_ms` is recorded so that case stays
   visible; §"Wins we keep only by overrunning" below is what it found.

### A control that could not pass, caught before the sweep finished

`--confirm`'s first version re-ran each scored prize **at the competition
budget** and required the same route to decide. A prize is by construction a
file the ladder does not decide at that budget, so the run returns `unknown`
every time: the control marks every prize unconfirmed regardless of the truth,
and the column reads like diligence while measuring nothing. That is the
*inverted* half of "a negative control fails two ways"; the vacuous half would
be a control that cannot fail, and the symptom is identical — a column whose
value does not depend on its subject. The three-host sweep was stopped and
restarted on the fix.

Confirming the stronger claim — that the winning route's own cost stays under
the budget when it runs **first** — needs the route-selection knob
`SolverConfig` does not have. That gap is the finding, not a caveat.

## What the existing 1,200-file trails already say

Free, from `bench-results/route-attribution-2026-09-07/logs.tgz`, before any new
run. Of the 1,200 files, **308 are lost with a trail**.

### The ladder does not stop at the binder — it starves what follows

On 258 of the 308 lost files, at least one attempt *after* the most expensive
one declined with reason `budget` having spent under 50 ms. It was not refused;
it was handed a spent clock. On 216 of those the starved attempts are only the
nine `fd:*` front-door pass-through stages, which are not portfolio arms. On the
remaining **42 files a real solver route was starved**:

| division | lost (with trail) | a real route starved |
|---|---:|---:|
| QF_UFLIA | 64 | 16 |
| QF_IDL | 35 | 10 |
| QF_LRA | 67 | 8 |
| QF_NIA | 77 | 4 |
| QF_UF | 4 | 4 |
| QF_ABV, QF_BV, QF_LIA, QF_NRA, QF_RDL | 138 | 0 |
| **total** | **308** | **42 (13.6%)** |

The starved routes are `lia-dpll` (26), `uf-arith-lazy-overbound` (16), `nra`
(8), `int-blast-ladder` (4), `qf-bv` (4). This is the population a portfolio
would race — and, equally, the population a sequential *reserve* would feed.

### How many arms a portfolio would need

Distinct real (non-`fd:`, non-probe) route attempts per file, same 1,200 files:

```
0 routes:  55    3 routes: 197    6 routes:  11    9 routes:  28
1 route : 175    4 routes: 145    7 routes: 116
2 routes: 269    5 routes:  74    8 routes:  34
```

Median 2–3, maximum 9. Per division the median runs from 0 (`QF_SLIA`, decided
at the front door) and 1 (`QF_IDL`, `QF_RDL`) up to 7 (`QF_UFLIA`) and 8
(`QF_NIA`). `QF_BV` never sees more than two, and one of them is `dl-online`
declining instantly — **a portfolio is arithmetically incapable of helping that
division.**

### Wins we keep only by overrunning the budget

Nine files were decided while their attributed trail already exceeded 24,000 ms.
All nine are `QF_ABV`, all nine were decided by `array-fast-path`, and every one
of their winning arms costs **15 ms to 719 ms**:

| file | winner | arm | ladder total |
|---|---|---:|---:|
| `dwp …vdir.strmode…` | `array-fast-path` | 15.0 ms | 24,038 ms |
| `dwp …chroot.get_quoting_style…` | `array-fast-path` | 626.7 ms | 24,639 ms |
| `dwp …id.close_stdout_set_file_name…` | `array-fast-path` | 718.7 ms | 24,730 ms |
| `dwp …printf.get_quoting_style…` | `array-fast-path` | 637.6 ms | 24,653 ms |
| `dwp …yes.get_quoting_style…` | `array-fast-path` | 627.0 ms | 24,633 ms |
| `dwp …dd.advance_input_offset…` | `array-fast-path` | 61.1 ms | 24,065 ms |
| `dwp …mkdir.set_char_quoting…` | `array-fast-path` | 140.1 ms | 24,147 ms |
| `dwp …seq.set_char_quoting…` | `array-fast-path` | 136.3 ms | 24,149 ms |
| `dwp …cat.next_line_num…` | `array-fast-path` | 648.5 ms | 24,655 ms |

These are `sat` today only because `WATCHDOG_GRACE` is 1 s and
`abv-online-cdclt` returns at 24.009 s. Under a real external 24 s limit they
are nine losses. Re-run on the current tree, the first of them still prints
`bound_by=abv-online-cdclt bound_ms=24009 total_ms=24029`: **the defect is
live.**

The cause is one line. Every adjacent dispatch site clamps —
`config_with_remaining_deadline` on the real branch, `int_real_relax_budget` on
the int tail, `cegar_probe_budget`'s quarter reserve on the UF ladder — and
`dispatch_abv_online` passes `config` through **unmodified**, so the array
routes below it inherit a spent clock.

### Route attempts are not competing answers about one query

94 of 796 files with a decided attempt carry **more than one**, and 79 of those
show *different verdicts* between attempts — e.g. `lia-dpll` `sat`, `lia-dpll`
`sat`, `lia-dpll` `unsat`, `fd:string-gate` `unsat`.

None of these is a soundness break. They are refinement rounds: the quantifier
loop above `check_auto` re-dispatches once per instantiation round, and each
round is a *different query* (the earlier sweep measured the same thing on a
UFLIA file — three rounds decided `sat` and were superseded by a final `unsat`).

The design consequence is sharp, and it corrects the obvious portfolio framing:
**"if two routes disagree that is a hard failure" is wrong at the granularity of
route attempts.** A portfolio whose arms are arbitrary route attempts would fire
its soundness alarm on 79 of 796 files while nothing was wrong. Arms must be
**top-level dispatches of the original query**; only then is a disagreement a
real one and a legitimate hard failure.

### What a portfolio costs in memory

Peak RSS of one whole solve on a sample of the loss population — an upper bound
on any single arm, since an arm is a subset of that work:

```
QF_ABV   804 MB / 19 MB / 173 MB     QF_LIA   12 MB / 201 MB / 62 MB
QF_BV    469 MB / 455 MB / 322 MB    QF_LRA   28 MB
QF_IDL    35 MB /  31 MB /  82 MB
```

Three or four arms of a typical file are affordable on these 16-core /
27 GB hosts. But a competition memory limit is per **solver**, not per thread,
so N arms means budget/N each — and
`QF_ABV/brummayerbiere/wchains140se.smt2` already fails a 127 MB allocation and
aborts (exit 134) with **one** arm running under 8 GiB. The files most likely to
want a second opinion are the ones a naive N-way portfolio kills outright.

## The oracle sweep

Committed population, three hosts, `taskset`-pinned slots, 24 s control /
120 s probe, 8 GiB `ulimit -v`. Data in
`bench-results/portfolio-oracle-20260908/`.

### The probe arm, per division

| division | files | ladder already wins | candidate | too-slow arm | no route at 120 s | aborted | no trail | win only by overrunning |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| QF_ABV | 19 | 7 | 0 | 2 | 7 | 1 | 2 | **4** |
| QF_BV | 6 | 0 | 0 | 2 | 2 | 0 | 2 | 0 |
| QF_IDL | 54 | 38 | 0 | 7 | 4 | 0 | 5 | 0 |
| QF_LIA | 27 | 5 | 0 | 2 | 13 | 0 | 7 | 0 |
| QF_LRA | 54 | 5 | 0 | 3 | 46 | 0 | 0 | 0 |
| QF_RDL | 47 | 37 | 1 | 5 | 2 | 0 | 2 | 0 |
| QF_SLIA | 7 | 0 | 1 | 0 | 5 | 0 | 1 | 0 |
| QF_UF | 38 | 35 | 0 | 2 | 1 | 0 | 0 | 0 |
| QF_UFLIA | 58 | 11 | 1 | 6 | 6 | 0 | **34** | 0 |
| UF | 32 | 0 | 0 | 0 | 27 | 5 | 0 | 0 |
| **total** | **342** | **138** | **3** | **29** | **113** | **6** | **53** | **4** |

**All three candidates failed confirmation** (§"neither instrument confirms a
prize"): the `QF_SLIA` one is a looped front door scored on one round of
fifty-five, the `QF_RDL` one does not reproduce under load, and the `QF_UFLIA`
one is `hash_sat_05_17`, whose real cost a budget walk puts at 33–34 s against a
21.3 s estimate.

`QF_NIA` (61) was still running at 60 of 61; its per-file progress log is
committed under `partial/` so the coverage is visible rather than implied.

**`QF_UFLIA`'s 34 no-trail rows are the largest blind spot in this table.** They
are watchdog kills where no route returned, so the probe can say only that the
file is lost — which route held the clock is unrecorded. The solo arm is what
covers them, and it had reached 35 of that division's 58 files.

### The solo arm, where it is complete

| division | files | ladder wins | ladder loses | decided alone in budget | no route decides alone |
|---|---:|---:|---:|---:|---:|
| QF_ABV | 19 | 7 | 12 | **2** | 10 |
| QF_BV | 6 | 0 | 6 | **0** | 6 |
| QF_LRA | 54 | 5 | 49 | **0** | 49 |
| QF_NIA (files 32-61) | 30 | 3 | 27 | **0** | 27 |
| QF_UF | 38 | 35 | 3 | **0** | 3 |
| UF | 32 | 0 | 32 | **0** | 32 |
| **total** | **179** | **50** | **129** | **2** | **127** |

`QF_NIA`'s second half is worth its own line: three files *are* decided alone
there, and all three are files **the ladder already wins**. They never were
prizes. (Re-run on another host two of the three do not even reproduce —
`datatype-native` / `datatype-elim` internally run a preprocessed dispatch, so
their cost moves between machines. Either reading disqualifies them; the
`STALE-DECIDED` one is the cheaper check.)

`QF_UFLIA`'s sweep was still running: over its first 35 files it found 7
ladder-losses with a solo decider — five are the 2 ms `euf-online` class above
(a normalization defect, not a scheduling one), one wants 37 s, and one is
`hash_sat_08_05.smt2`, the confirmed middle-band case.

Both `QF_ABV` wins are `qf-bv` — 611 ms (`unsat`) and 567 ms (`sat`), verdicts
matching the census. The other entry points that "decide" them
(`lra-dpll` 653 ms, `nra` 656 ms, `array-elim` 769 ms, `aufbv` 772 ms) are the
same computation through different doors, not four arms.

### The band that decides it

From the **solo** arm, over the six divisions where it is complete — 129
ladder-losing files:

```
fastest route that decides ALONE, on files the ladder loses:
  under 1 s (a reserve reaches it)                       2
  1 s to 6 s (a reserve reaches it)                      0
  6 s to 24 s (MIDDLE BAND: only a portfolio)            0
  no route decides alone at all                        127
```

**The middle band is empty across those 129 files.** That, not the count, is what
the decision turns on. `QF_UFLIA`'s incomplete sweep then supplied exactly one
member of it, which is why the answer below is "not yet" rather than "no".

### Two outstanding middle-band candidates, and they are the ones to settle

Honesty requires the other half. The **probe** arm proposes five more candidates
in the two divisions whose solo sweeps had not finished, and two of them land in
the middle band:

| division | file | winning route | probe's arm estimate | band |
|---|---|---|---:|---|
| QF_NIA | `From_T2__ex36…p26` | `nia-linearize` | 4,595 ms | reserve reaches it |
| QF_NIA | `From_T2__ex36…p28` | `nia-linearize` | 3,778 ms | reserve reaches it |
| QF_NIA | `From_T2__ex36…p29` | `nia-linearize` | 4,186 ms | reserve reaches it |
| QF_NIA | `SAT14/1509.smt2` | `nia-linearize` | 10,149 ms | **MIDDLE** |
| QF_UFLIA | `Hash/hash_sat_05_17` | `uf-arith-lazy-overbound` | 21,309 ms | **MIDDLE** |

A 21.3 s arm against a 24 s budget is exactly the case a reserve cannot serve:
there is no way to guarantee a route 89% of the clock and still protect the
routes below it. If either survived confirmation it would be a portfolio case
and nothing else would be. So both were confirmed, and both failed.

**`hash_sat_05_17` — the 21.3 s estimate was one lucky run.** At a 120 s budget
`uf-arith-lazy-overbound` decides it in 17,819 ms with a clean trail (9
attempts, exactly one `decided`, so not looped). Walking the budget:

```
budget= 24000  unknown  route given 18,003 ms  (24000 * 3/4)
budget= 24000  unknown  route given 18,004 ms
budget= 30000  unknown  route given 22,506 ms
budget= 40000  unknown  route given 30,006 ms
budget= 60000  sat      route DECIDED in 33,353 ms
budget= 90000  sat      route DECIDED in 34,107 ms
```

The route's real cost is **33–34 s**, twice the probe's estimate and well past a
24 s budget. It fails at 40 s while holding 30 s — more than the 21.3 s it was
credited with. The single 17,819 ms reading was the outlier, not the signal.

**`SAT14/1509.smt2` — no starvation at all.** At 24 s the ladder finishes in
10,860 ms and returns `unknown`; at 40 s it finishes in 17,980 ms and still
returns `unknown`. Nothing ran out of clock. `nia-linearize` declines on a
**deterministic bound that scales with the configured budget**, so at 120 s it is
a more capable procedure than at 24 s — not the same procedure with more time.

**`QF_NIA`'s seven candidates are the same thing, seven times.** They are the
largest candidate cluster in the sweep, four of them nominally in the middle
band (9.5 s, 10.1 s, 11.5 s, 17.6 s). One question settles each: at the 24 s
budget, does the ladder run out of clock, or stop early? Measured on all seven:

| file | `nia-linearize` held | ladder total of 24,000 ms |
|---|---:|---:|
| `From_T2__ex36…p26914` | 6,670 ms | 15,773 ms |
| `From_T2__ex36…p28763` | 6,668 ms | 14,579 ms |
| `From_T2__ex36…p29986` | 6,666 ms | 12,860 ms |
| `SAT14/456` | 6,667 ms | 10,781 ms |
| `SAT14/687` | 6,678 ms | 10,800 ms |
| `SAT14/803` | 6,663 ms | 10,750 ms |
| `SAT14/1509` | 6,691 ms | 10,860 ms |

**Nothing was starved.** The ladder finishes in 11–16 seconds of a 24-second
budget and returns `unknown`; `nia-linearize` takes the same ~6.67 s share every
time and declines on a **deterministic bound that scales with the configured
budget**. At 120 s it is a stronger procedure, which is the whole of why the
probe saw a "prize". A portfolio arm at 24 s would hit the same bound.

### Why the enlarged-budget probe can never confirm a prize

Four candidates tested, four refuted, and the fourth one gives the mechanism:

> **A route's own cost is a function of the budget it was handed.** The routes
> here are anytime / CEGAR / bounded procedures: `cegar_probe_budget` hands one
> three quarters of what remains, `nia-linearize`'s admission bound scales with
> the budget, and a CEGAR loop's refinement schedule is set from its deadline.
> So "the deciding route's own segment under a 5x budget" is not the cost that
> route would incur at 1x. It can be smaller — a lucky search path — or the
> route can simply be a *different, stronger* procedure at the larger budget.

That is a limitation of the method, not of any one file, and it retires the
probe as an oracle: it can say *the ladder does not decide this at 5x* (a real
and useful negative) and it can nominate candidates, but it cannot establish a
prize. Only running a route **alone at the competition budget** — the solo
prober — can, and that is the arm whose band table is above.

So each of the probe's middle-band candidates was an artifact of measuring a
route under a budget it will never be given.

### One confirmed middle-band file, found by the right instrument

The solo prober then produced one, and it survives every check:

`QF_UFLIA/mathsat/Hash/hash_sat_08_05.smt2` is `unknown` at 24 s and `unknown`
at 120 s. `uflia-online`, run **alone at the 24 s competition budget**, decides
it `sat` — declared `sat`, reference `sat` — three times running:

```
run1  uflia-online  sat  18,173 ms
run2  uflia-online  sat  18,885 ms
run3  uflia-online  sat  19,278 ms
```

18–19 s of a 24 s budget: **76–80% of the clock, needed by one route.** No
reserve can serve that and still protect the routes below it, which is the
definition of the band only a portfolio reaches. This one is not an artifact of
an enlarged budget — it was measured at the budget that counts, by the
instrument that runs one route and nothing else, and it reproduces.

**So the middle band is not empty. It has one confirmed member in the roughly
330 files measured**, and the earlier "empty" reading in this note is corrected
by it. The recommendation below does not change — one file does not pay for a
concurrent dispatcher — but the mechanism is real rather than theoretical, and
the honest form of the negative is *"one confirmed case in 330"*, not *"none"*.

And the ladder's own trail on it is the mechanism in one picture:

```
uf-arith-lazy-overbound-pre-lia  declined budget         272.2ms
lia-dpll                         declined budget           0.2ms
uf-arith-lazy-overbound          declined budget      18,006.1ms   <- 24000 * 3/4
euf-online                       declined incomplete      11.8ms
euf-offline                      declined incomplete       1.3ms
uf-arith-online                  declined incomplete   5,181.6ms   <- what was left
```

`uf-arith-online` **is** `check_qf_uflia_online` (`auto.rs:3747`); the trail
calls it by the dispatch site's name. So the file needs two things at once:

- `uf-arith-lazy-overbound` takes 18.0 s — three quarters of the clock, by
  `cegar_probe_budget`'s design — and fails;
- the route that wins needs 18–19 s and is handed the **5.5 s that were left**.

**Two routes, each needing about eighteen seconds, and one twenty-four-second
clock.** There is no split of one clock that serves both, and no reserve setting
that does either — any reserve large enough for the winner starves the route
that wins other files. Two cores serve both trivially. That is the portfolio's
case, demonstrated rather than argued.

The `QF_UFLIA` solo sweep had covered 35 of 58 files when this was written, and
this file came out of those 35 — a division whose ladder happens to contain two
eighteen-second routes. **Finishing that sweep, and `QF_NIA`'s, is the cheapest
thing anyone can do to change this answer**, and it is the first thing to do
before the question is treated as closed.

## Neither instrument confirms a prize on its own, and the first two did not survive

The probe scores a file by `preamble + deciding route's own segment`. That is a
valid arm cost **only when the ladder is a single pass**. Both of the first two
candidates broke it, in opposite directions, and both were caught by testing the
claim rather than by a check failing:

**`QF_SLIA/…/new.8618.corecstrs.readable.smt2` — the front door LOOPS.** The
probe reports `int-blast-ladder` with an own cost of 1,172 ms and scores it a
1.2 s prize. Traced at 24 s the same file prints
`; partial route decided_by=int-blast-ladder bound_by=lia-dpll bound_ms=8044
total_ms=24622 attempts=55`, and the probe needed **110,546 ms** of the 120 s
budget to finish. The front door is walking a string-bound ladder and
re-dispatching the whole query per round; the deciding segment is one round of
fifty-five, not an arm's cost. A portfolio arm started at t = 0 would have to
walk the same rounds.

The oracle now counts how many times the winning route appears in the trail and
files a file with more than one as `LOOPED-NOT-SCORED` rather than scoring it.

**`QF_RDL/scheduling/orb06_900.smt2` — the solo prober cannot confirm it
either.** Run alone at the competition budget, `dl-online` reports
`unknown, 24,018 ms, budget exhausted`. That is not evidence against the file:
the solo prober skips preprocessing and passes no `extended_dl_probe_timeout`,
so it is not running the computation the dispatcher runs. It is evidence that
**"not shown" is all the solo prober can say about a negative**, exactly as its
own module docs claim — and therefore that it cannot serve as the confirmation
instrument for a probe candidate.

So every count below is `PRIZE-CANDIDATE`, never `PRIZE`. Confirming a candidate
needs the route-selection knob `SolverConfig` does not have — the same gap the
2026-09-07 sweep hit. **Two instruments that each see what the other misses do
not add up to one that sees everything**, and the honest form of this table is a
candidate column with the confirmation gap named, not a prize column with a
footnote.

## Five QF_UFLIA files are unsat in 2 ms, and the reason we lose them is not scheduling

`mathsat/EufLaArithmetic/medium/{9,10,13,16,19}.smt2` are on the committed loss
list, `unknown` at 24 s and still `unknown` at 120 s. `euf-online` run alone
decides **unsat in 2, 2, 5, 10 and 13 ms**. All five are declared `unsat` with a
matching `reference_verdict`, so these are right answers — and an abstraction
that drops arithmetic semantics refutes soundly, so a fast `unsat` here is not
the over-abstraction it would be if it said `sat`.

It looked like the portfolio's best case. It is not, and three controls say so.

**The ladder does try `euf-online`, and it declines in 1.1 ms.** Not an ordering
problem:

```
uf-arith-lazy-overbound-pre-lia  declined budget       254.2ms
lia-dpll                         declined budget         0.0ms
uf-arith-lazy-overbound          declined budget     18002.9ms
euf-online                       declined incomplete     1.1ms  boolean skeleton
                                                                outside the online CDCL
```

**Control 1 — the reduction is not the cause.** `route_solo`'s `auto` and
`auto-nopre` arms run the shipped `check_auto` on the same parsed input with
`config.preprocess` on and off. Both lose (42,279 ms and 42,271 ms), so
`preprocess_reduce` is not what takes the admission away. My hypothesis, tested
and refuted.

**Control 2 — removing the route that eats the budget does not help.**
`AXEYUM_UF_ARITH_OVERBOUND=skip` is the one route-skip switch in the tree. With
`uf-arith-lazy-overbound` gone, `uf-arithmetic` takes the whole 24 s instead
(`bound_by=uf-arithmetic bound_ms=24001`) and all five files are still lost.

**Control 3 — the budget is not the cause either.** At a 500 ms budget the
ladder reaches 22 attempts and `euf-online` declines just the same, on an arena
barely touched by the routes ahead of it.

So `check_auto` loses on exactly the input `euf-online` decides in 2 ms, with
preprocessing off, at every budget. The transformation that costs the route its
admission is **inside `check_auto` and is not `preprocess_reduce`** — the
remaining candidate is `check_auto_inner`'s `to_real`/`to_int` normalization.
Located, not identified; that is a defect lead for whoever owns the UF ladder.

**And it is not a portfolio finding.** A portfolio arm running inside the
dispatcher receives the same transformed query and declines the same way. These
five files are worth more than anything else in this note, and parallelism is
not what recovers them.

## The reservation itself costs a win, and that is the portfolio's structural edge

`QF_RDL/scheduling/orb06_900.smt2` is on the committed loss list and is still
lost by the current tree at 24 s. The probe decides it at 120 s via `dl-online`,
whose **own** cost is 19,690 ms — comfortably inside a 24 s budget, so it scores
as a prize. The mechanism is not a slow route. It is the reserve:

```
budget=24000  unknown  bound_by=dl-online bound_ms=18010 total_ms=24003 attempts=14
budget=27000  unsat    decided_by=dl-online bound_ms=17685 total_ms=17689 attempts=3
budget=32000  unsat    decided_by=dl-online bound_ms=15014 total_ms=15017 attempts=3
```

`dl_probe_budget` hands the probe `remaining − min(timeout/4, 6 s)`, so at a 24 s
budget `dl-online` gets **18,010 ms** — the number the trace prints — and the
route needs more. Raise the budget to 27 s and the same route decides the same
file in 17.7 s. Nothing about the route changed; the ladder's guarantee to the
routes below it is what took the win away.

That is the sharpest available statement of what a portfolio buys that a
reservation cannot: **a reserve is zero-sum over one clock.** Every second it
guarantees to the routes below is a second the leading route does not get, and
on a file the leading route would have won, the guarantee is the loss. A
portfolio arm has no such trade — it starts at t = 0 and gets the whole budget,
and so does every other arm.

**Correction, same evening, heavier load: the win does not reproduce.** Re-run
after the host picked up two more sweeps:

```
budget=24000  unknown  bound_by=dl-online bound_ms=18013 total_ms=24004 attempts=14
budget=25000  unknown  bound_by=dl-online bound_ms=19012 total_ms=25003 attempts=14
budget=26000  unknown  bound_by=dl-online bound_ms=20010 total_ms=26003 attempts=14
budget=27000  unknown  bound_by=dl-online bound_ms=21011 total_ms=27003 attempts=14
```

At 27 s it now loses where an hour earlier it won in 17.7 s. So `orb06_900` is a
**contention-sensitive near-miss, not a stable prize**, and the earlier "raise
the budget and it decides" reading is withdrawn as a claim about the file.

What survives is the part that does not move: `bound_ms` is `budget − 6000` at
every one of the four budgets — 18013, 19012, 20010, 21011. The reserve costs
`dl-online` exactly six seconds of every budget on this file, reproducibly. That
is the measurement. Whether six more seconds wins *this* file was observed both
ways in one evening, and neither observation is worth more than the other.

The same division's five `TOO-SLOW-ARM` files are the honest other half:
`dl-online` needs 26.4 s, 29.4 s, 42.0 s, 62.7 s and 107.0 s of its own time
there. Removing the reserve would hand it 24 s and still lose all five. Neither
a reservation nor a portfolio reaches them; they need a faster route.

## The two QF_ABV prizes, and the chain that explains all of them

`bmc-arrays/bubbleSort.smt2` and `brummayerbiere/fifo32ia04k08.smt2` are the two
files in this whole measurement where the finding is unambiguous: the ladder
loses both, and **`qf-bv` — the plain bit-blaster, called with the same
arguments `check_auto_dispatch` calls it with — decides them alone in 611 ms
(`unsat`) and 567 ms (`sat`)**. Both verdicts match the census's
`reference_verdict`.

`qf-bv` is *reachable* for these queries: the array branch falls through to it
whenever `has_non_bv_array` is false. It never gets a turn, because the two
routes in front of it can each consume the whole clock —
`abv-online-cdclt` (which takes `config` unmodified, §"wins we keep only by
overrunning") and then `array-fast-path`, whose own cost on `fifo32ia04k08` is
**86,910 ms**.

That is the same shape as the QF_UFLIA control above: remove the route that eats
the budget and the next one eats it instead. It is worth naming, because it is
the structure underneath every case in this note:

> **A per-route reserve divides one clock N ways; a portfolio gives every arm
> the whole clock on its own core.** Where a ladder has several routes each able
> to consume the entire budget ahead of a cheap winner, a reserve must be
> applied at every position, and each one is zero-sum against the routes it
> protects — the `orb06_900` case is that trade going the wrong way.

## The answer to the strategic question, and why it is still no

The middle band is where a portfolio uniquely wins: a winner that needs a
**large fraction** of the budget, queued behind another route that needs the
same. A reserve cannot serve that band, because splitting the clock leaves the
winner too little. Sixteen idle cores can.

That band is, in this population, close to empty — and the two ends explain why.

- **The winners we found are cheap.** 611 ms, 567 ms, 1,202 ms, 2–13 ms. A
  winner that needs under a second does not need a core of its own; it needs a
  reserve of one second, which is free.
- **The winners that need the whole budget need more than it.** Every
  `TOO-SLOW-ARM` file wants 26.4 s, 29.4 s, 42.0 s, 50.1 s, 62.7 s, 86.9 s,
  87.2 s, 94.5 s, 107.0 s of a single route's own time. No arm of a 24 s
  portfolio reaches any of them. They need a faster route.

That band is, in this population, nearly empty — **one confirmed member in
roughly 330 files measured** (`hash_sat_08_05.smt2`, above) — and the two ends
explain why the rest is not in it.

So the recommendation is **do not build the portfolio yet**, and the reason is
not the one the 2026-09-07 sweep gave. That sweep said parallelism cannot help
because the binder already holds the clock; that is refuted — on
`hash_sat_08_05` there are two routes each wanting 18 s of one 24 s clock, and
handing the binder more cores is exactly what would help. The measured reason to
wait is narrower and honest: **the band a portfolio uniquely serves has one
confirmed member so far, and the solo sweep that found it had covered 35 of that
division's 58 files.** One file does not pay for a concurrent dispatcher; three
or four might, and the measurement that would say so is already running.

What to do next, in the order the measurements support it:

0. **Finish the `QF_UFLIA` and `QF_NIA` solo sweeps** (`scripts/route-solo-slot.sh`;
   partial progress logs are committed). They are the only measurement that can
   move the band count, and the single confirmed portfolio case came out of the
   35 `QF_UFLIA` files already covered. Decide the portfolio on the finished
   number, not on this one.

Then, whatever that number says, these three are worth more per hour than a
concurrent dispatcher:

1. **Clamp `dispatch_abv_online`.** It is the only dispatch site of its kind
   that passes `config` through unmodified, it costs nine QF_ABV files their
   verdict under a strict limit today, and it is one line. (Coordinate with the
   `budget-discipline` lane; this is their shape of change, not this lane's.)
2. **Find what takes `euf-online`'s admission away inside `check_auto`.** Five
   files, `unsat` in 2–13 ms, lost at 120 s. Not `preprocess_reduce`; the
   remaining candidate is `check_auto_inner`'s `to_real`/`to_int` normalization.
3. **Re-cut the loss population.** 122 of the 230 files probed are already
   decided by the current tree. Any planning against the 2026-09-05 lists is
   planning against a number that has moved.

## A portfolio and a reservation are the same policy in two execution modes

A sibling lane is building the **sequential reservation**: a route that runs
first must leave the ones after it something. That is the same problem's
sequential approximation, and the two must not both edit the ladder.

They are not competitors, and the boundary between them is not a matter of
taste:

- **A reservation is the right fix when cores are scarce or memory is the
  binding limit.** It costs nothing but clock arithmetic, it needs no second
  arena, and a competition memory limit is per solver — so under a tight limit
  the reservation is the only one of the two that can run at all.
- **A portfolio is the right fix when a genuinely different engine may win and
  the cores are free.** It buys what a reservation cannot: a route whose own
  cost is a large fraction of the budget still gets the *whole* budget, because
  it does not have to wait for anything.

They compose as **one policy object with two execution modes**, expressed over
the same ladder order:

1. The reservation assigns each ladder position a share of the budget. This is
   already the shipped shape — `cegar_probe_budget`'s
   `UF_ARITH_LADDER_RESERVE_SHARE` quarter, `dl_probe_budget`'s
   `min(timeout/4, 6 s)`, `int_real_relax_budget`'s sixth.
2. A portfolio policy names a **contiguous group** of positions to fuse. Every
   arm of a fused group starts at t = 0 and gets the group's whole share.
3. **With one worker, a fused group degenerates exactly to the reserved
   sequence.** That is the property that makes this safe to ship: the sequential
   path stays the default and stays byte-identical, and a portfolio is a
   configuration, not a fork of the dispatcher.

The deterministic budget primitive already has the right shape for step 1 and
nobody calls it: `axeyum_ir::budget::Budget::split` produces cumulative slices
with carry-over, so an under-spending arm donates its remainder to the next —
and it is clock-free, so two runs of the same policy allot the same work. Today
every reserve in `auto.rs` is `Duration` arithmetic over `Instant::now()`. The
reservation lane and a portfolio are the two natural first callers of `split`,
and that is the concrete thing to share rather than duplicate.

### What determinism means for a racing dispatcher

Determinism is a public API promise here, and a race does not have to break it,
but the promise has to be stated at the right granularity:

- **The verdict must be deterministic**, and it is — provided every arm is
  sound, `sat` and `unsat` are not two answers to one query but one answer and
  one bug. That is why the cross-route disagreement check in
  `scripts/route-solo-sweep.py` exits non-zero rather than printing.
- **The attribution may vary**, and the trace must say so: which arm won, and
  that the run was concurrent. A `; route decided_by=X` line that silently means
  "X happened to be scheduled first today" is worse than no line.
- **Arms must be top-level dispatches of the original query.** At the
  granularity of route *attempts* a disagreement is normal (79 of 796 files
  above), because attempts are refinement rounds over different queries. A
  portfolio that raced attempts would have to choose between a false alarm on
  79 files and a soundness check that cannot fire, and both are worse than the
  restriction.
- **Simultaneous winners need a fixed priority**, not a race: when two arms
  finish within the same scheduler tick, the reported `decided_by` should be the
  earlier ladder position, so re-running the same file on the same input yields
  the same attribution as well as the same verdict.

## Method notes

Populations are the committed
`bench-results/parity-losses-20260905/<DIV>.txt` lists (403 files, 11
divisions). Hosts s5/s6/s7, three `taskset`-pinned slots each (cores 0-3, 4-7,
8-11), one division at a time per slot, 8 GiB `ulimit -v`, control 24 s / probe
120 s. Each division records the load average before and after in
`out/<DIV>.frame`: all three hosts were also carrying another lane's A/B sweep,
so **timings here are advisory** — the decide/not-decide bit and the ordering of
arm costs are what the conclusions rest on, not the absolute milliseconds.
