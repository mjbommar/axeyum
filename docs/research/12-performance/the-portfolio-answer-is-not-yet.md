# The portfolio: not yet, one live example, and a method that could not answer it

Measured 2026-09-08. Records a correction to my own framing AND a correction to
the correction, because both matter.

## The history of this question

1. A route-attribution lane measured that on files we lose, the binding route
   holds a **median 84% of the trail**, and put the diversity ceiling at 1.33x.
   I relayed that as "parallelism will not help much."
2. **The user pushed back**, pointing at a QF_ABV file where one route spends
   24.009 s failing and a fallback then decides it in 0.191 s. He was right and
   my summary was wrong: **one route holding most of the clock is consistent
   with a portfolio winning big.** "How much waiting disappears if we run the
   same routes concurrently?" is not "is there a route that would have decided
   this, had it been given the budget?"
3. This lane measured the second question properly. The answer is **not yet**,
   and the reason is not what either earlier reading said.

## The cheap method is wrong for this question — a finding in itself

The obvious probe is to run a file at 5x budget and read the deciding route's
own `elapsed_ns`. It nominated 7 candidates. **Four were tested; four were
refuted.**

The mechanism: **a route's own cost is a function of the budget it was handed.**
`cegar_probe_budget` gives a route 3/4 of what remains; `nia-linearize`'s
admission bound scales with the budget; a CEGAR loop takes its refinement
schedule from its deadline. On `hash_sat_05_17` the probe read 21.3 s from a
clean trail while a budget walk found the route needs **33-34 s** — it fails at
a 40 s budget while *holding* 30 s.

Only a **solo prober** — one route, one process, at the real 24 s budget — can
establish a prize. Retired the enlarged-budget probe as an oracle; it still
establishes the denominator.

## The table — FULL 403-file loss population, not the partial one

The lane continued past its first report to the whole population. The
conclusion holds and the evidence is much stronger; these numbers supersede the
105-file table below.

| division | files | ladder wins | ladder loses | decided alone | none |
|---|---:|---:|---:|---:|---:|
| QF_ABV | 19 | 7 | 12 | **2** | 10 |
| QF_BV | 6 | 0 | 6 | 0 | 6 |
| QF_LRA | 54 | 5 | 49 | 0 | 49 |
| QF_NIA | 30 | 3 | 27 | 0 | 27 |
| QF_UF | 38 | 35 | 3 | 0 | 3 |
| UF | 32 | 0 | 32 | 0 | 32 |
| **total** | **179** | **50** | **129** | **2** | **127** |

**The cheap probe nominated 10 candidates across 403 files and every one tested
was refuted**, by three distinct mechanisms rather than one: a looped front door
scored on 1 of 55 rounds (1,172 ms scored against 110,546 ms real); a result
that does not reproduce (decided once at 27 s, then failed at 24/25/26/27 s
under load); and seven files where nothing was starved at all — the ladder
finished in 10.8-15.8 s of a 24 s budget and the route is simply stronger under
a bigger one.

## The number that changes planning

**141 of the 403 loss files are already decided.** The lists were cut on
2026-09-05 and today moved three divisions. Planning against them is planning
against a number that moved, and every lane pointed at "the N files we lose" is
partly pointed at files we now win.

## The table (first report, 105 files — superseded above)

| division | files | ladder wins | ladder loses | decided alone in budget | no route decides alone |
|---|---:|---:|---:|---:|---:|
| QF_ABV | 19 | 7 | 12 | **2** (611 ms / 567 ms) | 10 |
| QF_LRA | 54 | 5 | 49 | **0** | 49 |
| UF | 32 | 0 | 32 | **0** | 32 |
| **total** | **105** | **12** | **93** | **2** | **91** |

The band that decides the question is the **middle** one — a winner needing a
large fraction of the budget, the only case a sequential reserve cannot serve:

```
under 1 s   (a reserve reaches it)      2
1-6 s       (a reserve reaches it)      0
6-24 s      MIDDLE BAND: portfolio      0
no route decides alone                 91
```

**91 of 105 are decided by no single route at all.** For those the gap is
capability, not scheduling, and neither a reserve nor a portfolio touches them.

## The one member, and it is exactly the shape the user described

`mathsat/Hash/hash_sat_08_05.smt2`, from QF_UFLIA's half-finished sweep: lost at
24 s AND at 120 s; `uflia-online` alone decides it `sat` in **18,173 / 18,885 /
19,278 ms** over three runs, matching the reference.

The trail is the whole argument in one line: `uf-arith-lazy-overbound` takes
18,006 ms — exactly 24000 x 3/4 — and fails, then the winning route receives the
5.5 s left. **Two routes, each needing ~18 s, one 24 s clock. No split of one
clock serves both; two cores do it trivially.**

One file does not pay for a concurrent dispatcher. Five solo sweeps are still
running (QF_UFLIA 35/58, QF_NIA 24/61 and 5/30, QF_IDL 26/54, QF_RDL 21/47,
QF_LIA 9/27) and **three or four such files would pay.** The decision is
deferred to that data, not refused.

## Two corrections to my brief

- **"If two routes disagree that is a hard failure" is wrong at route-attempt
  granularity.** 79 of 796 files have disagreeing attempts, because attempts are
  refinement rounds over *different* queries. Portfolio arms must be top-level
  dispatches; the soundness gate belongs there, not at every attempt.
- **N arms means budget/N in memory, not N times the memory.** A competition
  limit is per solver. `wchains140se` already aborts at 8 GiB with ONE arm, so
  arms are not free even where cores are.

## What is worth more per hour than a portfolio, in order

1. **Clamp `dispatch_abv_online`** — the only dispatch site passing `config`
   through unmodified. Nine QF_ABV files are "wins" today only because
   `WATCHDOG_GRACE` is 1 s (`bound_ms=24009, total_ms=24029`); their winning
   arms cost 15-719 ms. One line, and it belongs to the budget-discipline shape.
2. **Find what removes `euf-online`'s admission inside `check_auto`** — five
   QF_UFLIA files are `unsat` in **2-13 ms solo** and lost at 120 s. Three
   controls already exclude preprocessing, route order and budget; the remaining
   candidate is `check_auto_inner`'s `to_real`/`to_int` normalization.
3. **Re-cut the loss population.** 127 of 284 probed files are already decided.
   Planning against the 2026-09-05 lists is planning against a number that moved.

## Composition with the sequential reserve

One policy, two execution modes. A reservation assigns each ladder position a
share; a portfolio fuses a *contiguous group* whose arms each get the group's
whole share, and **with one worker a fused group degenerates exactly to the
reserved sequence**. `axeyum_ir::budget::Budget::split` already has the right
shape — cumulative slices with carry-over, clock-free — and **zero callers**.
That is the thing to share rather than duplicate.

Also measured, against the reserve's own case: on `orb06_900` the reserve
*costs* the win (`bound_ms` = budget − 6000 at all four budgets).
