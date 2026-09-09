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

**Running; this section is empty because the sweep has not finished, not because
it found nothing.** The three-host run over the 403-file committed loss
population is in flight (`bench-results/portfolio-oracle-20260908/` when it
lands). Everything above this heading is measured and complete on its own terms;
the per-division prize table is what this section will carry, and no conclusion
about whether to build a portfolio is drawn until it is here.

## Method notes

Populations are the committed
`bench-results/parity-losses-20260905/<DIV>.txt` lists (403 files, 11
divisions). Hosts s5/s6/s7, three `taskset`-pinned slots each (cores 0-3, 4-7,
8-11), one division at a time per slot, 8 GiB `ulimit -v`, control 24 s / probe
120 s. Each division records the load average before and after in
`out/<DIV>.frame`: all three hosts were also carrying another lane's A/B sweep,
so **timings here are advisory** — the decide/not-decide bit and the ordering of
arm costs are what the conclusions rest on, not the absolute milliseconds.
