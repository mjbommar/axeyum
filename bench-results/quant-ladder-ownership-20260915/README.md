# ADR-2103 sizing: the quantified ladder's ownership ceiling

**The number, first: 0 of 482.**

ADR-2100 typed the quantifier-free dispatch ladder and measured, on the way,
that **482 of 643 undecided Tier 1 rows (75 %) never reach that ladder at all** —
their budget goes to the `q:` rungs of the quantified ladder in `solve`. This
lane's first question is whether the same ownership rule has anything to reach
there. It does not, and this directory is the measurement.

## What was measured, and how

No sweep was re-run. The evidence is ADR-2100's own committed `--trace` capture
(`bench-results/route-ownership-20260915/trace-tier1-undecided.tsv`, 645 rows
with the full `route-trail` JSON per row), joined by corpus-relative PATH to
lane PLAN-SIZING's inventory
(`bench-results/dispatch-plan-sizing-20260915/phase1-ceiling.tsv`) — 643 of 643
join, and `size-q-ceiling.py` ABORTS rather than reporting a smaller number if
one is missing from either side.

| script | what it answers |
|---|---|
| `explore-q-ladder.py` | what the `q:` ladder does on the 482 — which rung is last, which reasons it gives |
| `explore-terminals.py` | what ENDED the ladder, and the record that proves it |
| `explore-rung-incidence.py` | which `q:` rungs run on these rows and which never appear |
| `size-q-ceiling.py` | **the ceiling** — see below |
| `check-candidates.py` | refutes the ceiling's own candidate list from the wall clock |

## The result

    POPULATION (never reached the QF ladder) : 482

    211  ladder exhausted (nothing below the terminal rung)
    195  clock (q:timeout recorded)
     53  A RUNG STOPPED THE LADDER (candidate)  <-- refuted below
     23  watchdog kill (partial trail)

| division | rows | candidate | clock | watchdog | exhausted |
|---|---:|---:|---:|---:|---:|
| AUFDTLIRA | 67 | 1 | 12 | 0 | 54 |
| AUFLIRA | 20 | 0 | 16 | 1 | 3 |
| UF | 108 | 48 | 19 | 6 | 35 |
| UFDTLIRA | 50 | 1 | 0 | 0 | 49 |
| UFLIA | 107 | 3 | 68 | 7 | 29 |
| UFNIA | 130 | 0 | 80 | 9 | 41 |
| **TOTAL** | **482** | **53** | **195** | **23** | **211** |

`AUFLIRA` contributes 20 rather than 22 and `UFNIA` 130 rather than 147 because
this is the 482-row no-QF-dispatch subset of ADR-2100's 643-row re-capture, not
PLAN-SIZING's 645-row `undecided` column. The denominator is 482 throughout.

**The 53 candidates are all the clock too**, and the method that says so is the
wall clock rather than another record: every one of the 53 sits between 24,015
and 24,950 ms of trail time against the sweep's 24,000 ms budget, 0 of 53 under
90 % of it (`check-candidates.py`, whose exit status depends on that finding).

So the ceiling is **0 of 482**, and it is 0 for **every possible ownership
table**, because no row's ladder was ended by a rung's non-decision at all. That
is a stronger statement than a ceiling computed from one particular table, and
it is why `size-q-ceiling.py` carries no ownership declaration.

## The finding the sizing produced instead

The 53 rows are clock-ended through the **one budget exit in the quantified
ladder that records nothing**:

```rust
// finish_quantified_solve_or_induct
let Some(induction_config) = config_with_remaining_timeout(config, deadline) else {
    return Ok(result);          // <-- no route record, no q:timeout
};
```

Every other budget exit goes through `quantified_timeout(..)`, which records
`q:timeout`. This one does not, so 53 of 482 rows — 11 % of the population, and
48 of `UF`'s 108 — are invisible to the sink that exists to catch exactly them,
and a census keyed on `q:timeout` under-reports the ladder's budget exits by
that much. ADR-2103 closes it.

## Two corrections these scripts' own runs produced

**`outcome != "declined"` does not detect a terminal `Unknown`.**
`RouteTrace::record_result` maps `CheckResult::Unknown` to `record_declined`, so
a rung whose `Unknown` WAS the answer and a rung that declined and let the
ladder continue are the same word on the trail. The first pass tested that word,
got 0 of 482, and 0 is exactly what a detector that cannot fire prints.

**Six rungs record nothing when they decline** — `q:checked-fast-path`,
`q:skolem-qf`, `q:vacuous-universal-qf`, `q:eq-partition`, `q:unsat-universal`,
`q:fourier-motzkin`. Their absence from a trail is not evidence they were
skipped; treating it as such reports all 482 rows as candidates. They are
excluded by name in `SILENT_ON_DECLINE`.

**And the candidate list was capped at 40.** `check-candidates.py`'s first run
verified 40 of 53 rows and printed "EVERY candidate row is at the budget". The
cap is gone; the published run covers 53 of 53.

---

## The A/B: what was run, and the two deviations from ADR-2100's recipe

| | |
|---|---|
| A arm | `51baff9ef` — this branch's **merge-base** with `main` |
| B arm | this branch |
| divisions | the seven Tier 1 plus `QF_LIA` and `QF_LRA`, 200 files each |
| envelope | 24 s wall, 8 GiB `ulimit -v`, one pinned physical core pair per shard |
| shards | 12 — three hosts x four core pairs — **one division at a time** |
| scripts | ADR-2100's `ab-run.sh` and `recheck-movers.sh`, **unchanged** |
| lists | ADR-2100's `ablists/`, **unchanged** |

**Deviation 1 — the A arm is `51baff9ef`, not the `7d922fe58` the brief named.**
`7d922fe58` was `main` when this lane branched. `main` then moved (ADR-2104,
typed `DeclineReason` detail) and the coordinator instructed this lane to merge
it. Measuring against `7d922fe58` would therefore put ADR-2104's diff in the B
arm and attribute its effect to ADR-2103. `51baff9ef` isolates this lane's
change exactly, which is the entire purpose of an A/B.

**Deviation 2 — the divisions run sequentially, and this is a defect in the
runner, not a preference.** ADR-2100's `launch-ab.sh` takes N division specs and
launches them ALL at once: its outer loop is over divisions and its inner loops
are hosts x cores, so nine divisions is **36 concurrent `ab-run.sh` per host
pinned onto 4 physical cores**. Measured on the first launch here:
`pgrep -cf ab-run.sh` returned **129, 129 and 133** on s5/s6/s7, one-minute load
~30 on 16 CPUs.

That does not merely slow the run. `ab-run.sh`'s own header says both arms run
"back to back on the SAME file on the SAME pinned physical core" so that ambient
load "cancels in the DIFFERENCE rather than landing entirely on whichever arm
ran second" — and at 9x oversubscription each 24 s solve gets about a ninth of a
core, so nearly everything times out and both columns collapse toward `unknown`.
**A wash of `unknown` reads exactly like "no movement".** The first launch was
killed, its partial output discarded, and `run-ab-sequential.sh` runs one
division at a time: 12 shards, one per pinned core pair, which is what
ADR-2100's own prose describes.

## The two files ADR-2100 named

`named-losses-recheck.tsv` — both **STABLE-GAIN**, A `unknown` 3/3 and B `unsat`
3/3, exit status 0 on all twelve passes. Read the direction carefully: **A here
INCLUDES ADR-2100**, so A is the arm that lost these two files and B is the arm
with the bound.
