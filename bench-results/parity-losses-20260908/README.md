# Loss population, 2026-09-08 — the re-cut

**This is the set a brief should cite.** It supersedes the eleven division
lists in [`../parity-losses-20260905/`](../parity-losses-20260905/), which
remain committed, byte-identical, as the record of what was true that day.
`../parity-losses-20260906/QF_NRA.txt` is superseded for QF_NRA by the list
here.

`python3 scripts/check-loss-list-freshness.py` prints the per-division
authority table and reds when a set goes unmarked or past its age budget. Its
`behind=` line is the one to read before briefing anyone: the 2026-09-05 set
read **`behind=606`** commits touching `crates/` when this set was cut, and the
number only grows.

## Why it was re-cut

The `parallel-portfolio` lane measured 141 of the 403 files on the 2026-09-05
lists as already decided. Re-measured here a day later, on the same 403, it is
**156 decided plus 4 flaky** — the number moved again between the two
measurements, which is the point rather than a correction. Every lane briefed against "the N files we lose in `<DIV>`" was partly
aimed at files the tree wins. Nothing was wrong with the old lists — they were
a correct measurement of 2026-09-05 sitting in a directory whose name says so,
and everyone read them as current anyway.

## The result

**480 → 318 files.** 157 already decided, 5 flaky.

| division | 2026-09-05/06 | **2026-09-08** | recovered | flaky |
|---|---:|---:|---:|---:|
| QF_ABV | 19 | **12** | 7 | 0 |
| QF_BV | 6 | **6** | 0 | 0 |
| QF_IDL | 54 | **19** | 35 | 0 |
| QF_LIA | 27 | **22** | 3 | 2 |
| QF_LRA | 54 | **49** | 5 | 0 |
| QF_NIA | 61 | **58** | 3 | 0 |
| QF_NRA | 77 | **75** | 1 | 1 |
| QF_RDL | 47 | **9** | 38 | 0 |
| QF_SLIA | 7 | **7** | 0 | 0 |
| QF_UF | 38 | **6** | 30 | 2 |
| QF_UFLIA | 58 | **23** | 35 | 0 |
| UF | 32 | **32** | 0 | 0 |
| **total** | **480** | **318** | **157** | **5** |

`python3 bench-results/parity-losses-20260908/scripts/reconcile.py` joins this to
`bench-results/PARITY.md`. QF_IDL, QF_LRA and QF_SLIA reconcile to zero; four
more to within two files. Four divisions decide FEWER files than their ledger
entry implies (QF_UF +3, QF_BV +2, QF_LIA +1, UF +1) and each survived a second
pass — `QF_UF.regression-candidates.txt` and `QF_BV.regression-candidates.txt`
name the supersets. No candidate list is emitted for QF_LIA (1 in 60) or UF
(1 in 84): a file that is 98% `neither` would be a worse artifact than none.

The writeup is
[`docs/research/12-performance/loss-population-recut-2026-09-08.md`](../../docs/research/12-performance/loss-population-recut-2026-09-08.md).

## Protocol

Byte-identical to the SCORED path of `scripts/parity-run.sh`, which is the
recipe every committed parity number was measured with, so a verdict here is
comparable to the census it replaces:

```
MEM_LIMIT_GB=8 timeout 29 env -u AXEYUM_EVIDENCE \
  scripts/mem-run.sh target/release/examples/smtcomp_cli <file> --timeout-ms 24000 \
  | grep -oE '^(sat|unsat)$' | tail -1
```

The external `timeout` is 29 s, exactly as in `parity-run.sh`: this sweep
reproduces the SHIPPED scoring, watchdog grace included, not a stricter one.
Whether a file needed that grace is the separate `over_budget` column, because
conflating the two would silently redefine the metric in the middle of a
re-measurement whose whole point is comparability.

Host s4, 16 cores, `taskset`-pinned slots, one solve per pinned pair. **The host
was not idle**: load average ran 11.5 → 27 across the sweep, carrying another
lane's `progress_frontier` run throughout. Per-slot load frames are in
`frames/`. That matters for the direction of every number here and is stated
again under "What this does not establish".

## The three passes

| pass | population | what it can change |
|---|---|---|
| `sweep/` | the 2026-09-05 loss lists, in full | establishes the first verdict |
| `confirm/` | only what `sweep/` left `unsolved` | can move a file OFF the loss list, never onto it |
| `comp/` | the division's parity list MINUS the 2026-09-05 loss list | finds files we no longer decide |

The confirm pass is one-sided on purpose. A 24 s budget is a wall clock and this
host was loaded, so a file that misses the budget under contention may decide on
an idle box. A loss list built from one contended pass over-counts losses —
which is the same defect as the staleness this re-cut is about, arriving from
the other direction. Because the second pass only ever removes, **the loss list
is an upper bound refined downward and the "already decided" count is a lower
bound.**

The complement pass exists because re-running the old loss list answers "which
files we lost do we now win?" and is *structurally incapable* of answering
"which files we won do we now lose?".

## Files

- `<DIV>.txt` — **the loss population**: files unsolved in every pass that ran
  them. This is what a brief cites.
- `<DIV>.flaky.txt` — decided in some passes and not others. Neither a clean win
  nor something to point a lane at.
- `<DIV>.census.tsv` — every file of the 2026-09-05 population with its
  per-pass verdict, wall time and `over_budget` flag, so all three classes are
  re-derivable without re-running anything.
- `comp/<DIV>.tsv` — the complement pass, raw.
- `abv-watchdog-blind.txt` + `abv-reserve-ab.tsv` — the per-file A/B of the
  `abv-online-cdclt` ladder reserve (see below).
- `scripts/` — everything that produced the above.
- `MANIFEST.json` — the solver commit, the binary digest, the budget. Read by
  `scripts/check-loss-list-freshness.py`.

## What this does NOT establish

- **It is not a parity measurement.** Only z3 is installed on s4, and these
  divisions are scored against cvc5 / bitwuzla / yices. No reference was re-run.
  A `<DIV>.txt` entry is "the reference decided it on 2026-09-05 and we do not
  decide it today"; a complement file that is now unsolved is a **loss
  candidate** whose reference verdict is not known here. `bench-results/PARITY.md`
  remains the ledger.
- **The declared `:status` is not a stand-in for the reference.** SMT-LIB
  benchmarks carry a curated status whether or not any competition solver
  decides them, so "unsolved with a declared status" over-counts losses badly:
  in the QF_LRA complement **52 of 54** unsolved files declare `sat`/`unsat`,
  and the ledger's own arithmetic puts all 49 of that division's reference-only
  losses on the old list, i.e. those 52 are the division's `neither` set. The
  complement's unsolved files are reconciled against the ledger's
  `reference-only` + `neither` cells at the COUNT level, and the residual is
  reported rather than absorbed.
- **A contended sweep cannot show that a file would decide when idle.** The
  confirm pass ran at equal or higher load than pass 1; it is a second sample,
  not a quieter one.
