# Loss population, 2026-09-08 — the re-cut

**This is the set a brief should cite.** It supersedes the eleven division
lists in [`../parity-losses-20260905/`](../parity-losses-20260905/), which
remain committed, byte-identical, as the record of what was true that day.
`../parity-losses-20260906/QF_NRA.txt` is superseded for QF_NRA by the list
here.

`python3 scripts/check-loss-list-freshness.py` prints the per-division
authority table and reds when a set goes unmarked or past its age budget. Its
`behind=` line is the one to read before briefing anyone: the 2026-09-05 set
reads **`behind=606`** commits touching `crates/` as of 2026-09-08.

## Why it was re-cut

Measured by the `parallel-portfolio` lane and re-measured here: **141 of the
403 files on the 2026-09-05 lists were already decided** by the shipped
default. Every lane briefed against "the N files we lose in `<DIV>`" was partly
aimed at files the tree wins. Nothing was wrong with the old lists — they were
a correct measurement of 2026-09-05 sitting in a directory whose name says so,
and everyone read them as current anyway.

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
  in the QF_LRA complement 37 of 39 unsolved files declare `sat`/`unsat`, and
  the ledger's own arithmetic puts all 49 of that division's reference-only
  losses on the old list, i.e. those 37 are the division's `neither` set. The
  complement's unsolved files are reconciled against the ledger's
  `reference-only` + `neither` cells at the COUNT level, and the residual is
  reported rather than absorbed.
- **A contended sweep cannot show that a file would decide when idle.** The
  confirm pass ran at equal or higher load than pass 1; it is a second sample,
  not a quieter one.
