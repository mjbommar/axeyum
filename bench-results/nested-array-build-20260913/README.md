# The nested-array prize: re-sized before the build, then measured after it

**2026-09-13, lane `nested-array-build`.** Two measurements and the order they
were taken in. Everything down to *"The bracket"* was committed at `9d246c830`,
**before a line of `crates/` changed**, because that is the only order in which
a prediction can be checked against a build rather than fitted to it. The A/B
below it is what the build then did. Decision: **ADR-1965**.

## The question

[ADR-1957](../tier1-divisions-headtohead-20260913/README.md)'s census puts the
nested-array parse refusal in front of a **projected ceiling of 20,399 files**,
of which 18,510 (91%) is AUFLIRA alone. A ceiling is a count of files we
**refuse at the front door**. It says nothing about whether the solver behind
that door would decide them, and this repository has watched that distinction
collapse an estimate five times (143→6, 51→2, 173→10, 27,150→1,135, 19,620→0).

[ADR-1955](../../docs/research/09-decisions/adr-1955-the-nested-array-sort-is-the-first-of-three-gates-and-the-only-one-the-ir-owns.md)
sized the reach by transferring a **family-matched control rate** onto each
division's blocked count, and got ~1,135 — essentially all of it one family of
ABV. For AUFLIRA and AUFNIRA, 95% of the prize, ADR-1955 records in the same
table that *no family-matched control exists*: every blocked file is
`nasa`/`peter`, not one `nasa` file parses, and
[ADR-1960](../../docs/research/09-decisions/README.md) adds that of the AUFLIRA
and AUFNIRA files that *do* parse, `grep -c Array` returns **0**. So the method
that produced ~1,135 has, by its own account, nothing to say about the part
that matters.

This measures it directly instead.

## The instrument: an array-free surrogate, sound for `unsat`

[`nested_array_surrogate.py`](nested_array_surrogate.py) rewrites a benchmark
so it parses **today**, without any IR change:

* each distinct `(Array I (Array J E))` becomes a fresh **uninterpreted** sort
  `NA_k`;
* every `select` whose base has that sort becomes a fresh uninterpreted
  function `na_sel_k : NA_k × I → (Array J E)`.

The outer level loses the array theory and keeps congruence. The inner level is
untouched.

The rewrite **deletes axioms and adds none** — outer extensionality goes,
outer read-over-write goes (and a file that uses a `store` at the outer level is
*refused* by the script rather than rewritten, since that is the axiom being
deleted). Deleting axioms admits more models, so

> **surrogate `unsat` ⟹ original `unsat`.**

The converse fails, so a surrogate `sat` transfers nothing and is reported in
its own column so the reach cannot be misread as a decide rate. 186 of
AUFLIRA's 187 winnable files and 138 of AUFNIRA's 139 carry `:status unsat`, so
the sound direction is the one that covers the population.

`python3 nested_array_surrogate.py --self-test` checks the rewrite on a fixture
with a let-bound carrier, a quantified carrier, a UF returning the carrier, and
a flat row sort that must survive untouched — plus a negative control (an
outer-level `store` must be refused).

## What it found

Over the **pinned full-span winnable lists** of
`bench-results/tier1-divisions-headtohead-20260913/`, at the board's own budget
(24 s, `taskset`-pinned, `AXEYUM_TIMEOUT` 24,000 ms), produced by
[`surrogate-launch.sh`](surrogate-launch.sh) and summarized by
[`surrogate-summarize.py`](surrogate-summarize.py):

| division | winnable | rewritten | refused | ax `unsat` | ax `sat`* | z3 `unsat` | reach | ADR-1957 ceiling | projected |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| AUFLIRA | 187 | 175 | 12 | **141** | 0 | 175 | **80.6%** | 18,510 | 14,914 |
| AUFNIRA | 139 | 121 | 18 | **115** | 0 | 121 | **95.0%** | 955 | 908 |
| ALIA | 36 | **0** | 36 | 0 | 0 | 0 | — | 511 | 0 |
| ABV | 17 | **1** | 16 | 1 | 0 | 1 | 100.0% | 423 | 423 |
| **total** | **379** | **297** | **82** | **257** | 0 | 297 | **86.5%** | **20,399** | **16,245** |

\* a surrogate `sat` transfers nothing; the column exists so the reach is not
read as a decide rate. It is 0 everywhere, which is itself the expected shape
for a population that is 96% `:status unsat`.

**The soundness check on the rewrite passed**: no surrogate `unsat`, from either
solver, lands on a file whose original is `sat` (by declared `:status` or by
z3's own board verdict). 257 axeyum + 297 z3 refutations were checked.

### Why 82 files are refused, and what that costs

| reason | AUFLIRA | AUFNIRA | ALIA | ABV |
|---|---:|---:|---:|---:|
| outer-level `store` (the axiom the rewrite deletes) | 10 | 8 | **33** | 12 |
| no nested array sort in the file at all | 2 | 10 | 3 | 0 |
| more than one distinct nested array sort | 0 | 0 | 0 | 4 |

**ALIA and ABV are essentially outside this instrument**: 33 of 36 ALIA and 12
of 17 ABV winnable files write to the outer array, so the outer read-over-write
axiom is load-bearing and a congruence-only abstraction cannot refute them. The
table above therefore says **nothing** about ALIA's 511 or ABV's 423 — those two
rows are the ones ADR-1955's ABV control was about, and they stay where ADR-1955
left them. The 16,245 is 98% AUFLIRA + AUFNIRA.

## The bracket, and what it is a bracket on

    lifting the parse refusal alone   →  measured after the build, this lane
    congruence-only refutation reach  →  16,245  (95% of it AUFLIRA+AUFNIRA)
    ADR-1957 census ceiling           →  20,399

The middle line is **not a forecast of the build**. It is the answer to a
question about the *files*: does a refutation exist that needs only congruence
through the nested read? For AUFLIRA and AUFNIRA the answer is yes for 86.5% of
the winnable set — which is the fact ADR-1955's family-matched transfer could
not see, because it had no family to transfer from.

Turning that into decided files is a **routing** decision, not a parsing one:
the query has to reach a route that abstracts the outer array as a congruent
uninterpreted function and reports only `unsat` from the abstraction. That is
the same one-directional argument the existing lazy ROW/extensionality CEGAR
already runs on flat arrays — *"the bare abstraction is a RELAXATION so its
`unsat` transfers to the original"* — so the capability is a reach extension of
a route that exists, not a new trust assumption.

Two directions in which 16,245 is still wrong, stated before the build so
neither is a retrofit (and see the A/B section below for how each landed):

* **Down.** It credits each division the rate measured on its *winnable* set —
  files where a reference decides and we do not. The blocked population is
  larger than the winnable one and no harder-file discount is applied.
* **Up.** It assumes the routing above exists. With only the parse refusal
  lifted and every array route still refusing a nested sort by construction, the
  reach is whatever the measurement after the build says — which is the number
  this lane is obliged to publish next to this one.

## What the build reached — the A/B

The IR change landed (ADR-1965). Interleaved per-file A/B against `main` at
`f9075838e`, both arms back to back on the same pinned core with the arm order
alternating per file, 24 s budget, over the **pinned full-span 200-file parity
lists** in `../parity-lists/`.

| division | files | `main` | this lane | moved | regressed |
|---|---:|---:|---:|---:|---:|
| **AUFLIRA** | 200 | 9 | **159** | **+150** | 0 |
| **AUFNIRA** | 200 | 3 | **122** | **+119** | 0 |
| ALIA | 200 | 0 | 0 | 0 | 0 |
| ABV | 200 | 4 | 4 | 0 | 0 |
| QF_ABV (control) | 200 | 188 | 187 | 0 | 1† |
| QF_BV (control) | 200 | 186 | 186 | 0 | 0 |

All 269 moved verdicts are `unsat`, and **both references agree with every one
of them**, with no file where either has no opinion:

```
z3    agrees 269 / 269, no opinion 0, CONTRADICTS 0
cvc5  agrees 269 / 269, no opinion 0, CONTRADICTS 0
```

That "no opinion 0" is what ADR-1957 requires beside a zero-disagreement claim:
every one of the 269 agreements was an opportunity for the check to fire.

† The one raw regression is a **timeout boundary**, re-checked rather than
argued away. `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_stty…` needs
about 25 s, so at 24 s it flips for whichever arm the machine favours. Three
interleaved re-runs at 24 s: base `unknown`/`unknown`/`unknown`, lane
`unknown`/`sat`/`unknown`. Three at 96 s: **both arms `sat`, three of three** —
base 25.02 / 25.22 / 24.82 s, lane 25.22 / 24.52 / 24.42 s.

AUFLIRA was also run twice end to end (the first pass used a binary that
differed at one call site, so it was discarded and re-run). Both passes moved
the same population: 149 and 150 files, a one-file difference that is the
documented ~1 % ambient flip rate at a 24 s budget.

### Re-measured after `main` moved under the lane

`main` gained ADR-1960 (the Real-element array gate) and ADR-1966 (the ground
ladder's decline rule) while this lane was running, so the A/B above describes
a merge that no longer exists. It was run again, end to end, with the **merged
branch** as the lane arm and **`main` at `9c24786d0`** as the baseline arm:

| division | files | `main` `9c24786d0` | merged | moved | regressed |
|---|---:|---:|---:|---:|---:|
| **AUFLIRA** | 200 | 10 | **164** | **+154** | 0 |
| **AUFNIRA** | 200 | 3 | **122** | **+119** | 0 |
| ALIA | 200 | 0 | 0 | 0 | 0 |
| ABV | 200 | 4 | 4 | 0 | 0 |
| QF_ABV (control) | 200 | 188 | 188 | 0 | **0** |
| QF_BV (control) | 200 | 186 | 186 | 0 | **0** |

```
273 moved files, all `unsat`
z3    agrees 273 / 273, no opinion 0, CONTRADICTS 0
cvc5  agrees 273 / 273, no opinion 0, CONTRADICTS 0
```

**Zero regressions anywhere**, including the QF_ABV boundary file, which the
pre-merge pass had flagged and the re-check had already shown was ambient.
AUFLIRA gains five more than the pre-merge pass (164 against 159) and the
baseline gains one (10 against 9); AUFNIRA is identical in both passes. Both
passes are committed, because a number that moves between two honest runs is
information about the measurement, not noise to be hidden.

### The surrogate against the build

| | AUFLIRA | AUFNIRA | ALIA | ABV |
|---|---:|---:|---:|---:|
| surrogate reach, winnable denominator | 80.6% | 95.0% | no fragment | no fragment |
| measured moved, winnable denominator | **82.4%** | **85.6%** | 0 | 0 |
| measured moved, of 200 | 77.0% | 59.5% | 0 | 0 |

AUFLIRA came in **above** its prediction; AUFNIRA 9 points below it.
For ALIA and ABV the surrogate refused to produce a number at all — 33 of 36 and
12 of 17 of their winnable files write the outer array — and the build moved
nothing there. **That is the agreement that matters most:** an instrument that
had produced a confident number for a population it could not model would have
been the more dangerous one.

## Files

| file | what it is |
|---|---|
| [`nested_array_surrogate.py`](nested_array_surrogate.py) | the rewrite, its soundness argument, and its self-test |
| [`surrogate-sweep.sh`](surrogate-sweep.sh) | one division through axeyum + z3 |
| [`surrogate-launch.sh`](surrogate-launch.sh) | all four, pinned, board budget |
| [`surrogate-summarize.py`](surrogate-summarize.py) | the re-size table, plus the soundness check on the rewrite |
| `sweep/` | the per-division surrogate TSVs |
| [`ab-run.sh`](ab-run.sh) | one division, both arms interleaved per file |
| [`ab-launch.sh`](ab-launch.sh) | four target divisions plus two controls, pinned |
| [`ab-summarize.py`](ab-summarize.py) | the A/B table, the regression list, and `--refs` for the z3/cvc5 cross-check |
| `ab/` | the per-division A/B TSVs against `main` at `f9075838e` (the branch point) |
| `ab-postmerge/` | the same A/B re-run against `main` at `9c24786d0` after the merge, plus its `reference-crosscheck.txt` |
