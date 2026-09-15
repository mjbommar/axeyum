# ADR-2102: the outcome ledger — one append-only table, written by three sweep shapes, so the question a lane spent a day on becomes a query

Status: accepted
Index-summary: Phase 3 of `docs/plan/dispatch-and-instrumentation-2026-09-15.md`. Every sweep in the preceding week computed `(file → route that decided → elapsed → routes declined and why)` and threw it away after grepping ONE token — `raw=$(timeout … "$AX" "$f")` then a bare-verdict `grep`, in THREE independent harnesses, none of which passes `--trace`, so even a kept capture would have carried no routing lines. PLAN-SIZING re-ran **645** undecided Tier 1 rows to recover exactly that. Decision: **one append-only table, one library that is its only writer and only reader, one shared per-file runner the sweeps call instead of inlining the capture.** 19 columns, the plan's §4 list; `exit_status` its own column ([ADR-2045] measured `losses=0` by verdict with five new ABORTS underneath); `corpus_path` never a basename (370 of the board's 3,200 are ambiguous). **Three columns carry a THIRD value and each third value is a bug already shipped here**: `partial` is yes/no/**unknown** (a capture with no trail cannot say), `features` is a class list/`none`/**empty**/**`not-dispatched`**, and `sha_status` is main/branch/**unknown-commit**. TSV over JSONL deliberately — exit criterion 2 `join`s ledger rows against committed board TSVs, and a ledger nobody can `cut`-check by hand is worse than one with an escape function; the separator hazard ([ADR-2020]) is answered by one `_escape`/`_unescape` pair with a hostile fixture that ASSERTS its own hostility. Three writers append, **none of them formats a row**, so schema drift at a writer is unreachable rather than tested for. The `features` column needed one line of Rust: the ladder's own construct scan now records itself (one relaxed compare-exchange, first writer wins) and the CLI prints one extra `--trace` line naming the classes — re-deriving it from `.smt2` text in Python would have been a second authority that drifts, the exact shape all five instruments in the plan's §0 failed in. Measured: **220 rows** across seven sweeps on s5/s6; **verdict invariance 100 of 100, 0 MOVED**; ADR-2065's 14 movers reproduced EXACTLY (**arm A 0 / arm B 14**, split `q:mbqi-quick` 8 / `q:bool-skeleton` 6, `lira-dpll` 0) with the base arm's tree CHECKED to predate the ADR rather than assumed to; ADR-2045's **74 of 93** re-derived from the committed census (40 aborts + 34 Fourier–Motzkin), and **59 of 93** on today's tree, a move the sparse-simplex entry between the two binaries explains and which is reported as a finding about the TREE; ADR-2075's nine reproduce as **7 of 9 partial, identical across three passes with the SAME two exceptions**, both completing their ladder at 23.3 s and 24.7 s of a 24 s budget — and one of them is precisely the file [ADR-2101] showed ADR-2075 had mis-attributed, an independent confirmation reached by a different route. Staleness fires on REAL rows in both directions (`2611e14b0` main, `cb460e737` branch, 20 of 40 flagged, `load()` refusing without `--allow-branch`). Mutation: 3 registered, **3 killed**, two of them exactly one named test — and the third **SURVIVED on its first run**, which was the finding: deleting the `cat-file -e` existence check left all 31 tests green because `merge-base --is-ancestor <garbage>` exits non-zero by itself, so the guard was real and unfalsifiable at once; it became falsifiable when the classification went three-valued. Stated rather than implied: `features` names the FIRST quantifier-free dispatch's fragment, which on a quantified file is a sub-solve's and not the file's (6 of 20 arm-B rows record `none` on files full of arrays and reals), and **the ledger does not replace the A/B** — a delta between two single-arm ledger runs at different loads is the 77/79/85 error with a database in front of it.
Index-status: accepted
Date: 2026-09-15

## Context

`docs/plan/dispatch-and-instrumentation-2026-09-15.md` §0 ends with one
sentence about what does not exist: *"Any accumulation of outcomes across runs.
Every sweep this week produced `(file → route that decided → elapsed → routes
declined and why)` and discarded it after one comparison."*

That is not a gap somebody noticed while tidying. It is measured, three times,
in the week before this lane:

| receipt | what the missing table cost |
|---|---|
| [PLAN-SIZING] | re-ran **645** undecided Tier 1 rows to recover routing the original sweep had already computed |
| [ADR-2035] | re-derived 22 "declining" rows to find 8 of them decided anyway |
| [ADR-2050] | re-derived 13 rows one at a time to check a list it had inherited |

And the reason is one line of shell, in three independent harnesses:

```sh
raw=$(timeout … "$AX" "$f" 2>/dev/null)
v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
```

The stdout goes into a shell variable, one token comes out, the rest is
dropped. PLAN-SIZING checked whether this was one script's bug and found the
same discard-after-grep in `quant-rounds/route-hit.sh`,
`tier1-divisions/shard-run.sh` and `nested-array-ir/shard-run.sh`: it is the
harness convention. And the second half is worse than the first — **none of
them passes `--trace`**, so even a kept capture would have carried no routing
lines at all.

## Decision

One append-only table, one library that is its only writer and its only
reader, and one shared per-file runner that every sweep shape calls instead of
inlining the capture.

### The schema, and the three columns that are not booleans

Nineteen columns, the plan's §4 list exactly:

```
sweep_id  arm  corpus_path  binary_sha  features  verdict  exit_status
decided_by  bound_by  attempts  attempt_trail  elapsed_ms
elapsed_ms_per_attempt  partial  decline_reasons  decline_details
host  core  load
```

Three of them carry a **third value** rather than a boolean, and each third
value is a bug this repository has already shipped:

- **`partial` is `yes` / `no` / `unknown`.** A capture with no trail line at all
  cannot say whether the reading was a total. Recording that as `no` is
  [ADR-2075]'s collapse from the other side — the watchdog rows swept into an
  aggregate that thought it had totals.
- **`features` is a class list / `none` / `not-dispatched` / the empty string** —
  four values, because there turned out to be four different things to say.
  Empty means the binary predates this ADR's `; features` line and cannot be
  asked; `not-dispatched` means it printed the line and said the query never
  reached the quantifier-free ladder, so the scan never ran; `none` means the
  scan ran and the set was empty. A pure Boolean query, a quantified file whose
  ladder was never reached, and a 2026-09-14 build are three different findings.
  `not-dispatched` was added after the first sweeps, on the evidence of a
  `UFLIA` row that ran 20 quantified rungs and recorded nothing — and
  [ADR-2100] measured that shape at **482 of 643** undecided Tier 1 rows, so it
  is the common case rather than an edge one.
- **`sha_status` is `main` / `branch` / `unknown-commit`** (the staleness rule,
  below).

`exit_status` is its own column and never folded into `verdict`, because
[ADR-2045] measured `losses=0` by verdict with **five new aborts** underneath
it. A run that printed no verdict token and exited non-zero gets
`verdict=abort`, which is an outcome and not an absence.

`corpus_path` is the corpus-RELATIVE path and never a basename. The
16-division board records basenames and **370 of its 3,200** resolve to more
than one corpus file, which is why its own README says the population "is not
reconstructible from what is committed."

`elapsed_ms` is the runner's WALL clock and `elapsed_ms_per_attempt` is the
trail's. On a partial reading the two are supposed to disagree — the gap is
the open segment no attempt accounts for, and keeping them in one column would
hide exactly the quantity [ADR-2075] needed.

### TSV, not JSONL

JSONL needs no escaping invented and would make [ADR-2020]'s separator bug
structurally unreachable. That is a real argument and it lost, for reasons
about how measurements get CHECKED here rather than about elegance:

- every board, census and sizing artifact in this repository is a TSV —
  `phase1-ceiling.tsv` is already 645 rows in nearly this shape — and exit
  criterion 2 below literally `join`s ledger rows against those files by
  `corpus_path`;
- `cut -f`, `sort`, `join` and `awk` are how every number here gets
  spot-checked, and a ledger nobody can spot-check by hand is a worse ledger
  than one with an escape function;
- the separator hazard is answered by making the library the only writer and
  the only reader, with **one** `_escape`/`_unescape` pair and a hostile
  round-trip fixture — tab, newline, CR, `|`, `;`, `=`, quote, backslash — that
  asserts its own hostility before using it.

### Three writers, and why the schema cannot drift at one

`scripts/ledger-run-one.sh` runs ONE file under the caller's envelope with
`--trace`, keeps the stdout as a file, and appends one row through
`scripts/outcome_ledger.py`. The three sweep scripts in `scripts/ledger-sweeps/`
call it; **none of them formats a ledger row**, so "a writer emits a column the
library does not know" is unreachable rather than merely tested for. The
control suite derives its writer population by globbing that directory rather
than from a list, so a fourth writer is covered the day it lands.

Each writer mirrors an existing runner shape and keeps that runner's own TSV,
so the summarizers downstream of it still work:

| writer | mirrors | what the ledger adds |
|---|---|---|
| `lane-ab-run-ledger.sh` | [ADR-2100]'s `ab-run.sh` | the capture; the same-binary sha256 refusal is kept, plus a refusal when both arms claim one commit |
| `board-ab-run-ledger.sh` | `ab-two-bins.sh` (the 16-division board) | the capture, the corpus-relative path, and `rc` as a column |
| `t1-board-run-ledger.sh` | `board-run.sh` (Tier 1 single-arm) | the capture and `--trace`, the two things PLAN-SIZING had to re-run 645 rows to get |

### `--trace` and verdict invariance

PLAN-SIZING measured 644 of 644 verdicts unchanged by adding `--trace`. That is
a measurement and not a guarantee, so `ledger-run-one.sh` carries
`--no-trace-control`: it re-runs the same file on the same binary WITHOUT
`--trace` and prints `INVARIANCE ok|MOVED`. A sweep counts it rather than
inheriting it.

### The staleness rule

A row whose `binary_sha` is not an ancestor of LOCAL `main` is flagged on load,
and `load()` raises unless `allow_branch=True`. Local `main` deliberately:
`origin/main` lags during a push window, and a commit on local main that is not
yet pushed is not a branch measurement.

The flagged rows are still RETURNED. A lane's own in-flight A/B is a legitimate
thing to read; what is not legitimate is reading it as a main measurement
without noticing.

### The `features` column needed one line of Rust

The construct scan the ladder already runs ([ADR-2100]'s `Features`) had no
route out of the dispatcher. The alternative was to re-derive the
classification from `.smt2` text in Python — a second authority that drifts
from this one, which is the exact shape all five instruments in the plan's §0
failed in. So `route_ownership` records what it already computed
(`record_query_constructs`, one relaxed compare-exchange, **first writer wins**
so a sub-solve cannot overwrite the query the file states) and `smtcomp_cli`
prints one extra `--trace` line:

```
; features Int|Function|UninterpretedSort
; features none
```

`|` and never `;`, and no line at all when nothing was dispatched. It is
printed on the watchdog path too and is NOT marked `; partial ` — the scan runs
once, before any rung, and a kill cannot catch it half-done. A killed file is
exactly where the column earns its place: *"which routes could ever have owned
this query"* is the first question about a file nothing decided.

## What this does NOT do

**It does not replace the A/B.** The ledger records; the interleaved A/B is
still how a claim is made. The same binary scored 77, 79 and 85 on one division
in a single day purely on ambient load, so a delta computed between two
single-arm ledger runs at different loads is that error with a database in
front of it. Every aggregate here carries `binary_sha`, `host`, `load` and
`partial` for that reason, and `verdict_counts` REFUSES a population containing
a partial or unknown-completeness reading unless told.

**It derives no ladder order and no budget constant.** That is Phase 4, and its
minimum is this repository's minimum for claiming a gain: three passes per arm,
a published noise floor, and an interleaved comparison.

## Measurements

Seven sweeps, **220 rows**, on s5/s6, one pinned physical core pair each, 24 s
wall / 8 GiB `ulimit -v`, `--trace` on. Arms are `2611e14b0` (a `main`
ancestor) and `cb460e737` (this lane's branch). Every figure below is produced
by `bench-results/ledger-20260915/rederive.py`, whose **exit status is the
finding** and which exits 0.

| writer | sweeps | rows |
|---|---|---:|
| `lane-ab-run-ledger.sh` | `ab-movers-20260915` | 40 |
| `board-ab-run-ledger.sh` | `board-qflra-20260915` | 40 |
| `t1-board-run-ledger.sh` | `t1-uflia`, `qflra93`, `partial9` ×3 | 140 |
| | | **220** |

Every file's header is checked against the library's 19-column schema per
sweep, not once.

### Verdict invariance: 100 of 100, 0 MOVED

Every file in all three smoke runs was also run WITHOUT `--trace` on the same
binary and the verdicts compared:

| sweep | ok | MOVED |
|---|---:|---:|
| `ab-movers-20260915` | 40 | **0** |
| `board-qflra-20260915` | 40 | **0** |
| `t1-uflia-20260915` | 20 | **0** |
| **total** | **100** | **0** |

### (a) ADR-2065's 14 `AUFLIRA` movers — reproduced exactly

The base arm has to predate the ADR or the comparison is vacuous, so that is
CHECKED rather than assumed: `git cat-file -e 2611e14b0:<the ADR's path>` fails,
so the file is absent from that tree.

| | ledger | ADR-2065 |
|---|---:|---:|
| arm A (pre-ADR-2065) decides | **0** of 14 | 0 |
| arm B (this tree) decides | **14** of 14 | 14 |
| net | **+14** | +14 |
| decided by `q:mbqi-quick` | **8** | 8 |
| decided by `q:bool-skeleton` | **6** | 6 |
| decided by `lira-dpll` (the route that was refusing) | **0** | 0 |

The `features` column separates the arms exactly as designed: arm A's is the
ABSENT value on all 14 (`feature_classes` answers `None`, not `[]`), arm B's is
a real class list — `Real|Int|Array|NonBvArray|NonBoolBvArray`,
`…|NestedArray`, `Int`, and `none`.

### (b) ADR-2045's 74 of 93 — 74 re-derived, 59 on today's tree

The 74 is re-derived from the **committed census** first, so the target is a
number this script computed rather than one it quoted:

| | |
|---|---:|
| undecided rows in `qflra-gap-20260914/census-rows.tsv` | **93** |
| of which `ABORT/oom` on the offline engine's allocation | **40** |
| of which exhausting the clock with the Fourier–Motzkin string | **34** |
| ONE ROUTE | **74** |

All 93 re-run through the ledger on `cb460e737`, and all 93 still undecided:

| | ledger, this tree | ADR-2045, its own tree |
|---|---:|---:|
| `verdict=abort` | **41** | 40 |
| decline details naming Fourier–Motzkin | **18** | 34 |
| the union — "one route" | **59** (63.4 %) | 74 (79.6 %) |

`bound_by`: `nra` 46, `none` 41, `dl-online` 4, `fd:parse` 2.

**The move is a finding about the TREE, not about the ledger**, and it is in the
expected direction: the LRA sparse simplex entry landed after ADR-2045 and
between these two binaries, and sixteen rows that used to exhaust the clock
inside the offline dense engine now bind elsewhere. What the ledger pins without
a tree-dependent number is that all 93 are still undecided, which is the
population's defining property.

### (c) ADR-2075's nine — 7 of 9, stable, and one exception confirms ADR-2101

Three passes, same envelope, same pinned core:

| pass | `partial=yes` |
|---|---:|
| `partial9-20260915` | 7 |
| `partial9-p2-20260915` | 7 |
| `partial9-p3-20260915` | 7 |

One draw cannot separate a tree change from a scheduling one, so what is
asserted is the STABILITY — an identical count, and **the same two files** as
the exceptions in all three passes. Both are on the wire: their ladder COMPLETES
inside the 24 s budget instead of being killed.

| file | wall | attempts |
|---|---:|---:|
| `UFNIA/2019-Zohar-ic/full/int_check_bvslt_bvurem1_ltr_no_inv.smt2` | 24,735 ms | 18 |
| `UFNIA/sledgehammer/Hoare/z3.850818.smt2` | 23,333 ms | 21 |

The second is exactly the file [ADR-2101] showed ADR-2075 had mis-attributed —
*"the committed receipt for that file took a different give-up path
(`ResourceLimit`, not `Watchdog`) and prints 0 `; partial ` lines"*. This is an
**independent confirmation of that correction from a fresh run**, reached by a
different route: ADR-2101 read the committed receipt, this one produced a new
one.

`verdict_counts` REFUSES this population as totals, and 0 of the nine carry
`partial=unknown` — a capture with no trail at all would land there, not in
`no`.

### (3) The staleness rule, fired in both directions on real rows

Not a fixture: the A/B sweep carries both binaries.

| `binary_sha` | classified | flagged |
|---|---|---|
| `2611e14b0` | `main` | no |
| `cb460e737` | `branch` | **yes, 20 of 40 rows** |

`load()` raises `StaleRows` without `--allow-branch`; with it, all 40 rows come
back AND all 20 are still flagged.

### Mutation

`SUITES["outcome-ledger"]`, three mutations, **all three killed**:

| mutation | tests killed |
|---|---:|
| the intra-field separator stops being escaped | 2 |
| a reading that cannot state its completeness is summed as a total | **1** |
| an unknown commit is reported as a branch | **1** |

The first kills two and that is reported rather than tuned down to one: the two
tests pin the escape's OUTPUT and the round trip through a real row, and
narrowing either to make the count one would weaken a guard to flatter a number.

**The third mutation SURVIVED on its first run, and that was the finding.**
Deleting the `cat-file -e` existence check left all 31 tests green, because
`git merge-base --is-ancestor <garbage> main` exits non-zero on its own and the
row was still FLAGGED. The guard was real and unfalsifiable at the same time. It
is falsifiable now because the classification went three-valued: a reader is
told `unknown-commit` instead of being sent to look for a branch that does not
exist.

### What `features` actually names, said before anyone quotes it

The column is the construct set of the **first query the quantifier-free
dispatch ladder scanned**, which on a quantifier-free file is the file's query
and on a QUANTIFIED file is the first sub-solve's fragment —
`check_with_quantifiers` runs first and the ladder is only ever reached from
underneath it. Measured here: **6 of the 20 arm-B rows** in the `AUFLIRA` A/B
record `none` on files full of arrays and reals. A top-level scan does not exist
to record instead, and inventing one would mean running the scan on every query
for the benefit of a telemetry column.

Two other absences the column distinguishes, both present in these rows: one
`UFLIA` row records **no line at all** from a binary that prints one, because 20
quantified rungs ran and the quantifier-free ladder was never reached — and nine
`QF_LRA` rows record nothing because the process OOM-aborted before any output.
The first of those is now its own token, `; features not-dispatched`, added
after this evidence was collected; the 220 committed rows predate it, so an
empty `features` in THEM is either "old binary" or "never dispatched".
[ADR-2100] measured the second case at **482 of 643** undecided Tier 1 rows, so
it is the common case and not an edge one.

## Consequences

* "Which files does route X decide, in how long, on what features, and did that
  change at commit Y" is a query over `bench-results/ledger/*.tsv` rather than
  a lane.
* Phase 4 has a table to derive from, and the three columns it needs —
  `features`, `decided_by`, `elapsed_ms_per_attempt` — are all in it.
* A branch measurement cannot be quoted as a main one without the reader being
  told, and a row from a commit this repository has never seen is reported as
  `unknown-commit` rather than as a branch somebody could go and look at.
* `features` is empty on every row from a pre-ADR-2102 binary and is not
  backfillable — the scan lives inside the binary. That is the column's absent
  value and is distinguishable from `none`.

## Alternatives rejected

**JSONL.** See above: the deciding factor is that exit criterion 2 joins ledger
rows against committed board TSVs, and that every check of a number here is a
`cut`/`join`/`awk` away.

**Let each sweep format its own row.** Rejected: that is precisely where a
column the library does not know would come from, and the three runners this
lane wired are already three copies of one inlined pipeline.

**Re-derive `features` in Python from the `.smt2` text.** Rejected: a second
authority for a classification the dispatcher already computes. Every one of
the five instruments the plan's §0 catalogues failed by having a producer and a
consumer that nothing typechecked against each other.

**Make the ledger the board.** Rejected explicitly, in the plan's own §7 risk
list and again here. A ledger row is an observation under stated conditions,
not a level.

[PLAN-SIZING]: ../../../bench-results/dispatch-plan-sizing-20260915/README.md
[ADR-2020]: adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
[ADR-2035]: adr-2035-two-populations-reach-one-boundary-and-a-round-cap-can-convert-neither.md
[ADR-2045]: adr-2045-the-bound-is-not-the-wall-qf-lra-is-one-offline-dense-engine.md
[ADR-2050]: adr-2050-the-eleven-are-four-causes-and-the-largest-is-one-refused-atom.md
[ADR-2065]: adr-2065-the-real-collector-can-hold-a-term-and-the-sat-exits-close-by-type.md
[ADR-2075]: adr-2075-the-silent-hang-is-not-silent-it-is-the-inventory-of-code-that-polls-no-deadline.md
[ADR-2100]: adr-2100-typed-route-ownership.md
[ADR-2101]: adr-2101-the-trace-is-the-api.md
