# QF_LIA addressable-gap census — 2026-09-12, lane `QF-LIA-GAP`

The first census of `QF_LIA`'s addressable gap. **All 55 winnable files, not a
sample** — the lists in `bench-results/` are path-sorted, so a prefix or a small
draw is a sample of one benchmark family rather than of the division.

## Population

`bench-results/session-20260911-smtlib/head-to-head/QF_LIA.tsv`, the 24 s
three-way board over the pinned 200-file list
(`bench-results/parity-lists/QF_LIA.txt`). "Winnable" = we return `unknown`
and at least one of z3 4.13.3 / cvc5 1.3.4 decides: **55 of 200**.

Re-derived from the board rather than inherited, because the brief's framing
("best-of is 172, gap 53") is the **z3-only** row: on this board
**axeyum 119, z3 172, cvc5 139, best-of-reference 174**, and we decide
**0** files neither reference decides. So the gap against best-of-reference is
**55**, the same number as the winnable set — every file we lose, a reference
wins, and there is no offsetting column.

**Name the reference when quoting this gap.** Against z3 alone it is 53;
against cvc5 alone, 22.

The board carries basenames only and **basenames are not unique in this
division** (`problem_2__026.smt2`, `prp-35-43.smt2`, ten `RC-*.smt2` …), so the
full paths in `winnable-55.txt` were recovered by joining the board to the
pinned list **by line order**, and the join was checked by comparing all 200
basenames — 0 mismatches.

## Method

`smtcomp_cli --timeout-ms 24000 --trace`, one process per file, pinned to
`taskset -c 0-7` (the P-cores of this 12600K; the E-cores are 1.84x slower and
mixing the two moves wall times).

Wrapper bound **120 s** around a 24 s budget — deliberate headroom. A previous
census used +8 s under load, killed 17 processes and produced rows that read as
"no reason". **No row here is `wrapper-killed`:** all 55 ran to their own
conclusion, so no bucket is a measurement artifact.

Box load at launch 0.88; it rose to ~15 during the run from other lanes' builds.
That can only move a *borderline* file across the budget, and 49 of 55 spend
23 s or more, so it does not move the reason distribution.

## THE CENSUS IS OF THE DISPATCH LADDER ON 30 OF 55 FILES

Before ranking any reason, `attempts=` in `--trace` was compared against the
ladder length. A completed `QF_LIA` dispatch records **16** attempts.

| `attempts=` | files | what it means |
|---|---:|---|
| none (no trail) | 1 | killed during INGEST; not even `fd:parse` recorded |
| 2 | 23 | `fd:parse`, `probe`, then nothing — **the ladder never ran** |
| 3–5 | 5 | died in the first few rungs |
| 13–16 | 26 | the ladder ran to the end |

**So 30 of 55 rows are a fact about which rung hangs first, not about what the
query needs.** This is ADR-1927's shape again. The corrected census — the same
55 files once the rung that hangs is fixed — lands with the fix, as `census-fixed.tsv`.

## The base census (`census-base.tsv`)

| cause | files |
|---|---:|
| **watchdog: un-instrumented phase right after `probe`** | **23** |
| search: lazy LIA CDCL(T) rounds hit the wall clock | 7 |
| search: LIA branch-and-bound hit the wall clock | 6 |
| search: LIA `sat`-model reconstruction hit the wall clock | 5 |
| admission: `lia-dpll` pre-SAT skeleton boundary | 4 |
| boundary: `i128` overflow in the exact-rational simplex | 3 |
| watchdog: un-instrumented phase after `cas-int-units` | 2 |
| watchdog: un-instrumented phase after `dl-online` | 1 |
| watchdog: inside `dpll-lia:justified-support` | 1 |
| watchdog: inside `dl-online:check` | 1 |
| watchdog: INGEST (parse is outside `--timeout-ms`) | 1 |
| other: lazy LIA SAT skeleton declined after round 317 | 1 |
| **no reason at all** | **0** |

All 23 files in the top row are `nec-smt/`'s `prp-*` family, and the phase
breadcrumb reads `stack=none depth=0` on every one of them — the worker was
outside every instrumented frame for the whole budget.

## What the top row is

`perf` leaf profiles, three files from three different `nec-smt` directories:

| file | share of the run in `term_identity::identity_normal_form` |
|---|---:|
| `checkpass_pwd/prp-17-34.smt2` | **99.81 %** |
| `getoption_directories/prp-9-46.smt2` | **97.43 %** |
| `getoption/prp-2-200.smt2` | **95.38 %** |

`term_identity_refutation` is the **second rung** of `check_auto`'s dispatch, it
takes **no deadline**, and it records **no route attempt** — which is exactly why
the trail says `attempts=2` and the breadcrumb says `stack=none`. Its
`identity_normal_form` descended both branches of every non-constant `ite`
without a memo, so on a `let`-shared DAG it is exponential in the nesting depth.
The `prp-*` family is 27 of the 55 winnable files (23 in this bucket, 4 further
down the table); they carry 25–372 integer variables and **519–11,162 `ite`
terms** over one deeply `let`-shared assertion.

## Columns

`census-base.tsv` / `census-fixed.tsv`: `file, outcome, verdict, secs, attempts,
decided_by, bound_by, last, open_ms, open_after, phase_in, phase_depth,
phase_deepest, phase_enters, giveup_kind, giveup_detail, class, bucket`.

`outcome` is the wrapper's own verdict (`ok` / `wrapper-killed` / `rc<N>`), so a
measurement failure can never be read as a solver result.
