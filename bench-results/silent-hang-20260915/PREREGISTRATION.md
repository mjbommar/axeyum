# SILENT-HANG — pre-registration

Written **before** any measurement on this lane's binary. The build was
launched first and was still compiling when this file was committed; nothing
below was written with a result in hand.

Branch base: `git merge-base main HEAD` is
`33c23a2fb0461fe71bf8f130289e597290e36d02`, which **is** local `main`'s HEAD.

## The subject

[ADR-2040] §8 and [ADR-2050] §4(C) both name the same untouched bucket and both
declined it:

> 12 undecided `UFNIA` rows have **no route line at all** — the watchdog fired
> before the worker thread returned.

The population is re-derived here from
`bench-results/skeleton-reach-20260914/ref/fd-census-208.tsv`: the rows whose
`verdict` is `unknown`, whose `bound_by` is `NONE`, and whose `giveup_kind` is
`Watchdog`. That is **13** rows — 12 `UFNIA` and 1 `UFLIA` — and the `UFLIA`
one is [ADR-2050]'s `f06`. The list is `lists/population-13.list`; it is derived
by a script from the committed census, never typed.

**This bucket is defined by an ABSENCE.** That is the whole methodological
problem and R2 exists for it.

## The rules

| | rule |
|---|---|
| **R1** | The inherited population is **re-derived on this branch** before it is counted. A row that no longer presents `bound_by=NONE` + `kind=Watchdog` is reported as re-derived-OUT, in its own column, never silently kept or silently dropped. |
| **R2** | **No conclusion of the form "the instrument reports nothing" is admissible without a POSITIVE CONTROL**: the same command, the same parser, on a row that DOES produce the thing said to be missing, shown to produce it. An empty result from an instrument never shown to fire is indistinguishable from a strong negative and is not evidence. |
| **R3** | Every bucket is published with its denominator. `NOT-MEASURED` and `DID-NOT-RUN` are columns of their own, never folded into a zero. |
| **R4** | A cause is named by **mechanism** — a sampled stack, a phase frame, a counter — never by a give-up label. If a label covers more than one program point, it is split before it is counted. ([ADR-2020]'s separator, [ADR-2040]'s `fd:parse`, [ADR-2060]'s 28 points behind 6 names.) |
| **R5** | Where the time goes is established by **profiling**, not by reading code. Any claim about which code runs cites a sampled stack or a live phase frame **with its sample count**. |
| **R6** | The watchdog's adequacy is decided by **naming, in advance, the observation that distinguishes** (a) the worker making progress, (b) the worker in a non-terminating loop, (c) the worker thrashing memory — and then taking that observation. A deadline passing decides none of the three. The named observations are in the next section. |
| **R7** | An **exit-status channel** is carried separately from verdicts. A row whose process dies is not a row that answered `unknown`. ([ADR-2045] was `losses=0` by verdict while creating five new aborts.) |
| **R8** | Wilson 95 % on every proportion. n ≈ 13 makes the interval wide; it is quoted, not hidden. |
| **R9** | Verdicts are checked against independent authorities with **comparable denominators printed beside any zero**, no-opinion counted separately ([ADR-1957]). `z3 -T:` is SECONDS, `cvc5 --tlimit` is MILLISECONDS. |
| **R10** | **No lever is built unless the profile names ONE bounded site.** A clean characterisation with no code is a complete lane. |
| **R11** | Every measurement is of **this branch**; the post-merge value is predicted explicitly. |
| **R12** | Binary freshness is established by `find -newer` against `crates/**/*.rs`, never by a build's exit status. Snapshot and target paths are reused on this box. |
| **R13** | No waiter greps for a process by a pattern its own command line contains. |
| **R14** | A check that did not finish is reported as **"did not run"**, never as an intention. |
| **R15** | A wall-clock timeout bounds **neither memory nor progress**. Every row's **peak RSS** is recorded, and every run that may expand carries an explicit ceiling. (A lane's `let`-expander reached 63.4 GB under a `timeout` and took the host down.) |
| **R16** | If a route change is built, the **fixture suites** run — an A/B over corpus rows is not a superset of them ([ADR-2065]). Interleaved per-file A/B, one binary two env values, arms back to back with alternating order, polarity in the runner header, 3 passes per arm on every moved row, and a published noise floor. |

## R6, discharged in advance: the three observations

The watchdog reports one bit — a deadline passed. These are the observations
that separate the three explanations, each named here **before** it was taken:

| explanation | the observation that distinguishes it |
|---|---|
| **(a) progress** — the worker is working and 24 s is simply not enough | the verdict **changes with the budget**: rerun at 24 s / 120 s / 600 s and see whether any row decides. A row that decides at 600 s is a budget row, not a hang. |
| **(b) stuck** — a loop that will never finish | the **live phase breadcrumb** (`; partial phase … in=<label> in_ms=<n> enters=<label>:<count>`), read from the watchdog thread while the worker is still inside the frame. `in_ms` ≈ the whole run on one frame is one long call; a huge `enters` count on a frame not currently on the stack is a re-entering loop. Plus a **sampled stack** (`perf record` on the live process), where a single hot cycle shows as one dominant call chain. |
| **(c) thrash** — allocating, not computing | **peak RSS** (`VmHWM`, which the span log already reads on the killed path) and the **`perf` `page-faults` / `minor-faults` count** against cycles. A run at 20 GB RSS with most samples in `malloc`/`memcpy`/`realloc` is thrashing; a run at 200 MB with samples in a solver loop is not. |

Additionally, the process-level channel: `/proc/<pid>/status` sampled on a
cadence gives RSS over time, and `/proc/<pid>/task/<tid>/stat` gives per-thread
utime — a worker at 100 % CPU is running, a worker at 0 % is blocked, and the
watchdog cannot tell those apart.

## Predictions

Recorded now so they can be wrong.

| | prediction |
|---|---|
| **P1** | The 13 are **not one cause**. At least two distinct innermost phases, or at least one row with no phase frame at all against at least one with one. |
| **P2** | At least one row will show **`stack=none`** — the worker outside every instrumented phase. All 41 `phase_breadcrumb::enter` sites are in `axeyum-solver` theory routes; **none** is in `axeyum-smtlib` (parse/ingest), `axeyum-rewrite`, or the quantifier ladder. A hang in any of those is invisible to the breadcrumb, and that would be a finding about the instrument, not the solver. |
| **P3** | At least one row's peak RSS exceeds **4 GB**. |
| **P4** | The profile's dominant frame is **not** in the CDCL SAT core. |
| **P5** | **At most 2** of the 13 re-derive out of the bucket on this branch. |
| **P6** | Raising the budget from 24 s to 600 s decides **at most 3** of the 13. If it decided most of them the bucket would be a budget bucket and there would be nothing to diagnose. |

[ADR-1957]: ../../docs/research/09-decisions/adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-2020]: ../../docs/research/09-decisions/adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
[ADR-2040]: ../../docs/research/09-decisions/adr-2040-the-reach-half-is-worth-two-and-the-whole-remaining-shape-is-the-ground-checker.md
[ADR-2045]: ../../docs/research/09-decisions/adr-2045-the-bound-is-not-the-wall-qf-lra-is-one-offline-dense-engine.md
[ADR-2050]: ../../docs/research/09-decisions/adr-2050-the-eleven-are-four-causes-and-the-largest-is-one-refused-atom.md
[ADR-2060]: ../../docs/research/09-decisions/adr-2060-the-give-up-variant-could-not-tell-six-gates-apart-and-nothing-asked-it-to.md
[ADR-2065]: ../../docs/research/09-decisions/adr-2065-the-real-collector-can-hold-a-term-and-the-sat-exits-close-by-type.md
