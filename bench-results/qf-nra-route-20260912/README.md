# QF_NRA — census of all 77 winnable files, 2026-09-12

Lane `qf-nra-route`. This directory holds the **population**, the **method**,
and the **raw per-file attribution** behind the QF_NRA row of the
2026-09-11/12 head-to-head board.

## Population — all 77, not a sample

Source: `bench-results/session-20260911-smtlib/head-to-head/QF_NRA.tsv`
(200 files; axeyum 117, z3 187, cvc5 186).

**Winnable** = axeyum's verdict is not in `{sat, unsat}` **and** at least one
reference verdict is. That is 77 of 200, listed in `winnable-77.txt` (absolute
corpus paths, sha256 `4c24f8e982c7a169a232e273aab18a16e86e6214f1c8ad1311f803c7fe3f9955`).

All 77 board basenames resolve to **exactly one** file in the 12,154-file
corpus root — checked, not assumed: 0 missing, 0 ambiguous.

### The population is not one family

Path-sorted lists let one family dominate the head of a census. This one does
not concentrate that way:

| family | files |
|---|---:|
| meti-tarski (sin 12, atan 9, sqrt 8, exp 7, CMOS 3, Chua 2, Nichols-Plot 2, polypaver 2, RL-high-pass 1) | 46 |
| LassoRanker (CooperatingT2 5, Ultimate 4, SV-COMP 3) | 12 |
| 20161105-Sturm-MBO | 5 |
| 20220314-Uncu | 3 |
| 20200911-Pine | 3 |
| 20211101-Geogebra | 2 |
| 20180501-Economics-Mulligan | 2 |
| 2019-ezsmt, UltimateAutomizer, hycomp, kissing | 1 each |

### Ground truth is not in dispute on these 77

Declared `:status` vs the two references:

| declared | z3 | cvc5 | files |
|---|---|---|---:|
| sat | sat | sat | 33 |
| unsat | unsat | unsat | 25 |
| unsat | unknown | unsat | 6 |
| unknown | sat | unknown | 3 |
| unknown | sat | sat | 3 |
| unsat | unsat | unknown | 2 |
| unknown | unsat | unsat | 2 |
| unknown | unsat | unknown | 2 |
| sat | unknown | sat | 1 |

**No row has z3 and cvc5 disagreeing**, and no reference contradicts a declared
`:status`. So any verdict we newly produce on these files has an uncontested
expected answer to be checked against.

### How it overlaps the 2026-09-06 census

`bench-results/parity-losses-20260906/QF_NRA.census.tsv` censused a 77-file
loss set too, but against **cvc5 alone** and before ADR-1751/ADR-1752. 70 of
77 are the same files; 7 are new and 7 dropped out. That census's classes are
therefore **not** re-usable here, and this one re-derives them from scratch.

## Method

Instrument: `smtcomp_cli <file> --timeout-ms 24000 --trace`, one file per
process, release build of this lane's tree.

Two fields are recorded per file, deliberately **not** collapsed into one:

- `give-up kind=… detail=…` — the reason the solver stated when it declined.
- `route bound_by=… last=…` — which route consumed the budget, and which route
  spoke last. The CLI's own docs record that classifying by the **last** route's
  message has been refuted here before (a 403-file census was wrong on 67 of
  70 in two divisions). Both are reported below; they disagree.

**Timeout wall.** A previous census wrapped a 24 s budget in `timeout 32` and
killed 17 processes at load 4–6, manufacturing false "no reason" rows. This one
uses `timeout -k 5 180` — 7.5x the budget — and counts any file that still
produced no reason as its own row rather than dropping it.

**Host.** s4, under concurrent load from other lanes (load average 12–23
throughout, 16 cores). The board itself was measured on s6, idle and pinned.
So the *reasons* here are comparable to the board; the *times* are not, and no
timing claim is made from this census. A structural, pre-budget decline (the
majority here) is load-independent; a watchdog kill is not.

## Result — all 77, 100% reason coverage

Raw per-file rows: `census-77.tsv`. Every one of the 77 ran to completion
(`rc=0` on all 77, **no process hit the wall**), every one returned `unknown`,
and **every one produced a stated reason** — 77 of 77, 0 reasonless rows.

| cause, from the solver's own `give-up detail` | files | share |
|---|---:|---:|
| **`ERROR: unsupported by backend: QF_LRA: nonlinear real multiplication`** | **20** | **26%** |
| `preprocessed dispatch timeout after reduced solve` | 18 | 23% |
| `nonlinear abstraction: refinement reached a fixpoint without deciding` | 16 | 21% |
| `nra lazy SMT: wall-clock timeout reached` | 7 | 9% |
| watchdog fired before the worker thread returned | 5 | 6% |
| `nonlinear abstraction: … past the consuming engine's capacity … (needs nlsat/CAD)` | 4 | 5% |
| `lra: Fourier–Motzkin elimination exceeded the wall-clock / size budget` | 3 | 4% |
| `nonlinear abstraction: refinement round bound reached` | 2 | 3% |
| online CDCL(T) LRA model did not replay | 1 | 1% |
| integer literal outside the `iN` reference range (ADR-1702) | 1 | 1% |

By `give-up kind`: `Error` 20, `Timeout` 18, `Incomplete` 18, `ResourceLimit` 16,
`Watchdog` 5.

### `bound_by` and `last` disagree, exactly as the CLI warns

| `bound_by` (consumed the budget) | files |   | `last` (spoke last) | files |
|---|---:|---|---|---:|
| `nra` | 47 |   | `fd:bounded-completeness-unsat` | **52** |
| `preprocess` | 10 |   | `dispatch-error` | 20 |
| `dispatch-error` | 10 |   | (none — watchdog kill) | 5 |
| (none — watchdog kill) | 5 |   | | |
| `nra-real-root` | 3 |   | | |
| `cas-ideal-refuter` | 1 |   | | |
| `fd:parse` | 1 |   | | |

`fd:bounded-completeness-unsat` is a **string** front-door wrapper. It has
nothing to do with QF_NRA; it is simply the last route in the chain, and it
re-reports the nonlinear decline it was handed. A census classifying by `last`
would have named a string route as the cause of 52 of 77 QF_NRA losses. This is
the third recorded instance of that failure mode in this repository.

## The largest cause is a defect, not a capability wall

**20 of 77 — the single biggest class — are not a decline at all. They are an
`Err` escaping the dispatcher.**

`solve_relaxation`'s incremental-linearization loop builds a point lemma
`(a = a₀ ∧ b = b₀) → r = a₀·b₀` from the **original** operand terms of an
abstracted product, and pushes it into the linear relaxation **without
rewriting it through the product→fresh-variable map** that every other lemma
builder there goes through. Its guard, `products.contains(&pa)`, skips an
operand that *is* a collected product but not one that merely *contains* one —
and `(+ c (* x (* x k)))`, the MetiTarski/Horner shape, is exactly the second
kind. The raw lemma then carries a live `(* x …)` into an engine that can only
linearize a product with a constant factor, which returns
`SolverError::Unsupported`, which `check_with_nra_impl` propagates with `?`.

Two things follow from that, and both were measured rather than argued:

- Localised with the admission lever on `MulliganEconomicsModel0051a.smt2`:
  `AXEYUM_NRA_ADMISSION=0` (relaxation never entered) → a clean
  `ResourceLimit` decline, 15 route attempts. `AXEYUM_NRA_ADMISSION=1000`
  (relaxation entered) → the error, 10 attempts. Default → the error.
- The error also **doubles the work**. `check_auto` catches an errored
  preprocessed dispatch and re-runs the whole thing on the original query, so
  `nra-real-root` and `cas-ideal-refuter` each run twice (156 ms + 150 ms, and
  101 µs + 77 µs, on that file) before the second pass errors again and the
  error finally escapes.

It also mis-*names* itself. The text says `QF_LRA`, so a reader is pointed at the
linear backend; the boundary that actually refused is the nonlinear abstraction
above it. And `unknown` is a first-class result in this project and never an
error — this path was a standing violation of that rule.

## The second-largest cause is an opaque relabel

**18 of 77** say only `preprocessed dispatch timeout after reduced solve`.
That sentence is not a cause; it is `dispatch_reduced` **replacing** the reduced
solve's own `UnknownReason` with a fixed string when the budget has expired. The
specific reason — which route gave up, and on what bound — existed at that line
and was dropped.

This is not local to QF_NRA. The same sentence is the top named `Timeout` detail
in two other censuses: 41 of 110 files in
`docs/research/03-measurements/qf-nia-is-not-a-width-problem-2026-09-12.md` and
30 of the 260 `unknown`s in
`docs/research/03-measurements/why-unknown-says-nothing-2026-09-11.md`. All of
those rows are classified by a string that carries no cause.

## What is a genuine capability wall

**22 of 77** (16 refinement fixpoint + 4 atom capacity + 2 refinement round
bound) are the linear-abstraction relaxation's documented sound-incomplete
boundary, and the capacity decline says so in its own words: *"this needs a
nlsat/CAD engine"*. That is ADR-0058 Phase C/D, and this lane does not attempt
it. `mbo_E1` projects **771 cross-products to 36,945 linear-real atoms** against
a capacity of 1,024; no tuning of a bound reaches that.

The remaining 16 are clock: 7 `nra lazy SMT` wall-clock, 5 watchdog, 3
Fourier–Motzkin budget, 1 replay failure — plus one wide-integer literal
(ADR-1702, already tracked elsewhere).

### The census times track the board

The board (s6, idle, pinned) and this census (s4, load 13–23) agree closely per
file where it matters: the seven rows the board timed at 24.1–25.1 s are the
same rows this census timed at 24.0–24.7 s. So the budget-expiry rows are real
and not an artifact of this box's load.

## The A/B — 200 files, interleaved, both arms on the same core set

`ab-200.tsv`. Both arms run **back to back on the same file and the same cores**
(`taskset -c 0-7`, the P-core threads on this hybrid CPU), with the **arm order
alternating** per file — 100 base-first, 100 treat-first — so a monotone drift in
machine load cannot land systematically on one arm. 24 s budget both arms, one
process each, inside a 180 s wall; `rc` is `timeout`'s own status, read from the
command substitution and not from `$?` after a pipeline. Box idle (load 0.8–3)
for this run. Binaries differ by sha256 (`34dc447d…` base, `a52d8756…` treat).

| | base | treat |
|---|---:|---:|
| decided | **117 / 200** | **117 / 200** |
| gains (`unknown` → decided) | — | **0** |
| losses (decided → `unknown`) | — | **0** |
| flips (`sat` ↔ `unsat`) | — | **0** |
| runs killed by the wall | 0 of 200 | 0 of 200 |
| total wall | 1,092.0 s | 1,210.9 s (**+10.9%**) |

The base arm reproduces the board's QF_NRA row **exactly** (117/200), which is
what makes the comparison mean anything.

**Disagreements: 0.** Every decided verdict on both arms was checked against the
file's declared `:status` (116 of the 117 declare one) and against both
reference columns (233 reference checks). No verdict contradicts a declared
status or either reference.

### So the fix decides nothing, and that is the finding

The largest named cause of this division's gap — 26% of it — was a defect, and
repairing it moves **zero** files. An error and an `unknown` are both "not
decided" to a scorer, and the routes that ran after the error was removed do not
decide these queries either. What the repair buys is a correct reason on 20
files, one dispatch instead of two on those files, and a `Timeout` class that
can be read at all.

The cost is **+10.9% wall**, concentrated exactly where predicted: the files
that used to abort early now run the relaxation to its fixpoint or its budget.
The eight largest slowdowns are all MetiTarski files that were in the 20, led by
`exp-problem-10-3-weak-chunk-0081.smt2` at +23.1 s. None of them changes verdict.

### A variant that scored +1 and −1, and why it is not what shipped

The first version of the fix rewrote the point lemma **after** building it from
the raw operands. Measured over the same 200 files: **+1 gain
(`exp-problem-10-3-weak-chunk-0081.smt2` → `unsat`, 7.0 s), −1 loss
(`sin-problem-7-chunk-0353.smt2`, `sat` in 1.7 s → `unknown`)**, net 0. Both
files were freshly re-verified against both references at a 120 s budget: 0081
is `declared unsat / z3 unsat / cvc5 unsat`, 0353 is `declared sat / z3 sat /
cvc5 sat`. So that variant's gain was correct and its loss was a real loss.

It is sound — validity does not depend on which constants the lemma pins — but
it is not what incremental linearization prescribes. The premise `â = a0` was
built with `a0` read off the **raw** operand, whose value under the candidate is
the true product of the model's variables rather than the relaxed value the
fresh variable holds, so the lemma does not exclude the current spurious point.
Rewriting the operands *before* reading their values restores `sin-problem-7-chunk-0353`
(1.7 s, unchanged) and gives up `exp-problem-10-3-weak-chunk-0081`.

Recorded here because it is a real, measured degree of freedom for whoever
builds the CAD route: **which point the refinement lemma pins changes which
files the relaxation closes**, by one in each direction on this division.

## What this leaves for the next lane

After the repair, the QF_NRA gap is the relaxation's own boundary and the clock.
The census's 22 genuine-incompleteness rows say so in their own words — *"this
needs a nlsat/CAD engine"* — and that is ADR-0058 Phase C/D. The 20 rows that
used to read as an error and the 18 that read as a bare timeout now carry real
reasons, which is the input that work needs and did not have.

## The re-census — what those 38 rows actually were

`census-77-after.tsv`. Same 77 files, same protocol, the shipped binary
(sha256 `a52d8756…`). 77 of 77 ran, 77 of 77 stated a reason, 0 killed.

| cause | before | after |
|---|---:|---:|
| `ERROR: unsupported by backend: QF_LRA: nonlinear real multiplication` | **20** | **0** |
| `preprocessed dispatch timeout after reduced solve` (no cause) | **18** | **0** |
| `nonlinear abstraction: refinement reached a fixpoint without deciding` | 16 | **27** |
| *carried*: `nonlinear abstraction: … past the consuming engine's capacity …` | — | **13** |
| `nonlinear abstraction: … past the consuming engine's capacity …` (direct) | 4 | 4 |
| `nra lazy SMT: wall-clock timeout reached` | 7 | 12 |
| *carried*: `lazy SMT: wall-clock timeout reached` | — | 4 |
| watchdog fired before the worker thread returned | 5 | 5 |
| `lra: Fourier–Motzkin elimination exceeded the wall-clock / size budget` | 3 | 3 |
| `nonlinear abstraction: refinement round bound reached` | 2 | 2 |
| *carried*: `auto-dispatch timeout after exact real-polynomial route` | — | 2 |
| integer literal outside the `iN` reference range (ADR-1702) | 1 | 3 |
| online CDCL(T) LRA model did not replay | 1 | 2 |

`give-up kind`: `Error` **20 → 0**. `Incomplete` 18 → 32, `ResourceLimit`
16 → 21, `Timeout` 18 → 19, `Watchdog` 5 → 5.

Rows marked *carried* are the ones the repaired relabel now reads out. **Thirteen
of the eighteen opaque timeouts were the CAD wall** — a query whose
cross-products project past the consuming engine's atom capacity, which the old
sentence reported as "the clock ran out". Four were a genuine lazy-SMT
wall-clock, two an exact-real-polynomial-route budget.

### The gap, restated on the repaired diagnosis

| | files | share |
|---|---:|---:|
| **the linear abstraction's own boundary** (refinement fixpoint 27, capacity 13 + 4, round bound 2) | **46** | **60%** |
| clock (lazy SMT 12 + 4, watchdog 5, Fourier–Motzkin 3, dispatch budget 2) | 26 | 34% |
| other (wide integer literal 3, model replay 2) | 5 | 6% |

Before the repair the same population read as *26% error, 23% "it ran out of
time", 21% relaxation boundary*. After, **60% is one thing and it names itself**:
the linear-abstraction relaxation cannot decide these, and the capacity rows say
in their own decline text that it *"needs a nlsat/CAD engine"*. That is
ADR-0058 Phase C/D, and it is now the measured majority of this division's gap
rather than an inference from a fifth of it.

`last` is still useless and `bound_by` still is not: 72 of 77 name the string
front-door wrapper `fd:bounded-completeness-unsat` as the last route, while
`bound_by` names `nra` on 66.
