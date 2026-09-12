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
