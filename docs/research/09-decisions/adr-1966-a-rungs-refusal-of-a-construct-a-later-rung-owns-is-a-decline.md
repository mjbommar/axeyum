# ADR-1966: A rung's refusal of a construct a later rung owns is a decline — and here is the enumerated list

Status: accepted
Index-summary: ADR-1927 made a quantified rung's fragment refusal a DECLINE and said its audit "was not exhaustive"; ADR-1960 then found two more of the shape by accident. All four known instances were found while chasing something else, so this lane enumerated the population MECHANICALLY instead — `scripts/enumerate-dispatch-refusal-propagation.py` derives all three of its inputs from the source (functions that can return `SolverError::Unsupported`, transitively closed; the dispatch path reachable from `auto.rs`'s own `pub fn check*`/`solve*`; and the propagation sites, counting `?`, TAIL POSITION and `return f(..)` — the second of which a `?`-only scan misses entirely, and adding it took the population from 37 to 72). **Baseline: 72 rung-to-sub-solve propagation sites, 40 with another sub-solve below in the same body.** **Five are closed here; the SIXTH — worth more than the other five combined — was built, measured, and REVERTED**, and saying so is the point of the ADR. The list is pinned with a `--fail-on-new` ratchet whose negative control fires on exactly one re-introduced site. Measured per-file A/B, both arms back to back on one pinned core with the order alternating, 10 s, over **1,606 well-formed rows in eight divisions**, with EVERY moved row re-run three times per arm at 24 s: **`AUFDTLIRA` 90 → 110 decided of 200, and after re-checking, +22 gained / −2 lost; 0 `sat`↔`unsat` flips anywhere; 11 of the 18 moved rows outside `AUFDTLIRA` were ambient and vanished on re-check.** All 23 new verdicts are `unsat` and all 23 agree with z3 4.13.3 and cvc5 1.3.4 — and the declared `:status` is comparable on **0 of 23**, because these files carry none, so it is reported as the vacuous authority it is rather than folded into a "three-way" claim (ADR-1957). **Every one of those `AUFDTLIRA` files comes from the ONE site that was reverted**, because converting it turns **7 assertions red in 4 registered pre-push suites** owned by ADR-1920/1935/1942/1946 — three of them read the refusal MESSAGE out of that `Err` because it is what the blocker census reads, one pins the `Err` itself, and four then get `Ok(Sat(model))` from a rung below. Landing a change that reds four other ADRs' gates is not a call this lane can make, so it ships as a **sized, verified, named handoff** instead of a result. **The change is also not free where the guard cannot fire**: the `UFLIA` control, chosen precisely because nothing in it can trigger a guard, still loses one file of 200 reproducibly — the ladder takes a longer path, `q:egraph` eats 19.3 s of the budget, and `q:mbqi-quick`, which decided it in 2.0 s before, never gets there. Two corrections are worth more than the file count: a STRUCTURAL hit rate is not reachability (184 of 200 `AUFLIRA` files declare the refused shape and 186 of 200 never get past the PARSER, so the division cannot exercise the change at all), and **site count is not file count** — the one site whose firing population was identified by name, `abv-online-cdclt` on 6 `QF_ABV` files, yields **0 verdicts** at 24 s.
Index-status: accepted
Date: 2026-09-13

## Context

The defect shape has now been found four times, and **every one of them by
accident, while chasing something else**:

- **ADR-1927** (`DT-DIVISIONS`): three quantified-ladder rungs propagated a
  speculative sub-solve's `Unsupported` with a bare `?`. A backend refusing a
  fragment of a query *the solver itself had rewritten* became the file's
  answer, and seventeen rungs below never ran. Worth +51 files; took
  `AUFDTLIRA` from 0 to 41.
- **ADR-1960** (`ARRAY-REAL-GATE`) found two more in a branch ADR-1927's audit
  never reached, and closed with: *"ADR-1927 established the rule for the rungs
  it audited; that audit was not exhaustive."*

A defect class found only by accident has no known size. That is what this ADR
changes.

## The instrument, and what it cannot see

`scripts/enumerate-dispatch-refusal-propagation.py`. Nothing in it is a
hand-written list of sites — this repository's own rule is that a test named
"every X" must derive its X from the authority, not a literal. Three
populations, all read off the source:

| population | how it is derived | size |
|---|---|---:|
| can return `Unsupported` | bodies that CONSTRUCT one, closed transitively over propagation | 1,207 fns |
| the dispatch path | reachable in the intra-crate call graph from `auto.rs`'s `pub fn check*`/`solve*` | 3,815 fns |
| broad sites | every propagated call into the first, from the second | 1,590 |
| **core sites** | …where the callee's SIGNATURE returns a `CheckResult` (a sub-solve) and the caller's does too (a rung) | **72** |
| …with a rung below | another, different sub-solve appears after the site in the same body | **40** |

Two details decided the numbers:

- **Tail position is a propagation.** `dispatch_uf_routes` ends with
  `dispatch_uf_fast_paths(arena, …)` — no `?`, and a `?`-only scan does not see
  it. Adding tail and `return f(..)` took the core population from **37 to 72**.
  Any future scan of this kind that counts only `?` is under-reporting by about
  half.
- **A match arm is not a construction.** Counting
  `Err(SolverError::Unsupported(m)) => …` as "this function refuses" marks every
  CONVERSION helper as a refuser and re-flags the sites it just fixed. The
  instrument distinguishes them; before it did, the population read 80 and the
  six closed sites reappeared under a new name.

**What it cannot see, stated up front** because three prior scans in this
repository each missed instances a probe later found:

1. Dynamic dispatch — a refusal arriving through `Box<dyn Backend>` is
   attributed to the trait method, not the implementation.
2. Macro-generated call sites; bodies are read as text.
3. Method calls are matched by BARE NAME, so same-named inherent methods merge
   (over-inclusive, never under).
4. **Refusals that are not `SolverError::Unsupported`.** An `Unknown` whose kind
   means "I refuse" and which is then `return`ed reads as a first-class verdict
   here and is not in this population at all. That class has to be found by
   reading, and ADR-1960's second site is one of them.
5. Whether a rung below actually OWNS the refused construct. The tool reports
   the structural precondition; a human classifies.

## Classification, and what was done with each

The discriminator is the one ADR-1927 implies: *does a rung BELOW this site own
the construct that was refused?* A refusal of something no later rung could
handle is a correct terminal refusal and must stay.

| site | rungs below | classification | action | fires on corpus |
|---|---:|---|---|---|
| `check_auto_dispatch` → `check_with_datatype_native` | 13 | **defect** — ADR-1927's own after-census names its ADR-0022 refusals as the top `AUFDTLIRA` blockers | **NOT TAKEN** — built, measured at +22/−2, reverted; see "The site that was not taken" | **yes**, +22 files |
| `dispatch_uf_fast_paths` → `check_with_uf_arithmetic` | 1 + the whole array ladder | **defect** — the refusal's own sentence says "use canonical AUFBV combination", a route below it | refusal → first-class `Unknown`, existing fall-through arm carries it | synthetic only; 0 of 1,521 |
| `dispatch_uf_nra` → `check_with_nra` | 10 | **defect** — a speculative sub-solve of a query THIS RUNG BUILT by eager Ackermann reduction, three statements after a guard that already declines when the reduction refuses | decline, `Ok(None)` | **0**, route entered on 3 of 58 `QF_UFNRA` files, guard never fires |
| `check_auto_dispatch` → `dispatch_uf_routes` | 4 | defect (same class) | `rung_or_decline` | see below |
| `check_auto_dispatch` → `dispatch_abv_online` | 3 | defect (same class) | `rung_or_decline` | **6 of 200 `QF_ABV`** |
| `check_auto_dispatch` → `dispatch_int_linear_refuters` | 5 | defect (same class) | `rung_or_decline` | 0 of 1,521 |
| `check_auto_dispatch` → `dispatch_array_fast_paths` | 2 | defect (same class) | `rung_or_decline` | 0 of 1,521 |
| `check_auto_dispatch` → `dispatch_arith_uf_overbound_probe_before_lia` | 6 | defect (same class) | `rung_or_decline` | 0 of 1,521 |
| `check_auto_dispatch` → `dispatch_nonlinear_int_tail` | 0 | **terminal** — it is the last rung | left | — |
| `solve` → `checked_quantified_fast_path` | 4 | ADR-1927 wrote this guard, measured it firing **0 times in 800 files** and deleted it | left, per that measurement | — |
| the remaining 62 | various | intra-route (a CEGAR loop's own sub-solve, an NRA branch-and-bound relaxation, a warm incremental check); the enclosing function is one route, not a ladder | left, pinned | — |

The rule is stated once, in `rung_or_decline`, rather than seven times.

### The `uf-nra` guard fires zero times, and the first measurement of that was vacuous

The first firing scan covered `NRA`, `QF_NRA`, `AUFNIRA` and `UFNIA` and found
zero. **That negative proved nothing**: `dispatch_uf_nra`'s own gate requires
`has_real && has_function && !has_int && !has_array && !has_datatype &&
!has_uninterpreted_sort`, which `NRA` and `QF_NRA` (no UF), `AUFNIRA` (arrays)
and `UFNIA` (ints) all fail by construction. The route could not have been
entered on a single file scanned. `QF_UFNRA` is the division whose logic matches
the gate; over **all 58** of its files the route is entered **3 times** and the
guard fires **0 times**.

The guard is kept, and labelled here rather than presented as a win: it is
correct by the rule, it costs nothing at run time, and the statement three lines
above it already declines in exactly this way with the comment "`unknown` is
never an error and the downstream routes may still decide it". What it is not is
evidence of anything, and no claim in this ADR rests on it.

## What it measured

Per-file A/B of the SAME binary with and without the guards, **both arms back to
back on one pinned core with the arm order alternating per file**, 10 s and
8 GiB per run, over the committed full-span pinned lists. The box carried other
lanes throughout (load 9–24); interleaving is what makes that cancel in the
difference, and every moved row was re-run.

Raw counts first, then the same rows after every mover was re-run **three
times per arm at 24 s on one pinned core**. Reporting only the raw column
would overstate the effect by 11 files and the cost by 5.

| division | role | rows scored | base dec | fixed dec | raw gain | raw loss | **re-checked gain** | **re-checked loss** | `sat`↔`unsat` |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| **AUFDTLIRA** | treatment | 200 | 90 | **110** | 23 | 3 | **22** | **2** | **0** |
| QF_AUFLIA | treatment | 200 | 142 | 140 | 1 | 3 | **0** | **0** | **0** |
| QF_ABV | treatment | 200 | 186 | 186 | 0 | 0 | 0 | 0 | **0** |
| QF_ABV (the 6 firing files, 24 s) | treatment | 6 | 4 | 4 | 0 | 0 | 0 | 0 | **0** |
| ABV | treatment | 200 | 4 | 4 | 0 | 0 | 0 | 0 | **0** |
| AUFLIRA | treatment | 200 | 8 | 8 | 0 | 0 | 0 | 0 | **0** |
| AUFNIRA | treatment | 200 | 3 | 3 | 0 | 0 | 0 | 0 | **0** |
| **QF_UFLIA** | **control** | 186 | 153 | 152 | 0 | 1 | **0** | **0** | **0** |
| **UFLIA** | **control** | 200 | 70 | 70 | 1 | 1 | **0** | **1** | **0** |
| **total** | | **1,606** | | | 25 | 8 | **22** | **3** | **0** |

39 rows of `QF_UFLIA`'s output are MALFORMED — the harness writes the refusal
sentence into the row and some sentences split the record — and they are
excluded from every column rather than scored as unchanged. `summarize.py`
counts and lists them; reading a parse failure of the results file as "no
movement" is how a measurement manufactures a null.

### The control is not free, and that is the most useful row in the table

`UFLIA` cannot trigger any guard added here — 200 of 200 files declare the
arithmetic UF that reaches the rung, 0 declare the array-valued one that makes
it refuse — and it still loses `sledgehammer/Hoare/smtlib.993567.smt2`,
reproducibly, `unsat` 3/3 before and `unknown` 3/3 after. The trail says why:

```
base  route decided_by=q:mbqi-quick bound_by=q:valid-universal-qf  total_ms=1999  attempts=7
fix   route decided_by=none        bound_by=q:egraph              total_ms=23313 attempts=20
      give-up kind=ResourceLimit detail=e-matching: instantiation time budget exhausted
```

A ladder that declines instead of stopping reaches routes it did not reach
before, and one of those routes can eat the budget that the deciding route
needed. **The cost of this change is not confined to the queries whose refusal
it converts**, and a control chosen to isolate the guard does not isolate that.
0 of 200 in `QF_UFLIA`, 1 of 200 in `UFLIA`.

### The controls are not empty, and that was checked rather than assumed

Two lanes this week shipped control divisions structurally unable to exercise
the route they were controlling for. The control here is chosen so that the
changed rung RUNS and cannot refuse: `QF_UFLIA` declares an applied
arithmetic-sorted uninterpreted function — the `has_arithmetic_function` gate on
the rung under test — in **194 of 200** files, and an array-VALUED one, the only
shape that rung refuses, in **0**. `UFLIA` is 200 of 200 and 0 of 200. The
route runs on essentially every file of both and the guard can never fire, which
is exactly what a cost control needs to be.

### Soundness: 23 new verdicts, and the authority that was vacuous

All 23 are `unsat`. Each was re-run against two independent solvers at 24 s on
the same box (`z3 -T:24`, **seconds**; `cvc5 --tlimit 24000`, **milliseconds** —
mixing those units silently corrupts a board):

| authority | comparable | disagreements |
|---|---:|---:|
| z3 4.13.3 | 23 of 23 | **0** |
| cvc5 1.3.4 | 23 of 23 | **0** |
| the file's declared `:status` | **0 of 23** | — |

The third row is the point. These `AUFDTLIRA` files carry no
`(set-info :status …)` at all, so quoting "three independent checks" here would
be quoting a check that never looked at anything. The extractor was confirmed
against a positive control (a `QF_ABV` file that does declare one) so the zero
is a property of the corpus, not of the tool. ADR-1957 requires the comparable
denominator to be published; this is what it looks like when one of them is
zero.

### The cost is real and is two files

Of the three `AUFDTLIRA` losses, re-running both arms **three times each at
24 s** on one pinned core shows:

- `…sorters_not_global.adb_76_40_index_check…` — `unsat` 3/3 in BOTH arms.
  **Not a loss**; a 10 s ambient artifact, exactly the 1–1.5 % single-pairing
  flip rate this budget carries.
- two `…higher_ordermnfold-T-defqtvc…` files — base `unsat` 3/3, fixed
  `unknown` 3/3. **Real, reproducible losses.** The ladder now runs to
  `attempts=20` and `attempts=43` instead of 8 and 15, and spends the budget.

The 23 gains were re-run the same way: **22 reproduce** (fixed `unsat` 3/3,
base never `unsat` in three tries) and one,
`…integer_stacks.ads_4_1_postcondition…`, does not — `unknown` 3/3 in both arms
at 24 s, so its 10 s `unsat` was ambient in the other direction.

That is ADR-1927's cost note made concrete: the refusal was fast because it was
wrong, and a query that used to stop early now can spend its whole budget.
**+22 / −2, net +20 on the division**, and all four named files are listed so a
later lane can look at them rather than rediscover them.

## The site that was not taken, and exactly what blocks it

`check_auto_dispatch` → `check_with_datatype_native` is the textbook instance:
thirteen rungs below it, and ADR-1927's own after-census names its four ADR-0022
refusals as the top blockers of `AUFDTLIRA` (70 + 32 + 13 + 1 of 200). The
conversion was written, built and measured — **every `AUFDTLIRA` number in this
ADR comes from it** — and then reverted.

**What it costs to take it.** With the site converted, these go red:

| suite | owner | failing | what it asserts |
|---|---|---:|---|
| `dt_uf_gate` | ADR-1920 | 1 | `solve` returns `Err(Unsupported)` on an array-of-datatypes query — literally *"expected a clean `Unsupported`"*, which is the hard rule inverted |
| `dt_capability_1935` | ADR-1935 | 3 | 2 read the refusal MESSAGE ("must name the FIELD, not the dispatcher"); 1 now gets `Ok(Sat(model))` |
| `dt_constructor_arg_1942` | ADR-1942 | 2 | both now get `Ok(Sat(model))` where they expected `Err` |
| `dt_valued_result_1946` | ADR-1946 | 1 | same |

Two different objections are stacked here and they need different answers:

1. **Three tests read the refusal message out of the `Err`.** That is not
   pedantry — ADR-1927's own headline finding is that the blocker census was
   measuring the ladder, and these messages are what the census reads. Moving
   the terminal refusal to the bit-blast tail replaces
   "array/UF datatype fields are not yet supported (ADR-0022)" with
   "unsupported pure-Rust BV operator `DtTest(…)`", which names the wrong thing.
   **Converting this site requires carrying the datatype rung's own sentence
   into the final `unknown` first.**
2. **Four tests get `Ok(Sat(model))` where they expected `Err`.** On the face of
   it that is a capability gain — the front door replay-checks every `sat`
   against the ORIGINAL assertions, and the neighbouring test in
   `dt_constructor_arg_1942` says in its own words that these queries are
   *"SATISFIABLE (z3, cvc5)"*. But those assertions exist because ADR-1930
   shipped a **wrong `unsat`** from an inexact datatype encoding, and granting
   a capability on another ADR's soundness gate is not something a lane can do
   from the outside.

So the handoff is exact: **+22 files, every one already confirmed `unsat` by
both z3 4.13.3 and cvc5 1.3.4, behind 7 named assertions in 4 named suites, and
one prerequisite (carry the datatype refusal's sentence into the final
`unknown`) that removes 3 of the 7.** The A/B, the verification and the
per-file rows are committed in
`bench-results/dispatch-decline-audit-20260913/`, so the next lane does not
re-measure any of it.

This is also why the site is left with a bare `?` and a long comment rather
than quietly. A file that records obstacles accumulates stale ones by
construction; this one carries its measurement and its expiry condition.

## The two findings worth more than the file count

### 1. A structural hit rate is an upper bound on reachability, not a measure of it

The first A/B batch was aimed by reading declarations out of the corpus text:
`AUFLIRA` declares an array-valued uninterpreted function in **184 of its 200**
files, the highest of any division, so it was the obvious treatment. It moved
nothing — because **186 of those 200 files never get past the PARSER**
("nested array element sort is unsupported", the gate ADR-1955 owns). The
division cannot exercise the change at all.

Aiming by text would have produced a confident zero and the wrong conclusion.
The second batch was aimed by `guard-firing.sh`, which reads the ROUTE TRAIL of
the fixed binary and counts the guards that actually fire — a measurement of
reachability rather than of syntax. **Before sizing a dispatch change by which
files "contain" the shape, check they reach the dispatcher.**

### 2. Site count is not file count, and the one site with a named firing population yields zero

`abv-online-cdclt` is the only fixed site whose firing population on real files
was identified **by name**: 6 of the 200 pinned `QF_ABV` files, refusing with
"online AUFBV lazy-ROW abstraction does not admit this array shape" — while
`dispatch_array_fast_paths`, the rung IMMEDIATELY below it, is the route that
owns array shapes. Textbook instance of the defect.

Re-running that complete population, both arms, at 24 s: **4 decided before, 4
decided after, 0 gained.** One file moved from a `Watchdog` kill to a
first-class `Timeout` carrying the reduced solve's own reason — a reason-quality
improvement, not a verdict.

This repository's recurring error is reporting a site count as a file count
(143→6, 51→2, 173→10, 84→49, 27,150→1,135, 19,620→0). Six sites closed; **one
of them is worth 23 files, one is worth 0 on its own identified population, and
four have no observed firing at all.**

## Evidence

- `crates/axeyum-solver/tests/dispatch_rung_refusal_declines.rs` — three tests.
  Its module note records the fixture that was **written and thrown away**: the
  obvious `x > 0 AND x < 0` contradiction is refuted by `int-box-eval` at
  `attempts=3`, before the rung under test, so it passes on the unfixed tree and
  tests nothing. Each surviving fixture was checked against a binary built
  WITHOUT the guards and kept only because the two arms differ.
- Mutation control, one guard deleted at a time in a scratch copy (never the
  shared worktree):

  | guard deleted | tests that die |
  |---|---|
  | uf-arithmetic | **none** |
  | `rung_or_decline` | **none** |
  | uf-arithmetic **+** `rung_or_decline` | `array_valued_uf_refusal_is_not_the_querys_verdict` |
  | uf-nra | **none** |

  The pair result is structural, not a gap: they are consecutive guards on ONE
  path, so whichever fires first stops the dispatch before the later one is
  reachable, and each individually is redundant with the other. The `uf-nra`
  row is the honest one — no test kills that guard, its firing rate is 0 on the
  only division that can enter the route, and both facts are stated above
  rather than smoothed over.

  (Before the datatype site was reverted, deleting ITS guard killed exactly one
  test — the only separable row. It went with the revert.)

  **These rows are deliberately NOT registered in
  `scripts/tests/mutation_controls.py`.** That harness exits 0 only when every
  registered mutation is `killed N`, and three of the four here kill nothing on
  their own — structurally, because they are redundant consecutive guards on
  one path. Appending them would turn a gate every lane runs red, which is a
  worse outcome than an unregistered control. The runner that produced the
  table is committed as
  `bench-results/dispatch-decline-audit-20260913/mutation-control.py`; it works
  on a `lane-snapshot.sh` copy, never the shared worktree, and it refuses to
  score anything if the unmutated tree is not green first.
- `scripts/enumerate-dispatch-refusal-propagation.py --fail-on-new
  bench-results/dispatch-decline-audit-20260913/refusal-propagation-baseline.json`
  — the pinned list, so a NEW site of this shape fails rather than waiting to be
  found by accident a fifth time. **Its negative control caught an inverted
  control in this lane**: the baseline first stored ABSOLUTE paths, so on any
  other tree root every site read as new and the ratchet fired on a clean tree —
  a gate that "fails" unconditionally looks exactly like a working one until you
  check that it also passes when it should. Paths are root-relative now, and
  re-introducing one closed site makes the ratchet name that site and exit 1
  while the restored tree exits 0.
- `bench-results/dispatch-decline-audit-20260913/` — the enumerator baseline,
  the A/B and its scripts, the guard-firing scan, the hit-rate measurement that
  was wrong and why, and the three-way verification of every new verdict.

## What this ADR does not claim

- No new theory capability. Nothing in the datatype, UF, array or NRA backends
  changed; the same routes decide the same fragments. What changed is which
  routes get to run.
- The enumeration is exhaustive **for `SolverError::Unsupported`**. The
  `Unknown`-that-means-refusal class — where a rung `return`s a first-class
  `unknown` that a later rung could have decided — is a different population
  that this instrument does not see, and ADR-1960's second site is in it.
- **The datatype site still has the defect.** It is the largest one, it is
  measured, and it is deliberately left in place — see "The site that was not
  taken". Nothing here claims `AUFDTLIRA` improved; the +22 is what the next
  lane can collect, not what this one delivered.
- **A separate terminal refusal sits right behind it.** With the datatype guard
  in place, the `QF_UFDT` fixture runs twenty-four more rungs and then meets
  `unsupported pure-Rust BV operator DtTest(…)` from the bit-blast tail, as an
  ERROR. That tail already converts such errors to `unknown` for
  `has_uninterpreted_sort` and `has_array` and not for `has_datatype`. It is the
  prerequisite named above, and it is a named, sized next increment.
