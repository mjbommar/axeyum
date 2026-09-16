# ADR-2125: `QF_LRA` — a warm simplex basis across the offline loop's cubes, and the two screens that made it inert

Status: proposed
Index-summary: PLACEHOLDER — rewritten when the A/B lands.
Index-status: proposed
Date: 2026-09-16

## Context

[ADR-2111] measured the lever it did not pull and [ADR-2122] named it again
without taking it: `cube_simplex_calls = 651` with `cube_matrices = 0` on
`_standard_init5_ground.i_3_2_2.bpl_7.smt2` is **651 simplex solves from
scratch, one per SAT model**, against four references that keep the basis across
every backjump and trail only the bounds.

**Read the population before the lever.** ADR-2111 also measured
`simplex_cold_restarts = 0` on every traced row, so the **online** CDCL(T)
engine is already warm — its tableau is built once and `assert`/`retract` move
only row bounds. The cold re-solve is in the **offline** lazy-SMT loop
(`dpll_t::check_with_lra_dpll_within` → `lra::decide_within` →
`simplex::feasible_within_sparse`), which is a different route over a different
set of files. A lane that reads "the simplex re-solves from scratch" and goes
looking in `lra_online.rs` will find a warm engine and conclude the finding was
wrong.

Branch base: `git merge-base main HEAD` is `5cb9553a6`, which **is** local
`main`'s HEAD at the time this lane opened.

Compute: **s5, physical core pairs `5,13` and `6,14`**, and nothing else. The
pairs were checked for a previous lane's leftover shards before the first
timing; there were none. A peer lane (`nra-cell-exact`) held cores 3 and 11
throughout, which are different physical pairs; the A/B's interleaving is what
makes that irrelevant to the difference and it is stated rather than assumed.

## 1. The sizing, taken before the code

[ADR-2122] is the reason this section exists and comes first. It ranked
implied-bound propagation as "the largest single lever in the division" from a
RATIO — 836,531 decisions per 19 propagations — built it, and measured **0 gains
over 600 rows**. Its own conclusion: *a ratio is not a prize; the number that
sizes a lever is how many of those decisions the lever could actually have
removed, and nobody had measured it*.

So the question here is not "how many cold solves are there" but **"what share of
the wall clock do they hold"**.

### 1.1 The instrument

Four additive fields on the `; lazy-smt` trail line (route-trace schema 3),
recorded by ONE call because they are one event — a reader holding
`simplex_cold_build_ms` without `simplex_cold_ms` has a numerator with no
denominator:

| field | what it counts |
|---|---|
| `simplex_cold_builds` | tableaux actually **allocated** |
| `simplex_cold_build_ms` | time in the construction — what a warm basis removes OUTRIGHT |
| `simplex_cold_ms` | the whole from-scratch call — the **denominator** |
| `simplex_cold_pivots` | pivots from a pristine basis — what a warm basis only SHORTENS |

`cube_simplex_calls` already existed and is **not** the same quantity: a call is
not a rebuild, because the cell cap can decline before allocating anything and
the same entry point is reachable from ADR-2122's implied-bound checker. `built`
is tracked separately from a nonzero duration for a reason that biases the
ceiling the dangerous way otherwise: a tableau whose construction is faster than
the clock still IS a rebuild, and inferring the count from the duration
under-counts exactly the cheap cubes a warm basis helps least on.

The trail's coverage is a test derived from the authority, not a byte pin.
`every_lazy_smt_counter_reaches_the_trace_line` destructures `LazySmtCounters`
with **no `..` rest**, so the compiler refuses it the moment a field is added,
and every field carries a distinct value so rendering the wrong source field
fails as loudly as rendering none. It checks both directions. On its first honest
run it found the three histogram keys the struct pattern did not name — which is
precisely what a byte pin cannot see: a pin that never mentioned a new field goes
green while that counter reads as absent to every consumer.

### 1.2 The population, and the 20 rows of silence

The whole pinned `QF_LRA` 200 — the 93 undecided **and the 107 decided as a
control**. A share measured over the undecided alone answers "how much do the
files we lose spend re-solving", which nobody disputes, and cannot answer whether
re-solving separates the halves.

```text
200 rows | 107 decided | 93 undecided
  reached the lazy-SMT loop (a `; lazy-smt` line):      180
  of those, built >=1 from-scratch tableau:              68
  never reached it (silent, NOT zero):                   20
```

The 20 report **nothing** about this loop, not zero, and are in no denominator
below. Folding them in would make every share smaller for a reason that has
nothing to do with re-solving — the mistake ADR-2122 refused when it sized its
ceiling over 23 rows rather than 93.

### 1.3 The ceiling

```text
share of wall clock, over the 68 rows that re-solve
  quantity                              median     min      max
  tableau CONSTRUCTION only               0.95 %   0.00 %   1.80 %
  the whole from-scratch call             4.15 %   0.61 %  99.31 %
    ... plus per-cube linearization      24.21 %   0.93 %  99.58 %
```

**The basis alone is worth about 4 % of the clock at the median, and its
structural half 1 %.** Construction is 32.7 % of the cold call at the median, so
two thirds of even that 4 % is pivoting a warm basis can only shorten.

The third line is the lever's real ceiling and it is six times the second,
because the ADR-2125 decider holds the atom translation for the whole entry: a
cube it answers never enters `lra::decide_within` and so pays no `Collector`
rebuild either. Over **every** row that reaches the loop:

```text
THE LEVER'S CEILING (cube_collect_ms + cube_simplex_ms), 153 rows
  median   0.00 %   min   0.00 %   max  99.58 %
  rows at or above 10 %: 61 of 153    at or above 25 %: 37
  restricted to the 73 UNDECIDED rows: median 23.87 %   max 99.58 %
```

**The median over all 153 is 0.00 % and that is real, not a bug.** A file the
ladder decides in 107 ms spends no measurable time in this loop, and a lever
cannot win a file that is already won. The addressable half is the undecided
rows, where the median is 23.87 %. Both are printed because quoting either alone
is a different claim.

### 1.4 The churn, which is why a warm basis is worth trying at all

```text
cube churn: median 1.79 flipped literals per round against a median 7,260 atoms
            (67 rows with a predecessor)
counts, median over the 68 that re-solve:
  from-scratch tableaux built     148   (max 1,543; 31,376 over the 68)
  pivots from a pristine basis 11,958   (max 404,257)
```

ADR-2111 measured 1.1–4.2 flips against 265–1,736 atoms on a different
population and a different tree; 1.79 against 7,260 reproduces it. Each round
hands the theory **nearly the same problem** and pays a cold decision for the
difference, which is the whole case for keeping the basis. The case for it being
*decisive* is what §1.3 refuses to make.

### 1.5 The three files the median hides

| share | `cold_ms` | `total_ms` | builds | file |
|---:|---:|---:|---:|---|
| 99.31 % | 23,908 | 24,073 | **1** | `latendresse/ecoliFBAyicesTest-3875-4` |
| 95.69 % | 23,022 | 24,058 | 42 | `miplib/danoint-266` |
| 65.27 % | 7,937 | 12,161 | 28 | `latendresse/ecoliMILPglycerolYices3-50000` |
| 28.09 % | 6,742 | 24,005 | 1,268 | `LassoRanker/…/2013POPL-BenAmGen-Ex4.2…` |
| 23.83 % | 5,720 | 24,007 | 894 | `sc/sc-39.base.cvc` |

**The top row is a warning, not a prize.** `ecoliFBAyicesTest-3875-4` spends
99.31 % of its budget inside the from-scratch simplex across **one** build: it is
a single enormous solve, not a re-solve, and a warm basis has nothing to reuse
there. `danoint-266` is 42 builds. The rows a warm basis can actually help are
the `sc/*` and `LassoRanker/*` families at 20–28 % across four figures of
builds — a smaller share held by many small solves.

That distinction is invisible in the share column alone and is why `builds` is
printed beside it.

## 2. The design claims, with `file:line` on both sides

Verified against `references/z3` at `e18d63bda0`, `references/cvc5` at
`1689f13331` and `references/opensmt` at `15b42c6f33`. Every range was re-printed
with `sed -n` and checked to cover a **complete** function body. The full table
is committed at `bench-results/lra-warm-basis-20260916/reference-citations.md`.

### 2.1 A correction to this lane's own brief

**`TheoryArithPrivate::push` and `TheoryArithPrivate::pop` do not exist in
cvc5.** A grep for any `push`/`pop` method definition across
`src/theory/arith/` returns nothing. The brief that opened this lane cited them
by name. The mechanism is real and is documented below — it is `context::Context`
membership, decided in the constructor's initialiser list — but there is no such
method to read, and a successor sent to find one would spend the hour ADR-2122's
lane spent on `try_add_bound`.

Recorded first, for the same reason ADR-2122 put its three corrections first: a
successor reading only the brief would look in the wrong place.

### 2.2 z3 — the basis is not trailed; two scalars are

| claim | `file:line` |
|---|---|
| `lar_solver::push()`, whole body | `lar_solver.cpp:532-543` |
| `lar_solver::pop(unsigned)`, whole body | `lar_solver.cpp:567-603` |
| the tableau is **not** pushed — `pop` ASSERTS its invariants instead | `lar_solver.cpp:576-579` |
| `lar_core_solver::push()` saves the strategy scalar and `m_column_types`, and nothing else | `lar_core_solver.h:123-130` |
| `lar_core_solver::pop(unsigned)` | `lar_core_solver.h:132-144` |
| tableau / basis / heading are plain members | `lar_core_solver.h:23,29,32-38` |
| **`m_r_pushed_basis` is declared and referenced NOWHERE in `src/`** | `lar_core_solver.h:35` |
| `find_feasible_solution()` — no rebuild, just `solve()` | `lar_solver.cpp:464-474` |
| the resume path: prefix, patch changed columns, pivot | `lar_solver.cpp:1286-1292` |
| only `m_columns_with_changed_bounds` is patched | `lar_solver.cpp:1280-1283` |
| an already-feasible point exits before any pivot | `lar_core_solver_def.h:85-95` |
| `init_run_tableau()` **asserts** the basis rather than building it | `lp_primal_core_solver_tableau_def.h:256-269` |
| bounds ARE trailed, one undo per bound | `lar_solver.cpp:922-931`, `:933-942`, `:107-119` |

`m_r_pushed_basis` is called out because the NAME is the hazard: a reader
grepping "is the basis pushed?" finds a `stacked_vector<unsigned>` with exactly
that name and concludes the opposite of the truth.

### 2.3 cvc5 — the tableau is simply not given a context

| claim | `file:line` |
|---|---|
| `SimplexDecisionProcedure` holds the tableau by reference, a plain member | `simplex.h:98-101` |
| the owning tableau is a plain value on `TheoryArithPrivate` | `theory_arith_private.h:310-313` |
| `Tableau`/`Matrix` carry **zero** `context::`/`CDO`/`CDList` members | `linear/tableau.h`, `linear/matrix.h` |
| the partial model gets the SAT context; the tableau is default-constructed WITHOUT one | `theory_arith_private.cpp:117`, `:122` |
| the bound journal is two `context::CDList` revert lists | `linear/partial_model.h:220-229` |
| pop restores a bound and re-enqueues the variable, whole bodies | `partial_model.cpp:722-732`, `:734-744` |
| the next solve resumes from the error set those reverts seeded | `dual_simplex.cpp:55-66` |

**NOT VERIFIED, and stated as such:** there is no comment anywhere in cvc5
saying the tableau survives a pop. The claim rests on the structural evidence
above, which is stronger than a comment, but it is not a quotation.

### 2.4 OpenSMT — a third data point with the same split

`Simplex.h:53-54` forwards both backtrack operations to the bound model and
nothing else; `Simplex.h:186` holds `Tableau tableau;` as a plain member;
`LRAModel.cc:98-99` is a bound trail with a limits stack.

### 2.5 Ours

| what | where |
|---|---|
| the ONLINE engine is already warm; `sync` moves only row bounds | `lra_online.rs`, `SimplexEngine::sync` / `LraTheory::feasibility` |
| the OFFLINE loop re-decides each cube from scratch | `dpll_t.rs`, `check_with_lra_dpll_within` → `decide_cube` |
| … rebuilding the whole atom translation per cube | `lra.rs`, `decide_within_with_options` → `Collector::collect` |
| … and allocating a fresh tableau per cube | `lra.rs:1498` → `simplex::feasible_within_sparse` → `Tableau::new_sparse` |
| what this lane added | `lra_online.rs`, `LraTheory::cube_check` / `SimplexEngine::sync_cube` |

## 3. What was built

`AXEYUM_LRA_WARM_CUBE=on` makes `dpll_t::check_with_lra_dpll_within` build **one**
`LraTheory` per entry, over the abstraction's atoms. Every cube the loop will ever
produce is an assignment to exactly those, so one row per constraint template
serves all of them and only the row BOUNDS move between rounds.

**The decider can only SHORTCUT.** Every outcome it does not produce falls
through to exactly the cold decision that would otherwise have run — including a
`Feasible` whose model does not replay, because the cold decider replay-checks
its own witness and may still answer, and declining on its behalf would be a
verdict thrown away rather than a shortcut declined. The risk this carries is
cost, not correctness.

**Two refusals, both whole rather than partial.** There is no warm engine — the
Fourier–Motzkin fallback behind it is a DIFFERENT engine, and answering from it
would make an A/B of this lever an A/B of two engines. Or the cube names an atom
this theory cannot represent (`Unsupported`, or an equality asserted FALSE, which
is a disjunction), where the system the engine would decide is strictly WEAKER
than the cube: a refutation of it is still sound, but a `Feasible` on it is not a
witness for the cube, and the call site cannot tell the two apart.

**The cube is installed WHOLE rather than by difference**, even though
consecutive cubes differ by a handful of literals. `live` is the index space
`rows_to_core` reads a Farkas refutation through, so a `live` not rebuilt in a
known order makes multiplier position *i* mean something other than atom *i* — a
wrong CORE, and so a blocking clause that rules out satisfiable assignments,
rather than a slow one. Rebuilding `live` is a `Vec` of small values and touches
no tableau; `sync_cube` then does the difference over the ROWS, where the cost
actually is.

## 4. Two screens made the arm inert, and the mechanism probe is what said so

This is the part of the lane worth keeping. **The first mechanism check read
`warm_cube_checks = 0` in BOTH arms.** ADR-2111 published exactly this reading
about its own `TableauReserve`: `net +0` from an inert arm is indistinguishable
from `net +0` from a working one that does not help. Had the A/B been run first,
it would have printed a clean `net +0` over 200 rows and the lane would have
concluded the warm basis buys nothing.

### 4.1 The cap that refused it is in the wrong currency

`Incremental::new` refuses when `m × (nvars+m)` exceeds
`MAX_TABLEAU_CELLS = 4_000_000`. That is a **dense-cell** count, and since
[ADR-2111] this tableau does not store dense cells — it stores `nnz` pairs at
about 40 bytes each. Measured with `AXEYUM_LRADENSEPROBE=1` on
`QF_LRA/sc/sc-39.base.cvc.smt2`:

```text
; LRADENSEPROBE site=feasible_within-entry nvars=554 m=2702 tableau_cells=8797712
; LRADENSEPROBE site=tableau-built         nvars=554 m=2702 tableau_cells=8797712 nnz=4688
```

**8,797,712 cells against 4,688 nonzeros** — 188 KB of real storage, refused by a
ceiling sized for 128 MB of dense ones.

What makes that indefensible rather than merely conservative is the other side of
it. The offline route's cold path consults `MAX_TABLEAU_CELLS` **only** under the
default-off `AXEYUM_LRA_CELL_CAP` lever, so on that same file the same structural
ceiling refused **one** warm tableau and permitted **797 cold builds of the
identical system**. That is [ADR-1752]'s finding one level down: a count is the
wrong currency, and the right one is the bytes.

**`MAX_TABLEAU_CELLS` is deliberately NOT changed.** It governs the online
engine's admission too, and moving it would make an A/B of one lever an A/B of
two routes — which is how ADR-2111's `TableauReserve` arm became unreadable.
`Incremental::with_nonzero_admission` is a second door for one call site, capped
at `MAX_WARM_CUBE_NONZEROS = 400_000` — not a new number but ADR-2111's own
`TableauReserve::Sparse` figure, **11.6× ADR-2055's measured median of 34,555
nonzeros on this route and 2.7× its extreme of 147,440**. Nobody has taken the
tail, and this says so.

The atom BUDGET is **not** raised. [ADR-2045] raised exactly that on exactly this
population and got **21 rows reaching the engine, 0 newly decided, five NEW
aborts**; repeating it inside a lever whose question is a warm basis would answer
a different question with the same number.

### 4.2 A refusal now names its screen

`warm_cube_build` renders `off | built | deadline | resource-limit |
memory-budget | no-tableau`. An enum and not a count, for ADR-2045's reason: the
remedies are disjoint. Without it the trail could not say WHY the arm was
silent, which is what made the first mechanism check a puzzle instead of a
measurement.

### 4.3 The second defect the same probe found: the reconciliation

With the engine admitted, the arm worked and was **slower**. `lra_rounds` fell
798 → 633 in the same budget, with **1,133,095 retractions and 1,135,797
assertions over 632 checks** — about 1,793 bound moves per check against 2,702
atoms. The whole cube, every round.

`SimplexEngine::sync` reconciles by **shared prefix**, which is exactly right for
a DPLL(T) trail: the driver grows `live` by `assert` and truncates it by `pop`, so
the divergence is always a suffix. A cube is not a trail. Its flips are anywhere
in the atom order, so the prefix ends at the FIRST one and everything after it is
retracted and re-asserted. The warm basis was removing 797 tableau builds and
paying for them in bound moves.

`sync_cube` compares the bound each row SHOULD carry against the one it DOES and
touches only the differences — z3's shape, patching
`m_columns_with_changed_bounds` and nothing else (`lar_solver.cpp:1280-1283`):

| on `sc-39.base.cvc.smt2`, 24 s | prefix `sync` | `sync_cube` |
|---|---:|---:|
| bound assertions | 1,135,797 | **4,238** |
| retractions | 1,133,095 | **0** |
| `lra_rounds` | 633 | **950** |
| `simplex_cold_builds` | 0 | **0** |
| `warm_cube_cold_restarts` | 0 | **0** |

`lra_rounds` in the `off` arm on the same file and core is **798**, so the
per-row diff is +19 % of rounds against the cold path rather than −21 %.

**Retractions are 0 and that is correct, not a bug.** A total cube over order
atoms bounds every row — `when_true` takes the slack's upper bound and
`when_false` its lower, on the same row (ADR-1701's 4× cut) — so no row is ever
left unbounded and nothing is retracted. The invariant fixture originally
*required* a retraction, because it was written against the prefix `sync`, and it
failed the moment the diff stopped doing work the cube does not imply. Its
assertion is now the property the diff exists for and is strictly stronger:
`assertions < cubes × atoms`, which the strawman fails by construction.

## 5. Soundness is the method

### 5.1 The invariant, and why `None` is not `true`

`Incremental::tableau_invariant_holds` checks that every basic variable's value
equals its row evaluated over the others, that the basic/nonbasic split is
internally consistent, and that no row stores a coefficient for its own basic
column. It answers **three** ways: `Some(true)`, `Some(false)`, and `None` when
its own exact arithmetic declined. A caller folding `None` into `true` would have
a verifier that passes hardest exactly where the numbers are most extreme.

A warm engine that keeps a basis it has CORRUPTED is worse than one that
rebuilds: the pivot loop repairs bound violations, it does not repair a row that
no longer expresses its basic variable, and pivoting from such a row is unsound
rather than slow.

### 5.2 The invariant fixture, over a sequence

`a_warm_cube_sequence_decides_exactly_what_a_cold_one_does_and_keeps_the_invariant`
runs **all 32** cubes of a five-atom, three-variable system. One theory is reused
across the whole sequence; a second is rebuilt for each cube, so its basis is
pristine and its tableau freshly constructed — which is exactly the comparison
"does keeping the basis change the answer". `Some(true)` is required after every
cube.

It publishes its own population: a run in which every cube DECLINED would satisfy
every assertion above and establish nothing, so the fixture requires both a
feasible and an infeasible corner. And it requires `cold_restarts == 0`, which is
the only thing in the test that can see a warm engine quietly rebuilding — the
verdicts, the invariants and the counts are all identical when it does.

### 5.3 The soundness-negative fixture is a pair, satisfiable arm SECOND

`a_stale_bound_from_a_popped_cube_would_refute_a_satisfiable_one`. Here the
infeasible arm is what CREATES the state the satisfiable arm must survive, so the
usual order is reversed deliberately:

1. `x ≥ 3 ∧ x + y ≤ 1 ∧ y ≥ 0` is refuted. That drives `x` up and leaves the
   basis and the assignment where the refutation left them.
2. The same two other atoms with the first FLIPPED — `x < 3 ∧ x + y ≤ 1 ∧ y ≥ 0`
   — is satisfiable at `x = 0, y = 0` and must come back `Feasible`.

If the bound from the first cube is not un-trailed, the engine refutes a
satisfiable system: a wrong `unsat`, the one verdict this route may never
produce. The witness is replayed through `eval` against the cube's own literals
rather than read out coordinate-wise — a `Feasible` whose model violates its cube
is the same defect wearing the right label, and no verdict comparison in the
suite could tell the two apart.

### 5.4 A new z3 seed class, because the existing five cannot reach this route

`qf_lra_cube_sequence_differential_fuzz`. The four existing `QF_LRA` fuzzes
generate **2 to 5 atoms** and the online engine admits **1,024**, so every one of
their instances is decided by the online engine and they would pass identically
with the warm cube decider deleted. Running them in both arms is necessary and
not sufficient.

This generator is **wide** (1,200 atoms over 4 variables) and **shallow**, so the
query falls through to the offline loop where each round installs a fresh total
cube. `the_generator_outruns_the_online_admission_screen` checks that as
arithmetic on two named constants rather than as a comment, because the screen
lives in another module and a budget change there would silently redirect the
whole suite to a different engine with nothing going red.

Equalities and disequalities are deliberately absent from it: an equality
asserted FALSE makes the decider refuse the whole cube, which is sound and would
turn most of the sweep into a fall-through to exactly the cold path the suite is
there to differ from. The existing fuzz covers those on the online route.

The suite is registered in `scripts/suite-gating-excuses.txt` with a real reason
rather than added to `hooks/pre-push`'s `--features full` dispatch block, where —
being `#![cfg(feature = "z3")]` — it would compile to ZERO tests and exit 0. That
is the trap that left the corpus sweep inert in this same hook for 15 days, and
registering a gate that cannot fail is worse than registering none.

### 5.5 The gates, each with a nonzero count

PLACEHOLDER — filled when the runs land.

## 6. The A/B

PLACEHOLDER — filled when the runs land.

## 7. Decision

PLACEHOLDER — filled when the runs land.

### 7.1 The criteria, written before the numbers

The ship criterion is not "net ≥ 0". It is, in order:

1. **0 soundness disagreements** against the files' declared `:status`, at a
   comparable denominator that is printed rather than implied.
2. **0 stable losses and 0 flips** on the pinned `QF_LRA` draw, where "stable"
   means the 3×-per-arm recheck agrees — a raw mover is not a finding, and
   ADR-1966 had 11 of 18 vanish under exactly this recheck.
3. **0 stable losses on the HELD-OUT draw too.** The pinned list is the
   population every number in ADR-2111 and on the board was measured on, so an
   A/B on it is an A/B on the training set.
4. **No regression in the five exposure divisions**, each with its own
   denominator, and a division with no rows reported as **did not run** rather
   than as zero movement.
5. **`warm_cube_build = built` on a nonzero share of the treatment rows.** New
   here, and it is §4's lesson made a criterion: without it, criteria 1–4 are all
   satisfied by an arm that never ran.

Anything short of all five ships `off`.

## 8. What this lane did not do

PLACEHOLDER — filled at the end.

[ADR-1701]: adr-1701-the-theory-interface-gains-final-check-a-driver-owned-queue-lazy-explanation-and-dynamic-atoms.md
[ADR-1752]: adr-1752-the-lra-admission-cap-becomes-budget-relative.md
[ADR-1966]: adr-1966-a-rungs-refusal-of-a-construct-a-later-rung-owns-is-a-decline.md
[ADR-2045]: adr-2045-the-bound-is-not-the-wall-qf-lra-is-one-offline-dense-engine.md
[ADR-2055]: adr-2055-the-tableau-is-the-memory-and-capping-it-costs-eighteen-clean-exits.md
[ADR-2111]: adr-2111-qf-lra-what-the-same-simplex-does-differently.md
[ADR-2122]: adr-2122-lra-bound-propagation-into-the-sat-core.md
