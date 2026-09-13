# ADR-1965: the nested-array prize was never the array theory — it was congruence

Status: accepted
Index-summary: ADR-1955's `ArraySortKey::Array(ArraySortId)` is BUILT. `Sort` stays `Copy`, `Sort::Array { index, element }` keeps its shape, and `ArraySortKey::to_sort` now returns `Option<Sort>` — the `None` for a nested component propagates through `Sort::array_sorts` and `Sort::array_widths` to their 19 call sites in 8 modules, so every array route declines by construction rather than by audit, and its mutation kills six tests, four of them adversarial fixtures over satisfiable queries. **AUFLIRA moves from 9 to 159 of 200 and AUFNIRA from 3 to 122** interleaved against `main` on the pinned full-span lists, 0 regressions, 0 disagreements with `:status`, and z3 AND cvc5 each agreeing with all 269 moved verdicts at `no opinion 0` — so the zero is not the empty kind ADR-1957 warns about; two control divisions are unmoved. The reach was re-sized BEFORE the build with an array-free surrogate that is sound for `unsat` — projected 16,245, and the mechanism it identified is the one that delivered: **a nested AUFLIRA query needs no array theory at all, only congruence through the nested `select`.** ALIA and ABV do not move: their winnable files WRITE the outer array, and outer read-over-write is still undecided.
Index-status: accepted
Date: 2026-09-13

## Context

[ADR-1955](adr-1955-the-nested-array-sort-is-the-first-of-three-gates-and-the-only-one-the-ir-owns.md)
chose a design, measured its blast radius, and **did not build it**, because its
own arithmetic said the thing was worth ~1,135 files:

```
parse refusal            27,150 files    IR   — that ADR's design
  +  nested select base   7,530 files    solver
  +  Real-element arrays 19,620 files    solver
```

[ADR-1960](adr-1960-the-real-element-array-gate-was-three-gates-and-none-of-the-19620-were-behind-it.md)
demolished the third line: the 19,620 and the 27,150 are one population counted
once per gate. It sent the next lane back to `sort.rs`.
[ADR-1957](adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md)
boarded the four divisions at n = 200 and put the census ceiling at 20,399
files, 18,510 of it AUFLIRA.

That left one question, and ADR-1955 could not answer it with the method it
had: **how many of those files DECIDE once they parse?** Its answer came from
transferring a *family-matched control rate* onto each blocked count. Its own
table records that for AUFLIRA and AUFNIRA — 95% of the prize — no
family-matched control exists; ADR-1960 adds that of the AUFLIRA and AUFNIRA
files that do parse, `grep -c Array` returns **0**. There was no population to
transfer from.

## 1. The re-size, measured and committed before any code

`bench-results/nested-array-build-20260913/` was committed at `9d246c830`,
before a line under `crates/` changed, so the build's number could be checked
against it rather than fitted to it.

The instrument is an **array-free surrogate** that needs no IR change. Each
distinct `(Array I (Array J E))` becomes a fresh **uninterpreted** sort, and
every `select` on it a fresh uninterpreted function. The outer level loses the
array theory and keeps congruence; the inner level is untouched. The rewrite
DELETES axioms and adds none — outer extensionality and outer read-over-write
both go, and a file using an outer `store` is **refused** by the script rather
than rewritten, because that is the axiom being deleted. Deleting axioms admits
more models, so

> surrogate `unsat` ⟹ original `unsat`,

and a surrogate `sat` transfers nothing (reported in its own column, 0
everywhere). 186 of AUFLIRA's 187 winnable files carry `:status unsat`, so the
sound direction is the one that covers the population.

Over the pinned full-span winnable lists at the board's own 24 s budget:

| division | winnable | rewritten | refused | `unsat` | reach | ceiling | projected |
|---|---:|---:|---:|---:|---:|---:|---:|
| AUFLIRA | 187 | 175 | 12 | **141** | **80.6%** | 18,510 | 14,914 |
| AUFNIRA | 139 | 121 | 18 | **115** | **95.0%** | 955 | 908 |
| ALIA | 36 | **0** | 36 | 0 | — | 511 | 0 |
| ABV | 17 | **1** | 16 | 1 | 100.0% | 423 | 423 |
| **total** | **379** | **297** | **82** | **257** | **86.5%** | **20,399** | **16,245** |

The soundness check on the rewrite passed: no surrogate `unsat`, from axeyum or
from z3, lands on a file whose original is `sat` by declared `:status` or by
z3's board verdict.

**The finding that mattered was not the number but the mechanism.** A surrogate
`unsat` is a file whose refutation needs only *congruence through the nested
read*. 33 of 36 ALIA and 12 of 17 ABV winnable files write the outer array, so
they are outside the instrument entirely and it says nothing about their 511 +
423; the 16,245 is 98% AUFLIRA + AUFNIRA.

**Every re-size this lane was pointed at had moved a projection DOWN** —
143→6, 51→2, 173→10, 84→49, 27,150→1,135, 19,620→0 — and this one moved it up.
That is structural rather than lucky, and the distinction is worth keeping:
each of those six was a **census** narrowing, a count of blocked files being
resolved into a count of reachable ones, and a census can only shrink
(ADR-1945). This asked a different question — what does the query CONTENT
permit — and answered it by running the solver on a rewrite that is sound in
one direction. A measurement of that kind has no reason to land below its
starting point, because it has no starting point.

## 2. The build

ADR-1955's Option B, unchanged: `ArraySortKey::Array(ArraySortId)`, an
arena-interned id behind the **component** key, so `Sort::Array { index,
element }` keeps its shape and `Sort` stays `Copy` — which `TermNode`
hash-consing requires, because `Op::ConstArray { index }` and `Op::SeqEmpty(_)`
carry an `ArraySortKey` inside the interning key.

### The one `None` that carries the soundness

`ArraySortKey::to_sort` returns `Option<Sort>` and answers **`None`** for a
nested component, because expanding one needs the arena. Therefore
`Sort::array_sorts` (`index.to_sort()?`) and `Sort::array_widths` answer `None`
for a nested array. Those two helpers have **19 call sites across 8
modules** (`axeyum-rewrite/src/arrays.rs`, `axeyum-solver`'s `abv.rs`,
`abv/lazy_ext.rs`, `incremental.rs` and `auto.rs`, `axeyum-ir/src/eval.rs`,
`axeyum-smtlib/src/write.rs`, `axeyum-py`), and every array route reaches its
components through one of them — so **every array route declines a nested sort
by construction rather than by audit**.

Changing the return type rather than adding a second method is what made this
checkable: the compiler enumerated all 41 call sites, and each was visited and
given either the `None` (refuse) or the arena-aware `TermArena::array_key_sort`
(follow the interning). None was given a default.

The mutation control says the guard is load-bearing rather than decorative.
Replacing that `None` with `Some(Sort::Bool)` kills **six** tests, and the six
are the informative part:

```
the arena-free expansion REFUSES a nested component   killed 6:
  the_arena_free_helpers_refuse_a_nested_sort
  outer_read_over_write_may_not_be_satisfied
  a_strictly_fractional_nested_read_is_satisfiable_over_reals
  distinct_outer_rows_may_read_different_values
  a_transposed_nested_read_is_independent
  flat_row_still_decides_beside_a_nested_declaration
```

Four of those are adversarial fixtures over **satisfiable** queries. So without
that `None` the solver does not merely over-reach — it returns **wrong
verdicts** on nested arrays. With it, it returns `unknown`.

### The three sites where `None` is the WRONG answer

ADR-1955 named one; there are three, and they differ from the 19 sites above
in that under-reporting there does not *decline*, it *mis-routes* or *corrupts
output*.

| site | what stopping early costs |
|---|---|
| `Features::note_sort` (`auto.rs`) | a `Real` leaf under a nesting level is never seen, `has_real` / `has_non_bv_array` under-report, and the query is routed as something it is not — a wrong-verdict path, not a decline |
| `datatype_elim::sort_mentions_datatype` | a datatype under `(Array I (Array J D))` is invisible; that is ADR-1920's divert-vs-content mismatch, measured there as a non-terminating cycle |
| `write.rs::collect_uninterpreted_sort` | a carrier that appears only inside a nested array loses its `declare-sort` line and the written script does not re-parse |

All three now take the arena and recurse through the interned key.
`Features` also gains `has_nested_array`, so the refusal has a name a future
route can gate on instead of being an accident of a helper returning `None`.

`note_sort`'s guard is worth its own paragraph, because its **first mutation
SURVIVED** 12 front-door tests. The reason is not that the guard is decoration:
it is that every `Real` leaf a query *reads* also appears as the sort of the
`select` term that reads it, so the flag gets set the other way round. The
fixture that isolates it —
`note_sort_sees_a_leaf_that_only_exists_under_a_nesting_level` — is an equality
between two nested arrays where **no term in the arena is `Real`-sorted at
all**, with an assertion over the arena's terms proving that premise, and a flat
control so it cannot pass on a scan that sets every flag. With that fixture the
mutation is killed. ADR-1960 documented a gate rather than changing it when its
mutation survived; this is the other resolution of the same situation — build
the fixture that makes the guard observable.

### Where the Python binding stops

`axeyum-py` has no arena at the surfaces that expose an array component, so it
raises `ValueError` naming the limitation rather than guessing a sort. That is a
smaller surface than the Rust one, and saying so is cheaper than a wrong sort
crossing the FFI boundary.

## 3. What it reaches

Interleaved per-file A/B against `main` at `f9075838e`, both arms on the same
pinned core, arm order alternating per file, 24 s budget, over the **pinned
full-span 200-file parity lists** — the same lists ADR-1957's board used.

| division | files | `main` | this lane | moved | regressed |
|---|---:|---:|---:|---:|---:|
| **AUFLIRA** | 200 | 9 | **159** | **+150** | 0 |
| **AUFNIRA** | 200 | 3 | **122** | **+119** | 0 |
| ALIA | 200 | 0 | 0 | 0 | 0 |
| ABV | 200 | 4 | 4 | 0 | 0 |
| QF_ABV (control) | 200 | 188 | 187 | 0 | 1† |
| QF_BV (control) | 200 | 186 | 186 | 0 | 0 |



**AUFLIRA is 20,011 files, the largest division in the corpus, and carried the
largest gap on any board: 10 of 200 against z3's 197, 187 of them winnable.** It
is now 159. AUFNIRA goes from 3 to 122 against z3's 138. All 269 moved verdicts
are `unsat` — 269 of 269, not a mixture, which is the shape a congruence-only
capability has to produce and a check on the claim rather than a coincidence.

**Every moved verdict is `unsat`, and both references agree with every one of
them.** Re-running z3 4.13.3 and cvc5 1.3.4 on the 269 moved files at the same
24 s budget:

```
z3    agrees 269 / 269, no opinion 0, CONTRADICTS 0
cvc5  agrees 269 / 269, no opinion 0, CONTRADICTS 0
```

The "no opinion 0" is the part ADR-1957 requires to be published beside a
zero-disagreement claim, and it is the reason this zero is not the empty kind:
**both references decide every file the check covers**, so every one of those
agreements was an opportunity to fire. ADR-1955's own ABV cross-check had 119
verdicts and zero opportunities. No moved verdict contradicts the benchmark's
declared `:status` either.

† **The one raw regression is a timeout boundary, not a capability.** The A/B
prints it rather than smoothing it, and it was re-checked rather than argued
away: `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_stty…` needs about
25 s, so at the 24 s budget it flips for whichever arm the machine happens to
favour. Three interleaved re-runs at 24 s: base `unknown`/`unknown`/`unknown`,
lane `unknown`/`sat`/`unknown`. Three at 96 s: **both arms `sat`, three of
three**, base 25.02 / 25.22 / 24.82 s and lane 25.22 / 24.52 / 24.42 s. It is
the same file taking the same time in both arms.

**The controls are the point of including them.** ADR-1965 changes
`ArraySortKey::to_sort`, `Sort::array_sorts` and `Features::note_sort`, which
every flat array query passes through. QF_ABV and QF_BV are the two divisions
where we already do well, so a regression in that machinery would show there and
nowhere else in this table — the four target divisions decide too little to
reveal one.

### The re-size against the build

| | AUFLIRA | AUFNIRA | ALIA | ABV |
|---|---:|---:|---:|---:|
| surrogate reach (winnable) | 80.6% | 95.0% | no fragment | no fragment |
| measured moved (of 200) | **75.0%** | **59.5%** | 0 | 0 |

The surrogate over-predicted on both divisions it could speak about, and the
two denominators are not the same population — the surrogate ran on the 187 and
139 **winnable** files, the A/B on all 200. On the winnable denominator the
measured moves are 150/187 = 80.2% and 119/139 = 85.6%, against 80.6% and 95.0%
predicted. AUFLIRA lands within half a point; AUFNIRA is 9 points short.

For ALIA and ABV the surrogate declined to predict, and the build moved
nothing — which is the agreement that matters most, because a surrogate that
happily produced a number for a population it could not model would have been
the more dangerous instrument.


## 4. What it does NOT reach, pinned as tests

`tests/nested_array_gate_map.rs` is the map, and it is written to fail when the
frontier moves. Its gate-1 test fired in this lane exactly as designed —
`nested_array_sort_is_refused_at_parse` panicked with `GOOD NEWS` — and is now
`nested_array_sort_parses_and_round_trips`. Two gates that are still closed are
added rather than described:

* `outer_read_over_write_on_a_nested_array_is_undecided` — the outer array's
  read-over-write axiom. **This is why ALIA's 511 and ABV's 423 do not move**:
  33 of 36 ALIA and 12 of 17 ABV winnable files write the outer array.
* `inner_read_over_write_under_an_outer_select_is_undecided` — read-over-write
  on an inner array whose base is an outer `select`, the shape ADR-1955
  attributed to `RowCtx::resolve_select` having no arm for an array-valued base
  that is itself a `Select`.

Both pin `Unknown` specifically rather than "not unsat", because each query is
unsat by construction and a `sat` there would be a soundness defect rather than
a frontier move.

## 5. Soundness

`tests/nested_array_row.rs`, 12 tests, named in `hooks/pre-push`. Every test is
either a satisfiable query that must never return `unsat` or an unsatisfiable
one that must never return `sat`, and every `Sat` is replayed against the
**original** assertions inside the test rather than trusted from the route,
because the route's own replay is part of the subject.

The file cannot read as "a solver that answers `unknown` to everything", and it
takes three things together to say so:

1. three **positive controls** that must return `Unsat` — nested `select`
   congruence over `Int`, the same at ABV's 64-bit width, and a flat
   read-over-write in the same script as a nested declaration;
2. the `Real`/`Int` fractional pair, the same query one token apart, forbidding
   **opposite** answers: `0 < m[i][j] < 1` is satisfiable over `Real` and
   unsatisfiable over `Int`, so a solver stuck on `unsat` fails the first and
   one stuck on `sat` fails the second;
3. `flat_row_still_decides_beside_a_nested_declaration`, which fixes the
   regression direction the rest of the file cannot see.

Ten hand-built shapes were cross-checked against **z3 4.13.3** and **cvc5
1.3.4** at 15 s: three we decide `unsat` where all three agree, seven where we
answer `unknown` and both references decide. **Zero disagreements.**

Mutation controls (`scripts/tests/mutation_controls.py`), every one `killed N`:

| suite | guards | result |
|---|---:|---|
| `nested-array-sort` | 3 | killed 6 / 1 / 1 |
| `nested-array-gate-map` | 1 | killed 1 |
| `nested-array-feature-scan` | 2 | killed 1 / 1 |

## Decision

1. **Build ADR-1955's Option B, and lift the parse refusal.** Done.
2. **Do not add a nested array decision procedure in this lane.** The
   conservative `None` is the soundness argument, and the measurement says the
   AUFLIRA/AUFNIRA population does not need one. A route that abstracts the
   outer array would be a separate, one-directional (refute-only) capability
   with its own fence.
3. **ADR-1955's ~1,135 is superseded, in the other direction.** Its chain
   arithmetic was a transfer from a control that did not exist for 95% of the
   population; the reach is measured, not transferred.

## Consequences

* **AUFLIRA's board row was the worst on any board and is no longer.** The
  division is 20,011 files, the largest in the corpus.
* **ALIA and ABV are the next lane, and the gate is named**: outer
  read-over-write on a nested array, pinned as
  `outer_read_over_write_on_a_nested_array_is_undecided`. The surrogate refuses
  those files by construction, so re-sizing that lane needs a different
  instrument — one that keeps outer read-over-write and abstracts only
  extensionality.
* **A re-size can go UP, and the method that makes it possible is running the
  solver on a one-directional rewrite rather than narrowing a census.** A census
  attributing N files to a blocker can only shrink as blockers behind it are
  found (ADR-1945). A surrogate answers a different question — what does the
  query CONTENT permit — and is the instrument to reach for when the population
  behind a gate has no control to transfer from.
* **`Sort` stays `Copy` and `TermNode` hash-consing is untouched.** Nested
  sequences (`Seq(Seq …)`) remain deferred; the same template applies when a
  sequence route exists to want them.
