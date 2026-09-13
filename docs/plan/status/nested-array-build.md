# Lane: nested-array-build — the nested array sort, built and measured

<!-- plan-section: lane-status -->

**Lane nested-array-build (`DONE`, nested-array-build, 2026-09-13).** ADR-1955's
design is built: `(Array I (Array J E))` parses, behind an arena-interned
`ArraySortId` in `ArraySortKey::Array`. **AUFLIRA moves from 9 to 158 of 200**
on the pinned full-span parity list, interleaved per file against `main` at
`f9075838e`, with **0 regressions and 0 disagreements**.

ADR: [ADR-1965](../../research/09-decisions/adr-1965-the-nested-array-prize-was-never-the-array-theory-it-was-congruence.md)
· artifact: [`bench-results/nested-array-build-20260913/`](../../../bench-results/nested-array-build-20260913/README.md)

## The re-size came first, and it went UP

Committed at `9d246c830` **before any change under `crates/`**, so the build's
number could be checked against it rather than fitted to it.

The instrument is an array-free surrogate: each `(Array I (Array J E))` becomes
a fresh uninterpreted sort and each `select` on it a fresh function. That
DELETES axioms (outer extensionality, outer read-over-write) and adds none, so
**surrogate `unsat` ⟹ original `unsat`** and a surrogate `sat` transfers
nothing. A file using an outer `store` is refused rather than rewritten.

    AUFLIRA 141/175 (80.6%)   AUFNIRA 115/121 (95.0%)
    ALIA      0/0   (36 of 36 refused)   ABV 1/1 (16 of 17 refused)
    total   257/297 (86.5%)  ->  projected 16,245 of ADR-1957's 20,399 ceiling

**The finding that mattered was the mechanism, not the number**: a surrogate
`unsat` is a file whose refutation needs only *congruence through the nested
read*. ADR-1955 sized the same population at ~1,135 by transferring a
family-matched control rate — from a family that, by its own table, does not
exist for AUFLIRA or AUFNIRA.

This is the first re-size in this repository that moved a projection **up**
(the five before: 143→6, 51→2, 173→10, 27,150→1,135, 19,620→0), and the reason
is structural: those were census narrowings, which can only shrink; this ran
the solver on a one-directional rewrite and asked what the query CONTENT
permits.

## What landed

`ArraySortKey::to_sort` now returns `Option<Sort>`, `None` for a nested
component. That one `None` propagates to `Sort::array_sorts` and
`Sort::array_widths`, so **every array route declines a nested sort by
construction rather than by audit**. Changing the return type (rather than
adding a second method) is what made the compiler enumerate all 41 call sites.

Three sites take the arena and recurse instead, because there `None`
under-reports rather than declines: `Features::note_sort` (mis-routes),
`datatype_elim::sort_mentions_datatype` (ADR-1920's non-terminating cycle) and
`write.rs::collect_uninterpreted_sort` (drops a `declare-sort` line).

## Soundness

`tests/nested_array_row.rs`, 12 tests, in `hooks/pre-push`. Every test is a
satisfiable query that must never return `unsat` or an unsatisfiable one that
must never return `sat`; every `Sat` is replayed against the ORIGINAL
assertions inside the test. Three positive controls plus a `Real`/`Int` pair
forbidding opposite answers keep it from reading as a solver stuck on
`unknown`.

Ten hand-built shapes cross-checked against z3 4.13.3 and cvc5 1.3.4: 3 we
decide `unsat` and all three agree, 7 we answer `unknown` and both references
decide. **Zero disagreements.**

Mutation controls, all `killed N`: `nested-array-sort` (6/1/1),
`nested-array-gate-map` (1), `nested-array-feature-scan` (1/1). The first
mutation — replacing the conservative `None` with `Some(Sort::Bool)` — kills
six tests, **four of them adversarial fixtures over satisfiable queries**: the
guard is what stands between a nested query and a wrong verdict, not between it
and an over-reach.

## What did NOT move, and it is pinned as tests

ALIA and ABV. 33 of 36 ALIA and 12 of 17 ABV winnable files **write** the outer
array, and outer read-over-write on a nested array is still undecided —
`outer_read_over_write_on_a_nested_array_is_undecided` in
`tests/nested_array_gate_map.rs`, which fails loudly when that changes.

## For the next lane

- The gate is named: outer read-over-write on a nested array
  (`RowCtx::resolve_select` has no arm for an array-valued base that is itself a
  `Select`). Re-sizing that lane needs a **different** instrument — the
  surrogate here refuses exactly those files by construction.
- Nested sequences (`Seq(Seq …)`) are still deferred; the interning template
  applies unchanged when a sequence route wants them.
- `axeyum-py` raises rather than exposing a nested array component. That is a
  real gap in the binding, deliberately smaller than a wrong sort crossing FFI.

### Landed commits

| commit | what |
|---|---|
| `9d246c830` | the re-size, committed before any code: the surrogate, its self-test, the sweep, 86.5% |
| `c3891327d` | the build: `ArraySortKey::Array(ArraySortId)`, 24 files, two suites, three mutation entries |

<!-- plan-section: landed-changes -->

| 2026-09-13 | nested-array-build | ADR-1955's nested array sort BUILT (`ArraySortKey::Array(ArraySortId)`): **AUFLIRA 9 → 158 of 200** interleaved against `main`, 0 regressions, 0 disagreements, 0 reference contradictions; re-sized BEFORE the build with an `unsat`-sound array-free surrogate (86.5%, projected 16,245) and the mechanism it found is the one that delivered — a nested AUFLIRA query needs **no array theory**, only congruence through the nested `select`; ALIA/ABV unmoved because their files WRITE the outer array, pinned as a failing-on-progress test; ADR-1965 |
