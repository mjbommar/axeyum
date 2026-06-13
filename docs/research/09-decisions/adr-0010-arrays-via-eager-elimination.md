# ADR-0010: Arrays (QF_ABV) Via Eager Elimination To QF_BV

Status: accepted
Date: 2026-06-13

## Context

The downstream consumer this stack is built backwards from — symbolic execution
of real programs — needs **memory**, i.e. arrays with `select`/`store`. The
first infosec client example
(`axeyum-solver/tests/symbolic_execution.rs`, 2026-06-13) is deliberately
memory-free for exactly this reason. The public QF_ABV corpus is already
fetched (3.4 GB under `corpus/public/`), and the roadmap's Phase 7 entry
requires an ADR for `select`/`store`, model replay, and the lowering route
before any array surface becomes public (foundational DAG gate).

The hard rules still apply: semantics must be written down first, every `sat`
model must replay against the original term, and the default build stays pure
Rust with no silent oracle fallback.

## Decision

Add a fixed-domain **array sort** and `select`/`store` to the IR, give them
executable read-over-write semantics in the ground evaluator, and decide
QF_ABV in the pure-Rust backend by **eagerly eliminating arrays to QF_BV**
before bit-blasting — not by a lazy array decision procedure (yet).

- **Sort and terms.** `Array { index: u32, element: u32 }` — a total map from
  `BV(index)` to `BV(element)`. Terms: `select(a, i) : BV(element)` and
  `store(a, i, e) : Array`. Array-sorted equality is deferred (extensionality
  needs more machinery); only `select`/`store` and array *symbols* are public
  first.
- **Evaluator (the semantic reference).** An array value is a finite map plus a
  default element. `store` updates the map functionally; `select` reads it,
  falling back to the default. This gives oracle-free ground truth for arrays,
  exactly as for BV.
- **Eager elimination to QF_BV** (a new preprocessing layer, before lowering):
  1. **Read-over-write.** Rewrite `select(store(a, i, e), j)` to
     `ite(i = j, e, select(a, j))`, repeatedly, until every remaining `select`
     reads an *array variable* (or a constant array).
  2. **Ackermann reduction.** Replace each distinct `select(a, idx)` over an
     array variable `a` by a fresh `BV(element)` symbol, and for every pair of
     selects `select(a, i)`, `select(a, j)` on the same `a`, add the consistency
     constraint `i = j -> fresh_i = fresh_j`.

  The result is pure QF_BV, decided by the existing AIG/CNF/SAT pipeline. This
  is sound and complete for quantifier-free arrays over finite bit-vector
  domains.
- **Model projection.** A `sat` model reconstructs each array variable as the
  finite map `{ idx_value -> fresh_value }` over the selected indices plus a
  default, and **replays against the original array term** through the
  evaluator before acceptance — the same level-1 evidence contract as BV.

## Evidence

- Eager read-over-write + Ackermann is the standard, simplest *sound and
  complete* route for QF_ABV in a bit-blasting solver (the STP lineage); it
  reuses the entire existing BV pipeline and lift/replay machinery rather than
  adding a new bit-blaster.
- The ground evaluator already provides oracle-free ground truth; array
  scenarios (memory-using programs in `axeyum-scenarios`) can self-check the
  same way BV scenarios do, and the symbolic-execution client can then analyze
  memory-using programs with concrete-re-execution cross-checks.
- Z3 remains available as a differential oracle for QF_ABV during bring-up.

## Alternatives

- **Lazy lemmas-on-demand array procedure** (Boolector/Bitwuzla style):
  far more scalable on large/aliased memories, but a substantial new engine
  with its own soundness obligations. Deferred to a later ADR, gated on eager
  elimination measurably blowing up on the QF_ABV corpus (per the benchmarking
  methodology) — the same "encodings first, complex engines when measured"
  discipline as the custom SAT core.
- **Ackermannization without read-over-write.** Incomplete in the presence of
  `store`; rejected.
- **Bounded/concrete-index memory only.** Simpler but does not cover symbolic
  addresses, which real symbolic execution needs; rejected as the public
  contract (though the read-over-write step naturally specializes to it).

## Implementation Note: Value Representation

Investigation (2026-06-13) surfaced a concrete constraint that shapes the first
sub-increment: `axeyum_ir::Value` currently derives `Copy`, but an array value
(a finite map plus a default element) cannot be `Copy`. Two routes:

- **Direct array evaluator (chosen).** `Value` gains a non-`Copy` `Array`
  variant, so `Value` moves from `Copy` to `Clone`. This keeps the ground
  evaluator the single executable semantic reference for arrays (read-over-write
  on real array values), against which the eager elimination is differentially
  tested. The cost is a mechanical `Copy → Clone` ripple across the crates that
  pass `Value` by copy; it is done as part of the IR sub-increment, behind the
  existing exhaustive tests.
- **Eliminate-before-evaluate (rejected as the reference).** Keep `Value` scalar
  and `Copy`, define array meaning solely by the elimination, and evaluate only
  the eliminated BV. Rejected because it makes the optimization (elimination)
  its own semantic reference, violating "semantics before optimization"; the
  elimination would have nothing independent to be checked against.

## Consequences

- `Sort` and `Op` gain array cases, rippling through the exhaustive matches in
  `axeyum-ir` (sort checks, evaluator, fmt, stats) and every downstream `match`
  on them; the pure-Rust backend gains an array-elimination preprocessing pass.
- The supported public fragment grows from QF_BV to QF_ABV (select/store, no
  array equality yet); the benchmark harness and scenario corpus extend to
  memory-using workloads.
- The lazy array procedure, array equality/extensionality, and QF_AUFBV (UF)
  remain future ADRs.
- Implementation lands as sound sub-increments (IR sort+ops+evaluator;
  then the elimination pass + model projection; then backend wiring + scenarios
  + the memory-using symbolic-execution client), each green and exhaustively
  checked, mirroring how the multiplier/divider and incremental stack landed.

## Implementation Progress

- **Sub-increment 1 — IR arrays (done, 2026-06-13).** Added the `Array` sort and
  `select`/`store` (`Op`, builders with sort/width checks), a non-`Copy`
  `ArrayValue` (default + normalized override map) with the `Value`
  `Copy → Clone` change rippled across all crates, and the read-over-write
  evaluator semantics. Exhaustive IR tests cover read-over-write,
  last-write-wins extensional equality, and the builder sort checks. Arrays are
  rejected by the bit-blasting and z3 backends (via the `first_unsupported_op`
  preflight) pending sub-increment 2.
- **Sub-increment 2 — eager elimination (done, 2026-06-13).**
  `axeyum_rewrite::eliminate_arrays` performs read-over-write +
  Ackermann reduction to pure QF_BV, with `ArrayElimination::project_model` for
  array-model reconstruction. Array equality and unsupported select bases return
  structured errors. Oracle-free tests prove denotation preservation under
  consistent models and Ackermann consistency.
- **Sub-increment 3 core — QF_ABV end to end (done, 2026-06-13).**
  `axeyum-solver/tests/arrays.rs` composes elimination → `SatBvBackend` →
  `project_model` → original-query evaluator replay, deciding aliasing loads,
  read-after-write (UNSAT), and aliasing SAT, each soundness-checked.
- **Sub-increment 3 finish (next):** first-class backend/bench wiring, QF_ABV
  scenarios, a memory-using symbolic-execution client, and eager-elimination
  blow-up measurement on the fetched QF_ABV corpus (to decide whether a lazy
  array procedure earns a future ADR).
