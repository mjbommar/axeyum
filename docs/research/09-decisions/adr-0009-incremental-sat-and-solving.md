# ADR-0009: Incremental SAT And Incremental Solving

Status: accepted
Date: 2026-06-13

## Context

The high-level [`Solver`] façade (consumer-models iteration 2) exposes an
incremental surface — `assert`, `push`/`pop` scopes, and one-shot
`check_assuming` — but the underlying `SatBvBackend` is one-shot: every check
re-lowers terms to a fresh AIG, re-encodes a fresh CNF, and solves a fresh
`BatSat` instance. A symbolic-execution consumer (the angr-shaped workload this
stack is built backwards from) issues thousands of closely-related queries down
a path; re-doing all work per query throws away the warm solver's learned
clauses and re-pays bit-blasting each time.

ADR-0007 already chose `rustsat-batsat`, noting it "exposes `solve`,
`solution`, assumptions, and incremental interfaces". This ADR decides how
Axeyum uses that incrementality, staged so each step stays sound (every `sat`
replays against the original terms; CNF variable identities stay stable; no
silent fallback).

This closes the [research-questions](../08-planning/research-questions.md)
entries "What is the minimum incremental-solving API?" and "What survives across
queries: learned clauses, bit-blast caches, phases?"

## Decision

Add incremental solving as a layered capability, in two stages, with a stable
variable namespace and assumption-literal scoping.

**Stage 1 (this ADR, implemented now): an incremental CNF SAT primitive.**
`axeyum-cnf` gains `IncrementalSat`, a warm wrapper over `rustsat-batsat` that:

- keeps the solver instance across solves, so added clauses and learned clauses
  persist (monotone `add_clause`, with the variable namespace growing as
  clauses reference higher variables);
- supports one-shot assumptions via `solve_assuming`, mapping to BatSat's native
  `solve_assumps`, with the same cooperative-timeout stop callback as the
  one-shot path;
- self-checks every `sat` exactly as the one-shot path does — the returned
  assignment must satisfy all accumulated clauses *and* the assumptions — and
  marks `unsat` lower-assurance until a proof path exists (consistent with
  ADR-0007).

Assumption literals are the mechanism for SMT-LIB `push`/`pop`: a scope gets a
selector variable, assertions in that scope are added as
`(¬selector ∨ clause)`, and a check solves under the selectors of the currently
open scopes. Popping simply stops asserting a scope's selector. This is sound
because the permanent clause database only grows; deactivation is by assumption,
never by clause removal.

**Stage 2 (implemented 2026-06-13): incremental bit-blasting.** A persistent
lowering context keeps one AIG (with its structural hashing), one symbol→input
map, and one term memo across asserts, emitting only the new AIG cone's clauses
into a shared `IncrementalSat`. A sibling incremental BV solver drives this so
the consumer gets end-to-end incremental solving. Delivered as three pieces,
each preserving the lift maps and model replay:

- `axeyum_bv::IncrementalLowering` — persistent AIG + symbol/term memo; proven
  structurally identical to batch `lower_terms`, so it inherits the batch path's
  per-operator correctness.
- `axeyum_cnf::IncrementalCnf` — simple per-node Tseitin over `IncrementalSat`
  (one CNF variable per AIG node), with selector-guarded roots for push/pop and
  direct AIG-node-value lifting.
- `axeyum_solver::IncrementalBvSolver` — `assert`/`push`/`pop`/`check`/
  `check_assuming`; push/pop compile to scope selector literals, `check_assuming`
  to ephemeral selectors, and every `sat` model is lifted (CNF → AIG node
  values → symbols) and replayed against the original terms with the evaluator
  before being returned.

Known limitations, deferred to a follow-up: the incremental encoder uses simple
per-node Tseitin rather than the one-shot path's sparse-CNF optimizations, and
ephemeral assumption selectors leak clauses into the monotone database (an
activation-literal GC/rebuild policy is future work).

## Evidence

- RustSAT's `SolveIncremental` trait provides `solve_assumps`, and the
  `axeyum-cnf` `Capabilities` already advertise `assumptions: Supported`.
- The one-shot path's variable reservation, clause translation, model
  extraction, and model self-check helpers are reused verbatim by the
  primitive, so the trusted lifting/replay code is unchanged.
- Stage 1 ships with tests: monotone add-then-solve across multiple solves,
  assumptions that flip a satisfiable formula to unsat for one solve only
  (proving non-persistence), warm reuse after adding a contradictory clause,
  and a selector-literal push/pop emulation that matches the façade semantics.

## Alternatives

- **Re-lower per check but keep the solver warm.** Rejected: re-lowering
  produces fresh CNF variables, so a warm solver's state is meaningless — warm
  reuse requires a stable variable namespace, i.e. persistent lowering.
- **Clause removal for pop.** Rejected: CDCL solvers do not support sound
  arbitrary clause deletion; selector/assumption literals are the standard,
  sound mechanism.
- **Do stages 1 and 2 together now.** Rejected for risk: incremental
  bit-blasting touches `axeyum-bv`, `axeyum-cnf`, and `axeyum-solver` and must
  preserve replay soundness; staging keeps each change reviewable and green.

## Consequences

- Axeyum has a sound, tested incremental SAT primitive and a recorded design
  for end-to-end incremental solving.
- The `Solver` façade's incremental interface is now backed by a real
  incremental engine at the SAT layer; wiring it through bit-blasting (stage 2)
  no longer needs a design decision, only implementation.
- A standalone `axeyum-sat` crate remains deferred (ADR-0007); the primitive
  lives in `axeyum-cnf` next to the one-shot adapter until stage 2 or a second
  adapter exercises the boundary further.
- `unsat` from the incremental path stays lower-assurance until the proof path
  (a future ADR) lands, exactly as for the one-shot adapter.
