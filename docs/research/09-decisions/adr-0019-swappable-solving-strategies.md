# ADR-0019: Swappable Solving Strategies

Status: accepted
Date: 2026-06-13

## Context

The path to destination 2 (a complete Z3/cvc5-class solver) is gated not by the
SAT search but by the **memory model**: the pure-Rust core eagerly bit-blasts
the whole problem into one CNF, so real instances blow memory and the pipeline
returns `EncodingBudget` *unknown* under the OOM-guard caps. Encoding
micro-optimizations are near their floor (polarity encoding +4–11%; a verified
Booth multiplier was *regressive* at the 8-bit frontier and reverted). The
measured conclusion is that the lever is a **low-memory solving strategy**, not a
smaller eager encoding — and today the only low-memory option is the Z3 oracle,
which contradicts the pure-Rust identity (ADR-0002).

The architecture already separates theory reductions, the `SolverBackend` trait,
the dispatcher, and the `Evidence` envelope; `SatBvBackend` (eager, high-memory)
and `Z3Backend` (low-memory oracle) are both backends. But the top-level
`solve()`/`check_auto()` hardwire the pure-Rust eager path, so "swap between the
low-memory and high-memory implementations" — the capability the user asked for
— is latent but not exposed.

This closes the architecture question raised in the research note
[solving-strategies-and-memory-model](../03-architecture/solving-strategies-and-memory-model.md)
and connects to the backend-model and incrementality notes in `03-architecture`.

## Decision

**Make the solving strategy a first-class, swappable choice behind one entry
point, with all strategies sharing the IR, result, evidence, and replay
discipline so they are interchangeable *and* cross-validatable.**

A `Strategy` value selects the solving policy:

- `EagerPureRust` — the existing pure-Rust eager bit-blast + theory-elimination
  pipeline. High-memory, complete for QF_BV and eager-reducible theories, fully
  checkable. The default; the only strategy in the no-C build besides future
  pure-Rust ones.
- `Oracle` (feature-gated on `z3`) — Z3 as a low-memory *reference* strategy,
  selectable for comparison and cross-validation. `sat` is still replayed
  through the evaluator. Its role remains bootstrap/cross-check per ADR-0002; the
  default build never requires it.
- Future strategies (`LazyBitblast`/`NativeBv`, `Auto`) slot in behind the same
  entry point and discipline without forking the core.

The entry point `solve_with_strategy(arena, assertions, config, strategy)`
returns the same `CheckResult` for any strategy; every `sat` is replayed; every
strategy's `unsat` carries whatever checkable evidence it can produce. Running
two strategies and diffing verdicts is a supported, first-class operation.

## Evidence

- Architecture mapping (this session) confirmed the seam already exists at the
  `SolverBackend` trait and `check_with_all_theories<B>`, so exposing strategy
  selection is a lift, not a rewrite.
- Measured dead-ends that motivate a strategy axis rather than more encoding
  work: polarity encoding (+4–11%), Booth multiplier (regressive at width 8),
  recorded in PLAN.md Status (2026-06-13).
- Existing native/lazy machinery (`lra.rs` simplex + Farkas, `dpll_t.rs` real
  DPLL(T) loop) shows the codebase already supports non-eager strategies behind
  the same result/evidence types — the generalization target for a low-memory
  BV strategy.
- The incremental warm path's measured 5.64× clause-reuse win shows the shared
  infrastructure a future lazy strategy builds on.

## Alternatives

- **Keep optimizing the eager encoding.** Rejected: measured to be near its
  floor; does not address the memory wall that produces the `EncodingBudget`
  unknowns.
- **Make Z3 the low-memory production path.** Rejected: violates the pure-Rust
  identity (ADR-0002); Z3 stays a selectable reference/oracle strategy only.
- **Jump straight to a lazy CDCL(T) BV engine.** Deferred, not rejected: it is
  the next strategy, but it needs a prototype + memory measurement and its own
  ADR. Exposing the seam first lets that engine land as one more strategy
  behind a stable entry point, validated against the eager one.
- **A trait-object `Box<dyn Strategy>` registry now.** Deferred: an enum is
  enough for the current strategy set and keeps the no-C build trivially
  feature-gated; a registry can come if external strategies appear.

## Consequences

- **Easier:** selecting low-memory (Z3) vs high-memory (eager pure-Rust) for any
  query is one argument; differential cross-checking across strategies becomes a
  first-class test and debugging tool; a future low-memory pure-Rust strategy
  lands behind the same entry point without disturbing callers.
- **Harder / to watch:** strategy proliferation must not fragment the trust
  discipline — every strategy MUST end in evaluator replay for `sat` and should
  produce checkable `unsat` evidence; this is a review rule, not enforced by the
  type system yet.
- **Revisited when:** the low-memory pure-Rust strategy prototype exists — a new
  ADR will record whether it generalizes `dpll_t.rs` (abstraction-refinement) or
  introduces a native BV theory solver, with the memory measurement that
  justifies it. `Auto` strategy selection is specified then, once there is more
  than one pure-Rust strategy to choose between.
