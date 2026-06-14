# Solving Strategies and the Memory Model

Status: draft
Last updated: 2026-06-13

This note researches the architecture of Axeyum's solving core and designs a
**swappable solving-strategy** layer so the system can move between a
high-memory eager implementation and a low-memory lazy one (today, between the
pure-Rust eager bit-blaster and the Z3 oracle), and grow toward Z3/cvc5,
Lean, and angr/unicorn parity. It is the research/design backing for
[ADR-0019](../09-decisions/adr-0019-swappable-solving-strategies.md).

It assumes the [north star](../00-orientation/north-star.md) destinations:
(1) foundation [where we are], (2) complete solver replacement, (3) Lean / angr
first-class.

## 1. The current architecture, as it actually is

The solver core is already layered, trait-based, and evidence-centric. The
seams matter for the design, so they are stated precisely.

- **IR + evaluator** (`axeyum-ir`): the trusted semantic reference. Every `sat`
  model is replayed here; it is the spec the rest is validated against.
- **Theory reductions** (`axeyum-rewrite`, wired in `combined.rs`): eager,
  exact, sequential — `arrays → (read-over-write + Ackermann) → UF →
  (Ackermann) → int → (bounded bit-blast) → QF_BV`. Each step ships a model
  projection back.
- **Core decision** behind the `SolverBackend` trait
  (`capabilities / check / check_query / last_stats`):
  - `SatBvBackend` — pure-Rust **eager** path: `term → AIG (axeyum-bv) → Tseitin
    CNF (axeyum-cnf) → rustsat-batsat`, then lift + **replay**.
  - `Z3Backend` — feature-gated oracle: translate → Z3 → lift.
  - `IncrementalBvSolver` — warm version of the eager path (persistent AIG +
    CNF + SAT), the symbolic-execution front end.
- **Native arithmetic**: `lra.rs` is a real exact-rational QF_LRA decision
  procedure (Fourier–Motzkin **and** a second simplex engine, complete for
  sat *and* unsat, Farkas certificates). `dpll_t.rs` is a **real lazy-SMT /
  DPLL(T) loop** (Boolean abstraction → SAT skeleton → theory check →
  conflict-driven blocking clauses), not a stub.
- **Dispatch** (`auto.rs`): `solve()` → `check_auto()` routes by *feature
  detection* (has-real → lazy LRA-DPLL; else eager all-theories), and a
  quantifier path (finite expansion, then E-matching / instantiation fallback).
- **Evidence** (`evidence.rs`): a pluggable envelope —
  `Sat(model)`, `Unsat(DRAT)`, `UnsatTermLevel` (exhaustive enumeration),
  `UnsatFarkas`, `UnsatLraDpll`, `Unknown(reason)` — each independently
  re-checkable via `Evidence::check`.
- **Governance**: `SolverConfig` budgets (timeout, deterministic rlimit,
  memory, node, CNF var/clause) with admission control, and a structured
  `Unknown(UnknownReason{kind, detail})` that is first-class, never an error.

The important truth: **the strategy seam already exists at the backend trait,
but it is not exposed.** `solve()`/`check_auto()` hardwire `SatBvBackend`; the
theory composition `check_with_all_theories<B>` is generic over the backend but
the top-level entry never lets a caller pick `B`. So "swap implementations"
is *latent* in the design and just needs to be lifted to a first-class knob.

## 2. The memory axis (the core of the user's request)

"High-memory vs low-memory" is not primarily about which SAT solver runs. It is
about **how much is materialized eagerly**:

| | High-memory (eager) | Low-memory (lazy / theory-aware) |
|---|---|---|
| Reduction | eliminate all theories up front | keep theory atoms; reason natively |
| Encoding | bit-blast the whole problem to one CNF in RAM | encode on demand; refine |
| Memory | O(bit-blasted circuit) — millions of clauses on real instances | O(active reasoning state) |
| Completeness (QF_BV) | complete, fully checkable (DRAT / term-level) | depends on the engine |
| Today | `SatBvBackend` (pure-Rust) | **only** `Z3Backend` |

This is exactly why the public-QF_BV frontier stalls: the eager pipeline hits
self-imposed CNF caps (the OOM guards on the dev host) and returns
`EncodingBudget` *unknown* — not because the SAT search failed, but because the
*materialization* is too big. The measured encoding micro-optimizations
(polarity encoding: +4–11%; Booth multiplier: regressive at the 8-bit frontier)
confirm the eager strategy is near its floor. **The lever is a low-memory
strategy, not a smaller eager encoding.** See PLAN.md Status (2026-06-13).

The pure-Rust stack has **no low-memory strategy yet** — the only low-memory
option is the Z3 oracle, which contradicts the pure-Rust identity (ADR-0002).
Closing that is the central destination-2 architecture task.

## 3. Gap analysis — what each target demands of the architecture

### 3a. Z3 / cvc5 (destination 2 — complete solver replacement)

Requirements and where Axeyum stands:

- **Theory breadth.** Have: QF_BV (full scalar set), arrays, EUF, conjunctive +
  Boolean-structured QF_LRA (native), bounded QF_LIA, first-cut quantifiers.
  Missing: floating point, strings/sequences/regex, datatypes, nonlinear
  (NIA/NRA), **unbounded** LIA (real integer reasoning, not bounded bit-blast),
  production quantifiers (MBQI), optimization (MaxSMT/OMT).
- **Low-memory core.** Z3 does not eagerly bit-blast by default; it has
  BV-specific theory solvers, preprocessing, and abstraction-refinement.
  Axeyum's only memory-frugal path is the oracle. **This is the binding gap on
  the one theory we do best.** Needs a pure-Rust low-memory BV strategy:
  lazy/abstraction-refinement bit-blasting and/or a native BV theory solver in a
  CDCL(T) loop (the `dpll_t.rs` skeleton generalizes).
- **Raw speed.** Real but priority-gated (ADR-0002 methodology): only after
  coverage and the memory architecture, since SAT time is not yet the binding
  constraint.
- **Surface + validation.** Have: `solve_smtlib` front door, incremental,
  artifacts. Missing: full SMT-LIB2 command set, get-proof/get-unsat-core
  surface, SMT-COMP-scale validation (gated by the OOM discipline).

### 3b. Lean (destination 3 — proving, kernel diversity)

- **Have:** a layered, independently-checkable `Evidence` envelope — the same
  untrusted-search/trusted-checking idea Lean's kernel-diversity argument uses.
- **Need:** evidence that rises above the clausal/Farkas level into
  **kernel-checkable proof terms**, an independent re-checking kernel (cf.
  nanoda), and proof export/import (cf. Alethe/lean-smt). The envelope is
  versioned and open, so this grows by adding `Evidence` variants and a kernel —
  *not* a rewrite. The mixed-theory `unsat` proof gap (currently `Unsat(None)`)
  is the first thing to close.

### 3c. angr / unicorn (destination 3 — program analysis)

- **Have:** `IncrementalBvSolver` (warm, push/pop, measured 5.64× clause reuse
  across shared-prefix path queries), arrays as a memory model, the ground
  evaluator as a concrete-execution oracle.
- **Need:** a real binary/IR frontend (lift + CFG), a realistic memory model
  (segmented/symbolic addresses), and symbolic execution + concrete emulation as
  first-class APIs. Today's `tests/symbolic_execution*.rs` is a hand-built
  register VM — the *shape* of the consumer, not the product. This is a new
  crate (e.g. `axeyum-symx`) sitting on the incremental solver; the solver work
  it forces back is low-latency incrementality and bounded-memory paths (gap
  3a again).

## 4. Design: a swappable solving-strategy layer

### Principle

A **`Strategy`** is a named solving policy. All strategies share the IR, the
`Query`, the `Model`/`CheckResult`/`Evidence` types, and the trust discipline
(every `sat` replayed through the evaluator; `unsat` carries checkable evidence
where the strategy can produce it). Strategies differ only in the
memory/completeness/speed tradeoff of *how they decide*. Because they share the
trust discipline, strategies are not just interchangeable — they are
**cross-validatable**: running two strategies and diffing verdicts is a
first-class capability and a direct expression of the project identity
("untrusted fast search, trusted small checking").

### The strategy set

- `EagerPureRust` — current pure-Rust eager bit-blast + theory elimination.
  High-memory, complete for QF_BV and eager-reducible theories, fully
  checkable. **Default.**
- `Oracle` *(feature `z3`)* — Z3 as a low-memory reference. Not pure-Rust;
  trusted externally, but `sat` is still replayed for parity. Its role stays
  bootstrap/cross-check per ADR-0002 — it is a *strategy you can select for
  comparison*, never a dependency the default build needs.
- *(future)* `LazyBitblast` / `NativeBv` — pure-Rust **low-memory**:
  abstraction-refinement bit-blasting (encode a Boolean skeleton, refine with
  bit-level lemmas on demand) and/or a native BV theory solver inside the
  CDCL(T) loop. This is the destination-2 architecture and the eventual
  Z3-class memory profile without the C dependency.
- *(future)* `Auto` — pick the best available strategy from the query shape and
  the configured budgets (e.g. small/decidable → eager; large → lazy).

### Layering

```
            Query / assertions  +  SolverConfig  +  Strategy
                                  │
        ┌─────────────────────────┴─────────────────────────┐
        │  shared: theory reductions are a *plan*, not a      │
        │  forced eager pass (a lazy strategy may keep atoms) │
        └─────────────────────────┬─────────────────────────┘
                                  │ strategy-specific core
     EagerPureRust         Oracle (z3)            LazyBitblast (future)
   eliminate→blast→SAT   translate→Z3        skeleton→refine-on-demand
                                  │
                 shared: Model lift + evaluator REPLAY + Evidence
```

The reductions stay shared but become a *plan* the strategy may consume eagerly
(eliminate now) or lazily (keep `select`/`store`/`apply`/arith atoms and let the
theory layer handle them). The first slice keeps reductions eager for all
strategies; the lazy strategy is where that generalizes.

### First implementable slice (this is small and real)

Expose the latent seam: a `Strategy` enum plus
`solve_with_strategy(arena, assertions, config, strategy)` that routes
`EagerPureRust` to the existing auto dispatch and `Oracle` (cfg `z3`) to the Z3
backend, both ending in the shared replay. Add a differential test that the two
strategies agree on a battery of queries (the oracle-free scenario catalog +
small mixed-theory cases). This makes "swap between the low-memory (Z3) and
high-memory implementations" a one-argument choice and validates parity — the
concrete capability requested — without committing to the larger lazy engine
yet. The default (no-C) build keeps only pure-Rust strategies.

## 5. Roadmap (architecture-first, OOM-safe)

1. **Strategy seam (now).** `Strategy` + `solve_with_strategy` + differential
   parity test. ADR-0019.
2. **Low-memory pure-Rust strategy (the destination-2 core).** Prototype
   abstraction-refinement bit-blasting on QF_BV: encode a coarse skeleton, run
   SAT, refine spurious models with bit-level lemmas. Measure memory vs the
   eager path on a *handful* of near-frontier instances (no corpus sweep).
   Generalize the `dpll_t.rs` loop to drive it. New ADR when the prototype shows
   the memory win.
3. **Coverage, in bounded units.** Unbounded QF_LIA (branch-and-bound over the
   existing simplex, replacing bounded bit-blast), then the next theory by
   value for program verification (datatypes, then FP/strings). Each: ADR +
   foundational-DAG check + oracle-free verification.
4. **Evidence toward Lean.** Close the mixed-theory `unsat` proof gap; grow the
   envelope toward kernel-checkable terms + an independent kernel.
5. **Symbolic-execution crate (destination 3).** `axeyum-symx` on the warm
   incremental solver + array memory model; a real lifter/CFG; then the
   angr/unicorn-shaped APIs.

Each step is a strategy or a theory behind the shared trait and evidence
discipline, so the architecture absorbs them without forking the core.
