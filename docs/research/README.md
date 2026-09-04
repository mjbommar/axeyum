# Axeyum research index

This tree is the durable design record for Axeyum: foundations, ecosystem
research, architecture, algorithms, verification strategy, planning contracts,
and accepted decisions. Notes preserve reasoning and context; they are not a
second live status tracker.

For current state and priority, start with:

1. [Project State](../PROJECT-STATE.md) — public built/measured/partial summary.
2. [Root `PLAN.md`](../../PLAN.md) — current status, ordered queue, stop
   conditions, and resume protocol.
3. [Capability matrix](08-planning/capability-matrix.md) — generated assurance
   claims and evidence routes.
4. [Support matrix](08-planning/support-matrix.md) — parser, IR, solver, and
   proof support by fragment.
5. [Trust ledger](08-planning/trust-ledger.md) — trusted versus independently
   checked boundaries.

A dated note may accurately describe an earlier checkpoint while being stale as
current status. Keep that history intact and route present-tense claims through
the authorities above.

## Recommended reading paths

### Project identity and architecture

1. [Mission and scope](00-orientation/mission-and-scope.md)
2. [North star: general reasoning, logic, and proving](00-orientation/north-star.md)
3. [Computable knowledge: extending the flywheel from Mathlib to the world](00-orientation/computable-knowledge-world-graph.md)
4. [Automated reasoning foundations](01-foundations/automated-reasoning.md)
5. [System architecture](03-architecture/system-architecture.md)
6. [Crate boundaries](03-architecture/crate-boundaries.md)
7. [Models, proofs, and certificates](04-data-structures/models-proofs-certificates.md)
8. [Evidence and checking](07-verification/evidence-and-checking.md)

### Implementation and planning

1. [Foundational dependency DAG](08-planning/foundational-dag.md)
2. [Roadmap](08-planning/roadmap.md)
3. [Benchmarking methodology](08-planning/benchmarking-and-performance-methodology.md)
4. [Frontier ratchet reference frame](08-planning/frontier-ratchet-reference-frame.md)
5. [Research questions](08-planning/research-questions.md)
6. [Decision records](09-decisions/README.md)
7. [Detailed engineering record](../plan/README.md)

### Ecosystem context

- [C and C++ solver ecosystem](02-ecosystems/cpp-solver-stack.md)
- [Rust ecosystem](02-ecosystems/rust-ecosystem.md)
- [Formats and interchange](02-ecosystems/formats-and-interchange.md)
- [Symbolic execution and verification](02-ecosystems/symbolic-execution-and-verification.md)
- [Agentic binary-security positioning](02-ecosystems/agentic-binary-security-positioning.md)

## Folder map

| Folder | Purpose |
|---|---|
| [`00-orientation/`](00-orientation/) | Scope, vocabulary, and project framing. |
| [`01-foundations/`](01-foundations/) | Logic, semantics, transition systems, and proof-assistant foundations. |
| [`02-ecosystems/`](02-ecosystems/) | Solver, checker, language, and verification ecosystem comparisons. |
| [`03-architecture/`](03-architecture/) | System boundaries, backend model, lifecycle, and resource architecture. |
| [`04-data-structures/`](04-data-structures/) | Terms, circuits, CNF, SAT state, models, proofs, and certificates. |
| [`05-algorithms/`](05-algorithms/) | Rewriting, bit-blasting, SAT, theory solving, and reconstruction designs. |
| [`06-rust-strategy/`](06-rust-strategy/) | Rust API, implementation, concurrency, performance, and observability principles. |
| [`07-verification/`](07-verification/) | Evidence, independent checking, differential testing, and assurance strategy. |
| [`08-planning/`](08-planning/) | Roadmap, foundational contracts, live generated authorities, and open research questions. |
| [`09-decisions/`](09-decisions/README.md) | Numbered ADRs that accept or reject consequential design choices. |
| [`10-cas/`](10-cas/README.md) | Proof-carrying computer-algebra initiative and its paused research diary. |
| [`templates/`](templates/) | Templates for new research notes. |

## How to add or change research material

Start a new note from
[`templates/research-note.md`](templates/research-note.md). State its purpose,
scope, claims, design implications, open questions, and sources. Prefer a new
dated result or amendment over rewriting an observed historical result.

Before adding a public operator, rewrite, encoding, backend, evidence artifact,
or logic fragment:

1. check the [foundational DAG](08-planning/foundational-dag.md);
2. check [research questions](08-planning/research-questions.md) and existing
   [ADRs](09-decisions/README.md);
3. write an ADR when the choice changes a public contract or trust boundary;
4. update the generated capability/support/trust authorities through their
   owning source and generator, never by hand.

ADR status is recorded in each ADR and its index. An unchecked question in an
older research note does not supersede a later accepted ADR.

## Current thesis

Axeyum owns a reusable reasoning substrate: typed terms, semantics-preserving
rewrites, explicit query and strategy contracts, theory solving, lowering to
circuits and CNF where appropriate, SAT search, model replay, and proof or
certificate checking. Fast search may be untrusted; supported definitive
results must identify a replay, checker, certificate, or explicit trust gap.

External solvers remain valuable as differential oracles and feature-gated
bootstrap backends. They do not replace the pure-Rust product path or erase the
need for independently checkable evidence.

## Primary external projects

- [Z3](https://github.com/Z3Prover/z3)
- [cvc5](https://github.com/cvc5/cvc5)
- [Bitwuzla](https://bitwuzla.github.io/docs/)
- [RustSAT](https://github.com/chrjabs/rustsat)
- [BatSat](https://github.com/c-cube/batsat)
- [Lean](https://lean-lang.org/)
