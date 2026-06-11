# Axeyum Research Index

Status: draft
Last updated: 2026-06-11

## Purpose

This tree captures the research foundation for Axeyum: a Rust-first automated
reasoning stack for logic, constraints, symbolic execution, model finding, and
checkable evidence.

The documents are organized as research notes, not implementation code. Each
note follows a common shape so decisions can be reviewed and revised without
losing context.

## Reading Order

1. [Mission and scope](00-orientation/mission-and-scope.md)
2. [North star: general reasoning, logic, proving](00-orientation/north-star.md)
3. [Automated reasoning foundations](01-foundations/automated-reasoning.md)
4. [C and C++ solver ecosystem](02-ecosystems/cpp-solver-stack.md)
5. [Rust ecosystem](02-ecosystems/rust-ecosystem.md)
6. [System architecture](03-architecture/system-architecture.md)
7. [Crate boundaries](03-architecture/crate-boundaries.md)
8. [Roadmap](08-planning/roadmap.md)
9. [Benchmarking and performance methodology](08-planning/benchmarking-and-performance-methodology.md)
10. [Decision records](09-decisions/README.md)

## Folder Map

| Folder | Purpose |
|---|---|
| `00-orientation/` | Project scope, vocabulary, and framing. |
| `01-foundations/` | Math and CS foundations: logic, transition systems, proof assistants. |
| `02-ecosystems/` | Existing C/C++, Rust, and verification ecosystem comparisons. |
| `03-architecture/` | Proposed stack architecture and crate boundaries. |
| `04-data-structures/` | Core representations: terms, circuits, CNF, clauses, models, proofs. |
| `05-algorithms/` | Algorithms: rewriting, bit-blasting, CDCL SAT, arrays, EUF. |
| `06-rust-strategy/` | Rust-specific implementation and performance principles. |
| `07-verification/` | Evidence, checking, differential testing, and soundness strategy. |
| `08-planning/` | Roadmap, benchmarking methodology, and open research questions. |
| `09-decisions/` | Decision records (ADRs) that close open questions. |
| `templates/` | Templates for future research notes. |

## Research Template

New files should start from [templates/research-note.md](templates/research-note.md)
and include:

- Purpose
- Scope
- Core claims
- Design implications
- Open questions
- Source pointers

## Current Thesis

Axeyum should own the reusable reasoning substrate:

```text
typed term IR
  -> rewrites and canonicalization
  -> query planning
  -> solver backend interface
  -> bit-vector bit-blasting
  -> circuit/CNF lowering
  -> SAT solving
  -> model, proof, and certificate checking
```

External solvers remain important as oracles and high-performance backends, but
the long-term research value comes from owning the lower layers cleanly enough
to experiment with representations, algorithms, and evidence checking.

## Open Questions

- [x] Which crate layout should be implemented first?
  - Answered: start with two crates
    ([ADR-0001](09-decisions/adr-0001-vertical-slice-first.md)); later
    format and benchmark crates were split after use proved the boundaries.
- [x] Which native solver backend should be the first oracle?
  - Answered: Z3 first
    ([ADR-0001](09-decisions/adr-0001-vertical-slice-first.md),
    [ADR-0002](09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md));
    Bitwuzla remains a later differential candidate.
- [ ] Which pure Rust SAT backend should be evaluated first?
  - Evaluate against the [benchmarking methodology](08-planning/benchmarking-and-performance-methodology.md);
    varisat's proof output weighs in its favor for the evidence thesis, but it
    is effectively unmaintained (last release 2019) — splr and rustsat are the
    actively maintained alternatives.

## Source Pointers

- Z3: https://github.com/Z3Prover/z3
- Bitwuzla: https://bitwuzla.github.io/docs/
- RustSAT: https://github.com/chrjabs/rustsat
- Lean: https://lean-lang.org/
