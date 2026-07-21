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
8. [Foundational logic and math DAG](08-planning/foundational-dag.md)
9. [Roadmap](08-planning/roadmap.md)
10. [Phase 3 exit audit](08-planning/phase3-exit-audit.md)
11. [Phase 4 exit audit](08-planning/phase4-exit-audit.md)
12. [Benchmarking and performance methodology](08-planning/benchmarking-and-performance-methodology.md)
13. [Decision records](09-decisions/README.md)

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
| `08-planning/` | Foundational DAG, roadmap, phase audits, benchmarking methodology, and open research questions. |
| `09-decisions/` | Decision records (ADRs) that close open questions. |
| `10-cas/` | **Computer algebra system** initiative: a proof-carrying CAS (SymPy/Mathematica compute surface) built on the decidable core. Vision, decidability map, gap analysis, phased build plan, running diary. |
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

The [foundational DAG](08-planning/foundational-dag.md) is the planning
checklist for that ownership: every public operator, rewrite, encoding,
backend, and later logic fragment needs a semantics source, a model/proof lift
story, and a replay or checker route before it graduates from experiment to
foundation.

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
- [x] Which pure Rust SAT backend should be evaluated first?
  - Answered: `rustsat-batsat` through RustSAT as the first CNF/SAT adapter
    ([ADR-0007](09-decisions/adr-0007-first-pure-rust-sat-adapter.md));
    varisat and splr remain design/reference and benchmark candidates.
- [x] Which evidence envelope should carry model replay, lift maps, benchmark
      provenance, and future proof artifacts?
  - Answered: layered, versioned envelope with query/source provenance, logic
    and semantics version, query schema, rule-set and later layer versions,
    resource config, replay, projection/lift-map references, proof/checker
    references, and separated triage
    ([ADR-0005](09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md)).

## Source Pointers

- Z3: https://github.com/Z3Prover/z3
- Bitwuzla: https://bitwuzla.github.io/docs/
- RustSAT: https://github.com/chrjabs/rustsat
- BatSat: https://github.com/c-cube/batsat
- Lean: https://lean-lang.org/
