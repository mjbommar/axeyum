# C And C++ Solver Ecosystem

Status: draft
Last updated: 2026-06-10

## Purpose

Summarize mature solver infrastructure Axeyum should learn from and interoperate with.

## Scope

In scope:

- SMT solvers, SAT solvers, and symbolic execution systems implemented in C/C++.

Out of scope:

- Exhaustive solver benchmarking.
- License/legal conclusions beyond basic awareness.

## Core Claims

- The mature high-performance SMT ecosystem is still primarily C and C++.
- Native APIs beat shelling out for performance, incrementality, and model handling.
- Solver internals separate term representation, preprocessing, theory solving,
  SAT solving, model construction, and proof/certificate machinery.
- Axeyum should use these systems as backends and correctness oracles while owning
  its own Rust-native IR and lowering pipeline.

## SMT Solvers

| Solver | Notes | Relevance |
|---|---|---|
| Z3 | Broad SMT solver from Microsoft Research with C/C++ core and bindings. | Primary backend/oracle candidate. |
| cvc5 | Broad SMT solver with strong theory coverage. | Cross-checking and alternative backend. |
| Bitwuzla | Successor lineage to Boolector, strong for BV/arrays/FP. | Key BV backend comparison. |
| Boolector | Archived, historically important BV/array solver. | Design reference and legacy benchmark point. |
| STP | Efficient SMT solver for bit-vectors. | Program-analysis historical baseline. |
| Yices | Mature SMT solver with C API. | Alternative backend and design comparison. |

## SAT Solvers

| Solver | Notes | Relevance |
|---|---|---|
| CaDiCaL | Modern CDCL solver with documented C++ API. | Design reference for maintainable high-performance SAT. |
| Kissat | Highly optimized SAT solver from the same research lineage. | Performance reference. |
| MiniSat/Glucose | Foundational CDCL designs. | Algorithmic reference and educational baseline. |
| CryptoMiniSat | SAT solver with richer inprocessing and XOR support. | Crypto/infosec workload comparison. |

## Symbolic And Verification Systems

| System | Notes | Relevance |
|---|---|---|
| KLEE | LLVM symbolic execution engine. | Program-analysis architecture reference. |
| CBMC | Bounded model checker for software. | BMC and verification architecture reference. |
| angr/Triton/BINSEC/Miasm | Binary analysis and symbolic execution systems. | Client-side use case models. |

## Design Implications

- Provide backend crates for native solvers without making them mandatory.
- Keep an SMT-LIB importer/exporter for interoperability, but do not make text
  protocols the internal representation.
- Use external solvers for differential testing of Axeyum rewrites and bit-blasting.
- Study SAT solver clause database and watch-list layouts before implementing a
  custom CDCL core.

## Risks

- External solver behavior differs on `unknown`, models, undefined operators, and
  simplification side effects.
- Licensing and distribution constraints vary by solver.
- Matching mature solver performance is a long-term research project.

## Open Questions

- [ ] Which native backend ships first: Z3, Bitwuzla, cvc5, or a trait-only layer?
- [ ] Should Axeyum support solver-specific options in a typed way?
- [ ] Should benchmark corpora include SMT-COMP, SAT Competition, and program-analysis queries?

## Source Pointers

- Z3: https://github.com/Z3Prover/z3
- cvc5: https://cvc5.github.io/
- Bitwuzla: https://bitwuzla.github.io/docs/
- Boolector: https://github.com/Boolector/boolector
- STP: https://github.com/stp/stp
- Yices: https://yices.csl.sri.com/
- CaDiCaL: https://github.com/arminbiere/cadical
- Kissat: https://github.com/arminbiere/kissat
- KLEE: https://klee-se.org/
- CBMC: https://www.cprover.org/cbmc/

