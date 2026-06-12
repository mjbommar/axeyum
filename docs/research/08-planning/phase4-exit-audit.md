# Phase 4 Exit Audit

Status: draft
Last updated: 2026-06-11

## Purpose

Record whether Phase 4's circuit, CNF, SAT-adapter, and replay obligations are
complete enough to start the Phase 5 pure-Rust BV backend work without hiding
gaps in code or status text.

## Scope

In scope:

- AIG structural hashing, evaluation, and debug export.
- Term-to-AIG lowering for the current supported Bool/BV subset.
- Tseitin CNF, DIMACS I/O, SAT adapter selection, and assignment replay.
- Default dependency evidence for the first pure-Rust SAT path.
- Explicit deferrals that should not block Phase 5 entry.

Out of scope:

- Multiplication, division, and remainder lowering.
- Proof-producing UNSAT.
- A standalone `axeyum-sat` crate or custom CDCL implementation.
- Public-corpus pure-Rust BV performance claims.

## Core Claims

- Phase 4 is complete for the supported scalar Bool/BV subset: values lower to
  AIG bits, encode to CNF, solve through `rustsat-batsat`, and replay satisfying
  assignments back to original Axeyum terms.
- ASCII AIGER (`aag`) debug export is implemented in `axeyum-aig`; binary AIGER
  remains unnecessary until external tooling requires it.
- The first SAT adapter path has no native solver or C/C++ build-tool dependency
  in the `axeyum-cnf` default dependency tree.
- Benchmark artifact fields for bit-blast/CNF/SAT/model-reconstruction timings
  were deferred at Phase 4 exit because `axeyum-bench` then exercised only the
  Z3 SMT-LIB backend path. The first Phase 5 slice now wires `--backend sat-bv`
  into `axeyum-bench` and records backend-layer statistics; artifact version 4
  introduced those fields, and version 5 adds node-budget and Z3-comparison
  provenance.
- UNSAT from the BatSat adapter remains lower-assurance until a proof-producing
  route and checker are added.

## Audit Evidence

| Obligation | Evidence | Result |
|---|---|---|
| Bit-order convention and shared value conversion | ADR-0006 plus `axeyum-ir` LSB-first conversion tests. | Satisfied. |
| AIG structural hashing and evaluator | `axeyum-aig` construction/evaluator tests. | Satisfied. |
| AIGER/debug export | `Aig::to_aiger_ascii` and deterministic ASCII AIGER smoke test. | Satisfied for ASCII debug export; binary export deferred. |
| Supported term-to-AIG lowering | `axeyum-bv` evaluator-vs-AIG tests for constants, symbols, Boolean connectives, bitwise ops, structural ops, add/sub/neg, comparisons, symbolic shifts, and constant rotates. | Satisfied for current subset. |
| Unsupported arithmetic is explicit | `bv_mul`, division, and remainder still return structured unsupported lowering errors. | Satisfied as an explicit boundary. |
| Tseitin CNF and DIMACS I/O | `axeyum-cnf` Tseitin, evaluator, parser, and round-trip tests. | Satisfied. |
| DIMACS corpus through SAT trait | `corpus/micro-cnf/*.cnf` plus `dimacs_micro_corpus_solves_through_sat_trait`. | Satisfied. |
| SAT adapter choice | ADR-0007 chooses `rustsat-batsat` through RustSAT after refreshing RustSAT, BatSat, splr, and varisat. | Satisfied. |
| `sat` assignment replay | `sat_assignment_lifts_through_cnf_aig_and_original_terms` checks CNF satisfaction, AIG node replay, reconstructed symbol model, and original evaluator replay. | Satisfied. |
| Default dependency evidence | `cargo tree -p axeyum-cnf --edges normal` shows `rustsat` 0.7.5, `rustsat-batsat` 0.7.5, and `batsat` 0.6.0 without native solver or C/C++ build-tool dependencies. | Satisfied locally; `cargo-deny` still requires installed tooling. |
| Benchmark/artifact layer telemetry | Phase 4 explicitly deferred this; the first Phase 5 slice now adds `axeyum-bench --backend sat-bv` backend stats for bit-blast/CNF layer counts and timings. Artifact version 5 further records node-budget and Z3-comparison provenance. | Deferred at Phase 4 exit; now closed by Phase 5 first slice. |
| Proof-backed UNSAT | ADR-0006 and ADR-0007 mark UNSAT lower-assurance until proof logging and a checker exist. | Explicitly deferred. |

## Design Implications

- Phase 5 should compose existing pieces rather than reselecting foundations:
  query planning, `axeyum-bv`, `axeyum-cnf`, `rustsat-batsat`, model
  reconstruction, and evaluator replay are the initial pure-Rust backend path.
- Artifact version 4 is the first Phase 5 schema that exercises the pure Rust
  path. It records backend kind, bit-blast/CNF timing, AIG nodes/inputs, CNF
  variables/clauses, SAT time, and model-lift time. Artifact version 5 keeps
  those fields and adds node-budget provenance plus optional Z3 oracle
  comparison. SAT result assurance still needs richer proof metadata once
  proof logging exists.
- Binary AIGER export, richer circuit rewriting, and aggressive CNF encodings
  should be demand-driven by debug tooling or benchmark artifacts, not added
  before the supported subset is measured.

## Risks

- `rustsat-batsat` gives useful adapter coverage but does not settle the future
  SAT trait shape for assumptions, incremental solving, proof logging, or the
  custom CDCL core.
- The pure-Rust backend may expose missing lowering support when full SMT-LIB
  scripts are routed through Phase 5; those cases must return structured
  unsupported results, not silently fall back to Z3.
- Dependency evidence from `cargo tree` is local and structural. License/advisory
  evidence still depends on `cargo-deny`, which was not installed in this
  environment.

## Open Questions

- [x] Which artifact schema version first carries pure-Rust bit-blast/CNF/SAT
      layer telemetry?
  - Answer: artifact version 4, introduced with `axeyum-bench --backend sat-bv`.
- [x] Which artifact schema version first carries pure-Rust-vs-Z3 public
      comparison metadata?
  - Answer: artifact version 5, introduced with `--compare-z3` and
    `--node-budget` provenance.
- [ ] Which proof checker discharges high-assurance UNSAT once proof logging is
      available?
- [ ] Which client or public corpus slice should be the first Phase 5
      pure-Rust-vs-Z3 differential baseline?

## Source Pointers

- Phase 4 roadmap: [roadmap](roadmap.md)
- Foundational DAG: [foundational-dag](foundational-dag.md)
- Phase 4 entry contract: [ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md)
- First pure-Rust SAT adapter: [ADR-0007](../09-decisions/adr-0007-first-pure-rust-sat-adapter.md)
- AIGER format: https://fmv.jku.at/aiger/FORMAT
