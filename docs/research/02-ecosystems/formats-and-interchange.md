# Formats And Interchange

Status: draft
Last updated: 2026-06-10

## Purpose

Catalogue the external formats Axeyum must read or write, and decide which are
load-bearing for testing versus convenience exports.

## Scope

In scope:

- Problem formats, proof formats, and model/witness formats.

Out of scope:

- Full parser implementation plans.
- Axeyum-native serialization design (covered by data-structure notes).

## Core Claims

- SMT-LIB 2 parsing (not just printing) is load-bearing, not optional: the
  SMT-LIB benchmark library is the only large corpus available for testing the
  rewriter and bit-blaster before Axeyum has clients.
- DIMACS and AIGER are cheap to support and unlock SAT Competition corpora and
  circuit tooling (ABC) respectively.
- BTOR2 deserves early attention: it is the word-level transition-system
  format from the Boolector lineage, directly matching the
  programs-as-transition-systems framing, and comes with a benchmark corpus
  (HWMCC) and reference tooling.
- Interchange formats are boundaries, never internal representations.

## Format Inventory

| Format | Role | Priority |
|---|---|---|
| SMT-LIB 2 | Problem import/export, benchmark ingestion, debug dumps. | High; parse and print. |
| DIMACS CNF | SAT problem import/export. | High; trivial cost. |
| DRAT / LRAT / FRAT | SAT unsat proofs (see proof-formats note). | High for evidence thesis. |
| AIGER | Circuit import/export, interop with ABC. | Medium; early export useful for debugging the AIG layer. |
| BTOR2 | Word-level transition systems, HWMCC corpus. | Medium; valuable for BMC-style clients. |
| Alethe / LFSC / CPC | SMT proof formats from cvc5/veriT lineage. | Low initially; consume, do not produce. |
| WCNF / pseudo-Boolean | MaxSAT and optimization. | Deferred. |

## Design Implications

- Plan a dedicated format crate (for example `axeyum-smtlib`) or per-format
  modules in `axeyum-cli`; parsers should not live inside `axeyum-ir`.
- The SMT-LIB parser only needs the QF_BV/QF_ABV slice initially; reject the
  rest with clear diagnostics rather than half-supporting it.
- Every format gets round-trip tests (parse, print, reparse, compare interned
  terms) as soon as it exists.
- Benchmark ingestion should record the source corpus and file hash so results
  are reproducible.

## Risks

- SMT-LIB has dark corners (`define-fun`, `let` scoping, named annotations,
  push/pop in scripts); scoping the parser to benchmarks-as-data avoids
  building a full interpreter prematurely.
- Format support can silently become the project's main surface area; keep
  parsers thin and corpus-driven.

## Open Questions

- [ ] Should the SMT-LIB parser handle full scripts (push/pop, get-model) or
      only single check-sat benchmarks first?
- [ ] Is BTOR2 import worth doing before arrays land in the IR?
- [ ] Should AIGER export precede AIGER import?

## Source Pointers

- SMT-LIB benchmarks: https://smt-lib.org/benchmarks.shtml
- AIGER format: https://fmv.jku.at/aiger/
- BTOR2 format and tools: https://github.com/Boolector/btor2tools
- Hardware model checking competition: https://hwmcc.github.io/
- ABC synthesis/verification system: https://github.com/berkeley-abc/abc
