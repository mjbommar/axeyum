# Bit-Blasting

Status: draft
Last updated: 2026-06-11

## Purpose

Define the path from bit-vector terms to Boolean circuits and SAT.

## Scope

In scope:

- BV operation lowering, circuit generation, CNF, and model lifting.

Out of scope:

- Floating-point bit-blasting.

## Core Claims

- Pure Rust QF_BV solving can start with bit-blasting to SAT.
- The first backend should support a small, well-tested BV subset before chasing
  complete SMT-LIB coverage.
- Model reconstruction is as important as satisfiability.
- External SMT solvers should be used as differential oracles for bit-blaster tests.

## Operation Lowering

| BV op | Lowering sketch |
|---|---|
| `not` | Per-bit inversion. |
| `and/or/xor` | Per-bit gates. |
| `add/sub` | Ripple carry first; adder tree variants later. |
| `eq/ne` | XOR bits, reduce. |
| `ult/ule` | Comparator circuit. |
| `concat` | Bit-vector append. |
| `extract` | Slice. |
| `zext/sext` | Append zero or sign bits. |
| `ite` | Per-bit mux. |
| `mul` | Partial products plus adder tree. |
| `div/rem` | Defer or implement with careful bounded algorithms. |

## Initial Subset

```text
Bool
BV constants and symbols
not/and/or/xor
add/sub
eq/ne/ult/ule
concat/extract/zext/sext/trunc
ite
```

## Design Implications

- Represent bit-vectors as ordered slices of Boolean wires.
- Keep one bit-order convention and document it everywhere.
- Preserve maps from original terms to output bits.
- Treat division, wide multiplication, and shifts by symbolic amounts as later
  milestones unless immediate workloads require them.
- The Phase 4 convention is LSB-first: wire vector element `i` denotes SMT-LIB
  bit index `i` and numeric weight `2^i`; constants and models use shared
  conversion helpers
  ([ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md)).
- The current `axeyum-bv` slice lowers the cheap Bool/BV, structural,
  ripple-carry arithmetic (`bvneg`, `bvadd`, `bvsub`), and signed/unsigned
  comparison operators, symbolic shifts, and constant rotates to AIG with
  evaluator-vs-AIG tests. Signed comparison lowering now avoids comparing the
  sign bit twice by using magnitude comparison under equal signs.
- The first SAT adapter path uses `rustsat-batsat` through RustSAT and only
  accepts `sat` after replay through CNF, AIG values, reconstructed symbol
  models, and the original evaluator
  ([ADR-0007](../09-decisions/adr-0007-first-pure-rust-sat-adapter.md)).
- CNF encoding now recognizes several private helper shapes created by the AIG
  lowering path: XOR, mux/not-ITE, private AND trees, and OR-of-private-AND
  parents. Positive root-only AND trees can also encode private XOR-backed
  parity/equality leaves directly, with a small parity-width cap to avoid
  exponential CNF growth. The encoder only emits the root-reachable AIG
  subgraph, normalizes generated clauses deterministically, and replays
  skipped/dead AIG nodes from children so model lifting still validates the
  full AIG. This keeps the AIG representation simple while borrowing a
  mature-solver pattern from Bitwuzla's AIG-to-CNF ITE recognition: encode the
  semantic gate directly rather than assigning every helper node a SAT variable.
- `SatBvBackend` now composes these layers behind the public
  `SolverBackend` trait for the supported subset. Unsupported operators still
  return structured unsupported errors instead of falling back to an oracle.

## Risks

- Naive encodings for multiplication/division can dominate clause counts.
- Bit-order bugs are easy and hard to diagnose without model-lifting tests.
- Arrays and memory need additional strategy beyond scalar BV bit-blasting.

## Open Questions

- [x] Should bit 0 be stored first in all wire vectors?
  - Answer: yes. Phase 4 uses LSB-first wire vectors; see
    [ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md).
- [ ] Which op subset is required by first external clients?
- [ ] Should symbolic shifts be mux trees, barrel shifters, or solver-delegated initially?
- [x] Which pure Rust SAT solver is the first adapter?
  - Answer: `rustsat-batsat` through RustSAT; see
    [ADR-0007](../09-decisions/adr-0007-first-pure-rust-sat-adapter.md).

## Source Pointers

- Boolector BV/array lineage: https://github.com/Boolector/boolector
- Bitwuzla: https://bitwuzla.github.io/docs/
- RustSAT: https://github.com/chrjabs/rustsat
- SAT Competition: https://satcompetition.github.io/
