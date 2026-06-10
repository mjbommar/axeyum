# Bit-Blasting

Status: draft
Last updated: 2026-06-10

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

## Risks

- Naive encodings for multiplication/division can dominate clause counts.
- Bit-order bugs are easy and hard to diagnose without model-lifting tests.
- Arrays and memory need additional strategy beyond scalar BV bit-blasting.

## Open Questions

- [ ] Should bit 0 be stored first in all wire vectors?
- [ ] Which op subset is required by first external clients?
- [ ] Should symbolic shifts be mux trees, barrel shifters, or solver-delegated initially?

## Source Pointers

- Boolector BV/array lineage: https://github.com/Boolector/boolector
- Bitwuzla: https://bitwuzla.github.io/docs/
- SAT Competition: https://satcompetition.github.io/

