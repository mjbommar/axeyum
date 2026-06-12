# Circuits And CNF

Status: draft
Last updated: 2026-06-11

## Purpose

Define the intermediate layers between bit-vector terms and SAT.

## Scope

In scope:

- Boolean wires, AIGs, CNF, Tseitin encoding, and mapping between layers.

Out of scope:

- Final gate optimization strategy.

## Core Claims

- A circuit layer is worth owning before CNF because it enables structural hashing,
  local simplification, and multiple SAT encodings.
- AIG is a strong first representation: simple, compact, and optimization-friendly.
- CNF should preserve a map back to wires and terms for model lifting and proof checking.
- Phase 4 starts with AIG before direct CNF, and uses LSB-first BV wire vectors;
  see
  [ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md).

## Candidate Types

```text
WireId(u32)
Lit(u32)        // variable plus polarity, SAT-level
AigLit(u32)     // AIG node plus polarity
CnfVar(u32)
ClauseId(u32)

AigNode =
  ConstFalse
  Input(SymbolBit)
  And(AigLit, AigLit)
```

## Encoding Flow

```text
TermId
  -> BV wires
  -> AIG nodes
  -> CNF vars and clauses
  -> SAT result
  -> wire values
  -> term/model values
```

## Tseitin Example

For `z = a and b`:

```text
(!z or a)
(!z or b)
(z or !a or !b)
```

## Design Implications

- Keep circuit IDs separate from SAT literals.
- Keep a reversible mapping for model lifting.
- Use structural hashing for AIG AND nodes.
- Use polarity bits instead of explicit NOT nodes.
- `axeyum-aig` now emits deterministic ASCII AIGER (`aag`) debug dumps for
  explicit output literals; binary AIGER is deferred until external tooling
  requires it.
- The current `axeyum-cnf` slice implements Tseitin-style encoding from AIG,
  DIMACS parse/write, CNF evaluation, a `rustsat-batsat` adapter, and replay
  from SAT assignments through CNF variables and AIG node values. Its first
  sparse encoding optimization recognizes private XOR and mux helper shapes
  before CNF, omits helper variables/clauses, and reconstructs skipped helper
  nodes from their children during AIG replay. `axeyum-bv` reconstructs Axeyum
  symbol models from those AIG values for original-term evaluator replay.

## Risks

- Direct CNF lowering may look simpler but loses useful optimization hooks.
- AIG may not be ideal for every encoding, especially cardinality or pseudo-Boolean constraints.

## Open Questions

- [x] Should the first bit-blaster produce AIG or CNF directly?
  - Answer: produce AIG first, then simple Tseitin CNF; see
    [ADR-0006](../09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md).
- [x] Should AIGER import/export be supported early?
  - Answer: support ASCII AIGER export for deterministic debug dumps now; defer
    binary import/export until a concrete external-tooling need appears. See
    [phase4-exit-audit](../08-planning/phase4-exit-audit.md).
- [x] Which pure Rust SAT solver is the first adapter?
  - Answer: `rustsat-batsat` through RustSAT; see
    [ADR-0007](../09-decisions/adr-0007-first-pure-rust-sat-adapter.md).
- [ ] How much circuit rewriting is needed before first benchmarks?

## Source Pointers

- AIGER format: https://fmv.jku.at/aiger/
- SAT Competition: https://satcompetition.github.io/
