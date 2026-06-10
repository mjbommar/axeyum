# Circuits And CNF

Status: draft
Last updated: 2026-06-10

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

## Risks

- Direct CNF lowering may look simpler but loses useful optimization hooks.
- AIG may not be ideal for every encoding, especially cardinality or pseudo-Boolean constraints.

## Open Questions

- [ ] Should the first bit-blaster produce AIG or CNF directly?
- [ ] Should AIGER import/export be supported early?
- [ ] How much circuit rewriting is needed before first benchmarks?

## Source Pointers

- AIGER format: https://fmv.jku.at/aiger/
- SAT Competition: https://satcompetition.github.io/

