# ADR-0586: Multiplicative selector maps precede semantic covers

Status: accepted
Date: 2026-08-26

## Context

The first PRIMATEs-inverse MC=7 cube experiments split raw DIMACS variables. Although the
covering proofs were sound, opaque variables `2,3` did not state which circuit choices were
partitioned. That makes a performance result hard to interpret and risks coupling research
artifacts to private allocation order. A SAT model found by an external portfolio also lacked
a single command that traversed every trust boundary back to the S-box truth table.

## Decision

Every complete multiplicative-circuit encoding exposes the same typed selector map before a
semantic cube cover is constructed. Each record binds a zero-based source variable to its
owner (left/right AND operand or output coordinate) and basis term (constant, primary input,
or earlier AND result). The portable Boolean-ANF route preserves these source indices before
introducing private definitional variables.

The PRIMATEs driver may emit the stable map and may import a strict complete SAT Competition
model. Imported models must satisfy the exact queried CNF, project to and replay the source
ANF system, lift to the portable circuit artifact, and pass exhaustive truth-table replay
before a circuit is written. `--model` and `--circuit-out` are inseparable.

## Evidence

A cross-backend control proves that truth-row CNF, direct-ANF CNF, and portable Boolean ANF
publish byte-for-byte equal semantic selector records. It pins constant, input, and
earlier-AND identities and the complete variable order. Malformed external-model cases are
already covered by the shared strict importer.

For the exact MC=7 query, the emitted map contains 191 selectors. Regenerating the enhanced
20,585-variable / 69,809-clause CNF remains byte-identical at SHA-256
`176513848d1fa511bca2a7b5c50255f6dabe6ebff696eb9f62abcfad0f43ae76`.
DIMACS variables 2 through 6 are now explicitly the five primary-input coefficients in gate
zero's left affine operand. Their 32-way Boolean product has a checked 16-step covering DRAT.
A proof-free eight-worker portfolio searches these cells without a wall-clock cutoff; this is
operational search, not mathematical evidence.

The literature refresh through 2026-08-26 rechecked Stoffelen, Soeken, Zhang--Huang, and
Szeider's LRAT-Catcher. Operand/gate symmetry and checked cube composition are prior work. No
located current source closes PRIMATEs-inverse MC=7, but negative retrieval is not proof of
currency or novelty. No priority claim is made.

## Alternatives

Continuing raw-variable splits was rejected because they are sound but semantically opaque.
Writing DRAT for every exploratory cell was rejected because incomplete prefixes already grew
past 10 GB each and carry no credit. Trusting an external SAT assignment or writing it directly
as a circuit was rejected because it skips the source-ANF and exhaustive semantic replay
boundaries.

## Consequences

Circuit-search partitions are now reproducible in mathematical terms and external SAT models
have an end-to-end checked admission path. A completed SAT cell can improve the upper bound
only after replay; a completed UNSAT cell still needs a checked proof, and all 32 checked
leaves plus the covering proof are required for a lower bound. The interval remains `[7,8]`.
