# ADR-0558: Portable Boolean circuits bind complete truth tables

Status: accepted
Date: 2026-08-26
Index-summary: Check named-wire Boolean circuit witnesses exhaustively under explicit bit ordering, gate semantics, and resource admission

## Context

The S-box lane needs to replay published positive circuits without trusting the SAT encoder
or its evaluator. SIMD and finite synthesis lanes also need a small semantic circuit format.
Axeyum has Boolean expressions, AIG lowering, and SAT evidence, but none is a portable
named-wire witness that binds a complete finite function and reports metric-relevant gate
counts. A producer-specific straight-line program can easily hide reversed bit numbering,
forward references, overwritten wires, or a truth table checked only on selected rows.

## Decision

Add `axeyum_cas::boolean_circuit` with schema `axeyum.boolean-circuit.v1`. An artifact binds:

- input and output wire order, both most-significant bit first;
- a topologically ordered sequence of uniquely named `and`, `or`, `xor`, `not`, `nand`,
  `nor`, or `xnor` gates; and
- the output integer for every input integer in ascending order.

The checker rejects schema drift, duplicate/empty definitions, forward or missing references,
wrong arity, output values outside the declared width, incomplete truth tables, and explicit
input/output/gate/wire-reference limit violations. It evaluates every one of the `2^n` rows
and returns either the first mismatching input or a verified row count plus stable per-operation
gate counts. The CLI exits zero, one, or two for verified, semantic mismatch, or
malformed/resource-declined input respectively.

Gate counts are observations, not an optimality claim. An UNSAT certificate bound to a
separate synthesis encoding is still required to prove that no smaller circuit exists.

## Evidence

- A two-input XOR matches all four rows; a truth-table mutation identifies row 2.
- A forward wire reference is rejected before evaluation.
- Zhang--Huang's 45-operation `PRIMATEs^-1` circuit from Appendix C.1 matches all 32 rows
  of the independently inverted original PRIMATEs specification table, with exactly 8 AND,
  35 XOR, and 2 NOT gates.
- Changing its first XOR to XNOR exits one on row 0 (`expected=1`, `observed=23`).

## Alternatives

### Reuse `BoolExpr`

Rejected as the artifact contract. Expression trees do not preserve named straight-line
sharing, so reported circuit metrics would be ambiguous.

### Store only the circuit and name an external S-box

Rejected. The function bytes and bit order are load-bearing evidence identity and must be
inside the checked object (or hash-bound by a later envelope), not recovered from a label.

### Accept one producer-supplied test script

Rejected. It would share parsing and convention assumptions with the witness producer and
would not create a reusable Axeyum semantic boundary.

## Consequences

- Published S-box SAT witnesses now have an Axeyum-native positive-certificate route.
- The same artifact can carry constructed synthesis controls, while domain-specific SIMD
  instructions still require a separate semantics layer.
- The next S-box capability is a deterministic synthesis CNF whose SAT models lift into this
  artifact and whose UNSAT results carry checked DRAT.
