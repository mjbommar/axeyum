# ADR-0561: Multiplicative circuit synthesis is proof-carrying and model-lifted

Status: accepted
Date: 2026-08-26
Index-summary: Encode complete affine-between-AND circuit synthesis with replayed SAT models and independently checked DRAT refutations

## Context

ADR-0558 checks a supplied Boolean circuit but does not search for one or prove that a gate
budget is impossible. S-box target 3 includes the multiplicative-complexity interval
`MC(PRIMATEs^-1) in [7,8]`. In this metric XOR, NOT, constants, and fanout are free. Every
circuit with at most `k` AND gates has a complete normal form: AND gate `g` consumes two
affine functions of the inputs and earlier AND outputs, and each output is another affine
function. This gives a finite SAT encoding without restricting valid witnesses.

## Decision

Add `axeyum-search::multiplicative_circuit` and let this high-level search crate depend on
both `axeyum-cnf` and `axeyum-cas`. The encoder allocates selector coefficients once, expands
their semantics on every truth-table row, Tseitin-encodes conjunction and parity, and pins
every output bit. Variable and clause order are deterministic.

A SAT result is not returned directly. Its model must satisfy the CNF, is lifted into
ADR-0558's portable named-wire circuit, and must pass exhaustive truth-table replay. An UNSAT
result is returned only with the exact formula and a DRAT proof accepted by the independent
backward checker. Conflict exhaustion and deadline expiry remain distinct undecided results.

The module also normalizes replayed XOR/XNOR/NOT/AND artifacts back into affine-between-AND
witnesses and can pin every selector in the synthesis formula. This proves that a published
witness inhabits the exact formula used for a lower-bound search, rather than merely computing
the same truth table in an unrelated representation.

## Evidence

- All sixteen two-input Boolean functions agree with their algebraic-normal-form boundary:
  exactly the eight affine functions synthesize with zero ANDs, and all sixteen synthesize
  with one.
- `AND_2` at budget zero emits a DRAT proof accepted by both backward and reference checkers;
  at budget one its model lifts and replays.
- Malformed truth tables and variable ceilings fail before search.
- The published PRIMATEs-inverse MC=8 artifact normalizes, pins all 222 selector coefficients
  in the 9,326-variable / 31,712-clause base formula, solves, lifts, and replays all 32 rows.
- Unpinned proof-producing searches at budget 8 for 30 seconds and budget 6 for 120 seconds
  both returned `Interrupted`, not a verdict. This is a performance calibration, not evidence
  for either boundary.

## Consequences

- Axeyum now has the complete proof-carrying substrate for the PRIMATEs multiplicative-
  complexity question and reusable vector Boolean functions.
- This does not yet cover bit-gate complexity, where AND/OR/XOR/NOT all carry costs and a
  different complete gate-choice encoding is required.
- The naive complete encoding has no symmetry breaking. Published-control reproduction is
  not yet fast enough: the known six-AND lower-bound run did not finish in 120 seconds.
  Performance and symmetry work must precede any credible seven-AND frontier run.
