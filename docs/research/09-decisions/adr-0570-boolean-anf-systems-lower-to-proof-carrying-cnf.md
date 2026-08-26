# ADR-0570: Boolean ANF systems lower to proof-carrying CNF

Status: accepted
Date: 2026-08-26
Index-summary: Lower bounded Boolean ANF systems to deterministic liftable CNF for SAT and checked DRAT

## Context

ADR-0562 introduced canonical sparse Boolean-polynomial systems and used Bosphorus as an
external preprocessing experiment. That route could search, but it could not authorize an
UNSAT result: Axeyum had no checked equivalence bridge from its source equations to the
external CNF. This left the published PRIMATEs-inverse six-AND lower-bound control
unreproduced even though the source system was small.

ANF-to-CNF conversion is established prior art. Bosphorus and later XOR/OR/AND-normal-form
work both convert algebraic systems for SAT solving. The architectural contribution here is
not a new conversion algorithm; it is an in-tree, resource-bounded bridge whose source
projection, model lifting, and negative-certificate route are explicit.

## Decision

Add a deterministic definitional-extension encoding for a bounded
`BooleanAnfSystem`. Source variables retain their original one-based CNF indices. Nonlinear
monomials use a shared prefix-conjunction DAG, and parity equations use exact XOR chains.
Every introduced gate is constrained in both directions, so each source assignment has a
unique extension and projected CNF models are exactly the source-system models.

Admission separately bounds source degree, total variables, and total clauses. SAT results
must project to the source variables, satisfy the generated CNF, and replay every original
ANF equation. UNSAT results gain authority only when Axeyum's independent DRAT checker
accepts a proof against the exact generated formula. Source-unit helpers allow a known
multiplicative-circuit witness to traverse the same bridge and then replay against the
original truth table.

The portable full-operand-order equations use named prefix-equality variables rather than
expanding prefix products. This preserves the semantics of ADR-0569 while avoiding
exponential polynomial growth.

## Evidence

- Exhaustive source-assignment enumeration agrees with projected CNF models on a mixed ANF
  system; lifted SAT assignments satisfy both representations.
- A contradictory system emits a DRAT refutation accepted by the independent checker.
- Shared nonlinear prefixes are deterministic, and degree/variable/clause limits fail
  explicitly. Contradictory and out-of-range source units are rejected.
- The published PRIMATEs-inverse MC=8 witness traverses portable ANF, the generic CNF bridge,
  SAT projection, ANF replay, circuit lifting, and exhaustive truth-table replay. The bridge
  produces 24,096 variables and 81,688 clauses before 222 witness units.
- The retained partial-order MC=6 ANF is byte-identical at SHA-256
  `5fc1286e...b2b2`. Its generic CNF has 16,820 variables, 57,017 clauses, and SHA-256
  `191a8c7b...df61`.
- CaDiCaL 3.0.1 produced a 1,068,108,069-byte DRAT refutation in 228.81 seconds. Axeyum's
  file-backed backward checker accepted it in 1,377.68 seconds with 1,028,208 KiB peak RSS.
  A proof truncated to its first 100 lines returns `Ok(false)` and the driver exits nonzero.

## Consequences

The six-AND PRIMATEs-inverse instance is now independently reproduced as UNSAT. Together
with the replayed eight-AND circuit, this establishes the already published bracket
`[7,8]` inside Axeyum; it does not decide the open seven-AND question.

The certificate is intentionally retained despite its size because it is the evidence for
the lower endpoint. Current web, arXiv, and Google Scholar/SerpAPI searches found prior SAT
optimality claims and ANF/CNF conversion, but no retained DRAT artifact for this S-box
boundary. Because Scholar's eight-record forward-citation set remains unavailable, any
claim that this is the first such machine-checkable artifact remains provisional and is not
made as a publication claim.
