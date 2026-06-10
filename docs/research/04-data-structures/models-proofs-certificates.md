# Models, Proofs, And Certificates

Status: draft
Last updated: 2026-06-10

## Purpose

Define evidence artifacts as first-class outputs, not solver afterthoughts.

## Scope

In scope:

- Models, model lifting, unsat proofs, rewrite certificates, and replay artifacts.

Out of scope:

- Final proof format selection.

## Core Claims

- `sat` results should carry models mapped to user symbols.
- `unsat` results should eventually carry a checkable explanation.
- Rewrites should be testable and ideally certifiable.
- Evidence should survive backend choice.

## Evidence Types

| Artifact | Meaning | Checker |
|---|---|---|
| Model | Satisfying assignment for symbols. | Evaluate formula or replay client semantics. |
| CNF assignment | SAT-level assignment. | Evaluate clauses. |
| Model lift map | Mapping from SAT vars to wires/terms. | Recompute bit values. |
| Unsat proof | Proof that clauses are unsatisfiable. | DRAT/LRAT/etc. checker. |
| Rewrite certificate | Justification for term transformation. | Local proof, solver check, or trusted rewrite ID. |
| Replay witness | Concrete input plus environment. | Client-specific deterministic replay. |

## Design Implications

- Do not discard lowering maps after solving.
- Store symbol names and widths in model artifacts.
- Keep proof/certificate APIs optional so early users are not forced into heavy artifacts.
- Make evidence serializable.

## Risks

- Proof traces can be huge.
- Model completion semantics differ across SMT solvers.
- Client replay may fail if frontend semantics are underspecified.

## Open Questions

- [ ] Should the first proof target be DRAT, LRAT, or only clause/model checking?
- [ ] Should rewrite rules have unique stable IDs?
- [ ] Should evidence artifacts be versioned independently from crate APIs?

## Source Pointers

- CreuSAT: https://github.com/sarsko/CreuSAT
- SAT Competition proof checking context: https://satcompetition.github.io/
- Lean trusted-kernel model: https://lean-lang.org/

