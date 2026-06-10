# Evidence And Checking

Status: draft
Last updated: 2026-06-10

## Purpose

Define how Axeyum should avoid over-trusting heuristic automation.

## Scope

In scope:

- Models, replay, proof checking, rewrite validation, and independent oracles.

Out of scope:

- Complete soundness proof for Axeyum.

## Core Claims

- Fast solving and trusted checking are separate concerns.
- A satisfying model can usually be checked cheaply by evaluating the original formula.
- Program-analysis witnesses should be replayed in the source semantics when possible.
- Unsat claims are harder and need proof artifacts or differential cross-checking
  before being treated as high assurance.

## Checking Levels

| Level | Evidence | Confidence |
|---|---|---|
| 0 | Backend result only. | Low to moderate. |
| 1 | Model evaluates against Axeyum term. | Higher for SAT. |
| 2 | Model replays in client semantics. | Higher for program witnesses. |
| 3 | Unsat proof checked. | High for UNSAT. |
| 4 | Rewrite/proof obligations checked. | Higher for optimizer trust. |

## Design Implications

- Implement formula evaluation for models early.
- Keep original and rewritten terms available for differential checks.
- Design proof logging as a future-compatible extension.
- Treat external SMT solvers as oracles, not trusted kernels.

## Risks

- Unsat proof checking for SMT is substantially harder than SAT proof checking.
- Replaying client semantics requires client cooperation and deterministic models.

## Open Questions

- [ ] Should Axeyum reject unchecked unsat in high-assurance mode?
- [ ] Should proof checking live in `axeyum-proof` or backend-specific crates?
- [ ] What is the minimum evidence artifact for the first release?

## Source Pointers

- Lean trusted kernel framing: https://lean-lang.org/
- CreuSAT verified SAT solver: https://github.com/sarsko/CreuSAT
- CBMC: https://www.cprover.org/cbmc/

