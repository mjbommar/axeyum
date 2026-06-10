# ADR-0002: Ground-Up Identity, Oracle As Bootstrap Scaffolding

Status: accepted
Date: 2026-06-10

## Context

The project owner's intent is to implement most of the reasoning stack from
the ground up — own IR, rewriter, bit-blaster, circuits/CNF, and CDCL SAT
core. That raised the question of whether the Z3 backend in ADR-0001's M0
contradicts the intent. After discussion, the resolution: the oracle is
needed to bootstrap safely. Our own layers cannot validate themselves —
`unsat` answers are uncheckable without a proof pipeline, and the proof
pipeline itself needs something trusted to be tested against. This ADR
records that resolution so it is not relitigated.

## Decision

Two commitments, held together:

1. **Ground-up implementation is the project identity.** The pure Rust
   stack — IR, evaluator, rewriter, bit-blaster, AIG/CNF, and a custom CDCL
   SAT core with proof logging — is the product, not an eventual aspiration.
   In particular, the custom SAT core (roadmap Phase 6) is a *when*, not a
   *whether*: the benchmark gate decides its priority relative to encoding
   work, not its existence. Adapting an existing Rust SAT solver in Phase 5
   is a validation step on the way, not the destination.

2. **The linked oracle is bootstrap scaffolding with a planned demotion
   path.** Z3 (feature-gated, leaf crate, default build stays free of
   C/C++) serves successively as: M0 backend that exercises the real API
   shapes → differential oracle validating the rewriter and bit-blaster
   (Phases 3–5) → CI cross-check once the own stack carries the load and
   unsat answers ship DRAT/LRAT proofs checked independently. Each demotion
   happens when the evidence pipeline replaces the trust the oracle was
   providing.

## Evidence

- The unsat asymmetry: a model is checkable by evaluating the original
  formula, but an unsat claim from our own bit-blaster + SAT path is
  uncheckable until proof logging and checking exist. Until then, an
  independent mature solver is the only referee for the worst class of bug
  (satisfiable formulas reported unsat).
- Differential testing against independent solvers is standard practice in
  the field; Bitwuzla, STP, and SAT competition entrants validate this way.
- The z3 crate (0.20+) no longer leaks context lifetimes, so the binding
  cost that previously argued against it is gone.

## Alternatives

- No linked oracle; subprocess-only cross-checks with bottom-up build order
  (SAT core first): workable and was drafted, but it delays the first
  end-to-end result, stacks unvalidated layers during the most error-prone
  construction phase, and weakens M0 as an API-shaping exercise.
- Oracle as permanent co-equal backend: rejected as identity creep; the
  demotion path above is part of this decision.

## Consequences

- Easier: every Axeyum layer is built against a referee from day one; M0
  stays small; the evidence pipeline has a trusted target to graduate away
  from.
- Harder: discipline is required to keep the oracle in its lane — any new
  reliance on a linked solver beyond backend/oracle/cross-check roles needs
  an ADR.
- Roadmap Phase 6's gate is reinterpreted (priority, not existence) — noted
  in the roadmap and benchmarking methodology.
