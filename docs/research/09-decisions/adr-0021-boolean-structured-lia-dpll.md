# ADR-0021: Boolean-Structured QF_LIA via Lazy-SMT over the Integer Simplex

Status: accepted
Date: 2026-06-13

## Context

ADR-0020 added `check_with_lia_simplex`, which decides a **conjunction** of
linear integer constraints (sound for sat and unsat). Real `QF_LIA` queries are
rarely pure conjunctions — disjunctions and implications of integer atoms
(`x ≤ 0 ∨ x ≥ 10`, `x > 5 ⇒ y > 10`) are ubiquitous in program verification.
The conjunctive path declines those (`Unsupported`), so they fell back to bounded
bit-blasting — sat-only and width-bounded. Closing this is a coverage step toward
Z3/cvc5 parity ([solving-strategies note](../03-architecture/solving-strategies-and-memory-model.md),
gap 1).

The codebase already has the pattern: `check_with_lra_dpll` is a real lazy-SMT /
DPLL(T) loop for Boolean-structured `QF_LRA`. The same loop, with the integer
simplex as the theory oracle, decides Boolean-structured `QF_LIA`.

## Decision

**Add `check_with_lia_dpll`: decide Boolean-structured `QF_LIA` by the standard
lazy-SMT loop over `check_with_lia_simplex`, and route the integer dispatcher
through it.**

- Abstract each integer order atom to a fresh Boolean proposition and each
  integer equality `a = b` to `(a ≤ b) ∧ (a ≥ b)` (so the theory solver never
  sees a disequality), leaving Boolean structure and original Boolean variables
  intact — a propositional skeleton.
- Decide the skeleton; map the atom truth assignment to a conjunction of integer
  order literals; theory-check it with the simplex branch-and-bound. `sat` ⇒
  build a model (integer values from the theory model, Boolean values from the
  skeleton) and **replay** the original assertions; `unsat` ⇒ add a blocking
  clause and retry. A round budget bounds the search (`unknown`, never wrong).
- `check_auto` now tries, for integer queries: conjunctive simplex
  (ADR-0020) → this lazy loop → bounded bit-blasting, in that order.
- Implemented self-contained (`dpll_lia.rs`), reusing the conjunctive simplex
  as the oracle; the real `dpll_t.rs` path is untouched.

## Evidence

- Mirrors the accepted, tested `check_with_lra_dpll` structure (same abstraction
  with equality-splitting; same conflict-block loop).
- Tests (oracle-free): `(x<0 ∨ x>10) ∧ x==15` is sat (replayed); `(x<0 ∨ x>10) ∧
  x==5` and `(x==2 ∨ x==4) ∧ x==3` are **unsat** (needs refuting every disjunct
  branch); an implication chain is sat. Full pure-Rust suite green.
- Soundness: `sat` replayed through the evaluator; `unsat` holds because the
  skeleton-plus-learned-clauses is propositionally unsatisfiable, so no truth
  assignment is theory-consistent, and the abstraction faithfully represents the
  originals over the atoms.

## Alternatives

- **Stay conjunctive-only.** Rejected: misses the common disjunctive integer
  queries; bounded bit-blasting can only return `unknown` for their `unsat`.
- **Generalize the existing `dpll_t.rs` to integers in place.** Deferred: it
  carries the delicate real Farkas-certified refutation export; a separate loop
  isolates risk now. Unifying the two theory loops (real + int, true combined
  `QF_LIRA`) is a clean follow-up.
- **Block only the conflict core (Farkas-minimized) instead of the whole
  assignment.** Deferred: whole-assignment blocking is sound and simple; core
  minimization (fewer rounds) needs an integer-infeasibility core extractor.

## Consequences

- **Easier:** Boolean-structured `QF_LIA` is now decided soundly (both verdicts);
  a base for combined `QF_LIRA` (run the real and integer loops together — they
  share no sort, so propositional coupling suffices) and for a checkable LIA
  `unsat` certificate.
- **Harder / to watch:** whole-assignment blocking can take many rounds on
  disjunction-heavy queries; the round budget makes that `unknown` (sound) until
  core minimization lands. No checkable `unsat` certificate yet (unlike the real
  Farkas/DRAT routes).
- **Revisited when:** the real and integer DPLL(T) loops are unified into one
  theory-parametric combination engine, and when conflict-core minimization and
  an LIA `unsat` certificate are added.
