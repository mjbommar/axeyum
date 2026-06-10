# Beyond Bit-Blasting

Status: draft
Last updated: 2026-06-10

## Purpose

Record the word-level and non-CDCL techniques that mature BV solvers layer on
top of eager bit-blasting, so the architecture does not hard-code "bit-blast
everything eagerly" as the only pure Rust strategy.

## Scope

In scope:

- Lazy/abstraction-refinement approaches, local search, int-blasting,
  parallel and portfolio solving.

Out of scope:

- Implementation plans; everything here is post-Phase-5 research.

## Core Claims

- Eager bit-blasting is the correct first backend, but the gap between a naive
  bit-blaster and Bitwuzla is mostly word-level preprocessing and lazy
  techniques, not SAT-core speed.
- Expensive operators (multiplication, division) are the natural targets for
  abstraction-refinement: replace with uninterpreted functions plus cheap
  axioms, solve, and refine with exact lowering only on spurious models
  (Boolector-lineage "lemmas on demand").
- Propagation-based local search (Bitwuzla's prop engine) is a complete-for-sat
  complement to CDCL: excellent on satisfiable instances, useless for unsat.
  It fits the backend model only if capabilities distinguish model-finding
  engines from refutation-complete engines.
- Int-blasting (translating BV to nonlinear integer arithmetic, as in cvc5) is
  a real alternative for wide arithmetic-heavy formulas; out of scope until an
  integer theory exists.
- Portfolio parallelism (run multiple engines/configs, first answer wins) is
  the cheapest parallel speedup and is almost free given the backend trait;
  cube-and-conquer is the heavyweight option for hard instances.

## Technique Inventory

| Technique | Where it lives in the stack | Prerequisite |
|---|---|---|
| Word-level rewriting/normalization | `axeyum-rewrite` | Phase 3 |
| Lemmas on demand for arrays | BV backend above SAT | Arrays in IR |
| UF abstraction + refinement for mul/div | BV backend loop | Phase 5 backend |
| Propagation-based local search | New engine behind solver trait | Capability split sat-only vs complete |
| Under/over-approximation of widths | BV backend loop | Phase 5 backend |
| Portfolio parallelism | Query planner | Send-able queries (see API note) |
| Cube-and-conquer | SAT layer | Custom or cooperative SAT core |

## Design Implications

- The abstraction-refinement loop is an argument for owning the layer between
  term IR and SAT: it needs to re-enter lowering with refinement lemmas, which
  is awkward over a foreign solver API.
- Backend capabilities must distinguish "complete" from "model-finding only"
  so a local-search engine can return `Unknown` instead of looping on unsat.
- Keep per-operator lowering pluggable so mul/div can switch between exact
  circuits and UF abstraction per query.
- The query planner is the natural home for portfolio dispatch; design its
  API so a query can be handed to several backends concurrently.

## Risks

- Refinement loops can diverge on adversarial instances without lemma
  generalization; budgets and fallback-to-eager must be designed in.
- Local search engines have very different tuning surfaces from CDCL; sharing
  a config vocabulary too early may force a lowest common denominator.

## Open Questions

- [ ] Which comes first after the eager path works: array lemmas on demand, or
      UF abstraction for multiplication?
- [ ] Is a propagation-based local search engine a good first "second engine"
      to validate the capability model?
- [ ] Should portfolio dispatch be in scope for the first public release?

## Source Pointers

- Bitwuzla (prop engine, preprocessing): https://bitwuzla.github.io/docs/
- Boolector lemmas on demand lineage: https://github.com/Boolector/boolector
- cvc5 (int-blasting): https://cvc5.github.io/
- Cube-and-conquer background: https://www.cs.utexas.edu/~marijn/publications/cube.pdf
- Mallob parallel SAT: https://github.com/domschrei/mallob
