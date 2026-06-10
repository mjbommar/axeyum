# CDCL SAT

Status: draft
Last updated: 2026-06-10

## Purpose

Summarize the algorithmic core of a future pure Rust SAT backend.

## Scope

In scope:

- CDCL mechanics and heuristics.

Out of scope:

- Full implementation plan for a competitive SAT solver.

## Core Claims

- CDCL is the right baseline architecture for a practical SAT backend.
- Boolean constraint propagation is the central hot path.
- Conflict analysis and learned clauses explain the performance difference from
  naive DPLL.
- It is pragmatic to start with existing Rust SAT solvers before implementing a custom core.

## Core Loop

```text
propagate()
if conflict:
  analyze conflict
  learn clause
  backjump
  enqueue asserting literal
else if all assigned:
  sat
else:
  choose decision literal
  enqueue decision
```

## Key Techniques

- Two-watched-literal propagation.
- First-UIP conflict analysis.
- Non-chronological backjumping.
- Clause learning.
- EVSIDS/LRB-style variable activity.
- Phase saving.
- Restarts.
- LBD/glue scoring.
- Clause database reduction.
- Inprocessing: subsumption, blocked clause elimination, vivification.

## Design Implications

- The SAT trait should allow assumptions.
- Clause addition should support incremental encodings.
- Statistics and traces are required for research.
- Proof logging should not be impossible to add later.

## Risks

- A correct CDCL solver is easy to write slowly and hard to make competitive.
- Inprocessing can complicate proof logging and model maps.

## Open Questions

- [ ] Which Rust SAT solver should be the first adapter?
- [ ] What benchmark suite is needed before writing a custom CDCL core?
- [ ] Should proof logging be enabled before inprocessing?

## Source Pointers

- CaDiCaL: https://github.com/arminbiere/cadical
- Kissat: https://github.com/arminbiere/kissat
- splr: https://github.com/shnarazk/splr
- varisat: https://github.com/jix/varisat
- RustSAT: https://github.com/chrjabs/rustsat

