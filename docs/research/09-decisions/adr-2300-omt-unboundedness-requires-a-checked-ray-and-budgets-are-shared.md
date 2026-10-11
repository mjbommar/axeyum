# ADR-2300: OMT unboundedness requires a checked ray; optimization budgets are shared

Status: proposed
Date: 2026-10-10
Index-summary: Replace integer search-ceiling unboundedness with affine recession witnesses; honor text/probe deadlines and stop lexicographic optimization after an unresolved objective.
Index-status: proposed

## Context

CON-5's audit found that the integer optimizer reported `Unbounded` when its
126-doubling or `i128` representation ceiling was exhausted. No theorem follows
from those limits. Both SMT-LIB optimizer entry points discarded `SolverConfig`,
and the lexicographic route optimized lower priorities without pinning an
unresolved higher priority. The user requested all identified OMT gaps repaired.

## Decision

1. A replayed feasible starting model plus an integer improving recession ray
   justifies `Unbounded` for admitted affine literal conjunctions. Homogenize
   each affine expression by dropping constants and retaining coefficients.
   Coefficients must be closed affine constant arithmetic. In particular,
   evaluating ground div/mod by zero under an empty model cannot establish a
   fixed coefficient: those values may depend on the feasible model.
   Require the objective slope to be at least one. For satisfied inequalities,
   require a slope with the preserving sign; strict comparisons use weak slope
   constraints. Equalities and disequalities require zero difference slope.
   Negated conjunctions or unsupported/nonlinear syntax decline this producer.
   Ray models are replayed against the rebuilt homogeneous query. Therefore
   base + n*direction remains feasible and the objective tends to infinity for
   natural n. The existing `OptOutcome` API remains unchanged; portable ray
   serialization and independent optimality evidence remain CON-5 O2 work.
2. Search and arithmetic ceilings without a witness produce resource-limited
   `Unknown`, never `Unbounded`. Negation outside the result range likewise
   cannot prove unboundedness. Binary bracket distance uses overflow-safe
   arithmetic. Every SAT feasibility probe is replayed before use.
3. Integer feasibility probes receive only the remaining optimization deadline;
   text objectives receive only the remainder of one text-call budget, including
   elapsed parsing time. Preemptible parsing and equivalent budget propagation
   across every BV/multiobjective internal probe remain follow-up obligations.
4. Generic satisfiability, model/value and session routes reject objective-bearing
   scripts with `Unsupported`, naming the explicit optimizer APIs. They must not
   return an arbitrary feasible value in response to an optimization request.
   Parsing/inspection still records objectives. A Python optimizer is subsequent
   CON-5 work; rejection is the immediate correctness repair, not completion of
   the requested product surface.
5. Lexicographic lower-priority objectives remain unknown after any higher
   objective has no optimum. Box objectives remain independent.

## Validation and trust boundary

Regression cases distinguish a genuine affine ray, a bounded wide objective,
a nonlinear bounded domain, strict/negated relations, coupled equalities,
zero-budget text optimization and an unresolved lexicographic prefix. Paired
SAT/infeasible cases and altered coefficient/constraint controls exercise the
ray transformation. The source-to-homogeneous transformation is part of this
small checking boundary; claiming unboundedness from a raw search limit remains
forbidden even when the ray producer declines.

Required gates are the focused optimizer and SMT-LIB tests, workspace library
suite, full-feature solver library suite, front-door regression suites and the
five linear-arithmetic z3 differential fuzzes. This ADR remains proposed until
the implemented increment is validated; it does not declare CON-5 complete.
