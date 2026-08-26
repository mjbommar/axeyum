# ADR-0578: Conditional energetic explanations become checked prefix clauses

Status: accepted
Date: 2026-08-26
Index-summary: Replay conditional energetic overloads and translate their assumptions into exact CNF prefix clauses

## Context

ADR-0577 exhausted unconditional energetic reasoning on `abz7@655`: the strongest root
interval requires 533 units of processing in 538 available units. Scheduling-aware solvers
nevertheless establish the lower bound quickly by reasoning under narrowed start domains.
Axeyum lacked a trust-preserving bridge from such a conditional resource contradiction to its
exact time-indexed SAT formula. An unchecked cut would accelerate search by assuming the very
inference that a final certificate must justify.

## Decision

Add a portable conditional energetic-conflict schema whose assumptions are canonical inclusive
`start-at-least` or `start-at-most` bounds. Independent replay reconstructs either job-chain or
detectable-precedence-closure domains, requires every assumption to strictly narrow one operation
on the claimed machine, rejects contradictions and redundancy, rebuilds the cumulative task
windows, and recomputes the strict energetic overload and redundant totals.

Translate each accepted assumption's semantic negation through the exact operation prefix-OR
variables already retained by `JobShopEncoding`. Thus `start >= L` contributes the literal
`start <= L-1`, while `start <= U` contributes `start > U`. A bound impossible under a tighter
encoding makes the explanation tautological and adds no clause. Search is never allowed to name
raw variables or bypass semantic replay.

Add a deterministic bounded producer for one machine interval. It evaluates both extreme
one-sided tightenings for every flexible operation, chooses exact energy gains in stable order,
and stops at an explicit assumption ceiling. It then relaxes each chosen assumption toward its
base domain while preserving strict overload, yielding a stronger learned clause. Producer output
is admitted only after the independent checker replays it. Expose the route through a small CLI
that can retain JSON and emit the exact strengthened DIMACS formula.

## Evidence

A two-task control produces a two-literal explanation. Falsifying both learned literals in the
original formula is independently refuted and its generated DRAT proof passes Axeyum's backward
checker. Adding the clause preserves a satisfiable makespan-four boundary; its SAT model lifts and
replays. Mutated energy, noncanonical assumptions, and redundant bounds fail closed. Fourteen
focused job-shop tests and all-target/all-feature Clippy pass.

On the previously strongest `abz7@655` interval, machine 5 over `[0,538)`, the producer evaluates
40 one-sided candidates. The base energy is 533/538. Assuming job 2 operation 10 starts at or
before 532 raises the independently recomputed requirement to 539, so every feasible schedule at
this bound must start that operation after 532. The exact precedence-closure CNF has 175,170
variables and 1,690,226 clauses; the checked deduction adds one negative prefix unit. A matched
30-second CaDiCaL seed-401 diagnostic remained unknown on both formulas. The baseline reached
255,432 conflicts near 28.79 seconds; the strengthened run reached 231,121 near 28.23 seconds but
used more memory. This is a useful propagation signal, not a demonstrated speedup or lower-bound
certificate.

## Alternatives

- Trust a CP solver's learned explanation: rejected because no portable explanation object was
  exported by the measured proprietary run.
- Inject the semantic deduction as an unproved SAT unit: rejected because semantic truth alone is
  not a checked derivation at the formula boundary.
- Encode a new family of auxiliary variables: rejected because the exact prefix variables already
  represent both start-bound polarities.
- Credit a bounded solver improvement: rejected because both matched runs remained unknown and
  one seed is not a performance study.

## Consequences

Axeyum can now convert a checked cumulative-resource explanation into an exact reusable CNF lemma
without expanding the trusted base. The first real lemma substantially narrows one `abz7`
operation, but one unit does not certify infeasibility. The next layer is a bounded all-interval
unit scan and propagation fixpoint, followed by multi-assumption clauses or checked cube-cover
composition if units do not close the instance.

Energetic reasoning, explanation generation, lazy clause generation, and cumulative
decomposition are established prior art, including Vilim (CPAIOR 2005) and Schutt et al. (CP
2009). Searches through 2026-08-26 found no basis for a technique-novelty claim, and none is made.
