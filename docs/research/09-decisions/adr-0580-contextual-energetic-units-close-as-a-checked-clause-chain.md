# ADR-0580: Contextual energetic units close as a checked clause chain

Status: accepted
Date: 2026-08-26
Index-summary: Iterate replayed scheduling bounds through precedence closure and energetic unit explanations

## Context

ADR-0579 exhausts energetic deductions made from one assumption over the root
precedence-closure domains. It deliberately does not use its own conclusions. That leaves a
generic propagation gap: an established start bound can tighten job-chain windows, force more
machine orders, and make a new energetic explanation possible. Hand-carrying those bounds between
scans is neither reproducible nor an adequate certificate contract.

The relevant scheduling algorithms are prior art. Detectable precedence, edge finding, energetic
reasoning, and explanations for unary resources all predate this work; recent constraint-programming
systems combine them routinely. The decision is about Axeyum's replay boundary and exhaustive
measurement, not a new propagation algorithm.

## Decision

Add propagation from canonical semantic start bounds. Reconstruct exact job-chain windows, narrow
them with assumptions on any machine, and rerun deterministic detectable-precedence closure. A
conditional energetic certificate using the new `assumption-closure` domain must contain the full
canonical assumption conjunction; its checker reconstructs the same propagation and recomputes the
claimed overload exactly.

Add a bounded contextual unit scan and fixpoint driver. The driver accepts only independently
replayed one-assumption premise conflicts. It negates those conflicts into entailed units, scans all
machine intervals and both polarities under the current context, and requires every returned
explanation to contain that complete context plus exactly one new conflicting bound. Negating the
new bound yields the next unit. Iteration stops only on a no-change round or an explicit round,
conflict, horizon, interval, or task-check limit.

Expose the complete ordered derivation as JSON and insert every premise and contextual conflict
into the exact precedence-closure CNF. Each clause is independently replayed before insertion; the
fixpoint is therefore a chain of checked implications rather than trusted mutation of solver state.

## Evidence

The `ft06 = 55` control starts from ADR-0579's two independently replayed premise conflicts, closes
to a stable context, replays every contextual certificate, inserts the complete clause chain, solves
the strengthened formula, lifts the model, and independently checks makespan 55. A non-unit premise
fails closed. Sixteen focused job-shop tests and all-feature Clippy pass.

For `abz7@655`, one release command independently replays both premise conflicts and reproduces four
contextual rounds with conflict counts 2, 2, 1, and 0. The stable context contains six conclusions:

- `start(0,9) >= 502`;
- `start(1,8) >= 476`;
- `start(2,10) >= 533`;
- `start(3,7) >= 405`;
- `start(6,9) >= 419`;
- `start(7,0) <= 22`.

Propagation now forces 861 of 2,850 machine-order directions, versus 256 at the root. The four
exhaustive rounds each inspect 128,904,000 candidate bounds and together perform 1,289,053,403 exact
task-energy checks. The run takes 10.43 seconds and 405,428 KiB peak RSS. Seven replayed conflicts
add exactly seven clauses to the 175,170-variable formula, from 1,690,226 to 1,690,233 clauses.

A matched seed-503 30-second CaDiCaL diagnostic remains unknown on both the prior and strengthened
formula. The strengthened run eliminates more variables during preprocessing, but a cutoff trace is
not proof and does not establish a speedup. The stable context has neither a precedence contradiction
nor a root energetic overload, so `abz7 >= 656` remains unproved.

## Alternatives

- Trust a list of manually derived start bounds: rejected because it severs the implication chain
  from replayed conflicts.
- Add derived units directly without retaining contextual explanations: rejected because a solver
  result would then depend on uncheckable propagation state.
- Treat contextual precedence infeasibility as a certificate: deferred until Axeyum has a portable
  precedence-cycle or bound-conflict artifact; the current target does not reach that case.
- Claim novelty for the propagation method: rejected because energetic fixpoints and resource
  explanations are established scheduling literature.

## Consequences

Axeyum can now turn replayed scheduling conflicts into a deterministic, bounded, portable clause
chain and exhaust that layer to a fixpoint. On `abz7@655`, this substantially strengthens domains but
does not solve the lower bound. The next proof increment must add a different complete inference
family—such as certified edge-finding/not-first/not-last explanations—or compose checked branch
leaves; repeating this energetic-unit closure cannot produce another deduction from the stable
context.
