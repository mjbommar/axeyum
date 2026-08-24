# 261 — Candidate capability demand projection

Date: 2026-08-24

## Result

The candidate-capability demand projection turns four proposed capabilities
into a deterministic investigation order based only on retained obstruction
families and episodes:

| Candidate | Obstruction families | Episodes |
|---|---:|---:|
| Checked declaration or inductive-package import | 3 | 11 |
| Bounded reproducible export environment | 3 | 7 |
| Checked declaration reuse | 2 | 2 |
| Typed transport and composition | 1 | 1 |

Package import and export reproducibility are the highest observed multipliers.
Typed transport is narrower but remains an explicit blocker, not a guessed
feature.

## Boundary

The order is not an implementation mandate. It does not measure expected proof
yield, cost, safety, downstream mathematical value, or suitability for the
98-fact producer-evaluation frontier. It never selects an operation or
authorizes a proof.

Every row must reproduce the candidate capability references, blocker
categories, family count, and episode count from the obstruction projection.
Its overlay status must remain `candidate`. The validator rejects invented
obstruction IDs, altered counts, and a claim that a candidate is active.

The next implementation decision can therefore choose one bounded candidate,
define independent checks, and measure a before/after funnel change against the
pre-registered producer frontier.
