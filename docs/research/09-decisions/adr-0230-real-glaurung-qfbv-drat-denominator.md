# ADR-0230: Real Glaurung QF_BV DRAT denominator

Status: accepted
Date: 2026-07-17

## Context

The publication review asks for a concrete proof-producing use case and a
coverage denominator, not merely a capability test. ADR-0226 measures the
stronger faithfulness-plus-DRAT route over a declared generated subset, but it
does not show how often real Glaurung UNSAT queries receive a rechecked proof.

The existing benchmark harness already has a high-assurance real-corpus mode:
it selects the proof-producing native core, independently rechecks inline DRAT,
compares every result with Z3 and a content-hashed manifest, replays SAT models,
requires deterministic resource limits, and fails below 100% decided. Reusing
this route preserves the distinction between proof deployment and performance.

## Decision

Run the raw, no-rewrite proof recipe over every member of the 128-query
representative Glaurung QF_BV manifest from a clean source worktree. Count SAT,
UNSAT, proof-checked, proof-missing, model-replay, oracle, and manifest outcomes
over the predeclared complete population.

Accept CNF DRAT coverage only when every observed UNSAT has
`unsat_proof_replay=checked`, no proof is missing, all SAT models replay against
the original query, Axeyum and Z3 agree, and no row is Unknown, unsupported, or
an error. Keep this denominator separate from ADR-0226's term-to-CNF
faithfulness certification.

## Evidence

At clean Axeyum `0e628764`, all 128 manifest rows decide and agree:

- 64 SAT, all 64 original-query models replay, zero replay failures;
- 64 UNSAT, all 64 inline DRAT proofs independently recheck, zero missing;
- 128/128 Z3 agreements with zero skip or disagreement;
- 128/128 manifest agreements with zero mismatch;
- zero Unknown, unsupported, error, or resource-bound outcome.

The 64 proved UNSAT rows cover 24 `register-slice`, 24 `slice-partial`, 11
`arithmetic`, and 5 `comparison` queries. Exact per-row content identities,
proof states/times, CNF sizes, configurations, and environment/source hashes
are committed under
[`bench-results/glaurung-real-query-proof-20260717/`](../../../bench-results/glaurung-real-query-proof-20260717/README.md).

## Consequences

The publication may report 100% rechecked CNF DRAT coverage over the declared
64-row real Glaurung UNSAT denominator and cite it as a concrete proof-producing
client use case. It must report the denominator and the encompassing 128-query
population.

This does not close the bit-blast faithfulness gap. ADR-0226 remains the only
current denominator for the stronger end-to-end certificate, and its generated
169-row result cannot be merged arithmetically with these 64 real rows. The
proof-run timers are also not comparable to the fair four-cell performance
map; the proof-producing core is deliberately a different assurance policy.

The content-hashed representative manifest derives from three Glaurung
drivers, not every current live trace or the complete 9,526-check corpus.
Widening real-query proof coverage and adding deadline-aware end-to-end
certification remain distinct follow-ups.

## Alternatives

- Cite the two-query micro proof smoke: rejected because it is not a real
  client-derived denominator.
- Count only proofs that happened to finish: rejected because the complete
  representative population must be selected before execution.
- Call CNF DRAT an end-to-end source proof: rejected because it does not certify
  term-to-bitblast faithfulness.
- Use proof timings as the solver headline: rejected because the assurance core
  and execution topology differ from the fair performance cells.
