# ADR-0149: Bounded CNF formula-header capacity

Status: proposed
Date: 2026-07-14

## Context

ADR-0148 pre-sized both the outer `Vec<CnfClause>` and the collision-safe
fingerprint index. It preserved content but regressed representative CNF 10.0%
because gate lookup rose 23.5%; a sparse eagerly sized hash table overwhelmed
any avoided growth. That result does not identify the contiguous formula-header
vector as harmful: it moves every already-emitted 24-byte `CnfClause` header as
it grows, while each clause's literal allocation stays separately owned.

The same artifact-v27 estimate remains bounded and no-pass:
`min(5 * cnf_variables + min(roots, 1_024), 65_536)`. It covers all 13,462
full-tier formulas, reserves 69,225,859 aggregate header slots for 49,199,541
emitted clauses, and is below the approximately 71,566,146 final slots implied
by ordinary power-of-two vector growth.

## Decision

Pre-size only the formula's contiguous clause-header vector from the bounded
hint, subject to the Glaurung acceptance benchmark.

- Leave the exact-dedup `HashMap` construction and growth byte-for-byte
  unchanged.
- Compute the hint after variable allocation from existing variable/root counts
  with saturating arithmetic, a 1,024-root contribution cap, a 65,536 total cap,
  and zero reservation for zero-variable encodings.
- Perform no AIG/clause traversal and expose no public API or resource-limit
  change.
- Keep clause literals, normalization, ordering, fingerprints, exact collision
  checks, lift maps, and replay unchanged.

The decision becomes accepted only if boundary tests pass, the CNF/SAT suites
and strict Clippy are green, and five clean representative processes improve
both CNF and end-to-end time with identical content/replay. A full-tier
confirmation under 4 GiB is then required; otherwise ordinary vector growth is
restored and the ADR is deferred.

## Evidence

Pending implementation measurement. ADR-0148's combined-container rejection is
recorded in `bench-results/glaurung-qfbv-2026-07-14.md`.

## Alternatives

- **Retry combined formula/index pre-sizing with a smaller table hint.**
  Rejected: ADR-0148 already shows lookup locality is sensitive, and this
  experiment must isolate the vector before tuning table load.
- **Reserve the exact clause count.** Rejected: it requires a new observational
  pass.
- **Inline clause literals.** Deferred as a broader public/checker ownership
  change.

## Consequences

The formula vector allocates expected header storage once for measured client
queries; the fingerprint table retains its accepted cache/growth behavior.
Underestimates grow normally, and the cap bounds eager memory. The real-corpus
time and memory gates decide whether header movement is material.
