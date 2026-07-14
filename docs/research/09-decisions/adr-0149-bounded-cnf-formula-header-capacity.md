# ADR-0149: Bounded CNF formula-header capacity

Status: deferred
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

Revision `84b39844` implements the isolated candidate. All 284 `axeyum-cnf`
tests, 30 SAT-BV tests, strict Clippy, formatting, and documentation-link checks
pass. Five clean artifact-v27 representative processes under the 4 GiB memory
cap remain 128/128 decided (64 SAT / 64 UNSAT), with zero errors,
disagreements, or model-replay failures. Every process emits the accepted
507,195 clauses and identifies 1,911 direct roots.

Against accepted ADR-0145 revision `c139d73b`, medians/means are:

| Measure | Accepted | Candidate | Delta |
|---|---:|---:|---:|
| Axeyum total p50 | 0.189851 s | 0.189539 s | -0.16% |
| Axeyum total mean | 0.189702 s | 0.189841 s | +0.07% |
| CNF p50 | 0.072978 s | 0.073583 s | +0.83% |
| CNF mean | 0.073648 s | 0.074138 s | +0.67% |
| total CV | 0.570% | 0.852% | +0.282 pp |

The matched subphase medians move +0.94% allocation, +0.68% gate encoding,
+2.09% root encoding, and -0.45% planning. Avoided formula-header growth does
not produce a stable CNF or end-to-end win. The predeclared gate requires both
median CNF and total improvement, so no full-tier run is warranted.

## Alternatives

- **Retry combined formula/index pre-sizing with a smaller table hint.**
  Rejected: ADR-0148 already shows lookup locality is sensitive, and this
  experiment must isolate the vector before tuning table load.
- **Reserve the exact clause count.** Rejected: it requires a new observational
  pass.
- **Inline clause literals.** Deferred as a broader public/checker ownership
  change.

## Consequences

Restore ordinary formula-vector growth exactly. Combined and isolated capacity
hints have now both failed the real-client gate, so close this micro-optimization
lane. Revisit allocation only with new attribution and a materially different
ownership design; next measure the shared normalization, fingerprinting, exact
duplicate-check, and formula-insertion path before selecting a larger GQ5
slice.
