# ADR-0148: Bounded CNF container capacity hints

Status: proposed
Date: 2026-07-14

## Context

After ADR-0145, canonical full-tier CNF encoding costs 7.23 seconds across
53.75 million clause attempts and 49.20 million emitted clauses. Every encoding
starts both the formula's outer `Vec<CnfClause>` and the collision-safe
fingerprint `HashMap` empty. They repeatedly grow and move clause headers or
rehash index entries during gate/root emission even though variable allocation
and root count are already known.

Artifact-v27 data gives a bounded no-extra-pass estimate. Across all 13,462
well-typed Glaurung queries,
`min(5 * cnf_variables + roots, 65_536)` covers every final clause count. It
reserves 69,225,859 aggregate clause slots for 49,199,541 emitted clauses
(1.407x), below the approximately 71,566,146 slots (1.455x) implied by ordinary
power-of-two vector growth. The maximum emitted formula has 62,255 clauses, so
the 65,536 cap also matches the current largest growth bucket.

## Decision

Pre-size the formula clause vector and exact-dedup index from a deterministic,
bounded hint, subject to the Glaurung acceptance benchmark.

- Compute the hint after variable allocation from already-known CNF-variable
  and input-root counts; perform no graph or clause traversal.
- Use five slots per variable plus at most 1,024 root slots, saturating all
  arithmetic and capping the result at 65,536.
- Return a zero hint when there are no CNF variables, avoiding eager allocation
  for constant-only scripts. An underestimated formula grows normally.
- Apply the same hint to the formula header vector and collision-safe
  fingerprint index. Clause normalization, literal storage, stable order,
  fingerprints, exact collision checks, and duplicate decisions do not change.
- Keep the hint private and non-semantic. It is neither a resource limit nor a
  public API promise.

The decision becomes accepted only if boundary tests prove zero/saturation/cap
behavior, the CNF/SAT suites and strict Clippy pass, and five clean
representative canonical processes improve end-to-end and CNF time with
identical content and replay. A full-tier confirmation under 4 GiB is then
required; otherwise empty-container growth is restored and the ADR is deferred.

## Evidence

Pending implementation measurement. The accepted ADR-0145 baseline and the
rejected ADR-0146/0147 experiments are recorded in
`bench-results/glaurung-qfbv-2026-07-14.md`.

## Alternatives

- **Reserve the exact final clause count.** Rejected: it requires a new planning
  traversal or speculative encoding, recreating the observational-work trap.
- **Reserve twice the reachable AIG nodes.** Rejected: it reserves 81.41 million
  aggregate slots (1.655x emitted) on this corpus.
- **Use an uncapped five-times-variable estimate.** Rejected: public encoders
  must not eagerly allocate proportional to an adversarially large AIG before
  clauses demonstrate that need.
- **Change `CnfClause` to inline literal storage.** Deferred: that is a broader
  public/checker-wide ownership change and should not be mixed with container
  growth.

## Consequences

Typical client formulas allocate their expected final containers once, while
large or unusual formulas retain ordinary growth after the bounded hint. The
hint may reserve unused capacity, so both performance and the 4 GiB full-tier
memory gate are acceptance requirements.
