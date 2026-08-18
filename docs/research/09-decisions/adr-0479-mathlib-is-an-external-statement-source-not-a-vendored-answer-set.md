# ADR-0479: Mathlib is an external statement source, not a vendored answer set

Status: accepted
Date: 2026-08-18
Index-summary: Keep bulk Mathlib exports external, commit statement-only identities and candidates, and isolate proof values from Autogenesis search

## Context

The leakage-safe nursery needs 100--300 provenance-classified Nat/Int facts,
but the current ledger cannot supply a held-out population. Fleet host s5
already holds a complete Mathlib v4.30.0 checkout, a 5.5 GB full-environment
`lean4export` stream, and a 680,925-row declaration-name index. Copying the
full stream into Git would duplicate a regenerable third-party corpus and hand
the future search process every proof body for its proposed evaluation goals.

The installed and importer-tested toolchain is Lean/Mathlib v4.30.0. Upstream
stable had advanced to v4.33.0 by 2026-08-18, with v4.34.0-rc1 available. A
silent in-place refresh would therefore change source statements, proof
dependencies, exporter bytes, and importer compatibility at once.

## Decision

Bulk Mathlib checkouts, `.olean` files, complete exports, and generated
statement inventories remain external, immutable, and content-addressed.
Git stores:

- the exact Mathlib, Lean, and extractor identity;
- a small extractor that reads theorem names, modules, level parameters, and
  types but never theorem values;
- a manifest binding the external bytes and regeneration command; and
- reviewed, small derived candidate metadata with statement and type hashes.

Candidate selection runs only over the statement-only artifact. It may not read
the Mathlib checkout, compiled environment, full export, theorem values, or
tactic traces. Imported proof dependencies may later be reduced to graph edges
by a separate evaluation-only process for leakage-safe component assignment,
but proof bodies never enter planner input or count as Axeyum construction.

v4.30.0 remains the importer-compatible baseline. A current-stable refresh is a
separate versioned artifact and comparison, not an overwrite. Final evaluation
facts must bind one source version; cross-version survival is reported as a
generalization result rather than assumed.

## Evidence

The tracked extractor produced 9,729 Nat/Int theorem statements from exact
Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`. The immutable
38,978,919-byte external NDJSON has SHA-256
`4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc`.
An independent Python checker rehashes every byte, parses every row, requires
portable lexical ordering, and permits exactly five statement fields. A first
producer attempt used Lean's internal `Name.lt`; the checker rejected its
different order, so the artifact was regenerated with rendered-name ordering
rather than weakening the consumer.

The first statement-only selection contains 240 candidates: twenty from each
of twelve Nat/Int families. It is explicitly not a nursery, has no assigned
dependencies, splits, routes, or Axeyum outcomes, and grants no proof credit.

## Alternatives

- Vendoring the complete export was rejected because it is large, regenerable,
  and an answer leak.
- Using only declaration names was rejected because names do not bind theorem
  strength or permit statement review.
- Updating the repository pin to the newest release as part of harvesting was
  rejected because it conflates source refresh with importer migration.
- Reading theorem values in the candidate selector was rejected because a
  future planner could accidentally receive its held-out answers.

## Consequences

- Git receives about 161 KB of candidate metadata instead of gigabytes of
  third-party proof streams.
- The bulk artifact can be removed and regenerated without changing repository
  history, while its absence is reported rather than mistaken for verification.
- Dependency-component extraction must be separately sandboxed and reduced to
  metadata before the evaluation split freezes.
- Version drift becomes an explicit comparison dimension and future robustness
  test.
