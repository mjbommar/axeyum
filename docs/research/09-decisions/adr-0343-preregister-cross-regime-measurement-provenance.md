# ADR-0343: Preregister cross-regime measurement provenance

Status: proposed
Date: 2026-07-21

## Context

G1 asks for one coverage-weighted parity matrix across the 35-row
curated/regression scoreboard and the 228-file public convenience inventory.
The two headline decide rates are useful but describe different selection
policies. Before this prototype they shared neither an identity schema nor an
exact overlap calculation.

The source audit finds 992 regression occurrences, of which 927 are
file-backed, 837 have unique normalized paths, and only 778 have unique exact
contents. The public inventory has 228 unique paths and contents. The two
regimes share 99 exact contents, so 43.4% of the public inventory is not
independent of the regression record. Both populations are non-official, and
neither has a neutral non-Z3 oracle on every exact row.

This addresses the open measurement question in
[`research-questions.md`](../08-planning/research-questions.md) and is backed by
the [design audit](../../plan/measurement-provenance-design-2026-07-21.md),
machine-readable
[`measurement-provenance-v1.json`](../../plan/measurement-provenance-v1.json),
and generated
[row matrix](../../plan/generated/measurement-provenance-matrix.md).

## Decision

**Give every benchmark measurement a versioned raw/path/content/population/
selection/scoring/oracle identity, keep unequal regimes as separate strata, and
forbid a global parity percentage unless an ADR defines a common eligible
population and aggregation rule first.**

The v1 contract defines:

- raw occurrence count, normalized path identity, and exact-content SHA-256 as
  three distinct denominators;
- aggregate-only cases as visible but non-hashable, never synthesized into
  file identities;
- population and selection classes separate from logic labels;
- row-local mean wall PAR-2 with its original limit and score source;
- benchmark status, Z3 library, Z3 binary, and neutral non-Z3 evidence as
  separate oracle classes;
- an observed Axeyum coverage class that is explicitly not intrinsic
  difficulty; and
- `near-duplicate = not-measured` until a later experiment defines and tests a
  normalization.

V1 reports exact-deduplicated denominators but does not compute deduplicated
PAR-2. Repeated contents can occur under different configurations, limits, and
rows; selecting one run would be a new policy, not a mechanical consequence of
hashing.

The official SMT-COMP 2026 rules remain a reference policy. A run receives
`official_selection = true` only if it binds a complete eligible release,
track/status filters, family partition, cap, seed, and selected set. Reusing the
competition scoring code is insufficient.

## Preregistered acceptance gates

1. The generator reproduces 35 regression rows / 992 raw cases and 18 public
   logic rows / 228 raw cases from committed artifacts without hand-entering a
   row result.
2. Exact file inspection reproduces 927 regression file occurrences, 837
   normalized paths, 778 unique contents, 58 exact-alias groups, 59 exact-alias
   excess paths, and 65 aggregate-only cases.
3. Public inventory, raw-result, and provenance artifacts agree on every
   normalized ID, logic, outcome class, count, and exact hash.
4. The cross-regime join reproduces exactly 99 shared SHA-256 values and emits
   every joined ID in machine-readable output.
5. Every PAR-2 value remains row-local. Public-inventory values are recomputed
   from raw wall times with the registered 120-second limit; no cross-row,
   cross-host, cross-limit, or cross-regime aggregate exists.
6. Every row records population, selection, official-selection, oracle, neutral
   oracle, operator-profile, and near-duplicate status. V1 has zero neutral rows
   on the exact populations and labels operator depth as logic-only.
7. Regeneration is byte-identical; manifest/path/count drift and stale generated
   outputs fail `--check`.
8. The parity-doc, scoreboard, SMT-COMP reproduction unit, documentation-link,
   formatting, and diff gates pass under the bounded job policy.

Acceptance authorizes the reporting schema and generator only. It grants no
new solver, soundness, performance, independence, representativeness, or
official-competition claim.

## Evidence

- The official
  [SMT-COMP 2026 rules](https://smt-comp.github.io/2026/rules.pdf) define
  directory-derived families, eligible/selected populations, capped seeded
  selection, and division-local scoring. Neither local population carries all
  of that provenance.
- `gen-scoreboard.py` exposes 35 row artifacts and 927 instance records; the
  two synthetic graduated artifacts contain 65 aggregate cases without
  instance identity.
- Exact hashing finds a triple-alias group plus 57 pair groups inside the
  normalized regression population.
- The committed public provenance reports 228 unique byte hashes and seven
  path-derived source families; exact joining against the scoreboard yields 99
  shared hashes.
- The separate 24-file QF_BV three-solver comparison does not use the exact
  228-file population and therefore provides no neutral-oracle credit to it.
- Follow-on commit `d9e71e21` adds a candidate 2024 full-tree cap/family
  selection and distributed runner. Its external 438,631-to-64,345 manifest is
  motivating operational evidence only: the first run terminated after 2,041
  progress rows with zero raw shards, so it is incomplete/uncommitted and
  the selector does not yet bind the full eligibility filters, official
  release/seed, corpus digest, or selected-file hashes.

## Alternatives

- **Keep only the two raw percentages.** Rejected: it hides repeated paths,
  exact aliases, source skew, and cross-regime overlap.
- **Merge the two regimes and deduplicate by hash.** Rejected: the regimes use
  different hosts, limits, configurations, selection policies, and available
  evidence; a merged score has no registered estimand.
- **Use normalized path as the sole identity.** Rejected: it misses 59
  additional exact-content aliases in the current scoreboard.
- **Normalize SMT-LIB syntax immediately.** Deferred: comments, options,
  command order, declarations, and symbol names can be semantically relevant.
  A normalization requires mutation and differential gates.
- **Call source-solver regression packs neutral oracle evidence.** Rejected:
  corpus provenance is not an execution result.
- **Weight each source family equally.** Deferred: equal family weighting is a
  substantive statistical policy, especially when family boundaries are
  directory-derived and incomplete.

## Consequences

Public claims can now name their exact denominator and overlap instead of
presenting one misleading scalar. New benchmark artifacts must state whether
they are curated, partial, official-style, or official; they cannot inherit a
neutral oracle from a different population.

The cost is that the honest answer remains less compact: selected-fragment
coverage, public-inventory coverage, exact deduplication, neutral agreement, and
official selection are separate axes. That complexity already exists in the
data; the schema prevents documentation from hiding it.
