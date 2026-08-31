# Lane: five-risk-coverage-audit

Status: IN PROGRESS (notes committed early per process rule; conclusions not yet
written).

## Task

Audit, per risk of the ADR-0717 threat model (kernel unsoundness, statement
error, vacuity, contamination, false evidence), what the L0 programme (S0-S6 of
`docs/plan/trusted-library-safety-roadmap-2026-08-30.md`) actually bought —
measured, with the gap reported first. Report only; no gate, census, or fact is
edited by this lane.

## Landed changes

| date | change |
|---|---|
| 2026-08-31 | lane opened; audit notes stub |

## Notes so far (unverified, gathering)

- ADR-0795 already found two census columns wrong: `circularity` (14 per-fact
  vs S2's central ~1,956) and `semantic_falsification` (96 named vs 8
  demonstrated). Neither may be quoted as coverage.
- Roadmap S0-S6 map onto risks unevenly: S1 -> risk 2, S2 -> risk 4, S3 ->
  risk 3, S4+S5 -> risk 1, S0+S6 -> risk 5.
- Open question 1: does any gate besides S1 now publish a per-fact set?
- Open question 2: is `independent_replay` at 7 a measurement gap (Lean replay
  grades ~1,985 declaration NAMES with no fact join) or a real one?
