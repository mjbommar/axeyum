# UF — quantified uninterpreted functions

<!-- Family: [SMT, quantified](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** on the parity board.

## Where the number lives

The ledger is [`bench-results/PARITY.md`](../../../../bench-results/PARITY.md)
and it is authoritative. The row below is a **copy, stamped**; re-read the
ledger rather than quoting this table, because it moves whenever a slice lands.

| as of solver commit | ours | reference | ratio | both / ours-only / reference-only | gap |
|---|---:|---:|---:|---|---:|
| `c28d7b7c6` | 85 | 93 | 91.4% | 61 / 24 / 32 | 8 |

- **Reference we measure against:** cvc5 1.3.4
- **Actual 2026 frontier for this logic:** cvc5 leads the quantified logics
- **Corpus size (SMT-LIB 2024 non-incremental):** 7,590 files; our list is a
  committed 200-file slice (or the division's full size where smaller).

> Where the frontier line names someone other than our reference, "parity" in
> this division means parity with our reference, **not** dominance. See
> [the survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md)
> section 1.1.

## Cause

**Unknown, and both hypotheses on record are refuted or unverified.** The August gap analysis said finite-model finding, unmeasured. The S3 census said all 32 were the declared-sort CEGAR bound; S11a showed that class is an artifact of the diagnostic tool, which runs the flat assertion view rather than the front door. Neither S1 nor S1b moved this division at all, which rules out the Boolean-search levers. The 24 axeyum-only files are the widest such column on the board.

> Read any census class with the two method corrections in
> [the parity plan](../../smt-parity-plan-2026-09-05.md) section 6: classify by
> the route that spent the budget, not the last route's message, and classify
> through the front door, never through the diagnostic corpus tool.

## Lever

**A front-door census, before any slice.** No lever is authorised here until one exists.

## Scoring population

The 32 reference-only files.

## Exit criterion

At or above 93; the 24 axeyum-only stay.

## Owning documents

- Slice detail and history: [the parity plan](../../smt-parity-plan-2026-09-05.md)
- Loss census: [the census note](../../../research/11-design-review/2026-09-05-parity-loss-census.md)
- Measurement protocol: `scripts/parity-run.sh`, and the parity plan section 6.
