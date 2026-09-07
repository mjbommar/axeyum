# QF_ABV — arrays over bit-vectors

<!-- Family: [SMT, quantifier-free](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** on the parity board.

## Where the number lives

The ledger is [`bench-results/PARITY.md`](../../../../bench-results/PARITY.md)
and it is authoritative. The row below is a **copy, stamped**; re-read the
ledger rather than quoting this table, because it moves whenever a slice lands.

| as of solver commit | ours | reference | ratio | both / ours-only / reference-only | gap |
|---|---:|---:|---:|---|---:|
| `9914a1c0e` | 179 | 197 | 90.9% | 178 / 1 / 19 | 18 |

- **Reference we measure against:** Bitwuzla 0.9.1
- **Actual 2026 frontier for this logic:** Bitwuzla, then bitwuzla-dandelion, then Yices2
- **Corpus size (SMT-LIB 2024 non-incremental):** 15,148 files; our list is a
  committed 200-file slice (or the division's full size where smaller).

> Where the frontier line names someone other than our reference, "parity" in
> this division means parity with our reference, **not** dominance. See
> [the survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md)
> section 1.1.

## Cause

Censused (S3), 19 files: 8 search timeouts on the array fast path, 3 a genuine array-shape gap in the lazy read-over-write and extensionality path (the ADR-0084/0085 boundary, confirmed on 3 files and **smaller than hypothesised**), 8 tool artifacts that are not capability findings.

> Read any census class with the two method corrections in
> [the parity plan](../../smt-parity-plan-2026-09-05.md) section 6: classify by
> the route that spent the budget, not the last route's message, and classify
> through the front door, never through the diagnostic corpus tool.

## Lever

A capability slice for the 3 shapes; the timeout half rides S7 and S8.

## Scoring population

The committed 19-file loss list.

## Exit criterion

At or above 197.

## Owning documents

- Slice detail and history: [the parity plan](../../smt-parity-plan-2026-09-05.md)
- Loss census: [the census note](../../../research/11-design-review/2026-09-05-parity-loss-census.md)
- Measurement protocol: `scripts/parity-run.sh`, and the parity plan section 6.
