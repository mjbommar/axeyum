# QF_RDL — real difference logic

<!-- Family: [SMT, quantifier-free](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** on the parity board.

## Where the number lives

The ledger is [`bench-results/PARITY.md`](../../../../bench-results/PARITY.md)
and it is authoritative. The row below is a **copy, stamped**; re-read the
ledger rather than quoting this table, because it moves whenever a slice lands.

| as of solver commit | ours | reference | ratio | both / ours-only / reference-only | gap |
|---|---:|---:|---:|---|---:|
| `c28d7b7c6` | 142 | 154 | 92.2% | 140 / 2 / 14 | 12 |

- **Reference we measure against:** cvc5 1.3.4
- **Actual 2026 frontier for this logic:** Yices2, then cvc5
- **Corpus size (SMT-LIB 2024 non-incremental):** 255 files; our list is a
  committed 200-file slice (or the division's full size where smaller).

> Where the frontier line names someone other than our reference, "parity" in
> this division means parity with our reference, **not** dominance. See
> [the survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md)
> section 1.1.

## Cause

Was 24 admission declines (23 of them the 1,024-atom online LRA cap) and 22 search timeouts. S1, S2 and S1b together moved the division from 107 to 142. **The remaining 14 have not been re-censused**, so the class breakdown above no longer describes them.

> Read any census class with the two method corrections in
> [the parity plan](../../smt-parity-plan-2026-09-05.md) section 6: classify by
> the route that spent the budget, not the last route's message, and classify
> through the front door, never through the diagnostic corpus tool.

## Lever

S7 for the search half, S10 for the atom cap — but re-census first.

## Scoring population

Re-census the 14; the pre-S1 list is stale.

## Exit criterion

At or above 154.

## Owning documents

- Slice detail and history: [the parity plan](../../smt-parity-plan-2026-09-05.md)
- Loss census: [the census note](../../../research/11-design-review/2026-09-05-parity-loss-census.md)
- Measurement protocol: `scripts/parity-run.sh`, and the parity plan section 6.
