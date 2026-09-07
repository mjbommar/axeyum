# QF_NIA — nonlinear integer arithmetic

<!-- Family: [SMT, quantifier-free](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** on the parity board.

## Where the number lives

The ledger is [`bench-results/PARITY.md`](../../../../bench-results/PARITY.md)
and it is authoritative. The row below is a **copy, stamped**; re-read the
ledger rather than quoting this table, because it moves whenever a slice lands.

| as of solver commit | ours | reference | ratio | both / ours-only / reference-only | gap |
|---|---:|---:|---:|---|---:|
| `9914a1c0e` | 39 | 87 | 44.8% | 26 / 13 / 61 | 48 |

- **Reference we measure against:** cvc5 1.3.4
- **Actual 2026 frontier for this logic:** Z3-Z3++ and Z3-alpha2, then Z3-GEX
- **Corpus size (SMT-LIB 2024 non-incremental):** 25,443 files; our list is a
  committed 200-file slice (or the division's full size where smaller).

> Where the frontier line names someone other than our reference, "parity" in
> this division means parity with our reference, **not** dominance. See
> [the survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md)
> section 1.1.

## Cause

Censused (S3), 61 files: 30 search timeouts on the generic int-blast ladder, 18 admission declines (17 of them the ladder's 64,000,000 CNF-clause size cap), 13 other (11 a bounded-width-32 model incompleteness). One benchmark family is 134 of the 200 files and 74 of the misses; excluding it we are at 74% of the reference. **Three cheap levers were built and refuted** (0, +1 and +3 files), and four times the clock buys 0 of 20 timeouts.

> Read any census class with the two method corrections in
> [the parity plan](../../smt-parity-plan-2026-09-05.md) section 6: classify by
> the route that spent the budget, not the last route's message, and classify
> through the front door, never through the diagnostic corpus tool.

## Lever

S12, the one unpriced hypothesis: admit a ladder rung when a *coefficient* rather than a bound is large, through an eager small-domain product split reached without the lazy refinement loop that fails.

## Scoring population

The 32 one-live-rung files, with files outside the dominant family reported separately.

## Exit criterion

**The reference count is not a target here.** It has read 89, 76, 76, 81, 83 and 87 across six sweeps of this list. The honest target is the axeyum count above 61.

## Owning documents

- Slice detail and history: [the parity plan](../../smt-parity-plan-2026-09-05.md)
- Loss census: [the census note](../../../research/11-design-review/2026-09-05-parity-loss-census.md)
- Measurement protocol: `scripts/parity-run.sh`, and the parity plan section 6.
