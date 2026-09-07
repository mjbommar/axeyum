# QF_LRA — linear real arithmetic

<!-- Family: [SMT, quantifier-free](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** on the parity board.

## Where the number lives

The ledger is [`bench-results/PARITY.md`](../../../../bench-results/PARITY.md)
and it is authoritative. The row below is a **copy, stamped**; re-read the
ledger rather than quoting this table, because it moves whenever a slice lands.

| as of solver commit | ours | reference | ratio | both / ours-only / reference-only | gap |
|---|---:|---:|---:|---|---:|
| `5c9b3a7c2` | 93 | 145 | 64.1% | 93 / 0 / 52 | 52 |

- **Reference we measure against:** cvc5 1.3.4
- **Actual 2026 frontier for this logic:** OpenSMT, then Yices2. **cvc5 is not the leader here.**
- **Corpus size (SMT-LIB 2024 non-incremental):** 1,753 files; our list is a
  committed 200-file slice (or the division's full size where smaller).

> Where the frontier line names someone other than our reference, "parity" in
> this division means parity with our reference, **not** dominance. See
> [the survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md)
> section 1.1.

## Cause

Censused (S3), 54 files at the time: 31 search timeouts and 23 the 1,024-atom online LRA admission cap. A clean two-way split with no other classes. The timeout half was profiled: final check into feasibility into simplex was 84% of wall, called 1,150 to 15,000 times per file. **The original diagnosis of that half was wrong** — S4 wired counters before changing anything and measured zero cold restarts across 6,571 checks, so the tableau was already warm and the cost was one redundant pass inside the pivot. The cap is load-bearing: removing it yields 0 new decides and 54 memory aborts.

> Read any census class with the two method corrections in
> [the parity plan](../../smt-parity-plan-2026-09-05.md) section 6: classify by
> the route that spent the budget, not the last route's message, and classify
> through the front door, never through the diagnostic corpus tool.

## Lever

S7 for the search; S10 to replace the atom constant with a measured memory budget rather than raising it.

## Scoring population

`bench-results/adr-1701-slice-1-20260905/qf_lra_population.tsv`, 33 files.

## Exit criterion

At or above 145.

## Owning documents

- Slice detail and history: [the parity plan](../../smt-parity-plan-2026-09-05.md)
- Loss census: [the census note](../../../research/11-design-review/2026-09-05-parity-loss-census.md)
- Measurement protocol: `scripts/parity-run.sh`, and the parity plan section 6.
