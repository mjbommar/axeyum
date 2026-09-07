# QF_BV — quantifier-free bit-vectors

<!-- Family: [SMT, quantifier-free](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** on the parity board.

## Where the number lives

The ledger is [`bench-results/PARITY.md`](../../../../bench-results/PARITY.md)
and it is authoritative. The row below is a **copy, stamped**; re-read the
ledger rather than quoting this table, because it moves whenever a slice lands.

| as of solver commit | ours | reference | ratio | both / ours-only / reference-only | gap |
|---|---:|---:|---:|---|---:|
| `9914a1c0e` | 188 | 194 | 96.9% | 188 / 0 / 6 | 6 |

- **Reference we measure against:** Bitwuzla 0.9.1
- **Actual 2026 frontier for this logic:** Bitwuzla-MachBV, then Bitwuzla, then Yices2
- **Corpus size (SMT-LIB 2024 non-incremental):** 46,191 files; our list is a
  committed 200-file slice (or the division's full size where smaller).

> Where the frontier line names someone other than our reference, "parity" in
> this division means parity with our reference, **not** dominance. See
> [the survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md)
> section 1.1.

## Cause

Measured at the SAT level rather than the encoding level: on identical CNF the native core needs about the same number of conflicts as Kissat and processes them roughly 1.5x slower, and Kissat spends only 26% of its own time inprocessing. Censused 6 files: 5 search timeouts, 1 tool artifact.

> Read any census class with the two method corrections in
> [the parity plan](../../smt-parity-plan-2026-09-05.md) section 6: classify by
> the route that spent the budget, not the last route's message, and classify
> through the front door, never through the diagnostic corpus tool.

## Lever

S8, native-core throughput — clause-arena locality, `reduce_db` tiering, restart policy, in measured order. Word-level rewriting is the other half of the reference’s advantage.

## Scoring population

113 p4dfa CNFs at 20 s (Kissat 11 / CaDiCaL 10 / native 6), plus the 6 reference-only files.

## Exit criterion

At or above 194.

## Owning documents

- Slice detail and history: [the parity plan](../../smt-parity-plan-2026-09-05.md)
- Loss census: [the census note](../../../research/11-design-review/2026-09-05-parity-loss-census.md)
- Measurement protocol: `scripts/parity-run.sh`, and the parity plan section 6.
