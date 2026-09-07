# QF_IDL — integer difference logic

<!-- Family: [SMT, quantifier-free](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** on the parity board.

## Where the number lives

The ledger is [`bench-results/PARITY.md`](../../../../bench-results/PARITY.md)
and it is authoritative. The row below is a **copy, stamped**; re-read the
ledger rather than quoting this table, because it moves whenever a slice lands.

| as of solver commit | ours | reference | ratio | both / ours-only / reference-only | gap |
|---|---:|---:|---:|---|---:|
| `c28d7b7c6` | 105 | 123 | 85.4% | 103 / 2 / 20 | 18 |

- **Reference we measure against:** cvc5 1.3.4
- **Actual 2026 frontier for this logic:** QiuQi, then the Z3 variants; Yices2 leads the 24-second score
- **Corpus size (SMT-LIB 2024 non-incremental):** 2,528 files; our list is a
  committed 200-file slice (or the division's full size where smaller).

> Where the frontier line names someone other than our reference, "parity" in
> this division means parity with our reference, **not** dominance. See
> [the survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md)
> section 1.1.

## Cause

The best-understood division on the board, and the model for how a cause should be established. Two measured causes, both fixed. Propagation was a full clause-database rescan with no watch lists, 19.4 s of a 24 s budget on the traced files with the theory at 0 ms. Dispatch overran the budget because a route spent a fixed ~8 s reserve before evaluating a size constant it could have checked immediately. S1, S2 and S1b took the division from 70 to 105; on the 50-file timeout population decided went 11 to 27, and one file fell from 15.5 s to 1.8 s while making identical decisions, which isolates the cost to the linear decision scan alone.

> Read any census class with the two method corrections in
> [the parity plan](../../smt-parity-plan-2026-09-05.md) section 6: classify by
> the route that spent the budget, not the last route's message, and classify
> through the front door, never through the diagnostic corpus tool.

## Lever

S7, engine unification, for what remains.

## Scoring population

`bench-results/adr-1701-slice-1-20260905/qf_idl_population.tsv`, 50 files.

## Exit criterion

At or above 123.

## Owning documents

- Slice detail and history: [the parity plan](../../smt-parity-plan-2026-09-05.md)
- Loss census: [the census note](../../../research/11-design-review/2026-09-05-parity-loss-census.md)
- Measurement protocol: `scripts/parity-run.sh`, and the parity plan section 6.
