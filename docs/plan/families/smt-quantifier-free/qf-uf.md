# QF_UF — uninterpreted functions, quantifier-free

<!-- Family: [SMT, quantifier-free](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** on the parity board.

## Where the number lives

The ledger is [`bench-results/PARITY.md`](../../../../bench-results/PARITY.md)
and it is authoritative. The row below is a **copy, stamped**; re-read the
ledger rather than quoting this table, because it moves whenever a slice lands.

| as of solver commit | ours | reference | ratio | both / ours-only / reference-only | gap |
|---|---:|---:|---:|---|---:|
| `c28d7b7c6` | 196 | 200 | 98.0% | 196 / 0 / 4 | 4 |

- **Reference we measure against:** cvc5 1.3.4
- **Actual 2026 frontier for this logic:** Saturated: OpenSMT, Yices2 and cvc5 all solve 1104 of 1104 in the 2026 results
- **Corpus size (SMT-LIB 2024 non-incremental):** 7,503 files; our list is a
  committed 200-file slice (or the division's full size where smaller).

> Where the frontier line names someone other than our reference, "parity" in
> this division means parity with our reference, **not** dominance. See
> [the survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md)
> section 1.1.

## Cause

**The census was wrong here, and the correction is the instructive part.** It classified all 38 losses as admission declines on an eager-Ackermann congruence count. S11a re-measured through the front door: on 35 files `euf-online` is entered first and spends 23.5 s of a 24 s budget, and the Ackermann decline that named the class is a millisecond tail after the budget is already gone. The cap genuinely blocked 3. S1b's order heap and S11a's fix together moved the division +6. **The remaining 4 have no cause named.**

> Read any census class with the two method corrections in
> [the parity plan](../../smt-parity-plan-2026-09-05.md) section 6: classify by
> the route that spent the budget, not the last route's message, and classify
> through the front door, never through the diagnostic corpus tool.

## Lever

A front-door census of the 4, then S7.

## Scoring population

The 4 remaining reference-only files; list not yet committed.

## Exit criterion

200.

## Owning documents

- Slice detail and history: [the parity plan](../../smt-parity-plan-2026-09-05.md)
- Loss census: [the census note](../../../research/11-design-review/2026-09-05-parity-loss-census.md)
- Measurement protocol: `scripts/parity-run.sh`, and the parity plan section 6.
