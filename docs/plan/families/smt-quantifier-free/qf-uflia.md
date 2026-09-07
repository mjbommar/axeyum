# QF_UFLIA — uninterpreted functions with linear integer arithmetic

<!-- Family: [SMT, quantifier-free](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** on the parity board.

## Where the number lives

The ledger is [`bench-results/PARITY.md`](../../../../bench-results/PARITY.md)
and it is authoritative. The row below is a **copy, stamped**; re-read the
ledger rather than quoting this table, because it moves whenever a slice lands.

| as of solver commit | ours | reference | ratio | both / ours-only / reference-only | gap |
|---|---:|---:|---:|---|---:|
| `c28d7b7c6` | 122 | 180 | 67.8% | 122 / 0 / 58 | 58 |

- **Reference we measure against:** cvc5 1.3.4
- **Actual 2026 frontier for this logic:** SMTInterpol, then Yices2. **cvc5 is not the leader here.**
- **Corpus size (SMT-LIB 2024 non-incremental):** 659 files; our list is a
  committed 200-file slice (or the division's full size where smaller).

> Where the frontier line names someone other than our reference, "parity" in
> this division means parity with our reference, **not** dominance. See
> [the survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md)
> section 1.1.

## Cause

Censused (S3), 58 files: 31 search timeouts in the lazy UF/arithmetic CEGAR loop, 21 admission declines from the same loop on an application and function-group count (**unexplained**), 6 integer literals wider than `i128`. The wide-literal six are now understood and are **not** a literal-type problem: S9 landed the parser and re-ran ADR-0376's ablation on current HEAD, and with every wide numeral rescaled, or every mentioning assertion deleted, all six are still `unknown`. The binding constraint is the decision procedure's width.

> Read any census class with the two method corrections in
> [the parity plan](../../smt-parity-plan-2026-09-05.md) section 6: classify by
> the route that spent the budget, not the last route's message, and classify
> through the front door, never through the diagnostic corpus tool.

## Lever

S7 for the timeouts, but **instrument the CEGAR refinement policy before changing it** — that instrument does not exist. The six wide files are width-ladder work, not literal work.

## Scoring population

The committed 58-file loss list.

## Exit criterion

At or above 180.

## Owning documents

- Slice detail and history: [the parity plan](../../smt-parity-plan-2026-09-05.md)
- Loss census: [the census note](../../../research/11-design-review/2026-09-05-parity-loss-census.md)
- Measurement protocol: `scripts/parity-run.sh`, and the parity plan section 6.
