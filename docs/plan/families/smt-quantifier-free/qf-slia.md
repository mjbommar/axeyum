# QF_SLIA — strings with linear integer arithmetic

<!-- Family: [SMT, quantifier-free](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** on the parity board.

## Where the number lives

The ledger is [`bench-results/PARITY.md`](../../../../bench-results/PARITY.md)
and it is authoritative. The row below is a **copy, stamped**; re-read the
ledger rather than quoting this table, because it moves whenever a slice lands.

| as of solver commit | ours | reference | ratio | both / ours-only / reference-only | gap |
|---|---:|---:|---:|---|---:|
| `9914a1c0e` | 193 | 194 | 99.5% | 187 / 6 / 7 | 1 |

- **Reference we measure against:** cvc5 1.3.4
- **Actual 2026 frontier for this logic:** Z3-Noodler, then OSTRICH; cvc5 is third
- **Corpus size (SMT-LIB 2024 non-incremental):** 84,395 files; our list is a
  committed 200-file slice (or the division's full size where smaller).

> Where the frontier line names someone other than our reference, "parity" in
> this division means parity with our reference, **not** dominance. See
> [the survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md)
> section 1.1.

## Cause

Censused (S3), 7 files: 4 the int-blast ladder's bounded width 32, 2 a parser gap (`str.replace_all` over a non-constant operand), 1 the string gate refusing to certify a bounded refutation. The certification hypothesis that motivated this division explains 1 of 7, not the majority.

> Read any census class with the two method corrections in
> [the parity plan](../../smt-parity-plan-2026-09-05.md) section 6: classify by
> the route that spent the budget, not the last route's message, and classify
> through the front door, never through the diagnostic corpus tool.

## Lever

S11 for the width ladder (shared with QF_NIA) plus a small parser slice. The gate slice is one file.

## Scoring population

The committed 7-file loss list.

## Exit criterion

At or above 194 with 0 disagreements.

## Owning documents

- Slice detail and history: [the parity plan](../../smt-parity-plan-2026-09-05.md)
- Loss census: [the census note](../../../research/11-design-review/2026-09-05-parity-loss-census.md)
- Measurement protocol: `scripts/parity-run.sh`, and the parity plan section 6.
