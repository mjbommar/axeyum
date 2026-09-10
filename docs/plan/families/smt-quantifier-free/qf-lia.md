# QF_LIA — linear integer arithmetic

<!-- Family: [SMT, quantifier-free](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** on the parity board.

## Where the number lives

The ledger is [`bench-results/PARITY.md`](../../../../bench-results/PARITY.md)
and it is authoritative. The row below is a **copy, stamped**; re-read the
ledger rather than quoting this table, because it moves whenever a slice lands.

| as of solver commit | ours | reference | ratio | both / ours-only / reference-only | gap |
|---|---:|---:|---:|---|---:|
| `c28d7b7c6` | 113 | 139 | 81.3% | 111 / 2 / 28 | 26 |

- **Reference we measure against:** cvc5 1.3.4
- **Actual 2026 frontier for this logic:** QiuQi, then OpenSMT. **cvc5 is not the leader here.**
- **Corpus size (SMT-LIB 2024 non-incremental):** 13,306 files; our list is a
  committed 200-file slice (or the division's full size where smaller).

> Where the frontier line names someone other than our reference, "parity" in
> this division means parity with our reference, **not** dominance. See
> [the survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md)
> section 1.1.

## Cause

Censused (S3), 27 files: 15 admission declines at the LIA driver's pre-SAT resource boundary, 4 search timeouts, 4 tool artifacts, 3 a wall-clock deadline inside branch-and-bound (**corrected 2026-09-10**: the census row reads "wall-clock deadline, node cap 20000000" — the DEADLINE fired and the cap was context; item 3.4 measured 0 of 911 benchmarks stopped by the cap, and one of these three is now decided `sat` in 409 nodes), 1 an i128 overflow inside the exact-rational simplex. Admission outweighs timeout more than three to one, so this is not primarily a search-speed division. **Separately owed:** S2's preflight now declines two `bofill-scheduling` files at 109 ms that the online probe used to refute in 8.1 s.

> Read any census class with the two method corrections in
> [the parity plan](../../smt-parity-plan-2026-09-05.md) section 6: classify by
> the route that spent the budget, not the last route's message, and classify
> through the front door, never through the diagnostic corpus tool.

## Lever

The S2 follow-up (let the size-gated route still run the online probe) is small and independent of the engine work. Then a cut-budget slice, and S9’s wide path applied inside the simplex for the overflow file.

## Scoring population

The committed 27-file loss list plus the two `bofill-scheduling` files.

## Exit criterion

At or above 139.

## Owning documents

- Slice detail and history: [the parity plan](../../smt-parity-plan-2026-09-05.md)
- Loss census: [the census note](../../../research/11-design-review/2026-09-05-parity-loss-census.md)
- Measurement protocol: `scripts/parity-run.sh`, and the parity plan section 6.
