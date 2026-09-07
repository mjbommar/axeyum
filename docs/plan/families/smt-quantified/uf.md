# UF — quantified uninterpreted functions

<!-- Family: [SMT, quantified](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** on the parity board.

## Where the number lives

The ledger is [`bench-results/PARITY.md`](../../../../bench-results/PARITY.md)
and it is authoritative. The row below is a **copy, stamped**; re-read the
ledger rather than quoting this table, because it moves whenever a slice lands.

| as of solver commit | ours | reference | ratio | both / ours-only / reference-only | gap |
|---|---:|---:|---:|---|---:|
| `c28d7b7c6` | 85 | 93 | 91.4% | 61 / 24 / 32 | 8 |

- **Reference we measure against:** cvc5 1.3.4
- **Actual 2026 frontier for this logic:** cvc5 leads the quantified logics
- **Corpus size (SMT-LIB 2024 non-incremental):** 7,590 files; our list is a
  committed 200-file slice (or the division's full size where smaller).

> Where the frontier line names someone other than our reference, "parity" in
> this division means parity with our reference, **not** dominance. See
> [the survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md)
> section 1.1.

## Cause

**Measured, 2026-09-06:** the
[front-door census](../../../research/11-design-review/2026-09-06-uf-front-door-census.md)
classified all 32 through `solve_smtlib`. Three causes with sizes:

1. **All 32 losses are cvc5 `unsat`** — the population is 100% refutation, and
   **50.4% of its wall (347.0 s of 688.0 s) goes to the pure-UF finite-model
   finder**, which cannot decide any of them. A finite-model rung is the
   budget-dominant stage on 16 of the 32.
2. **25 of 32 saturate the e-graph loop's `MAX_GROUND_TERMS = 8192`**, and the
   7 `search-timeout` files spend 3.1–21.2 s (median 14.7 s) inside the untraced
   cap-hit refutation check at `qinst_egraph.rs:1341` over the saturated set.
3. **The budget is neither spent nor bounded:** 11 of 32 return with 5–19 s
   unspent (all 11 `route-decline(residual-quantifier)` — out of routes, not out
   of time), and 6 overshoot, one to 62 866 ms of a 24 s budget.

**Both prior hypotheses are refuted.** Finite-model finding (the August gap
analysis) cannot decide an unsat file — and the finder we already ship is the
largest single consumer of these files' budget. The declared-sort CEGAR bound
(the S3 census) appears in no front-door trace of any of the 32; all 32 enter the
quantified ladder, where that bound does not live. Neither S1 nor S1b moved this
division, consistent with 0.0% of the loss wall sitting in a quantifier-free SAT
search. Size does not separate the losses from the wins either: the 32 losses,
the 61 both-solved and the 83 nobody-solved are indistinguishable on every size
axis measured.

> Read any census class with the two method corrections in
> [the parity plan](../../smt-parity-plan-2026-09-05.md) section 6: classify by
> the route that spent the budget, not the last route's message, and classify
> through the front door, never through the diagnostic corpus tool. The census
> adds a third: `qtrace`'s six top-level stages share ONE `t0`, so their printed
> numbers are cumulative and a stage's own cost is the difference.

## Lever

**The obvious lever was built and refuted.** Returning the finite-model probe's
half-budget to the refutation family (`probe_budget` `t/2` → `t/16`, measured
interleaved on both populations) decides **0 of the 32** and costs **1 of the
24** axeyum-only wins. Do not spend a slice on re-tuning `probe_budget`, the
ladder order, or the `mbqi_first_refusal` fraction.

Two levers the data does support, in order:

1. **Bound the cap-hit refutation check** (`qinst_egraph.rs:1341`). Scored on the
   7 `search-timeout` files; exit at ≥3 deciding `unsat` inside 24 s with 0
   verdict flips on the 61 both-solved and the 24 axeyum-only.
2. **Instantiation reach for nested / existential / non-top-level quantifiers**
   — the terminal decline in `decide_instantiation`. This is a capability slice,
   not tuning: the 11 files in group A return with the budget unspent, so no
   scheduling or cap change can reach them.

Plus one correctness fix that is not a parity lever: **enforce the quantified
ladder's deadline** (62 866 ms and 115 835 ms runs against a 24 s budget were
measured).

## Scoring population

The 32 reference-only files
(`bench-results/parity-losses-20260905/UF.txt`), with the per-file front-door
classification in
`bench-results/parity-losses-20260906/UF.front-door.census.tsv`. Lever 1 scores
on its 7-file subset, lever 2 on the 11-file group A. The 24 axeyum-only wins
(`bench-results/parity-losses-20260906/UF.axeyum-only24.txt`) are the regression
population for any lever that touches the finite-model finder — they are 22
`sat` files that **only** that finder decides, 21 of them in 1.1 s or less.

## Exit criterion

At or above 93; the 24 axeyum-only stay.

## Owning documents

- Slice detail and history: [the parity plan](../../smt-parity-plan-2026-09-05.md)
- Loss census: [the census note](../../../research/11-design-review/2026-09-05-parity-loss-census.md)
  (its UF class is superseded) and the
  [front-door census](../../../research/11-design-review/2026-09-06-uf-front-door-census.md)
  that replaces it
- Measurement protocol: `scripts/parity-run.sh`, and the parity plan section 6.
