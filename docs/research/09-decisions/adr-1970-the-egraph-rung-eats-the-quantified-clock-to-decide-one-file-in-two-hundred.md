# ADR-1970: `q:egraph` eats 94 % of the quantified clock to decide one file in two hundred — and taking it away is worth two

Status: accepted
Index-summary: `UFNIA` and `UFLIA` are censused over their WHOLE winnable sets (129 rows). The largest family in both — `quantified solve time budget exhausted after e-matching`, 23 rows each — is attributed to ONE route: `q:egraph` holds a median 94 % / 88 % of the 24 s budget on 44 of those 46 rows, declines, and starves full MBQI and the finite-model finder. The same run measures what that budget buys: the rung is ENTERED on ~61 % of files and DECIDES 1 of 200 (`UFNIA`) and 8 of 200 (`UFLIA`). A ladder reserve is therefore the obvious fix, and it was built as a one-binary env lever and sized by its own CEILING arm (`share = 1`, the rung gets 1 ms, the ladder below gets everything): **46 blocked rows → +4 / −2 over 400 files after re-checking, with `UFLIA` net zero and `AUFLIA` — a quantified control on which the route runs — flat at 0/0.** The lever ships OFF. Two corrections that outlast the null: ADR-1957's "`UFNIA` is genuinely clock-bound" is half right (its 18-row second family gives up with a median 8,768 ms of 24,000 UNSPENT), and 0 of 129 rows reach the instantiation round ceiling, so ADR-1956 holds on two more divisions.
Index-status: accepted
Date: 2026-09-13

## Context

`UFNIA` and `UFLIA` are Tier-1 #2 and #3 — 23,592 files on disk, and the
fragment the flywheel dispatches into. Six lanes worked Tier 1 on 2026-09-13 and
every one of them targeted the array divisions or the dispatch ladder. These two
rows had not been aimed at.

What existed going in:

- [ADR-1957]'s Tier-1 board censused `UFNIA`'s 61 winnable rows and wrote that
  it is *"the one division on the board where more time would plausibly buy
  verdicts"* — **genuinely clock-bound**.
- `UFLIA`'s census was [board-six]'s, taken **before** [ADR-1956] split the
  e-matching loop's three exits. Its largest bucket was 25 rows of
  `watchdog fired before the worker thread returned`, which is not a reason.

Both were re-censused here on the current tree, over the whole winnable set of
each. The measurement, the artifacts and every derivation script are in
[`bench-results/ufnia-uflia-census-20260913/`](../../../bench-results/ufnia-uflia-census-20260913/README.md).

## What the census found

129 winnable rows; 100 classified, 29 UNCLASSIFIED under [ADR-1941], 0 with no
route trail.

    by kind:  CLOCK 81   SHAPE 14   PARSE 2   OTHER 2   ROUND 1

**One family is the largest in both divisions, with the same count in each:**

| family | kind | UFNIA | UFLIA | tot | ms_left median |
|---|---|---:|---:|---:|---:|
| **ladder CLOCK exhausted after e-matching** | CLOCK | 23 | 23 | **46** | **−61** |
| e-matching instantiation CLOCK | CLOCK | 18 | 14 | 32 | **+6,346** |

and it is attributable to a single route. On **44 of those 46 rows** the route
holding the largest attributed segment is `q:egraph`:

| division | `bound_ms` median | share of the 24 s budget |
|---|---:|---:|
| UFNIA | 22,554 ms | **94 %** |
| UFLIA | 21,065 ms | **88 %** |

It then declines. `finish_quantified_solve` reaches its next
`config_with_remaining_timeout` with nothing left, so **full MBQI and the full
pure-UF finite-model finder never run at all**, and the ladder ends at
`quantified_timeout("e-matching")`.

The same run measures what that budget buys:

| division | `q:egraph` ENTERED | it DECIDED | it BOUND the run |
|---|---:|---:|---:|
| UFNIA | 125 / 200 (62 %) | **1 / 200** | 82 / 200 |
| UFLIA | 119 / 200 (60 %) | **8 / 200** | 69 / 200 |
| AUFLIA *(control)* | 115 / 200 (57 %) | **0 / 200** | 35 / 200 |

A rung that runs on 61 % of files, holds the largest time segment on 38 %, and
decides between 0.5 % and 4 % is the textbook case for a ladder reserve — the
same shape, with the same evidence, that
[ladder-budget-discipline-2026-09-08] built `ABV_ONLINE_LADDER_RESERVE_SHARE`
and `UF_ARITH_LADDER_RESERVE_SHARE` on. `finish_quantified_solve`'s own comment
had already recorded the mechanism in prose: *"the e-graph instantiation loop
reliably consumes every second it is given"*. The fix applied there — a bounded
first-refusal MBQI rung on 1/8 of the budget — was placed **above** the loop and
left everything below it unprotected.

## Decision

**Build the reserve as a lever, size it with the lever's own ceiling arm, and
ship it OFF because the ceiling is 2 files in 400.**

1. `QuantEgraphReservePolicy` in `auto.rs`, selected by
   `AXEYUM_QUANT_EGRAPH_RESERVE`, **default `WholeBudget`** — byte-identical to
   the code before it existed, asserted directly rather than inferred, and
   mutation-killed by exactly one test.
2. `share = n` reserves `1/n` of the remaining clock for the rungs below.
   `share = 1` hands the rung `MIN_LADDER_SLICE` (1 ms) and the ladder below
   essentially the whole budget — **strictly more clock than any real reserve
   can give the lower rungs**, which is what makes it a ONE-WAY ceiling: a file
   the `share = 1` arm does not decide is out of reach of every reserve at
   every share. This is [ADR-1965]'s sound-one-way-surrogate technique, which is
   the only sizing method in this repository whose measured reach went UP.
3. **The measurement decides, not the mechanism.** Interleaved per-file A/B, one
   binary and two env values, both arms back to back on one pinned physical core
   with the order alternating, 24 s / 8 GiB:

   | division | n | base | ceiling arm | net | gain | loss | flips |
   |---|---:|---:|---:|---:|---:|---:|---:|
   | UFNIA | 200 | 53 | 55 | **+2** | 2 | 0 | 0 |
   | UFLIA | 200 | 73 | 73 | **+0** | 3 | 3 | 0 |
   | AUFLIA *(control)* | 200 | 86 | 86 | **+0** | 0 | 0 | 0 |

   Every moved row re-run three times per arm and against `:status`, z3 4.13.3
   and cvc5 1.3.4: **GAIN 4, LOSS 2, UNSTABLE 2, CONTRADICTED 0**. Two of the
   eight the A/B moved were ambient and vanish on re-check.

4. **The lever stays in the tree, defaulted off and registered.** Same
   disposition as `AXEYUM_QINST_ROUNDS` after [ADR-1956] and
   `AXEYUM_NIA_REFINEMENT` after its own A/B: the next lane re-asks the question
   with one environment variable and no patch.

## Why the null is a null and not a missed opportunity

**The bracket is `46 → 2`, and 2 is inside the band this run measures on
itself.** The base arm reads **73** in the `UFLIA` A/B and **76** in the
single-arm census sweep — same commit, same boxes, same budget. A 3-file ambient
band is larger than the whole effect.

**The route is not absent from the population.** Three lanes this week shipped
controls structurally unable to exercise the route they changed — `ufbv_online`
on 0 of 400 files, `q:egraph` on 0 of 200 for three **quantifier-free**
divisions. So the hit rate is published beside the null: `q:egraph` is entered
on 62 % / 60 % / 57 % of `UFNIA` / `UFLIA` / `AUFLIA`, and the control is
`AUFLIA` — a **quantified** division — for the same reason. Its null is a null
of a route that runs on 115 of its 200 files and bounds 35 of them.

**Losing files is the cost, and it is real.** The `UFLIA` arm loses two
`grasshopper/uninstantiated` files reproducibly — `unsat,unsat,unsat` in the
base arm and `unknown,unknown,unknown` in the ceiling arm. `q:egraph` decides 8
of `UFLIA`'s 76, and a reserve takes clock from exactly that. A gain column
printed without this one would be half a measurement.

**The 44 starved rows are not starved by an accident of scheduling.** That was
the hypothesis and it is what the ceiling arm falsifies: given essentially the
entire budget instead of nothing, the rungs below `q:egraph` decide **two** of
the 46. Whatever else those 44 files need, it is not the clock that `q:egraph`
is holding.

## Two corrections that outlast the null

### 1. "`UFNIA` is genuinely clock-bound" is half right, and the half matters

[ADR-1957] read `UFNIA`'s 21 + 15 CLOCK rows as one finding. They are two, and
[ADR-1950]'s own falsification mechanism separates them:

- `quantified solve time budget exhausted after e-matching` — 23 rows, median
  **61 ms PAST** the deadline. Clock-bound, no argument.
- `e-matching: instantiation time budget exhausted` — 18 rows (`UFLIA`: 14),
  median **8,768 ms of 24,000 UNSPENT** (`UFLIA`: 6,346), range −80 to +10,948.
  A family named for a clock whose median row leaves a third of the clock on the
  table. On 14 of the 18 the run is bound by `q:mbqi`, not `q:egraph` — the
  ladder ran out of RUNGS, not out of time, which is the shape
  [uf-quantified-loss-attribution] found on `UF`.

**No larger wall budget reaches those 32 rows**, and a reader who took the
division-level label at face value would have spent a sweep finding that out.

### 2. The instantiation round ceiling is not the blocker here either

    e-matching ROUND CEILING (the round budget)     0 of 129
    e-matching FIXPOINT (no instance left to admit) 1 of 129
    e-matching GROWTH-HEADROOM (a clock exit)       1 of 129

[ADR-1956] measured 0 of 177 on six divisions. It is 0 of 129 on these two.
`AXEYUM_QINST_ROUNDS` buys nothing on `UFNIA` or `UFLIA`.

And **no nested-array refusal appears in either division** — 0 of 129 — so
[ADR-1965]'s 20,399-file array-IR ceiling does not reach here.

## Soundness

Re-ordering a ladder's clock is soundness-relevant in one direction: it changes
WHICH rung answers, and a rung that answers by an unsound instantiation yields a
wrong `unsat`.

- `crates/axeyum-solver/tests/quant_egraph_reserve_row.rs`, registered in
  `hooks/pre-push`. Every fixture runs under **all three arms**. Two are
  adversarial fixtures over **satisfiable** quantified queries whose plausible
  wrong answer is `unsat`, each pinned `Sat` — not merely "not unsat", because
  an `unknown` would skip the in-test model replay and leave the adversarial
  half checking nothing. Each has an `unsat` twin in the same file differing in
  ONE small term (`5` → `-5`; a ground sum `2` → `3`), so the pair cannot be
  passed by a solver stuck on `unknown` or one that answers `unsat` to
  everything. The replay COUNTS the assertions it evaluated and fails at zero.
- `scripts/tests/mutation_controls.py` gains `quant-egraph-reserve`: three
  mutations, **3 killed, 1 test each**, including one that makes the lever's OFF
  position reserve — the silent behaviour change a defaulted-off lever must
  never make.
- **0 `sat`↔`unsat` flips in 1,200 solves** across the three divisions, and all
  six checkable moved rows agree with `:status`, z3 and cvc5.
- [ADR-1957]'s denominator is published: **1 of the 8 re-checked rows has no
  independent check at any budget.** `UFNIA/2019-Preiner/combined/t3_rw1159.smt2`
  declares `:status unknown`, cvc5 returns `unknown` at 24 s and at 600 s, and
  z3 emits no verdict line at either budget. Our `unsat` there is reported as
  **unconfirmed**, not counted in a zero.

One checker failed and is recorded rather than quietly fixed. The first
`confirm-moved.sh` classified inside the measuring script and printed
**CONTRADICTED** — the word a soundness board is scanned for — on two rows where
the arm had simply returned `unknown`. `unknown` is a first-class result and is
never a contradiction. It was visible only because the raw per-run columns sat
in the artifact beside the verdict; had the script printed only its conclusion,
the wrong word would have been the whole record. Measurement and classification
are now separate files, and the finding-dependent exit status lives in
`confirm-summarize.py`.

## Consequences

- No behaviour change ships. The default path is byte-identical and every
  recorded `UFNIA` / `UFLIA` baseline still describes the shipped tree.
- **The next lane on these divisions should not build a scheduling fix.** The
  46-row family is attributed and its ceiling is measured; what is left is the
  32-row family that stops with a third of the clock unspent, whose remedy is a
  rung that does not yet exist, and the 29 UNCLASSIFIED rows.
- `q:egraph`'s 61 % entry rate against its 0.5–4 % decision rate is now a
  measured number rather than a comment. A future change to instance
  **selection** — the capability [uf-quantified-loss-attribution] named for `UF`
  and the one thing the ceiling arm does *not* rule out — has a denominator to
  be measured against.

[ADR-1941]: adr-1941-attempts-alone-cannot-classify-a-census-row-the-open-segment-is-the-discriminator.md
[ADR-1950]: adr-1950-a-round-budget-and-a-clock-budget-are-different-findings-and-a-census-must-not-merge-them.md
[ADR-1956]: adr-1956-do-not-raise-the-instantiation-round-ceiling-zero-of-the-177-rows-reach-it.md
[ADR-1957]: adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-1965]: adr-1965-the-nested-array-prize-was-never-the-array-theory-it-was-congruence.md
[board-six]: ../../../bench-results/six-divisions-headtohead-20260912/README.md
[ladder-budget-discipline-2026-09-08]: ../12-performance/ladder-budget-discipline-2026-09-08.md
[uf-quantified-loss-attribution]: ../12-performance/uf-quantified-loss-attribution-2026-09-09.md
