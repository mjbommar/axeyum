# Why the e-matching loop produces nothing on 86.9% of its rounds

**Date:** 2026-09-10
**Lane:** coordinator-solver
**Population:** `bench-results/parity-losses-20260908/UF.txt` — the 32 declared-status
UF files we return `unknown` on and z3 refutes.
**Method:** `AXEYUM_QPROBE=1 target/release/examples/axeyum_cli <file> --timeout-ms 24000`,
four at a time on an otherwise quiet box, 19,975 per-universal probe rows.
**Reproduce:** the probe rows are `universal[i] vars=… patterns=… joined=… starved_joins=… admitted=…`
emitted from `qinst_egraph.rs`; classify them with the buckets in the first table.

## The headline

**17,300 of 19,975 universal-rounds (86.6%) admit zero instances**, and the
reason is not one thing. It is four, and only one of them is a capacity problem:

| | rows | share | cause |
|---|---:|---:|---|
| A | 919 | 4.6% | universal has **no trigger pattern at all** (`patterns=0`) — it can never instantiate |
| B | 8,219 | 41.1% | pattern present, **matched nothing** in the e-graph |
| C | 5,101 | 25.5% | joins found, **every one starved** by the shared per-round ceiling |
| D | 3,110 | 15.6% | joins found, **admission filter dropped all of them** |
| E | 2,626 | 13.1% | produced instances |

C and D together are **41.1% of all rounds in which the machinery found
candidate instances and discarded every one.** Those are our own caps and
filters. Category A is a trigger-selection gap that no budget can fix.

## The scale we are working at

| file | max universal index | fixpoint rounds | final ground |
|---|---:|---:|---|
| f01 | 501 | 3 | **8192** (the cap) |
| f05 | 483 | 1 | **8192** |
| f12 | 711 | 2 | **8192** |
| f20 | 676 | 2 | **8192** |
| f31 | 3 | 1 | 2546 |

Files carry **483–711 universals**, the loop completes **1–3 fixpoint rounds**,
and the ground set pins at `MAX_GROUND_TERMS = 8192`. z3 refutes the same files
with **2–10 instantiations in ≤ 0.21 s**.

We are not short of instances by three orders of magnitude. We are over-producing
by three orders of magnitude and never selecting the right one. This is why every
capacity lever measured in Phase 3 came back DO NOT BUILD — 3.1 (local search),
3.2 (inprocessing passes), 3.3 (rewrite depth), 3.5 (cvc5's six instantiation
strategies), 3.7 (interpolation strength) and 3.4 (the LIA node cap) are all
answers to "are we missing capability?", and the answer is no.

## Refuted here: the position gradient is not the cause

Starvation is a clean monotone function of a universal's **position** in the list:

| index | rounds | starved | produced |
|---|---:|---:|---:|
| 0–7 | 450 | **0.0%** | 32.9% |
| 8–15 | 440 | 5.7% | 29.5% |
| 16–31 | 809 | 10.3% | 26.0% |
| 32–63 | 1,490 | 13.2% | 25.2% |
| **64+** | **16,786** | **50.1%** | **10.8%** |

`match_witness_tuples` issues one `ground_budget().join_ceiling` per round and
consumes it walking `0..n`, so the same low-index universals claim it every
round. That reads like an obvious fairness bug — **and fixing it changes nothing.**

Rotating the walk's start by the round counter (same total work, same ceiling,
deterministic) was implemented and measured on the same 32 files:

| index | starved before | starved after | produced before | produced after |
|---|---:|---:|---:|---:|
| 0–7 | 0.0% | **58.1%** | 32.9% | 29.9% |
| 32–63 | 13.2% | 13.3% | 25.2% | 24.9% |
| **64+** | **50.1%** | **50.9%** | **10.8%** | **10.9%** |
| all | 43.6% | 46.9% | **13.4%** | **13.3%** |

It spread starvation evenly instead of relieving it: low-index universals got
much worse, the 64+ tail — 84% of all rounds — did not move, and the aggregate
produce rate fell slightly. Verdicts were unchanged at 0 of 32.

**Conclusion: the gradient is correlation, not cause.** The tail does not starve
because someone drank the budget first; it starves because one per-round ceiling
cannot serve 500–700 universals no matter who goes first. The change was
reverted — `qinst_egraph.rs` warns in its own comments that this loop's admission
schedule is perturbation-sensitive (a per-pattern match split once cost a scored
refutation), so a measured-neutral change here is a bad trade.

**Do not re-derive this.** Rotation, and per-universal fair shares of the same
ceiling, are the same lever.

## Also checked and cleared

`FLOOD_FINAL_SUBSET_MAX_GENERATION = 1` caps the final refutation check at
generation ≤ 1 once ground ≥ 2048, and the required instance is at generation ≥ 2
on 10 of the 14 selection-blocked files — which looks exactly like a checker that
cannot see the answer. It is not: `finish_quantified_ground_check` runs the
shallow subset first under a quarter of the budget and then **falls through to a
full-set check** (`qinst_egraph.rs:3500`). It is a 25% tax on those files, not a
wall.

## What did move a verdict

`prove_unsat_by_ematching` gated the e-graph loop on `retried.residual_quantifier`
— a claim about the query's SHAPE standing in for "the cheap route failed". Of 62
entries into that function across the slice, 58 report `residual=true`, and 4
report `residual=false` and reach the decline having logged no `skolemized-egraph`
line at all: the loop was never called at any budget.

`Hoare/smtlib.1116374` is one of the 4. Running the loop after
`decide_instantiation` fails flips it to **unsat in 96 ms against a 748 ms
slice** — it was never short of time. The slice goes **0 → 1 of 32 decided**.
Fixed in `318930806`, pinned by `tests/quant_skolem_egraph_routing.rs` (an
asserted verdict: `corpus/regression/` skips `unknown` and would have stayed
green through a regression).

## What to do next, in order

1. **Category A first — 919 rounds on universals with no trigger at all.** No
   budget, cap or schedule reaches these. Find why trigger selection returns
   nothing for them, and whether a body-derived fallback trigger applies.
2. **Category B — does the required term ever enter the e-graph?** 41.1% of
   rounds match nothing. On 10 of 14 selection-blocked files the required
   instance sits at generation ≥ 2 behind a Skolem-function term, so the trigger
   that would build it cannot fire in round 1. The decisive experiment is a
   structural dump of our ground set against z3's `(_ quant-inst …)` terms for
   the same file — it splits "we never build it" from "we build it and rank it
   1000th", and those need different fixes.
3. **Category D — the admission filter.** 3,110 rounds where joins existed and
   nothing was admitted. Unlike C, this is a decision we make per candidate,
   which means it can be made better rather than merely bigger.

   **Done — see
   [`what-the-admission-filter-rejects-2026-09-10.md`](what-the-admission-filter-rejects-2026-09-10.md).**
   It is four causes, not one. A quarter of D is bookkeeping (the same instance
   admitted under another universal's name), the entailment filter is 94.5%
   provably free, and the real cause is a per-round PRIORITY: the deferred pool
   is gated on urgent traffic running dry, which on the large files here happens
   once in the whole run. Releasing it alongside urgent traffic takes the slice
   from 1 of 32 to **3 of 32** with no measured loss.

   That document also **refutes the A–E split in the table above.** It was
   measured before `318930806`, the fix this same document announces; on the
   current tree the shares are A 4.5% / B 69.0% / C 8.3% / D 4.0% / E 14.2%.
   The 86.6% headline survives (85.8% now); the four-way split does not.
4. **Not category C by raising the ceiling.** Flooding harder is the lever
   Phase 3 already measured at zero from two directions (3.5's 8x ground-ceiling
   arm, and the 120 s budget arm where 24 of 32 files return `unknown` *before*
   spending the budget).
