# Lane: decline-wiring — the fallback was already offered; the bucket was a per-rung test reported as a cause

<!-- plan-section: lane-status -->

**Lane decline-wiring (`DONE`, decline-wiring, 2026-09-14).** [ADR-2020]
handed over two sized defects. **The first does not exist as described**, and
finding that out changed what the second is for. Full reasoning in [ADR-2030];
artifacts in
[`bench-results/decline-wiring-20260914/`](../../../bench-results/decline-wiring-20260914/PREREGISTRATION.md).

## Defect 1 — refuted, on all 13 files

[ADR-2020] concluded that `combined.rs:86` hard-declines where its sibling at
`auto.rs:4068` treats the same constant as a route selector, that **17 of 17**
censused replays are at the site with no fallback, and that *"the lazy fallback
that already exists for the other caller is simply not offered to them"* — 21.8 %
of the population, *"missing wiring rather than a policy question."*

The census cannot show that. It records the CONTEXT NAME of whichever site
refused **last** and nothing about the gates upstream of it. A new ordered probe
(`AXEYUM_ACKPROBE`, off by default, printed and never acted on) can:

| | |
|---|---:|
| files where the selector NEVER engaged | **0 of 13** |
| total selector engagements | **470** |
| ...with the CEGAR's own abstraction re-entry (direct evidence it ran) | 414 |
| total `combined.rs:86` refusals | **5,702** |

Every file shows pair counts at **both** sites; the pair count fingerprints the
term set. And the argument is structural, not statistical: reaching
`combined.rs:86` requires `dispatch_uf_arith_overbound` to have returned
`FallThrough`, and under the shipped `CegarProbe` policy the only route there is
the lazy CEGAR **running** and returning an inconclusive `Unknown`. Its two
earlier exits both return.

**The 17 replays are 13 FILES**, so at row level this bucket is at most
**13 of 127 = 10.2 %**, not 21.8 %.

## What the bucket actually is

The integer bit-blast width ladder consults a **width-independent** admission
test once per rung — 60 to 1,605 identical refusals per file — and the last
one's sentence becomes the query's verdict. `check_with_all_theories` binds
`width` only at reduction 3, after array elimination and the eager Ackermann
bound, so no rung could have answered differently. **Each one paid a full
`arena.clone()` first** — the whole file's term DAG, which is the cost
[ADR-2020] §5 attributed to the ladder as unavoidable.

## Defect 2 — the batch is not "uncapped", it is all-of-it-at-once

Distribution published **before** any cap existed, from the committed census,
31 observations:

| field | min | p25 | med | p75 | p90 | max |
|---|---:|---:|---:|---:|---:|---:|
| `violated_pairs` | 0 | 0 | 8 | 47 | 229 | 3,120 |
| `equal_arg_pairs` = `lemmas_added` | 0 | 0 | 191 | 3,246 | 12,440 | 17,750 |

`lemmas_added == equal_arg_pairs` on **all 31**, and on the 15 that emit
anything `lemmas_added == last_new_lemmas` — the entire equal-argument pair set
goes in during **one** round and the loop never gets another. Amplification from
the pairs actually violated reaches **1,555x** (8 → 12,440).

**And it is the same mechanism as [ADR-2020]'s largest bucket:** 10 of the 16
flooded files are on its 22-file pre-SAT skeleton list. The lemma flood is what
builds the ~15 k-atom skeleton the boundary then refuses. [ADR-2020] raised the
boundary and got 0 of 129; this attacks the size instead, which is the axis its
own §8 names.

The two defects are **disjoint populations** — `files-eager-ackermann` ∩ flooded
is **0 of 13** — so they are measured as separate arms.

## `solve_rounds = 2` is the second solve choking, not convergence

There is **no round cap** in the lazy loop, so `solve_rounds=2` means the second
solve did not finish — and the census carries what it said. All 16 flooded
observations die there, and **10 of 16 die at the pre-SAT skeleton boundary**,
which is [ADR-2020]'s largest bucket. [ADR-2020] raised that boundary 4x and
moved 0 of 129; the flood is the other end of the same chain.

Bound on that: the 15 observations with `lemmas_added == 0` reach the **same**
boundary, 12 of 15. Of its 22-file skeleton bucket, 10 are flooded; the other 12
arrive without a flood and a cap cannot help them.

## The A/B — both ship OFF

Interleaved per file, one binary, two env values, shards fixed across arms
(s5 `{1,3}`, s6 `{1,3}`, both arms inside each shard).

| run | rows | GAIN | LOSS | FLIP | wall |
|---|---:|---:|---:|---:|---:|
| ladder hoist `UFLIA`+`UFNIA` | 129 | **0** | 1 | 0 | 1.001x |
| lemma cap 256 `UFLIA`+`UFNIA` | 129 | **1** | 1 | 0 | 0.956x |
| targeted: the 13 files the hoist fires on | 13 | 0 | 0 | 0 | **0.978x** |
| control `QF_BV`, 52 families, **57 decided** | 97 | **0** | **0** | 0 | 1.006x |
| noise floor (both arms shipped) | 129 | **0** | **0** | 0 | 0.993x |

**Every LOSS in the lane is one row.** `UFNIA/sledgehammer/FFT/z3.885941.smt2`
lost in *both* arms — two independent levers touching different code — and under
3x re-runs its direction **inverted** (OFF 0 of 3, ON 2 of 3 and 1 of 3). It is
also the single row the byte-identical noise floor decides, `unsat` on both arms.
So the same-arm band is not zero, and this lane's own data says so rather than
inheriting [ADR-2020]'s 1.

The cap's one gain is **STABLE-GAIN**: `javafe.ast.StandardPrettyPrint.322`,
0 of 3 versus 3 of 3, reproduced on a second binary, verified `unsat` against
`:status`, z3 and cvc5 at a comparable denominator of **1/1 on each**, zero
disagreements. Real — just not six.

Against R2's pre-registered go/no-go of **>= 6 STABLE-GAIN**, **both levers ship
OFF**, exactly as predicted in writing beforehand. Five guards, four
mutation-verified at exactly one test killed each.

**R2 was the wrong instrument for the hoist**, which is verdict-preserving by
construction, and that is said rather than worked around. What it buys is a
correct give-up string and **0.978x wall on the files it fires on** — two per
cent, not the order of magnitude the clone counts suggest at first reading.

[ADR-2020]: ../../research/09-decisions/adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
[ADR-2030]: ../../research/09-decisions/adr-2030-the-fallback-was-already-offered-and-the-lemma-batch-is-the-whole-set-at-once.md

<!-- plan-section: landed-changes -->

| 2026-09-14 | decline-wiring | [ADR-2020] handed over two sized defects. **The first does not exist as described**: it read a census that records the context name of whichever site refused LAST and concluded the lazy fallback "is simply not offered" to the queries `combined.rs:86` declines. An ordered probe (`AXEYUM_ACKPROBE`, off by default, printed and never acted on) says the selector at `auto.rs:4068` engages on **13 of 13** files, **470** times, **414** of them immediately followed by the CEGAR's own abstraction re-entry -- and inside the held-set replay probe where the 17 censused replays actually live, **23 of 23** `combined theories:` replays are preceded by an engaged selector. The argument is structural: reaching `combined.rs:86` requires `FallThrough`, and under the shipped `CegarProbe` policy the only route there is the lazy CEGAR RUNNING and returning inconclusive. **The size is also wrong** -- 17 replays are **13 FILES**, so at ROW level the bucket is **10.2 % `[6.1 %, 16.7 %]`**, not 21.8 %. What it IS: the integer bit-blast width ladder consulting a **width-independent** admission test once per rung (15 rungs; 60-1,605 refusals per file = 4-107 invocations) and reporting the last rung's refusal as the query's verdict, **with 14 of every 15 `arena.clone()`s discarded** -- a cost [ADR-2020] read as intrinsic to the ladder. Defect 2, measured BEFORE building: `lemmas_added == equal_arg_pairs` on **all 31** census observations (the batch is the ENTIRE equal-argument set the moment one pair is violated; amplification to **1,555x**), and `solve_rounds<=3` is not convergence -- there is no round cap, so it is the SECOND solve choking, and **10 of the 16 flooded observations die at the pre-SAT skeleton boundary that is [ADR-2020]'s LARGEST bucket**. The flood and that bucket are one mechanism and [ADR-2020] built its lever at the wrong end of it (0 of 129); bound on the claim, 12 of the 15 unflooded observations reach the same boundary, so a cap cannot help 12 of its 22 files. Two levers, both failing closed, parse split out of the `OnceLock` so the guard is testable at all; five guards, **four mutation-verified at exactly one test killed each**. A/B interleaved per file, one binary, shards fixed: **ladder 0 of 129 `[0.0 %, 2.9 %]`, cap 1 of 129 `[0.1 %, 4.3 %]`, ZERO FLIPs**; control `QF_BV` 97 rows over 52 families with **57 decided on both arms** (non-vacuous by construction -- [ADR-2020]'s 6-row all-unknown control was structurally blind to a LOSS) moves **0**; noise floor **0 of 129** -- **but the one row it decides is the same volatile row that produced EVERY loss in both arms and then INVERTED under 3x re-runs**, so the band is not zero and this lane's own data says so. The cap's single gain is STABLE-GAIN (0/3 vs 3/3, reproduced on a second binary) and verified `unsat` against `:status`, z3 and cvc5, comparable denominator **1/1 each**, 0 disagreements. Against a pre-registered go/no-go of **>= 6**, **BOTH SHIP OFF**, as predicted in writing beforehand. R2 was the wrong instrument for a verdict-preserving lever and that is said rather than worked around: the hoist is worth a correct give-up string and **0.978x wall on the 13 files it fires on**. Also found: [ADR-2020]'s A/B table reports its secondary `QF_LIA` run at 27 rows and its committed artifact has **12**; and `oversized_admission_probe`'s decider is pure-LIA, which LOOKS like a fragment mismatch for a UF+arith population and is not -- `abstract_functions` has already removed every application by then, so the gap is a missing call, not a missing capability. | ADR-2030 |
