# ADR-2030: the fallback was already offered — the 21.8 % bucket is a per-rung admission test reported as a cause

Status: accepted
Index-summary: [ADR-2020] handed over two sized defects. **The first does not exist as described.** It concluded that `combined.rs:86` hard-declines where `auto.rs:4068` treats the same constant as a route selector, that 17 of 17 replays sit at the site with no fallback, and that "the lazy fallback ... is simply not offered to them" -- 21.8 % of the population, "missing wiring rather than a policy question". A census cannot show that: a give-up string carries the context name of whichever site refused LAST and nothing about the gates upstream of it. An ordered probe (`AXEYUM_ACKPROBE`, off by default, printed and never acted on) can. The selector engages on **13 of 13** files, 470 times, 414 of them immediately followed by the CEGAR's own abstraction re-entry; and inside the held-set replay probe where the 17 actually live, **23 of 23** `combined theories:` replays are preceded by an engaged selector. The argument is structural, not statistical: reaching `combined.rs:86` requires `FallThrough`, and under the shipped `CegarProbe` policy the only route there is the lazy CEGAR RUNNING and returning inconclusive. **The size is also smaller than published** -- 17 replays are **13 FILES**, so at ROW level the bucket is 10.2 % `[6.1 %, 16.7 %]`, not 21.8 %. What the bucket IS: the integer bit-blast width ladder consulting a WIDTH-INDEPENDENT admission test once per rung (15 rungs; 60-1,605 refusals per file = 4-107 invocations) and reporting the last rung's refusal as the query's verdict, **with 14 of every 15 `arena.clone()`s discarded** -- a cost [ADR-2020] read as intrinsic. Defect 2 measured before building: `lemmas_added == equal_arg_pairs` on **all 31** census observations (the batch is the ENTIRE equal-arg set the moment one pair is violated; amplification to **1,555x**), and `solve_rounds<=3` is not convergence -- there is no round cap, so it is the SECOND solve choking, and **10 of the 16 flooded observations die at the pre-SAT skeleton boundary that is [ADR-2020]'s largest bucket**: the flood and that bucket are one mechanism, and [ADR-2020] built its lever at the wrong end of it (0 of 129). Two levers, both failing closed, parse split from the `OnceLock` so the guard is testable; five guards, **four mutation-verified at exactly one test killed each**. A/B interleaved, one binary, shards fixed: **ladder 0 of 129 `[0.0 %, 2.9 %]`, cap 1 of 129 `[0.1 %, 4.3 %]`, zero FLIPs**; control `QF_BV` 97 rows / 52 families with **57 decided on both arms** (non-vacuous by construction, where [ADR-2020]'s 6-row control was blind to a LOSS by design) moves 0; noise floor 0 of 129 -- **but the one row it decides is the same volatile row that produced EVERY loss in both arms and then inverted under 3x re-runs**, so the band is not zero. The cap's one gain is STABLE-GAIN (0/3 vs 3/3, reproduced on a second binary) and verified `unsat` against `:status`, z3 and cvc5 at a comparable denominator of 1/1 each. Against a pre-registered go/no-go of >= 6, **both ship OFF**, as predicted in writing beforehand. R2 was the wrong instrument for a verdict-preserving lever and that is said rather than worked around; the hoist is worth a correct give-up string and **0.978x wall on the 13 files it fires on** -- two per cent, not the order of magnitude the clone counts suggest.
Index-status: accepted
Date: 2026-09-14

## Context

[ADR-2020] handed over two sized defects "neither of which is a policy
question". This lane took them in the order it was asked to.

Branch base: `git merge-base main HEAD` is
`37ff18b568f414dc21e151c3a53292c40fb7fa71`, which **was** local `main`'s HEAD
when this lane branched.

Rules were [pre-registered](../../../bench-results/decline-wiring-20260914/PREREGISTRATION.md)
in their own commit (`d7360d8fe`) before either A/B ran, together with both
levers and the batch distribution the cap's value was chosen from.

## 1. Defect 1 does not exist as described

[ADR-2020] §8.3 reads:

> `combined.rs:86` **hard-declines** on the eager Ackermann bound with no
> fallback, while `auto.rs:4068` treats the same bound as a route selector and
> runs the lazy/CEGAR route instead. **17 of 17** censused replays are at the
> hard-decline site. Giving it the fallback its sibling already has is 21.8 % of
> the population.

**The census it read cannot support that claim.** A give-up string carries the
`context` name of whichever site refused **last** and nothing whatever about the
gates upstream of it. Both readings — "this query never reached the selector"
and "this query reached the selector, was offered the lazy route, and came out
the other side" — produce the identical string.

A new ordered probe separates them. `AXEYUM_ACKPROBE=1` (off by default,
printed and never acted on, the same discipline as the held-set replay probe)
emits one line per consultation of the bound at either site, with the pair
count, the verdict and the site's own gate state. Over all **13 files** behind
those 17 replays, 24 s budget, pinned core:

| | |
|---|---:|
| files where the selector at `auto.rs:4068` NEVER engaged | **0 of 13** |
| total selector engagements | **470** |
| ...immediately followed by the CEGAR's own abstraction re-entry | 414 |
| total `combined.rs:86` refusals | **5,702** |

Per file the selector engages 5 to 145 times, and every file shows pair counts
appearing at **both** sites — the pair count is a fingerprint of the term set,
so a shared value is the same set reaching the selector first and the hard
decline afterwards.

**The argument is structural, not statistical**, and is short enough to check
against `dispatch_uf_arith_overbound` directly. Reaching `combined.rs:86`
requires that function to have returned `FallThrough`. Under the **shipped**
policy (`CegarProbe`; `terminal` and `skip` are opt-in through
`AXEYUM_UF_ARITH_OVERBOUND`) the only route to `FallThrough` is the lazy CEGAR
**running** and returning an inconclusive `Unknown` — its two earlier exits,
`NotEngaged` and `Answer(refusal)` from the pathological bound, both return. So
on these files the lazy route was not merely offered. It ran, and it declined,
before the query ever reached the site [ADR-2020] wanted to give it to.

### And the same measurement inside the replay probe, where the 17 live

The sweep above measures the **shipped 24 s path**. [ADR-2020]'s 17 censused
replays live in the **held-set replay probe**, which re-runs a discarded ground
set on its own fresh budget. It enters the very same `check_auto` — but "the same
dispatcher" is an argument, and this lane's whole point is that an argument about
which site a query reached is what needs measuring.

So both instruments were turned on at once (`AXEYUM_QPROBE_HELD_SET_REPLAY=10000`
plus `AXEYUM_ACKPROBE=1`) and the question asked per replay: when a replay's
`why=` is the `combined theories:` refusal, was the selector at `auto.rs:4068`
engaged **earlier in that same replay**?

| | |
|---|---:|
| files | 13 |
| held-set replays | 31 |
| ...whose `why=` is the `combined theories:` refusal | **23** |
| ...of those, preceded by an engaged selector | **23 of 23** |

Not one exception, in the exact population [ADR-2020] read.

**And the size is smaller than published.** The 17 replays come from **13
distinct files**. 21.8 % is a replay-level share of a replay-level denominator;
at ROW level this bucket is at most **13 of 127 = 10.2 %, Wilson 95 %
`[6.1 %, 16.7 %]`**. [ADR-2020] made exactly this replay-vs-row correction for
[ADR-2015] in its own §1 and then quoted a replay share in its recommendation.

## 2. What the bucket actually is

The integer bit-blast width ladder calls `check_with_all_theories` once per
width rung. That function binds `width` only at **reduction 3** — after array
elimination (reduction 1) and the eager Ackermann admission bound (reduction 2),
both of which are width-independent. So on an over-bound set every rung refuses,
identically, and the **last** one's sentence becomes the query's verdict.

The ladder has **15 rungs** (`4..=16`, then 24 and 32), so one invocation on an
over-bound set produces 15 identical refusals. Measured per file over the whole
24 s solve: **60 to 1,605** such refusals — that is **4 to 107 ladder
invocations**, each spending 15 rungs to re-derive one width-independent answer.

And the loop does `let mut scratch = arena.clone();` *before* each rung — a copy
of the whole file's term DAG, 14,235 nodes for a held set of 11 by [ADR-2020]'s
own §5 profile. [ADR-2020] read that clone cost as intrinsic to the ladder
("the width ladder clones the arena per rung by design"). On this population it
is not: **14 of every 15 clones** are discarded by a refusal that could not have
depended on the width they were cloned for.

So the `combined theories:` bucket is not a *cause*. It is a per-rung admission
test being reported as the query's verdict — the same class of defect
[ADR-1927], [ADR-1966] and [ADR-1980] name, but pointing the other way. Those
three are about a rung refusing a construct a later rung owns. This is a rung's
own internal admission test overwriting what the ladder actually ended on, which
is why a census keyed on that string ranked it as a remedy.

## 3. Defect 2: the batch is not "uncapped", it is all of it at once

[ADR-2020] recorded that `violated_pairs=448` adds `lemmas_added=17,750` and
that no per-round cap exists. Re-reading the committed census for the whole
distribution **before building anything** (31 observations, published in full in
[`cegar-batch-distribution.md`](../../../bench-results/decline-wiring-20260914/cegar-batch-distribution.md)):

| field | min | p25 | med | p75 | p90 | max |
|---|---:|---:|---:|---:|---:|---:|
| `violated_pairs` | 0 | 0 | **8** | 47 | **229** | 3,120 |
| `equal_arg_pairs` | 0 | 0 | 191 | 3,246 | 12,440 | 17,750 |
| `lemmas_added` | 0 | 0 | 191 | 3,246 | 12,440 | **17,750** |
| `solve_rounds` | 1 | 1 | 2 | 2 | 2 | **3** |

Three things are visible that the single quoted pair is not:

1. **`lemmas_added == equal_arg_pairs` on all 31.** The batch is not
   occasionally large — it is *the entire equal-argument pair set*, emitted the
   moment any single pair is violated.
2. **On the 15 that emit anything, `lemmas_added == last_new_lemmas`.** The whole
   batch goes in during **one** round and the loop never gets another. This is a
   CEGAR that refines once.
3. **The amplification reaches 1,555x** — 8 violated pairs producing 12,440
   lemmas on `javafe.ast.StandardPrettyPrint.322.smt2`.

### `solve_rounds = 2` is not convergence, it is the second solve choking

There is **no round cap** in `check_with_function_consistency`. The loop runs
until the candidate model is functionally consistent, or until the inner `solve`
returns `Unsat` (done) or `Unknown` (give up). So `solve_rounds=2` does not mean
the CEGAR converged in two rounds — it means **the second solve did not
finish**, and the census carries what that solve said.

Reading it: **all 16 flooded observations die at `solve_rounds=2`**, and the
inner reason is:

| n of 16 | the inner solve's own words |
|---:|---|
| **10** | `lazy linear arithmetic pre-SAT skeleton exceeds the joint resource boundary` |
| 3 | `lazy linear arithmetic exhausted the configured timeout after N rounds` |
| 1 each | LIA sat-model reconstruction declined / NIA real-relaxation timeout / SAT skeleton declined after round N |

**The leader there is [ADR-2020]'s largest binding cause** (22 of 78, 28.2 %).
So the two are one mechanism end to end:

    round 1 finds 8 violated pairs
      -> the batch emits ALL 12,440 equal-argument pairs
        -> round 2's skeleton is ~15 k atoms / ~24 k CNF vars
          -> the pre-SAT skeleton boundary refuses it
            -> CEGAR inconclusive -> fall through -> unknown

[ADR-2020] built its lever at the **fourth** step, raised the boundary 4x, moved
**0 of 129**, and concluded — correctly — that the skeleton is undecidable
inside the budget at that size and that *"the target is the SIZE of the set, not
the bound that refuses it."* The cap is a lever on the **second** step.
Correspondingly, 10 of the 16 flooded files are on [ADR-2020]'s 22-file skeleton
list.

**The honest bound on that claim, stated because it limits the ceiling:** the 15
observations with `lemmas_added == 0` reach the **same** boundary, 12 of 15 of
them. The flood is not the only route there. Of the 22-file skeleton bucket, 10
are flooded; the other 12 arrive without a lemma flood and **a batch cap cannot
help them at all**.

**The two defects are disjoint populations.** `files-eager-ackermann` ∩ flooded
is **0 of 13**, so they are measured as separate arms and a joint arm would have
confounded them.

## 4. The levers

Both off by default, both failing **closed** (unset, empty, malformed, or zero
returns the shipped constant), both resolved once through a `OnceLock` with the
**parse split out** so the fail-closed guard is a pure unit test — a
`OnceLock`-backed reader resolves once per process, so a test that sets the
variable after any other test has read it measures the wrong arm and still
passes.

| lever | OFF (shipped) | ON |
|---|---|---|
| `AXEYUM_BLAST_LADDER_ADMISSION` | unset | `1` — evaluate the width-independent admission test ONCE for the ladder |
| `AXEYUM_FC_LEMMA_BATCH_CAP` | unset | `256` — per-round ceiling on the lemma batch, violated pairs first |

**Both arms visible BY MECHANISM, asserted before measuring:**

* hoist — `ACKPROBE site=combined.rs:86` count on
  `UFLIA/sledgehammer/QEpres/smtlib.1120322.smt2`: **736 OFF, 91 ON**.
* cap — `FunctionConsistencyStats::summary` prints `lemma_batch_cap=<n|off>`,
  the **effective** value, so an ignored or mistyped variable prints `off`,
  which is the shipped value.

**Why 256, by a rule fixed before the value.** The cap must (a) admit the full
violated set on at least 90 % of observed rounds — `violated_pairs` p90 is
**229**, so `cap >= 229` — and (b) still bind on the flooded tail. 256 is the
smallest round value satisfying both, and is the value of the only existing
constant of its kind in the same file
(`MAX_PRESEEDED_FUNCTION_CONSISTENCY_LEMMAS`). It binds on 15 of 31.

**Soundness of the cap.** A congruence lemma is a valid implication of the input
under every interpretation, so emitting fewer per round can never make a
refutation unsound — only slower. Pairs not emitted are **not** marked `added`,
so they remain available to the next round, and termination is unaffected.

**Soundness of the hoist.** Width-independence is structural (see §2), and the
probe runs on a clone so nothing it declares reaches the caller's arena. The one
behavioural difference is *which* `Unknown` a caller sees: a later rung could
previously time out inside reduction 1 and report `combined-theory timeout after
array elimination` instead. Both are `Unknown`.

**Carrying the message out.** [ADR-1980]'s named prerequisite. The hoisted
`Unknown` names THIS rung as the one that gave up, says how many rungs were
skipped and why they could not have differed, and appends the refusing bound's
sentence **verbatim** — checked in test against the sentence the bound itself
emits, not against a literal copy of it.

**Five guards, four mutation-verified at exactly one test killed each:**

| deleted guard | tests killed |
|---|---|
| the cap rejects zero | **1** |
| violated pairs queued before merely equal-argument ones | **1** |
| the hoist is off for every spelling but an exact `1` | **1** |
| the refusing rung's own sentence is carried out | **1** |

The fifth, `the_ladder_hoist_premise_no_width_dependence`, pins the hoist's
structural premise over the REAL ladder width set: if a future change makes
`check_with_all_theories` consult `width` before the admission bound, the hoist
stops being verdict-preserving and that assertion is what breaks.

One trap caught while registering the mutations: the ladder suite first named
its two tests as a **space-separated** filter. `cargo test --lib 'a b'` runs
zero tests and exits 0, so that registration would have measured nothing and
reported both mutations as unmeasured. The three tests now share one prefix and
the baseline reports 3 tests.

## 5. The A/B

Interleaved per file, **one binary** (sha256 `e7e3538c…`, recorded in every
runner log), two env values, arms back to back on the same pinned core with the
order rotating per file. **Shard configuration fixed across arms and stated**:
s5 cores `{1,3}` for the ladder hoist, s6 cores `{1,3}` for the cap, **both arms
inside each shard** so a shard can never move one arm relative to the other.
24 s budget, `ulimit -v` 8 GiB. Controls and the noise floor ran afterwards on
the same cores, never concurrently with the main arms.

| run | rows | OFF dec | ON dec | GAIN | LOSS | FLIP | wall |
|---|---:|---:|---:|---:|---:|---:|---:|
| **ladder hoist** `UFLIA`+`UFNIA` | 129 | 1 | 0 | **0** | 1 | 0 | 1.001x |
| **lemma cap 256** `UFLIA`+`UFNIA` | 129 | 1 | 1 | **1** | 1 | 0 | 0.956x |
| targeted: the 13 files the hoist fires on | 13 | 0 | 0 | 0 | 0 | 0 | **0.978x** |
| **control** `QF_BV` (must not move) | 97 | **57** | **57** | **0** | **0** | 0 | 1.006x |
| **noise floor** (both arms shipped) | 129 | 1 | 1 | **0** | **0** | 0 | 0.993x |

Ladder GAIN 0 of 129, **Wilson 95 % `[0.0 %, 2.9 %]`**. Cap GAIN 1 of 129,
`[0.1 %, 4.3 %]`. **Zero FLIPs anywhere** — no `sat`/`unsat` disagreement, which
is the only one of the three classes that would be a soundness finding.

### The row that "lost" in BOTH arms

`UFNIA/sledgehammer/FFT/z3.885941.smt2` shows a LOSS under **both** levers —
`unsat(2,310 ms) -> unknown` under the hoist and `unsat(5,415 ms) -> unknown`
under the cap. Two independent levers, touching different code, losing the same
row is the signature of noise, not of either lever; and the shipped arm itself
reports two different times for it in the two runs. s5/s6 load went from **0.00
at launch to 3.6** during the sweep as another lane arrived.

R3 settles it — 3x per arm, interleaved on one core, on the **HEAD** binary:

| row | arm | OFF x3 | ON x3 | class |
|---|---|---|---|---|
| `FFT/z3.885941` | ladder | unknown, unknown, unknown | unknown, **unsat**, **unsat** | **UNSTABLE** |
| `FFT/z3.885941` | cap | unknown, unknown, unknown | unknown, unknown, **unsat** | **UNSTABLE** |
| `javafe.ast.StandardPrettyPrint.322` | cap | unknown, unknown, unknown | **unsat, unsat, unsat** | **STABLE-GAIN** |

On re-run the OFF arm decides `FFT/z3.885941` **0 of 3** in both experiments, so
the direction has **inverted** — the ON arm now decides it more often than OFF.
That is an unstable row by the pre-registered definition and it counts toward
neither arm.

**Net: ladder 0 STABLE-GAIN / 0 STABLE-LOSS / 1 UNSTABLE. Cap 1 STABLE-GAIN /
0 STABLE-LOSS / 1 UNSTABLE.**

### One row accounts for every LOSS in the lane, and the noise floor names it

The same-arm noise floor moves **0 of 129**, `[0.0 %, 2.9 %]` — tighter than
[ADR-2020]'s, which moved 1 on the same population. But **the one row the noise
floor decides at all is `UFNIA/sledgehammer/FFT/z3.885941.smt2`**, and it decides
it `unsat` on **both** of its byte-identical arms.

That is the same row that "lost" in both main arms and then inverted under 3x
re-runs. Collected, this lane observed it as:

| where | OFF | ON |
|---|---|---|
| ladder main | `unsat` (2,310 ms) | `unknown` |
| cap main | `unsat` (5,415 ms) | `unknown` |
| noise floor (both arms shipped) | `unsat` | `unsat` |
| ladder 3x | `unknown`, `unknown`, `unknown` | `unknown`, `unsat`, `unsat` |
| cap 3x | `unknown`, `unknown`, `unknown` | `unknown`, `unknown`, `unsat` |

It lands on either side of the 24 s budget essentially at random, and **every
LOSS this lane recorded is this one row.** So: a single same-arm pass measuring
zero does not make the band zero — this lane's own data shows the band is at
least one row, evidenced from inside the experiment rather than inherited from
[ADR-2020].

This is also what makes the cap's single gain worth distinguishing from it.
`javafe.ast.StandardPrettyPrint.322` is **0 of 3 versus 3 of 3**, reproduced on
a second binary, and verified `unsat` against three authorities. The 3x rule is
precisely the instrument that separates that from a row like `FFT/z3.885941`,
and it did. The gain is real; it is simply not six.

### The control is non-vacuous by construction, not by argument

[ADR-2020]'s `QF_BV` control was **6 rows, all `unknown` on both arms**. A
control where nothing is decided can only detect a spurious GAIN; it is
structurally blind to a LOSS, which is the direction that matters for a lever
that removes work. It argued non-vacuity by ROUTE instead.

This one is **97 files across 52 `QF_BV` families**, sampled deterministically
two per family (`sample-control-qfbv.py`, seeded) rather than taken as a prefix
of a directory walk. **57 of the 97 are decided on both arms**, so a LOSS would
have been visible. Nothing moved in either direction, and no verdict flipped.

### What the hoist is actually worth

On the 129-row population the hoist's wall ratio is **1.001x** — nothing, because
the affected files are 13 of 129. On the 13 files where it fires it is
**0.978x**: a 2.2 % saving. So the discarded arena clones are real (14 of every
15) but they are **not where the budget goes**; [ADR-2020]'s `perf` profile
attributed ~22.5 % to the allocator across the whole solve, and this says the
ladder's own discarded clones are a small part of that. **Reported because it
bounds a plausible follow-up**: removing this work is worth about two per cent,
not the order of magnitude the clone counts suggest at first reading.

## 6. Decision

**Both levers ship OFF.** R2's threshold was >= 6 STABLE-GAIN; the ladder hoist
is **0** and the cap is **1**. Both stay committed and off by default, as
[ADR-2020]'s knob did, because the next lane on this gap will want the same A/B
against a different value and should not rebuild the harness.

Three things this ADR asserts that are **not** contingent on that A/B, because
they are observations rather than lever outcomes:

1. **[ADR-2020]'s defect 1 does not exist as described.** 0 of 13 files fail to
   reach the selector; 23 of 23 `combined theories:` replays are preceded by an
   engaged selector in the same replay. The recommended fix — "give
   `combined.rs:86` the fallback its sibling already has" — would wire a second
   copy of a route the query has already taken and lost.
2. **The bucket is a per-rung admission test, not a cause**, and at ROW level it
   is 10.2 % `[6.1 %, 16.7 %]`, not 21.8 %. A census keyed on the old string
   ranks a non-remedy second. The carried message fixes that, and the fix is
   demonstrated through the shipped give-up string, not only in a unit test.
3. **The lemma batch and [ADR-2020]'s largest bucket are one mechanism.** All 16
   flooded observations die at `solve_rounds=2`, and 10 of 16 die at the pre-SAT
   skeleton boundary that [ADR-2020] raised 4x for 0 of 129.

**What the cap's single STABLE-GAIN is worth, said plainly.** One row is the
size of the noise floor, and this lane's own same-arm floor is reported above.
It is a STABLE-GAIN by the pre-registered test (0/3 vs 3/3, reproduced on the
HEAD binary) and it is verified `unsat` against three independent authorities —
but one row against a go/no-go of six is a null, and it is recorded as one. The
mechanism it demonstrates (round 2's skeleton becoming solvable when round 1
stops flooding it) is the interesting part, not the count.

**What this ADR does not claim.** That 256 is the right cap. It is the value a
pre-registered rule picked from the distribution, and it is the only value
tested. Any other value needs its own pre-registration — value-shopping after
seeing this result is exactly the failure the rules exist to prevent.

**R2 was the wrong instrument for the hoist, and that is said rather than
worked around.** The hoist is verdict-preserving by construction, so holding it
to a verdict threshold guarantees it fails. What it actually buys is a correct
give-up string and ~2 % wall on the files it touches. Deciding that on its
merits needs a rule about message correctness and wasted work that this lane did
**not** pre-register, so the pre-registered rule stands and the lever stays off.
The evidence for the message defect
([`carried-message.md`](../../../bench-results/decline-wiring-20260914/carried-message.md))
is independent of the A/B and does not expire with it.

## 7. The rules that were pre-registered, against what happened

| rule | pre-registered | outcome |
|---|---|---|
| R1 | report the two levers separately; populations are disjoint | done — `files-eager-ackermann` ∩ flooded = **0 of 13**, two arms |
| R2 | ship only at >= 6 net, every moved row STABLE-GAIN | ladder **0**, cap **1** → **both ship OFF** |
| R3 | re-run every moved row 3x per arm and classify | done, on the HEAD binary. 1 STABLE-GAIN, 0 STABLE-LOSS, **1 UNSTABLE whose direction inverted** |
| R4 | publish a noise floor, whole division, same arm | **0 of 129** at byte-identical config — but the ONE row it decides is the same volatile row that produced every LOSS in both arms, so the band is **not** zero |
| R5 | control division that must not move, shown non-vacuous | `QF_BV` 97 rows / 52 families, **57 decided on both arms**, 0 moved. Non-vacuous by construction, not by a route argument |
| R6 | interleaved, one binary, two env values, polarity stated | done; polarity in the runner header, binary sha256 in every runner log |
| R7 | shard config fixed across arms and stated | s5 `{1,3}` / s6 `{1,3}`, both arms inside each shard |
| R8 | new verdicts vs three authorities, denominators printed | 1 new verdict: `:status` **unsat**, z3 **unsat**, cvc5 **unsat**. Comparable denominator **1/1 on each**; no authority abstained; **0 disagreements**, and the checker's exit status depends on that |
| R9 | Wilson for every small-n proportion | every ratio here |
| R10 | the A/B measures THIS BRANCH | see below |
| R11 | unfinished checks reported as "did not run" | see §8 — `oversized_admission_probe` |
| R12 | freshness licensed by a rebuild that RECOMPILED | **it fired**: the first build reported `Finished in 0.04s` over an edit it never compiled; sources were touched and the rebuild took 33 s |
| R13 | carry the refusing rung's message out | done, and shown through the shipped give-up string |

**The pre-registered predictions, against what happened.** The ladder hoist was
predicted to move **0 rows** because it is verdict-preserving by construction —
it moved 0, with one unstable row that the re-run inverted. The cap was
predicted to come in **under 6** and ship OFF, because six lanes before this one
on this gap shipped OFF or nothing and all six were right to — it came in at
**1**. Both predictions were right, and both were written down before the
measurement.

**R10 — post-merge prediction.** The A/B arm measures this branch: `main` at
`37ff18b56` plus this lane's two levers, both read only through `OnceLock`s that
return the shipped constants when unset. **Predicted post-merge value:
unchanged** — 0 and 1 respectively, and the shipped division totals identical to
`main`. The reason is that no shipped call site reads a different value than it
did before: `dispatch_int_blast_width_ladder` gets `None` from the hoist and runs
its loop as it always did, and `select_function_consistency_batch` gets
`cap = None` and emits the same batch in the same order. The one thing that is
**not** byte-identical is the `FunctionConsistencyStats` summary string, which
now carries a trailing `, lemma_batch_cap=off` — deliberate, so the arm is
visible by mechanism, and exactly the kind of string a golden pin notices.
**Checked rather than assumed**: no file outside `euf.rs` references
`last_new_lemmas`, and no golden, snapshot or JSON artifact pins the summary.
The 1,749-test solver lib sweep and `corpus_regression` both ran green with the
change in place.

## 8. Found while doing this, not asked for

- **[ADR-2020]'s A/B table does not match its own committed artifact on one
  row.** It reports the secondary `QF_LIA` run at **27 rows**;
  `bench-results/ground-decide-20260914/ab/secondary-qflia.tsv` has **12**. Its
  main and noise-floor rows both match their artifacts at 129. Nothing in
  [ADR-2020]'s conclusion turns on it (that row moved 0 either way), but the
  number is not reproducible from what it published.
- **`oversized_admission_probe` is still not wired into the UF+arith route**,
  and this lane did **not** size it — reported as **did not run**, not as
  closed. But one thing about it was read rather than assumed, because it is the
  obvious reason a next lane would decide not to try. Its decider is
  `check_qf_lia_online_cdclt`, a **pure-LIA** online CDCL(T), and the population
  is UF+arith — which looks like a fragment mismatch. It is not. By the time the
  lazy EUF loop reaches `check_with_arith_dpll_reusing_lemmas`,
  `abstract_functions` has already replaced every application with a fresh
  symbol, so the term set at that point is pure arithmetic plus congruence
  lemmas and sits inside the probe's fragment. Confirmed by reading:
  `check_with_arith_dpll_reusing_lemmas` contains **zero** references to
  `oversized_admission_probe`, while `check_with_arith_dpll` calls it at
  `dpll_lia.rs:641`. The gap is a missing call, not a missing capability.
- **The `bv_reduction` capability frontier was pinned from a run that says it
  must not be.** Running the ratchet as a gate rewrote the artifact from
  `frontier: 34` to `39`. The committed 34 carries `comparable: false,
  ratchetable: false` in its own machine block (load_start 8.42); this run
  carries `true, true` (load_start 2.50). Not attributable to this lane — both
  levers are off by default and `bv_reduction` is `QF_BV`, which reaches neither
  code path — and no enforced `baseline` moved. Recorded in `d3f2e1e11` rather
  than left dirty.

[ADR-1927]: adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md
[ADR-1957]: adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-1966]: adr-1966-a-rungs-refusal-of-a-construct-a-later-rung-owns-is-a-decline.md
[ADR-1980]: adr-1980-the-cheap-check-was-the-whole-target-a-dispatch-decline-not-a-datatype-capability.md
[ADR-1995]: adr-1995-the-instantiation-loops-verdict-is-not-monotone-in-its-budget.md
[ADR-2000]: adr-2000-the-front-door-refusal-was-not-the-binding-constraint.md
[ADR-2015]: adr-2015-the-round-head-is-a-symptom-the-ground-checker-is-the-wall.md
[ADR-2020]: adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
