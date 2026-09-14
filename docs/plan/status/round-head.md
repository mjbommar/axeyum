# Lane: round-head — the round head is a symptom, the ground checker is the wall

<!-- plan-section: lane-status -->

**Lane round-head (`DONE`, round-head, 2026-09-14).** Four lanes closed four
explanations for the `UFLIA`/`UFNIA` gap in one day — budget policy
([ADR-1995], 0 of 87), the round ceiling ([ADR-1956], 0 of 177), reach
([ADR-2005], e-matching alone decides 111 of 115) and front-door refusal
([ADR-2000]) — leaving one hypothesis: the loop is *killed at a round head*
holding a set it never checks. **It does not survive, and it needed splitting
before it could even be censused.** Full reasoning in [ADR-2015]; artifacts in
[`bench-results/round-head-20260914/`](../../../bench-results/round-head-20260914/PREREGISTRATION.md).

## The string needed splitting, and so did the instrument that split it

[ADR-1956] split `InstantiationLoopExit` into `{Fixpoint, GrowthHeadroom,
RoundCeiling}` because one give-up string covered three exits. **The loop has
seven, and all three of those are `break`s.** The other four `return` early, so
they never become an `InstantiationLoopExit` at all — and
`e-matching: instantiation time budget exhausted` was ONE string on THREE of
them, while **four of the seven printed no `QPROBE loop-exit` line at all**. The
instrument a census would reach for could see three of seven exits.
`InstantiationTimeoutSite` splits the string and `timeout_exit_probe` gives the
other four the same line. **After the split, 0 of 127 rows give up with the
merged string.**

## Where rounds actually die

All 129 winnable rows re-run at base `94389e480`. **2 rows main now decides**
are dropped from every denominator and both verified `unsat` against `:status`,
z3 and cvc5 — **0 disagreements, comparable denominator 2/2 on each**.
Denominator **127**. Every exit listed **even at zero**.

| exit | | occurrences | last exit on |
|---|---|---:|---:|
| `SHAPE` | `Fixpoint` — **28 of these are saturations** | 45 | 23 rows |
| `CLOCK` | `GrowthHeadroom` | 11 | 3 rows |
| `ROUND` | `RoundCeiling` | 2 | 1 row |
| `timeout-round-head` | discards, **no** final check | **1** | 1 row |
| `timeout-mid-round` | checked, **not decided** | **147** | **74 rows** |
| `timeout-ground-check` | no clock left | 0 | 0 rows |
| `ground-ceiling` | ground-term cap | 3 | 3 rows |
| — | never reached an exit | — | 22 rows |

**The round head proper is 1 of 209 exits.** The binding exit is
`timeout-mid-round` — and it does **not** mean the set went unexamined. It sits
immediately after `quantifier_qf_refutation_check` over the same `ground` and
fires only when that check has just returned non-`Unsat`, on the **full shared
deadline** for every round inside the cadence window (the median such exit is at
round 2). The set was **CHECKED and NOT DECIDED**. This lane shipped the wording
`(ground set discarded unchecked)` and had to correct it two commits later, in
the direction that would have justified its own lever.

## `SHAPE` was a merged label too

The census turned the instrument on the instrument. **28 of the 45 `SHAPE`
exits sit at exactly `ground=8192`** — `MAX_GROUND_TERMS`, which
`GroundBudget::join_ceiling` equals. They are admission-cap **saturations
reported as fixpoints**: 62.2 %, Wilson `[47.6 %, 74.9 %]`. `Fixpoint`'s detail
asserts *"no further instance to admit; **more rounds cannot help**"*, and with
the join capped that is a conclusion the break is not entitled to.
`InstantiationLoopExit::GroundSaturated` (`SATURATED`) now names it; both arms
fire here (28 saturations, 17 fixpoints); the guard is on the property *all four
census kinds are distinct*, mutation-verified to kill **exactly one** test.

**28 and not 29**: a raw `grep` finds 29, one of which belongs to a row `main`
now decides and so sits outside the 127-row denominator.

## The measurement that decides it

`AXEYUM_QPROBE_HELD_SET_REPLAY` (off by default; verdict **printed, never acted
on**; separate stats sink) re-runs the check over the set at every exit on a
fresh 10 s budget. **Live by MECHANISM: 0 lines with the variable unset, 1 with
it set** — a silently ignored variable prints the same verdict.

    122 replays across 99 of 127 rows
    verdicts: unknown 78   sat 40   unsat 2   error 2

> **ROWS WHOSE HELD SET REFUTES ON A FRESH CLOCK: 2 of 127 = 1.6 %,
> Wilson 95 % `[0.4 %, 5.6 %]`**, against a pre-registered go/no-go of **≥ 10**.
> **So this lane ships no lever.**

Both are `UFLIA`, both `timeout-mid-round`, refuting in 2,236 ms and 1,844 ms.
That is the lever's entire ceiling, and it is **smaller than the noise floor of
the measurement that would have to detect it** — [ADR-2005] ran this same
division three times at fixed code for **+1 / −2 / +0** with every moved row
UNSTABLE.

**The other 120 replays name the real wall.** 40 are `sat` (the instantiation is
genuinely insufficient, correctly reported). 78 are `unknown` because *our*
ground checker declines *our* set, in its own words: `integer bit-blast width
ladder: wall-clock timeout reached`; `no model within the bounded integer width
32`; `eager Ackermann elimination would emit 57,219 congruence constraints,
exceeding the deterministic admission bound of 64`; `lazy Ackermann abstraction
build would still construct 8,633,894 congruence terms, exceeding the secondary
bound of 2,000,000`. Plus 2 hard `unsupported by backend: sort (Uninterpreted 0)
that the pure-Rust BV backend cannot bit-blast`. Sets of **11 ground terms**
spend a whole fresh 10 s budget and return `unknown`.

## What a solver that succeeds does differently: it does not get here

cvc5 1.3.4, all 129 rows, same envelope, its own instruments and none of ours.

| | |
|---|---|
| refuted | **115 of 129** = 89.1 % `[82.6 %, 93.4 %]` (reproduces [ADR-2005] exactly) |
| `global::totalTime` | min 3, p25 29, **median 75**, p75 195, max 17,410 ms |
| ≤ 100 ms | **60.0 % `[50.9 %, 68.5 %]`** |
| instantiation tuples | **median 48** |

`--dump-instantiations` is **live by MECHANISM**: non-zero tuples on 96 of the
115 refuted files and **0 of the 7 `NONE`** rows. `NONE` (7) is kept distinct
from `unknown` (7).

Head to head on a **comparable denominator of 129, zero one-sided leftovers**:
113 rows the reference refutes and we fail; our wall is a **median 262x** its
clock; our largest ground set at a loop exit is a **median 2,224** terms against
its median of **48** tuples. **Sixty per cent of this population is finished
before our loop enters its second round.**

## So

**Ship nothing.** The `UFLIA`/`UFNIA` gap is downstream of the instantiation
loop entirely. We reach the instances, build them, admit them, and hand the
conjunction to a quantifier-free decision procedure that cannot decide it.
**The missing capability has a name: deciding ground NIA and UF+arith
conjunctions**, and every remaining lever aimed at the loop — reserve, ceiling,
share, selection — is aimed at the wrong component. Whoever sizes that work must
first split the 40 `sat` replays from the 78 `unknown` ones; only the second is
addressable by a stronger checker, and merging them is the same mistake this
lane's first section is about, one layer down.

## Pre-registered rules against what happened

Committed in `ac34cc0e5`, before the population was touched.

| rule | pre-registered | outcome |
|---|---|---|
| R1 | classify by the **post-split** detail | **0 UNSPLIT** of 127 |
| R2 | all seven exits, denominators, zeros included | done |
| R3 | lever only if **≥ 10** rows replay `unsat` | **2** → **no lever** |
| R4–R7 | reserve lever, A/B, 3x stability, `UF` control | **did not run** — R4 was conditional on R3. Reported as "did not run", never as zeros |
| R8 | new verdicts vs three authorities | 2 rows, 0 disagreements, 2/2 each |
| R9 | Wilson, never normal | every ratio |
| R10 | no conversion rate | none quoted |

The pre-registered **prediction** was that the hypothesis fails with fewer than
10 rows, *"most likely zero"*. It failed with **2** — direction right, count
wrong, both recorded.

## Noise floor — it closes the question

The whole family run again with **both arms the byte-identical shipped
configuration**, back to back on the same file on the same pinned core, order
rotating, same 4 shards.

    verdict identical across the repeat:   127/129 = 98.4 % [94.5 %, 99.6 %]
    DIVISION TOTAL decided:  pass A 0,  pass B 2   -> band = 2 files AT FIXED CODE
    sat<->unsat flips:                     0
    LAST-EXIT CLASS identical:             104/107 = 97.2 % [92.1 %, 99.0 %]

**The lever's entire measured ceiling is exactly the noise floor.** The replay
found 2 rows whose set refutes; this same-arm repeat moves 2 rows at fixed code,
and [ADR-2005] measured the same band on this division independently.

**And the two rows the census reports as "`main` now decides" are those same two
rows, unstable**: `unknown` in pass A, `unsat` in pass B, `unsat` in the census.
Dropping them from the denominator stays right — we cannot count a row we
sometimes fail as one we fail — but *"main now decides them"* is the wrong
reading; *"they decide about half the time"* is the right one. Their verdicts
still agree with all three authorities.

**The exit table is stable enough to read as a table**: the last-exit class is
identical on 104 of 107 comparable rows. No conclusion above rests on a
difference smaller than the 3 that flip.

## Things found that were not asked for

- **`SHAPE` was a second merged label, and the file already knew it.** 28 of 45
  fixpoint exits are at the admission ceiling; a comment at one site calls that
  a *"CAP-INDUCED fixpoint"* while the exit's own detail says *"more rounds
  cannot help"*. Split as `GroundSaturated`, with the guard on the property.
- **`InstantiationLoopExit` is not the loop's exit enum, it is the loop's
  *`break`* enum.** Four of seven exits bypass it, and the ADR that created it
  to stop a merged label could not see them. A census keyed on its
  `census_kind()` was blind to 151 of 209 exits in this population.
- **An in-process replay of a DEADLINE exit can never complete**: the exit fires
  exactly when the clock is out, so the probe races a watchdog it cannot win.
  Measured at both 24 s and 60 s — a longer clock just moves the watchdog. The
  probe's blindness is published as a number (**53 of 127 rows**, 41.7 %
  `[33.5 %, 50.4 %]`, never replayed their largest discarded set) rather than
  left as a zero.
- **This lane's own summariser guessed a label and printed a zero that was
  memory**: `census_kind()` spells `Fixpoint` as `SHAPE`, so the first table
  read `FIXPOINT occurrences=0` while listing the 14 real fixpoint exits beside
  it as `*** UNLISTED EXIT ***`. The catch-all arm is the only reason it was
  caught; without it the zero would have read as a measurement.
- **`q:egraph` is not starved of clock on this family.** It is `bound_by` on 63
  of 127 rows and on the exemplar holds 22,615 ms of 24,119 — the 1.5 s figure
  visible in one trace is the `q:mbqi-quick` retry rung, a different and earlier
  one. That distinction matters because a budget lane could easily aim at the
  wrong rung's number.
- **`cargo check -p axeyum-solver --all-targets` on DEFAULT features is red on
  `main`** (`model.rs` calls `set_quantified_sat_certificate` /
  `quantified_sat_certificates`, both `#[cfg(feature = "full")]`, from code that
  is not). It is green at workspace scope because feature unification pulls
  `full` in, so the aggregate gate never sees it. Not this lane's diff; not
  fixed here.

## Branch point

`git merge-base main HEAD` is **`94389e480`**, which **was** `main`'s HEAD when
this lane branched and throughout every measurement above, so every number
measures the shipped tree plus this lane's diagnostics. Local `main` advanced to
`c8f1e4bfa` while the census was running — `94389e480` is an ancestor of it, and
that commit touches neither `qinst_egraph.rs` nor the quantified ladder, so the
census was not re-run against it. **Stated rather than glossed**: a base that is
"main's HEAD" at dispatch and a base that is main's HEAD at report time are
different claims.
**Predicted post-merge value: identical.** The diff adds probe output and splits
three give-up detail strings; nothing branches on them, and the old string is a
prefix of all three new ones, so a census keyed on it still matches.

## Compute

s5 core pairs `1,9` `3,11` and s6 `1,9` `3,11` — **4 pairs, the brief's cap**,
held **fixed across every arm** ([ADR-2000] measured a shard configuration
moving a count by more than repeating the sweep did). **All of s7 untouched**; a
16-division board sweep owned it. The cvc5 reference sweep ran on two local
cores and touched no fleet host.

[ADR-1956]: ../../research/09-decisions/adr-1956-do-not-raise-the-instantiation-round-ceiling-zero-of-the-177-rows-reach-it.md
[ADR-1995]: ../../research/09-decisions/adr-1995-the-instantiation-loops-verdict-is-not-monotone-in-its-budget.md
[ADR-2000]: ../../research/09-decisions/adr-2000-the-front-door-refusal-was-not-the-binding-constraint.md
[ADR-2005]: ../../research/09-decisions/adr-2005-the-instances-are-e-matchable-and-we-already-build-them.md
[ADR-2015]: ../../research/09-decisions/adr-2015-the-round-head-is-a-symptom-the-ground-checker-is-the-wall.md

<!-- plan-section: landed-changes -->

| 2026-09-14 | round-head | The last standing hypothesis for the `UFLIA`/`UFNIA` gap — *killed at a round head holding a set it never checks* — **does not survive, and it needed splitting before it could be censused**. [ADR-1956] split `InstantiationLoopExit` into three because one give-up string covered three exits; **the loop has SEVEN**, all three of those are `break`s, and the other four `return` early — `e-matching: instantiation time budget exhausted` was ONE string on THREE of them and **four of seven printed no `QPROBE loop-exit` line at all**, so the instrument built to stop a merged label was itself blind to 151 of 209 exits here. Split and re-censused over all 129 winnable rows (127 still failing; 2 now decided by main, both verified `unsat` against `:status`, z3 and cvc5, **0 disagreements, comparable denominator 2/2 each**): **the round head proper is 1 of 209 exits**. The binding exit is `timeout-mid-round` — **147 occurrences, last exit on 74 of 127 rows** — and it does **not** mean the set went unexamined: it sits immediately after `quantifier_qf_refutation_check` over the same `ground` and fires only when that check just returned non-`Unsat` on the full shared deadline. (This lane shipped `(ground set discarded unchecked)` and corrected it two commits later, in the direction that would have justified its own lever.) A new probe — `AXEYUM_QPROBE_HELD_SET_REPLAY`, off by default, verdict **printed and never acted on**, **live by MECHANISM: 0 lines off, 1 on** — re-runs the discarded set on a fresh 10 s clock: **122 replays over 99 of 127 rows, and 2 rows refute — 1.6 %, Wilson 95 % `[0.4 %, 5.6 %]`** against a pre-registered go/no-go of **≥ 10**, so **this lane ships no lever**; that ceiling is also smaller than the 3-file band [ADR-2005] measured for this division at fixed code. **The other 120 replays name the real wall**: **40 are `sat`** (the instantiation is genuinely insufficient) and 78 are `unknown` because *our* ground checker declines *our* set — `integer bit-blast width ladder: wall-clock timeout`, `no model within the bounded integer width 32`, `eager Ackermann elimination would emit 57,219 congruence constraints, exceeding the deterministic admission bound of 64`, `lazy Ackermann abstraction build would still construct 8,633,894 congruence terms, exceeding the secondary bound of 2,000,000`, plus 2 hard `unsupported by backend: sort (Uninterpreted 0)`. Sets of **11 ground terms** burn a whole fresh 10 s budget. The reference settles the order of magnitude without our instrumentation: cvc5 1.3.4 refutes **115 of 129**, `global::totalTime` **median 75 ms**, **60.0 % `[50.9 %, 68.5 %]` under 100 ms**, **median 48 instantiation tuples** (`--dump-instantiations` live by mechanism: non-zero tuples on 96 of 115 refuted, **0 of 7 `NONE`**) — while on the 113 rows it refutes and we fail (**comparable denominator 129, zero one-sided leftovers**) our wall is a **median 262x** its clock and we hold a **median 2,224** ground terms. **Sixty per cent of this population is finished before our loop enters its second round.** So the gap is **downstream of the instantiation loop entirely**: we reach, build and admit the instances and then hand the conjunction to a quantifier-free decision procedure that cannot decide it. **Do not size another lane against the loop on this population** — the best remaining loop-side lever has a measured ceiling of 2 of 127 inside a noise band of 3; **the missing capability is deciding ground NIA and UF+arith conjunctions**, and whoever sizes that must split the 40 `sat` replays from the 78 `unknown` ones first. ADR-2015 |
