# ADR-2015: the round head is a symptom — the instantiated conjunction is handed to a ground checker that cannot decide it

Status: accepted
Index-summary: Four lanes closed budget policy ([ADR-1995], 0 of 87), the round ceiling ([ADR-1956], 0 of 177), reach ([ADR-2005], e-matching alone decides 111 of 115) and front-door refusal ([ADR-2000]) on the `UFLIA`/`UFNIA` gap, leaving one hypothesis: the loop is *killed at a round head* holding a set it never checks. **It does not survive, and it needed splitting before it could even be censused.** `e-matching: instantiation time budget exhausted` was ONE string on THREE call sites, and **four of the loop's seven exits printed no `QPROBE loop-exit` line at all** — [ADR-1956] split the three `break` exits and the four early-`return` exits were invisible to the instrument that split them. Split and re-censused over all 129 winnable rows (127 still failing at this base; 2 now decided, both verified `unsat` against `:status`, z3 and cvc5, 0 disagreements, comparable denominator 2/2 each): the round head proper is **1 of 209 exits**. The binding exit is `timeout-mid-round`, **147 of 209 occurrences and the last exit on 74 of 127 rows**, and it is **not** a set going unexamined — it sits immediately after `quantifier_qf_refutation_check` over the same `ground` and fires only when that check has just returned non-`Unsat` on the full shared deadline. A new probe (`AXEYUM_QPROBE_HELD_SET_REPLAY`, off by default, verdict **printed and never acted on**, shown live by mechanism: 0 lines off, 1 on) re-runs the discarded set on a fresh 10 s budget: **122 replays over 99 of 127 rows, and 2 rows refute — 1.6 %, Wilson 95 % `[0.4 %, 5.6 %]`**, against a pre-registered go/no-go of **≥ 10**. **So this lane ships no lever.** The 120 non-refutations name the real wall in the checker's own words: **40 are `sat`** (the instantiation is genuinely insufficient, correctly reported) and 78 are `unknown` because *our* ground checker declines *our* set — `integer bit-blast width ladder: wall-clock timeout`, `no model within the bounded integer width 32`, `eager Ackermann elimination would emit 57,219 congruence constraints, exceeding the deterministic admission bound of 64`, `lazy Ackermann abstraction build would still construct 8,633,894 congruence terms, exceeding the secondary bound of 2,000,000`, plus 2 hard `unsupported by backend: sort (Uninterpreted 0) that the pure-Rust BV backend cannot bit-blast`. The reference measurement settles the order of magnitude without our instrumentation: cvc5 1.3.4 refutes **115 of 129** with `global::totalTime` **median 75 ms**, **60.0 % `[50.9 %, 68.5 %]` under 100 ms**, and a **median of 48 instantiation tuples** — while on the 113 rows it refutes and we fail (comparable denominator 129, zero one-sided leftovers) our wall is a **median 262x** its clock and our largest ground set at a loop exit is a **median of 2,224 terms**. A reserve lever redistributing 24,000 ms is implicitly claiming the work is of the same ORDER as the budget; against 75 ms it is not. **The `UFLIA`/`UFNIA` gap is downstream of the instantiation loop entirely: the missing capability is a quantifier-free decision procedure for the instantiated NIA / UF+arith conjunction, and every remaining lever aimed at the loop is aimed at the wrong component.**
Index-status: accepted
Date: 2026-09-14

## Context

Four lanes closed four explanations for the `UFLIA`/`UFNIA` gap in one day:

- [ADR-1995] — **budget policy is not it.** A genuine one-way ceiling handing
  the whole remaining root deadline back decides **0 of 87**, Wilson
  `[0 %, 4.2 %]`; the loop is measured non-monotone in its budget.
- [ADR-1956] — **the round ceiling is not it.** 0 of 177 rows reach it; a
  2x/4x/8x sweep gains 0 and loses 0.
- [ADR-2005] — **reach is not it.** Of the 115 winnable files cvc5 decides,
  e-matching alone decides 111 (97 %), and 0 of 115 need the combination.
- [ADR-2000] — **front-door refusal is not it** for the `distinct` family.

What [ADR-2005] handed over, in its own words, was *"the failure is downstream
of admission, not reach"*, with an exemplar reporting
`ematch retried residual=true instantiated=false` and **no fixpoint line** —
killed at a round boundary — and the explicit note that it **did not size
this**. That is what this lane was briefed to size.

Sizing, instruments and decision rules were
[pre-registered](../../../bench-results/round-head-20260914/PREREGISTRATION.md)
in their own commit (`ac34cc0e5`) before the population was touched, **including
the prediction that the hypothesis would fail** — recorded so it could be wrong.

Branch base: `git merge-base main HEAD` is `94389e480`, which **was** `main`'s
HEAD when this lane branched and throughout every measurement below, so the
measured tree is the shipped tree plus this lane's diagnostics. Local `main`
advanced to `c8f1e4bfa` (another lane's board sweep) while the census was
running; `94389e480` is an ancestor of it, and nothing in that commit touches
`qinst_egraph.rs` or the quantified ladder.

## The give-up string needed splitting, and so did the instrument that split it

[ADR-1956] exists because one give-up string covered three loop exits and only
one of them was a round budget. It split `InstantiationLoopExit` into
`{Fixpoint, GrowthHeadroom, RoundCeiling}` and every one of those is a `break`
that falls through to `finish_quantified_ground_check`.

**The loop has seven exits, not three.** The other four `return` early, so they
never become an `InstantiationLoopExit` at all:

| # | site | give-up before this lane | reaches the final check? |
|---|---|---|---|
| 1 | `for` runs to completion | `RoundCeiling` detail | yes |
| 2 | growth-headroom `break` | `GrowthHeadroom` detail | yes |
| 3 | fixpoint `break` | `Fixpoint` detail | yes |
| 4 | round head, deadline passed | `…instantiation time budget exhausted` | **no** |
| 5 | mid-round, deadline passed | *the same string* | **no** |
| 6 | ground ceiling | `…ground-term count budget exhausted` | no (runs its own full check first) |
| 7 | `quantifier_qf_check`, no budget | *the same string again* | n/a |

So **exits 4, 5 and 7 shared one string** — the same shape ADR-1956 was written
about, and the string its own "other" bucket reported four rows under without
splitting. Worse, exits 4–7 printed **no `QPROBE loop-exit` line at all**, so
the instrument a census would reach for could see three of seven exits and
would report the rest as "did not reach an exit".

`InstantiationTimeoutSite` splits the string three ways (each detail a suffix on
the historical text, so a census keyed on the old string still matches) and
`timeout_exit_probe` gives exits 4–7 the same `QPROBE loop-exit` line the
`break` exits already had. **After the split, 0 of 127 rows give up with the
merged string** — rule R1, reported rather than assumed.

## Where rounds actually die

All 129 winnable `UFNIA`/`UFLIA` rows re-run at this lane's base. 24 s wall,
8 GiB `ulimit -v`, one pinned physical core per shard, **4 shards held fixed
across every arm: s5 `{1,9  3,11}` and s6 `{1,9  3,11}`**; s7 untouched
(a 16-division board sweep owned it). Binary built into an empty target dir and
licensed by `find crates -name '*.rs' -newer "$BIN"` returning nothing, not by
the build's exit status.

**2 of 129 rows main now decides**, so they are dropped from every denominator
below and the count is published here rather than absorbed. Both are `unsat`;
both were checked against three independent authorities and **all three agree,
with the comparable denominator on the line** ([ADR-1957]):

    z3.885941.smt2              ours unsat  :status unsat  z3 unsat  cvc5 unsat
    javafe.parser.TokenQueue.576  ours unsat  :status unsat  z3 unsat  cvc5 unsat
    DISAGREEMENTS: 0.  Comparable denominator: 2/2 on :status, 2/2 z3, 2/2 cvc5.

**Denominator: 127 still-failing rows. Every exit is listed even at zero** — an
omitted row and a zero row read the same in a table and only one of them is a
measurement.

| exit | what it means | occurrences | last exit on |
|---|---|---:|---:|
| `SHAPE` | `Fixpoint` — **but see below** | 45 | 23 rows |
| `CLOCK` | `GrowthHeadroom` | 11 | 3 rows |
| `ROUND` | `RoundCeiling` | 2 | 1 row |
| `timeout-round-head` | discards, **no** final check | **1** | 1 row |
| `timeout-mid-round` | checked, **not decided** | **147** | **74 rows** |
| `timeout-ground-check` | no clock left for a check | 0 | 0 rows |
| `ground-ceiling` | ground-term cap | 3 | 3 rows |
| — | never reached a loop exit | — | 22 rows |

**The round head proper is 1 of 209 exits.** The brief's framing — *killed at a
round head* — is right that the loop dies at a deadline exit and wrong about
which one, and the difference decides the remedy. 81 of 127 rows
(63.8 % `[55.1 %, 71.6 %]`) hit a `timeout-*` exit; 54 of 127
(42.5 % `[34.3 %, 51.2 %]`) do so holding ≥ 400 ground terms.

### `SHAPE` was a merged label too — 28 of those 45 are saturations

The census turned this lane's instrument on the instrument that motivated it.
Of the 45 `SHAPE` exits, **28 sit at exactly `ground=8192`** — which is
`MAX_GROUND_TERMS`, and `GroundBudget::join_ceiling` equals it. They are
**admission-cap saturations reported as fixpoints**: 28 of 45 = **62.2 %,
Wilson 95 % `[47.6 %, 74.9 %]`**.

This file already knew the shape and named it in a comment at one site — *"every
flooded file reaches that arm only at a CAP-INDUCED fixpoint with
`ground=8192`"* — but the exit the census reads did not distinguish it, and
`Fixpoint`'s give-up detail asserts *"no further instance to admit; **more
rounds cannot help**"*. With the join capped, that second clause is a conclusion
the break is not entitled to: *nothing more was admitted* already has a
sufficient explanation. [ADR-1956] created this enum to stop exactly this, and
it stayed merged one layer down for the same reason it was merged the first
time — the label was believed rather than measured.

`InstantiationLoopExit::GroundSaturated` (census kind `SATURATED`) now names that
break. It is a statement about **the cap being in force**, not a proof the cap is
what stopped admission — the loop cannot know that at the break. The point is the
reverse: neither could `Fixpoint`, and it said so anyway. Both arms fire on this
population: **28 saturations, 17 true fixpoints**. The guard is on the *property*
(all four census kinds distinct) rather than on four literals, because this label
has now been merged twice; mutation-verified, returning `"SHAPE"` from
`GroundSaturated::census_kind` kills `the_exit_kinds_follow_adr_1950_and_are_distinct`
and **exactly** that test (116 passed, 1 failed).

**The 28 is 28 and not 29 for a denominator reason worth writing down.** A raw
`grep` over the committed census finds 29 `SHAPE` exits at `ground=8192`; one of
them belongs to a row `main` now decides, which is outside the 127-row
denominator. The table above and this paragraph both use 127.

### And `timeout-mid-round` does not mean the set went unexamined

This lane shipped the wording `(ground set discarded unchecked)` on that exit
and then had to correct it two commits later, in the direction that would have
justified its own lever. Reading the loop body to the bottom:

```rust
if interleaved_check_due(round) {
    let check = quantifier_qf_refutation_check(arena, &ground, …, check_deadline, …)?;
    if matches!(check, CheckResult::Unsat) { … return Ok(CheckResult::Unsat); }
}
if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
    …
    return Ok(egraph_timeout(MidRound));   // <-- HERE
}
```

The exit sits **immediately after** a full ground check over the same `ground`,
and fires only when that check has just returned non-`Unsat` — on the **full
shared deadline** for every round inside the cadence window (`round < 8`, and
the median `timeout-mid-round` exit is at **round 2**). So the set was
**CHECKED and NOT DECIDED**: the check consumed the remainder of the budget and
returned `unknown`. "Examined but undecided" and "never looked at" have opposite
remedies, which is exactly why these exits now have separate names.

## The measurement that decides it: replay the set on a fresh clock

No aggregate count can separate *"we hold an unsat set and never looked"* from
*"we hold a set our checker cannot decide"* — both print `unknown`.
`AXEYUM_QPROBE_HELD_SET_REPLAY=<ms>` re-runs `quantifier_qf_refutation_check`
over the set at every exit, on a **fresh** budget unrelated to the rung deadline
(which has by definition already passed), and **prints the verdict without
acting on it** — the same discipline as the clause-shape probe in the same file.
It carries the `unknown` **kind and detail** through, because a checker that ran
out of time and one that declined the fragment are different findings that both
print `unknown`.

**Live by MECHANISM, not by verdict counts**, on `f2_rw160.smt2`: with the
variable unset the run emits **0** `held-set-replay` lines; set to 5000 it emits
**1**. A silently ignored variable prints the same verdict either way.

### The result, and it is a clean negative

10 s fresh budget, `min_ground=0` (every exit), arms interleaved per file on the
same pinned core with the order rotating.

    122 replays across 99 of 127 rows (78.0 % [70.0 %, 84.3 %])
    verdicts: unknown 78   sat 40   unsat 2   error 2
    ground set replayed: median 923, min 5, max 8,192

> **ROWS WHOSE HELD SET REFUTES ON A FRESH CLOCK: 2 of 127 = 1.6 %,
> Wilson 95 % `[0.4 %, 5.6 %]`.**

The pre-registered go/no-go (R3) was **≥ 10 rows**, chosen as a count and not a
rate for [ADR-2005]'s reason. **2 < 10, so this lane ships no lever.**

The two are named, because they bound what a reserve could ever buy:

| file | exit | ground | replay |
|---|---|---:|---|
| `UFLIA/sledgehammer/Hoare/smtlib.993567.smt2` | `timeout-mid-round` | 334 | `unsat` in 2,236 ms |
| `UFLIA/simplify2/…/javafe.parser.TagConstants.001.smt2` | `timeout-mid-round` | 1,621 | `unsat` in 1,844 ms |

**The lever's entire measured ceiling is 2 files, and it is smaller than the
noise floor of the measurement that would have to detect it**: [ADR-2005] ran
this same `UFLIA` division three times at fixed code and got **+1 / −2 / +0**
with **every moved row UNSTABLE**, base band 3 files. A reserve also *shrinks*
the round budget it reserves from, so it can lose rows as easily as gain them.

### What the other 120 replays say — the actual wall

This is the part that redirects the work. The replays that did not refute are
not silent:

- **40 are `sat`.** The held set is genuinely satisfiable: the instantiation is
  insufficient and the loop reports that correctly. Nothing downstream of the
  loop can fix those.
- **78 are `unknown`, and our ground checker names its own bounds.** Verbatim,
  with the counts:

      8  integer bit-blast width ladder: wall-clock timeout reached
      6  auto-dispatch timeout after nonlinear integer real relaxation
      4  no model within the bounded integer width 32; widen the bound
      +  eager Ackermann elimination would emit 7,260 / 57,219 / 132,477
         congruence constraints, exceeding the deterministic admission bound of 64
      +  UF+arithmetic: lazy Ackermann abstraction build would still construct
         2,427,485 / 8,633,894 / 12,996,685 congruence terms, exceeding the
         secondary bound of 2,000,000
      +  lazy LIA pre-SAT skeleton exceeds the joint resource boundary
         (atoms=15,203  cnf_vars=26,308); declining before the first SAT round

- **2 are hard errors**: `unsupported by backend: term #0 has sort
  (Uninterpreted 0) that the pure-Rust BV backend cannot bit-blast`.

Sets as small as **11 ground terms** spend a whole fresh 10 s budget and return
`unknown`.

## What a solver that succeeds does differently at this point

It does not reach this point. The reference measurement uses cvc5's own
instruments and none of ours: all 129 rows, cvc5 1.3.4, same 24 s / 8 GiB /
pinned-core envelope, `--stats --dump-instantiations`.

| | |
|---|---|
| refuted | **115 of 129** = 89.1 % `[82.6 %, 93.4 %]` (reproduces [ADR-2005]'s 115 exactly) |
| `global::totalTime` on those 115 | min 3, p25 29, **median 75**, p75 195, max 17,410 ms |
| ≤ 100 ms | **69 of 115 = 60.0 % `[50.9 %, 68.5 %]`** |
| ≤ 1,000 ms | 97 of 115 = 84.3 % `[76.6 %, 89.9 %]` |
| instantiation tuples used | **median 48** |
| quantifiers instantiated | median 12 |

`NONE` (7) is kept **distinct** from `unknown` (7) throughout; neither is a
solver opinion about the file.

**`--dump-instantiations` is shown live by MECHANISM**: it emits a non-zero
tuple count on **96 of the 115** files cvc5 refutes and on **0 of the 7 `NONE`**
rows. A silently ignored flag would print the same verdict.

Head to head, on a **comparable denominator of 129 with zero one-sided
leftovers** (both sweeps ran every row):

    rows the reference REFUTES and we still fail:      113
    our wall / cvc5's own clock:      median  262x   max 5,158x
    our largest ground set at a loop exit:  median 2,224   max 9,050
    cvc5's instantiation tuples:            median    48

**Sixty per cent of this population is finished before our loop enters its
second round**, and where cvc5 needs a median of 48 instantiations we are
holding a median of 2,224 ground terms and cannot decide them.

## Decision

**Record the finding; build nothing.** The round head is a symptom, and every
remaining lever aimed at the instantiation loop — reserve, ceiling, share,
selection — is aimed at the wrong component.

The `UFLIA`/`UFNIA` gap is **downstream of the loop entirely**. The loop reaches
the instances ([ADR-2005]), builds them, admits them, and hands the resulting
conjunction to a quantifier-free decision procedure that, on this population,
hits an integer bit-blast width ladder, a bounded-integer model width of 32, an
eager-Ackermann admission bound of 64 against expansions of 57,219 and 132,477,
and a lazy-Ackermann secondary bound of 2,000,000 against builds of 8,633,894.
**That is the missing capability, and it has a name: deciding ground NIA and
UF+arith conjunctions.**

Two consequences for whoever picks this up:

1. **Do not size a lane against the instantiation loop on this population.** The
   measured ceiling for the best remaining loop-side lever is 2 of 127, inside a
   noise band of 3.
2. **The 40 `sat` replays and the 78 `unknown` replays are different
   populations with different fixes**, and only the second is addressable by a
   stronger ground checker. Any lane sizing that work must split them first —
   which is the same mistake this ADR's first section is about, one layer down.

### What is shipped

Diagnostics only. No verdict changes, no control flow changes:

- `InstantiationTimeoutSite` — splits the merged give-up string three ways.
- `timeout_exit_probe` — the four early-`return` exits now print the same
  `QPROBE loop-exit` line the `break` exits always did.
- `held_set_replay_probe` — `AXEYUM_QPROBE_HELD_SET_REPLAY` (off when unset,
  empty, zero or unparseable) and `AXEYUM_QPROBE_HELD_SET_REPLAY_MIN_GROUND`.
  A separate `QuantifierLoopStats` sink, so an arm with the probe on cannot move
  the shipped counters; the verdict is printed and **never acted on**.
- `InstantiationLoopExit::GroundSaturated` — the one behaviour change beyond
  diagnostics, and it changes only which give-up string a saturated fixpoint
  reports. No verdict depends on it.

### The rules that were pre-registered, against what happened

| rule | pre-registered | outcome |
|---|---|---|
| R1 | classify by the **post-split** detail; any merged row is `UNSPLIT` | **0 UNSPLIT** of 127 |
| R2 | publish all seven exits with the denominator, zeros included | done; round head 1 of 209 |
| R3 | build a lever **only if** ≥ 10 rows replay `unsat` | **2** → **no lever** |
| R4–R7 | the reserve lever, its A/B, 3x stability, the `UF` control | **not reached**, because R4 was conditional on R3. Reporting them as "did not run" rather than as zeros |
| R8 | every new verdict against three authorities, denominators separate | 2 rows, 0 disagreements, 2/2 on each |
| R9 | Wilson for every small-n proportion | every ratio in this ADR |
| R10 | no conversion rate pre-registered | none quoted |

The pre-registered **prediction** was that the hypothesis fails with fewer than
10 rows, *"most likely zero"*. It failed with **2** — the direction was right,
the exact count was not, and both are recorded.

[ADR-1941]: adr-1941-attempts-alone-cannot-classify-a-census-row-the-open-segment-is-the-discriminator.md
[ADR-1956]: adr-1956-do-not-raise-the-instantiation-round-ceiling-zero-of-the-177-rows-reach-it.md
[ADR-1957]: adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-1995]: adr-1995-the-instantiation-loops-verdict-is-not-monotone-in-its-budget.md
[ADR-2000]: adr-2000-the-front-door-refusal-was-not-the-binding-constraint.md
[ADR-2005]: adr-2005-the-instances-are-e-matchable-and-we-already-build-them.md
