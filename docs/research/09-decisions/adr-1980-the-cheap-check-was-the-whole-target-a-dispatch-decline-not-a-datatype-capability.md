# ADR-1980: the cheap check WAS the whole target — a dispatch decline, not a datatype capability

Status: accepted
Index-summary: [ADR-1975] handed over **124 winnable rows in three divisions**, all blocked by `datatype_expansion_is_exact`, and named the step it had not taken: run [ADR-1966]'s check on the three refusal sites FIRST, because a rung below may own the construct. **It comes out positive, and the answer was already on disk** — but three call frames had to be read to see it. The `mbqi declined an unsupported fragment` prefix on all 124 rows makes MBQI look like the propagating rung and it is not (both MBQI rungs already decline); the sentences are produced in `datatype_native.rs`; and they are PROPAGATED at `check_auto_dispatch`'s bare `?`, the one site ADR-1966 sized at **+22/−2 on `AUFDTLIRA`** and reverted because it turned 7 assertions red in four other ADRs' suites. **A refusal message names the rung that PRODUCED the sentence, never the rung that decided to propagate it**, and on a ladder those are routinely different frames. This ADR builds ADR-1966's one named prerequisite (`relabel_with_datatype_refusal` carries the datatype sentence out to whatever the ladder ends on — measured: that alone turns 2 of the 7 green with no test edit), takes the site behind a one-binary lever whose polarity is INVERTED relative to every other runner here, and moves the remaining assertions to where their guard actually lives, at `check_with_datatype_native` itself. **No encoding changed**: every exactness precondition fires on exactly the same queries under both arms, so ADR-1930's wrong `unsat` stays impossible by construction. Measured, both arms back to back on one pinned core, order alternating: **`UFDTLIRA` 105 → 143, `UFDT` 31 → 50, `AUFDTLIRA` 96 → 118 — +79 net, 81 gains, 2 losses, 0 sat↔unsat flips**, with the `UF` control moving **nothing at all** (ADR-1966's control lost one). All 83 movers re-run 3× per arm: **81 STABLE-GAIN, 2 STABLE-LOSS, 0 UNSTABLE**; noise floor **143/143/143, band 0**; **240 comparisons against `:status`, z3 4.13.3 and cvc5 1.3.4, 0 disagreements**, denominators published per authority (80/81, 79/81, 81/81). `AUFDTLIRA` reproduces ADR-1966's +22/−2 exactly from a base six files higher. **The pre-registered bracket (8–35, point estimate 23, committed before any solver code was measured) was too low, and the reason generalises: a conversion rate measured on a MIXED blocker population does not transfer to a subset of it** — ADR-1966's 19% was over four refusal families of which the exactness three were 39 of 116. **80 of the 124 converted (65%)**, and the 44 left are no longer what ADR-1975 described: they were declining with 23.9 s of 24 s unspent and now spend a median of up to 17.4 s, so the next lane must re-census rather than inherit that figure. The cost is real and lands on the rows that did NOT move (+0.55 to +2.5 s/row), which is also the mechanism behind both losses. Mutation: 4 mutations, 4 non-empty and pairwise-DISTINCT kill sets. And `verify-new-verdicts.sh`'s `:status` stage was found to match NOTHING on every file, always — ADR-1966 published that zero as "these files carry none"; they carry it.
Index-status: accepted
Date: 2026-09-13

## Context

[ADR-1975] handed over **124 winnable rows across three divisions**, every one
declining with a median 23.9 s of its 24 s budget unspent, and every one resting
on `datatype_expansion_is_exact` — false exactly when a constructor field has
sort `Datatype(_)`. It sized the population statically (97 of 124 nested but not
recursive, field-chain depth ≤ 6, not one flat), said plainly that *"124 is a
blocker count, not a reachable count"*, and named the step it had not taken:

> **Run [ADR-1966]'s check on these three refusal sites first.** A rung BELOW
> may own the construct, in which case the refusal should be a DECLINE and the
> fix is far smaller than a capability. **This is the cheapest thing to try and
> this lane did not try it.**

## The ADR-1966 check, and why it took three steps to answer

It comes out **positive**, and the answer was already on disk. Three things had
to be established, because the obvious reading is wrong at every step.

**1. The MBQI rungs are already declines.** All 124 rows carry a
`mbqi declined an unsupported fragment: …` prefix, which makes MBQI look like
the propagating rung. It is not: `mbqi_first_refusal` records
`unsupported_decline(&message)` and returns `Ok(None)`, and the full rung in
`finish_quantified_solve` turns the same `Err` into a `CheckResult::Unknown`
with the comment *"MBQI refusing this query's FRAGMENT is not a verdict on the
query"*, after which the full pure-UF finite-model rung runs. The sentence the
census reads is the last `unknown`'s detail, not an unconverted propagation.

**2. The sentences are manufactured one level in.** All three are produced
inside `datatype_native.rs`, and `check_with_datatype_native` has exactly two
callers: a tail call in `datatype_elim.rs`, and `check_auto_dispatch` — where
until this ADR it was a bare `?`. MBQI's ground sub-solves route through
`check_auto_dispatch`, so the refusal that ends the quantified ladder is made at
that `?`: the ground sub-solve dies as an ERROR and the thirteen dispatch rungs
below the datatype branch never run **inside the sub-solve**.

**3. That `?` is the one site ADR-1966 sized and did not take.** It measured the
conversion at **+22 / −2 files on `AUFDTLIRA`** (90 → 110 of 200), 0
`sat`↔`unsat` flips, all 23 new verdicts confirmed `unsat` by z3 4.13.3 and cvc5
1.3.4 — and reverted it, because it turns **7 assertions in 4 registered
pre-push suites** red. It named one prerequisite that removes 3 of the 7:
*carry the datatype rung's own sentence into the final `unknown` first*.

**So these 124 rows do not need a recursive tag/field expansion to move.** That
capability question is still open and this ADR does not touch it: neither
`datatype_expansion_is_exact` nor `field_sort_expands` nor any encoding is
modified here.

### The generalisable half

ADR-1975's instruction was right and its framing was one step short. "Run the
cheap check first" is not "grep the refusal site"; three separate call frames
had to be read before the propagating one was identified, and the *first* one —
the rung whose name is in the message — was already correct. **A refusal message
names the rung that PRODUCED the sentence, never the rung that decided to
propagate it**, and on a ladder those are routinely different frames. The check
is over when you have found the frame where the `?` is, not when you have found
the frame where the string is.

## What changed

### The prerequisite, built first

`relabel_with_datatype_refusal` carries the datatype rung's own sentence out to
whatever terminal refusal or `unknown` the ladder ends on, with the tail's
message appended rather than dropped. Without it the DT blocker census reads
`unsupported pure-Rust BV operator DtTest(…)` where it used to read the
capability sentence.

**Measured: the relabel alone turns 2 of ADR-1966's 7 red assertions green with
no test edit at all.** A decided result is never relabelled — a route that
declined does not get to rename a verdict.

### The conversion, behind a lever

`DatatypeNativeRefusalPolicy::{Propagate, Decline}`, selected by
`AXEYUM_DATATYPE_NATIVE_REFUSAL`, with a thread-scoped guard so a test can drive
both arms without an ambient environment variable. `Decline` is the shipped
default; absent, empty and unparseable values all resolve to it, and only
`propagate` / `off` / `0` selects the historical arm. `Propagate` is
byte-equivalent to the bare `?` it replaced, **recorder included** — the `?`
never reached `record_result`, so neither does it.

The lever is not tidiness. It is what lets the four suites that own the old
behaviour keep asserting it rather than having it deleted out from under them,
and it is what makes every new fixture non-vacuous: the `propagate` arm must
produce the `Err` and the `decline` arm must produce something else, in the
same process, on the same term. `dispatch_rung_refusal_declines`' own history is
a fixture that was vacuous.

### Why this is not a soundness change

The exactness guards are untouched and fire on exactly the same queries under
both arms, so the inexact congruence clause [ADR-1930] shipped a wrong `unsat`
from is never emitted by either. What changed is only whether the DISPATCHER
treats one route's refusal as the whole query's verdict. Every `sat` a lower
rung returns is replay-checked against the ORIGINAL assertions at the front
door, and — per [ADR-1976] — that replay, not the reference cross-check, is what
a `sat` rests on; the new tests replay it a second time inside the test, because
the route's own replay is part of the subject.

## The seven assertions, and where each one went

| suite | owner | was | now |
|---|---|---|---|
| `dt_capability_1935` ×2 | ADR-1935 | read the message off `solve`'s `Err` | **unchanged, and green** — the relabel keeps the sentence leading |
| `dt_uf_gate` ×1 | ADR-1920 | `Err(Unsupported)` on an array-of-datatypes | `Ok(Unknown)` whose detail LEADS with the datatype sentence |
| `dt_capability_1935` ×1 | ADR-1935 | `Err` | guard read off `check_with_datatype_native`; front door `Sat` + replay; `propagate` arm pinned |
| `dt_constructor_arg_1942` ×2 | ADR-1942 | `Err` | same shape |
| `dt_valued_result_1946` ×1 | ADR-1946 | `Err` | same shape |

The `dt_uf_gate` row is the one to read carefully, because it looks like a
weakened guard and is not. The property that test exists for is **termination** —
the pre-ADR-1920 binary aborted there with `fatal runtime error: stack
overflow`, which kills the whole test binary before any assertion runs. That
property is unchanged and still asserted. What changed is how the termination is
spelled, and `Ok(Unknown)` is strictly better than `Err` by this repository's own
hard rule that *`unknown` is a first-class solver result, never an error*.

The other four keep their guard by reading the sentence off
`check_with_datatype_native` **directly**, which is where the guard lives. A test
that asserted the dispatcher's routing was never testing ADR-1935's precondition;
it was testing that nothing downstream could answer. Moving the assertion to the
unit makes a revert of the guard kill it, which is the property that matters.

## The honest half, pinned as a test

**A decline is not a promise that something below can answer.** When no rung
below decides either, the TAIL route refuses in its own right and that refusal
still leaves `solve` as an `Err`. The conversion's value is therefore exactly
the files where a lower rung answers — which is why this lane sized itself by an
A/B and not by the blocker count.
`a_decline_is_not_a_promise_that_something_below_can_answer` pins it, and fails
loudly if a later change improves it rather than letting that go unrecorded.

## The measurement

Full protocol, every artifact and every derivation:
[`bench-results/dt-exactness-20260913/AB.md`](../../../bench-results/dt-exactness-20260913/AB.md).
One binary, two arms selected by `AXEYUM_DATATYPE_NATIVE_REFUSAL`, both arms
back to back on the same file on the same pinned physical core, arm order
alternating per file, 24 s wall, 8 GiB `ulimit -v`.

| division | base | arm | net | gain | loss | flips |
|---|---:|---:|---:|---:|---:|---:|
| UFDTLIRA | 105 | **143** | **+38** | 38 | 0 | 0 |
| UFDT | 31 | **50** | **+19** | 19 | 0 | 0 |
| AUFDTLIRA | 96 | **118** | **+22** | 24 | 2 | 0 |
| **total** | **232** | **311** | **+79** | **81** | **2** | **0** |
| **UF** *(control)* | **90** | **90** | **0** | **0** | **0** | **0** |

**The control moved nothing at all** on 200 files — ADR-1966's `UFLIA` control
lost one file reproducibly to this change's cost mechanism, so a zero here was
not the expected outcome and is reported as a measurement rather than assumed.

Every one of the 83 moved rows was re-run **three times per arm**: **81
STABLE-GAIN, 2 STABLE-LOSS, 0 UNSTABLE, 0 FLIP**. Nothing vanished on re-check,
against ADR-1966's 11-of-18 ambient rate on the rows it did not verify.

**`AUFDTLIRA` comes out at +24 / −2 from a base of 96, which reproduces
ADR-1966's +22 / −2 from a base of 90 exactly.** Two lanes, two baselines six
files apart, same delta. That is the closest thing to an independent replication
this protocol can produce.

### The bracket was pre-registered and it was too low

This lane committed **8–35, point estimate 23** at `7b1e88363`, before any
solver code was measured. The realised figure is **+79**, more than double the
top of the bracket, and the reason is specific rather than "we got lucky": the
19 % conversion rate it extrapolated from was measured on `AUFDTLIRA`, where the
three exactness refusals are only 39 of 116 blocked rows, so the rate was
DILUTED by refusal families that convert poorly. The two divisions where
exactness refusals dominate — `UFDTLIRA` 49, `UFDT` 36 — had never been measured
for this conversion at all, and they are where the extra 57 files came from.

**The generalisable correction: a conversion rate measured on a mixed blocker
population does not transfer to a subset of it.** ADR-1966's 22/116 is a rate
over four refusal families; applying it to one of them assumes they convert
alike, and they do not.

### Every gain is inside the population ADR-1975 sized

**80 of the 124, 65 %.** The one gain outside is a different ADR-0022 refusal
family travelling through the same site. All three refusal messages are
represented (46 argument / 28 result / 6 non-atomic), so this is not one arm of
the guard doing all the work.

### What is left, and how it changed

The 44 rows that did not convert are the honest remainder for the recursive
expansion — but **ADR-1975's description of them no longer holds**. It measured
these rows declining with "a median 23.9 s of 24 s UNSPENT — a shape refusal,
not a clock problem". After this change the remainder spend a median of 1.4 s
(`UFDTLIRA`), 3.0 s (`UFDT`) and **17.4 s** (`AUFDTLIRA`), up to the full
budget. They have moved from SHAPE-bound to genuinely searching and failing. A
lane taking the capability next must re-census rather than inherit that
decline-time figure — which is ADR-1975's own rule about stale blockers, now
applying to ADR-1975.

### The cost, and where it lands

| division | whole-division wall, base → arm | on the rows that did NOT move |
|---|---|---|
| UFDTLIRA | 209 s → 301 s (+92 s) | +0.55 s/row over 162 rows |
| UFDT | 1,287 s → 1,737 s (+449 s) | +2.5 s/row over 181 rows |

The gains are nearly free (median 107 ms base → 109 ms arm on the `UFDTLIRA`
gains); essentially the whole cost is thirteen rungs running on queries they
still cannot answer. That is also the mechanism behind both losses — the same
SPARK higher-order-fold pair, `unsat → unknown` at 808 ms → 6.3 s and 1.6 s →
24.1 s.

### Noise floor

Three independent runs of the SHIPPED arm over the whole of `UFDTLIRA` at fixed
code: **143 / 143 / 143, band 0, and 0 files disagreed with themselves.** The
shipped arm is measured on purpose — it runs strictly more code per file, so the
base arm would understate the floor. A band of 0 against a measured effect of
+38 on that division, and run 1 independently reproduces the A/B's own arm value
from a different script on different cores.

### Soundness

Every new verdict against three authorities, with the comparable denominator
published per authority ([ADR-1957]):

| division | new verdicts | `:status` | z3 4.13.3 | cvc5 1.3.4 | comparisons | disagreements |
|---|---:|---:|---:|---:|---:|---:|
| UFDTLIRA | 38 | 38/38 | 38/38 | 38/38 | 114 | **0** |
| UFDT | 19 | 18/19 | 17/19 | 19/19 | 54 | **0** |
| AUFDTLIRA | 24 | 24/24 | 24/24 | 24/24 | 72 | **0** |
| **total** | **81** | **80/81** | **79/81** | **81/81** | **240** | **0** |

The 3 no-opinion rows are 1 file declaring `:status unknown` and 2 z3 timeouts,
reported rather than dropped. All 81 new verdicts are `unsat` and there were 0
`sat`↔`unsat` flips in 1,200 solves — which is also what makes the cross-check
worth quoting here, since per [ADR-1976] it is strong for an `unsat` and weak
for a `sat`.

### This is a BRANCH measurement, and what it should be worth on `main`

Today's post-merge board found one lane's `+22` was worth about `+6` on `main`
and seven others landed within 0–6 files, so the question is not rhetorical.

**Expectation: +79 survives the merge close to intact, because the base arm
already IS `main`.** Every base value here lands on the published `main` number
exactly — `UFDTLIRA` 105, `AUFDTLIRA` 96, `UF` 90, `UFDT` 31 — and the branch is
`main` at `c2fb0ade4` plus this lane's commits and nothing else. A branch whose
base has drifted is measuring against a tree nobody will merge into; that is the
mechanism behind a `+22` becoming `+6`, and it has not happened here.

Two things can still reduce it, named in advance: another lane landing on the
same exactness-refused rows (the board is a max, not a sum — `AUFDTLIRA` has
already lost 14 files that way once), and the per-row cost interacting with a
busier box, which can only cost files. **If the post-merge number lands
materially below +79, check overlap with whatever else merged before suspecting
this lane's protocol** — the noise floor is 0 files over three full-division
runs and 0 of 83 movers were unstable.

### A defect found in the verifier, and a published zero it invalidates

`verify-new-verdicts.sh`'s `:status` stage piped
`grep -oE '\(set-info :status (sat|unsat|unknown)\)'` into
`grep -oE '(sat|unsat|unknown)$'`. The first emits `(set-info :status unsat)`;
the second anchors on `$` and that string ends in `)`. **It matched nothing on
every file, always.** ADR-1966 reported the result as "the declared `:status` is
comparable on 0 of 23, because these files carry none" — they carry it, and its
23 rows have a third authority that agrees. CLAUDE.md's banned idiom, *an empty
grep as a negative result*, reaching a published ADR. Fixed in this lane's copy
(`78fcd2b26`); ADR-1966's artifact directory is another lane's committed
evidence and is left alone.

## Mutation control

`scripts/tests/mutation_controls.py dt-native-refusal-decline`, four mutations
over `auto.rs`, run against `dispatch_rung_refusal_declines` (baseline green, 6
tests). Every anchor was checked to resolve to exactly one place in the source
before the suite was run.

| mutation | killed |
|---|---|
| the decline conversion is the shipped default | 2: `…still_names_its_own_capability`, `…is_not_the_querys_verdict` |
| the datatype sentence survives into a terminal `Err` | 1: `a_decline_is_not_a_promise_that_something_below_can_answer` |
| the datatype sentence survives into a terminal `unknown` | 1: `…still_names_its_own_capability` |
| the historical `propagate` arm is really reached | 1: `…is_not_the_querys_verdict` |

**Four mutations, four non-empty and pairwise-distinct kill sets**, so no two
guards are rejecting through one shared check — the shape that made six of seven
guards removable in the audit CLAUDE.md cites. Three kill exactly one test; the
table says so rather than claiming "exactly one" across the board.

The fourth is the one worth reading: it deletes the PROPAGATE arm, and a
survivor there would have meant the two-arm fixtures' control assertions never
reach the historical arm — every fixture in that suite comparing the shipped arm
against itself. It did not survive.

**What the table does NOT show**, stated because it is the useful half:
`sound_the_datatype_decline_never_manufactures_an_unsat` survives all four. That
is correct and expected — it is a soundness FENCE over a satisfiable query whose
plausible wrong answer is `unsat`, and none of these four mutations can produce
a wrong `unsat`, because none of them touches the exactness encoding. It is not
counted as coverage.

## What this ADR does not claim

- **It does not claim the datatype capability.** 97 of ADR-1975's 124 are nested
  but not recursive and a recursive tag/field expansion would terminate on them
  with no new soundness story. That target is untouched and still open; what
  this ADR establishes is that it is not the *only* route to those rows, and
  that the cheaper route had to be priced first.
- **It does not claim 124 files.** A blocker count is not a reachable count, and
  this repository's tally (143→6, 51→2, 173→10, 84→49, 27,150→1,135, 19,620→0,
  177→0, 934→0, 46→2) is why the bracket was pre-registered before any solver
  code was measured.
- **It does not claim the terminal `Err` is gone.** See "The honest half".

[ADR-1957]: adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-1930]: adr-1930-a-wrong-constructor-selector-is-unspecified-not-defaulted.md
[ADR-1966]: adr-1966-a-rungs-refusal-of-a-construct-a-later-rung-owns-is-a-decline.md
[ADR-1975]: adr-1975-valid-universal-elimination-spends-24-seconds-to-prevent-a-107-millisecond-refutation.md
[ADR-1976]: adr-1976-qf-nia-is-model-bound-adr-1937-took-the-sat-half-and-the-eager-split-is-worth-four.md
