# Lane `ROUND-HEAD` — pre-registration

**Written before any at-scale measurement**, committed in its own commit, so the
rules below can be compared against what was realised rather than reconstructed.

Branch base: `94389e480`. `git merge-base main HEAD` is `94389e480`, which **is**
`main`'s HEAD at the time of writing.

## What was already read (disclosed, not hidden)

Source reading only; no benchmark was run. `crates/axeyum-solver/src/qinst_egraph.rs`
was read around the instantiation round loop (lines 2251–2700) and
`finish_quantified_ground_check` (4070–4120). Nothing in the population has been
measured.

## The finding that motivates the design (structural, from source)

[ADR-1956] split `InstantiationLoopExit` into `{Fixpoint, GrowthHeadroom,
RoundCeiling}` because one give-up string covered three exits. **The loop has
more exits than that enum has variants, and the extra ones do not go through
the enum at all.** Reading the loop body, the exits are:

| # | site | give-up | runs `finish_quantified_ground_check`? |
|---|---|---|---|
| 1 | `for` runs to completion | `RoundCeiling` detail | yes |
| 2 | growth-headroom `break` (2274) | `GrowthHeadroom` detail | yes |
| 3 | fixpoint `break` (2575) | `Fixpoint` detail | yes |
| 4 | **round head, deadline passed (2256)** | `e-matching: instantiation time budget exhausted` | **NO — returns `egraph_timeout()`** |
| 5 | **mid-round, deadline passed (2348)** | *the same string* | **NO — returns `egraph_timeout()`** |
| 6 | ground ceiling (2290) | `e-matching: ground-term count budget exhausted` | no, but it *does* run a full check first |
| 7 | `quantifier_qf_check` with no remaining budget (3127) | *the same string as 4 and 5* | n/a |

So **`e-matching: instantiation time budget exhausted` is a merged string
covering three distinct exits** (4, 5, 7), exactly the shape ADR-1956 was
written about, and it has not been split. It is also the string ADR-1956's own
"other" bucket reported four rows under without splitting it.

Exits 4 and 5 are the ones this lane is about. They **discard the accumulated
ground set without ever asking whether it already refutes the goal.** The
thing they skip is not a formality: `finish_quantified_ground_check` runs a
shallow-generation subset check its own comment calls strictly additive ("it
can only turn an unknown into unsat") and then the full ground check. A row that
dies at exit 4 or 5 has never had either run over its final ground set.

This is what the brief means by "killed at a round head", and it is a
*different* claim from ADR-1995's. ADR-1995 gave the rung more clock and got
0 of 87; more clock spends itself on more rounds and still exits at a round
head. It never tested **checking the set we already hold**.

## Hypothesis under test

> **H1.** A material share of the winnable `UFLIA`/`UFNIA` rows we fail exit the
> instantiation loop at exit 4 or 5, and the ground set they hold at that moment
> is already unsatisfiable — i.e. we build a refutation and throw it away
> unexamined because the deadline landed inside a round rather than at a break.

The negation is equally publishable and is the more likely outcome given three
negatives today: the held set is genuinely not refuting, the loop needed
instances it did not have, and the round head is a symptom of that rather than
a cause.

## Instruments (both are measurements, not levers)

**I1 — split the merged string.** Sites 4, 5 and 7 get distinct `detail`s naming
which one fired. Pure diagnostic; no control flow changes. This is I1 because
requirement 2 of the brief forbids censusing the merged label.

**I2 — held-set replay probe.** `AXEYUM_QPROBE_HELD_SET_REPLAY=<ms>`: at exits 4
and 5, run `quantifier_qf_refutation_check` over the ground set being discarded,
under a **fresh** budget of `<ms>` unrelated to the rung deadline, and print

    QPROBE held-set-replay exit=<kind> ground=<n> verdict=<v> ms=<t>

then **return the original `egraph_timeout()` unchanged**. The verdict is
printed, never acted on — the same discipline as the existing probe at
`qinst_egraph.rs:8417`. Off by default; one environment lookup when off.

I2 is what decides H1. It is decisive in both directions and cannot be answered
by any aggregate count, because "we hold an unsat set" and "we hold an
insufficient set" produce the identical `unknown`.

## Population

`bench-results/ufnia-uflia-census-20260913/winnable/{UFNIA,UFLIA}.txt` — 61 + 68
= **129 rows**: files a reference decides and we returned `unknown` on.

**Re-derived, not inherited.** That list was produced at `c281a4b22`; this lane's
base is `94389e480`. The census re-runs our own binary over all 129 and reports
only rows we still fail on **at this lane's base**. Rows main now decides are
reported and dropped from the denominator, with the count published beside every
ratio ([ADR-1957]).

## Pre-registered decision rules

Written now, before the census.

- **R1 (split first).** The census classifies by the **post-split** detail. Any
  row whose give-up is still the merged string is a bug in I1 and is reported as
  `UNSPLIT`, not folded into a neighbour.
- **R2 (exit census).** Publish the full distribution over all seven exits for
  the still-failing population, with the denominator on the same line. Report
  zero counts explicitly.
- **R3 (the go/no-go, on I2, not on R2).** Build a lever **only if** the
  held-set replay returns `unsat` on **≥ 10** still-failing rows. Fewer than 10:
  publish the negative, ship nothing, and say the round head is a symptom.
  *A count and not a rate*, following ADR-2005's correct refusal to
  pre-register a conversion rate off a mixed blocker population.
- **R4 (the lever, if R3 fires).** The only lever this lane may build is a
  **reserve**: hold back a slice of the rung budget so the finish always runs,
  i.e. make exits 4 and 5 unreachable rather than making them do more work at a
  deadline that has already passed. Shipped OFF behind
  `AXEYUM_QINST_FINISH_RESERVE`; `off`/`0`/`false`/empty/unparseable/absent all
  resolve to the shipped behaviour. **Stated polarity: the BASE arm runs with
  the variable UNSET; the ARM runs with it set.**
- **R5 (A/B discipline, if R4 is built).** Interleaved per-file, **one binary and
  two env values**, both arms back to back on the same file on the same pinned
  physical core, order alternating. 24 s wall, 8 GiB `ulimit -v`.
  **Shard config held fixed across arms: 4 shards, s5 {1,9 / 3,11} and
  s6 {1,9 / 3,11}.** s7 untouched.
- **R6 (stability).** Every moved row re-run **3x per arm** and classified
  STABLE-GAIN / STABLE-LOSS / UNSTABLE / FLIP. A noise floor is published from
  one whole division run repeatedly in the **same** arm.
- **R7 (control).** `UF` is the control division and must not move. Reported
  even at zero, and shown **non-vacuous** by naming the route that binds its
  undecided rows.
- **R8 (soundness).** Every new verdict checked against `:status` and against
  independent authorities with
  `bench-results/dt-exactness-20260913/verify-new-verdicts.sh` (**not** the
  `dispatch-decline-audit-20260913/` copy, whose `:status` stage matches nothing).
  No-opinion counts kept separate from agreements.
- **R9.** Wilson 95 % intervals for every small-n proportion; never normal.
- **R10 (no conversion rate).** Deliberately not pre-registered, for ADR-2005's
  reason: a rate measured on a mixed blocker population does not transfer to the
  subset this lane would act on.

## Prediction, recorded so it can be wrong

H1 **fails**: the held-set replay returns `unsat` on fewer than 10 rows, most
likely on **zero**, and this lane ships nothing. Reason: three lanes today have
each found the loop reaching, building and admitting the right terms and still
not refuting, and the most economical reading of that is that the final check is
not the missing step. The measurement is worth making anyway because it is the
only one that can tell "insufficient set" from "unexamined set", and those have
opposite next moves.

[ADR-1956]: ../../docs/research/09-decisions/adr-1956-do-not-raise-the-instantiation-round-ceiling-zero-of-the-177-rows-reach-it.md
[ADR-1957]: ../../docs/research/09-decisions/adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-1995]: ../../docs/research/09-decisions/adr-1995-the-instantiation-loops-verdict-is-not-monotone-in-its-budget.md
[ADR-2005]: ../../docs/research/09-decisions/adr-2005-the-instances-are-e-matchable-and-we-already-build-them.md
