# ADR-1956: do not raise the instantiation round ceiling — 0 of the 177 rows reach it

Status: accepted
Index-summary: The largest blocker on the six-division board — 177 of 390 winnable files reported as `did not refute within the round budget` — is NOT bound by a round budget: 0 of 177 reach the 512-round ceiling, 167 reach a FIXPOINT with the e-graph empty or inert, and a 2x/4x/8x sweep of the ceiling decides 0 additional files. A give-up string shared by three different loop exits will be classified by whichever one it names, so an exit must record which condition stopped it.
Index-status: accepted
Date: 2026-09-13

## Context

[ADR-1950](adr-1950-a-round-budget-and-a-clock-budget-are-different-findings-and-a-census-must-not-merge-them.md)
made a census split "budget exhausted" by WHICH budget, and applied that split
to lane `board-six`'s six-division census. The result was the largest actionable
finding anyone had put on the board:

> **`e-matching instantiation did not refute within the round budget` is 177 of
> 390 winnable files (45 %), across four divisions** — LRA 117, AUFLIA 48, BV
> 10, NRA 1 (plus 1 UFLIA) — and the median such row gives up with **23,994 ms
> of its 24,000 ms budget unspent**.

ADR-1950 classified that family `ROUND` and said, correctly, that only an A/B
could tell whether the ceiling is worth raising. It also said the classification
rests on the string, "because the string is all a census can read."

That is the sentence this ADR is about. **The string was shared by three
different exits, and only one of them is a round budget.** The loop's own dump
label for the point already said so — it was spelled `"fixpoint-or-break"`.

    for round in 0..MAX_EXTENDED_INSTANTIATION_ROUNDS {   // 512
        …
        if <remaining budget cannot fit another round> { break; }   // CLOCK
        …
        if <nothing left to admit>                       { break; } // SHAPE
        …
    }
    // ALL THREE arrive here, and this is what they said:
    "e-matching instantiation did not refute within the round budget"

So ADR-1950's `kind` column was derived from a message that could not
distinguish the three, and its own evidence column (`ms_left`) could not correct
it: a fixpoint at round 1 and a 512-round ceiling exit *both* leave the clock
untouched. The remaining-budget distribution separates ROUND from CLOCK. Nothing
in that census separated ROUND from SHAPE.

## What was measured

Same envelope as the board the population came from: 24 s wall, 8 GiB address
space, one pinned physical core per shard, binary built from scratch and
verified newer than every `crates/**/*.rs`. Boxes s5/s6/s7, idle (load ≤ 0.13 at
launch). The population is re-derived from `board-six`'s committed
`census/*.tsv` by the ranked string, not transcribed — `mkpop.py` prints
117/48/10/1/1/0 = **177**, which is ADR-1950's number.

Artifacts, runners and derivations:
[`bench-results/quant-rounds-20260913/`](../../../bench-results/quant-rounds-20260913/README.md).

### 1. The sizing bracket: 0 of 177

Every one of the 177 rows re-run with the exits split
(`summarize.py exit`):

| population | n | SHAPE (fixpoint) | CLOCK | **ROUND** | other | max rounds entered |
|---|---:|---:|---:|---:|---:|---:|
| LRA | 117 | 117 | 0 | **0** | 0 | 7 |
| AUFLIA | 48 | 40 | 4 | **0** | 4 | 99 |
| BV + NRA + UFLIA | 12 | 10 | 1 | **0** | 1 | 65 |
| **TOTAL** | **177** | **167** | **5** | **0** | **5** | **99** |

**Not one row reaches the ceiling.** The ceiling is 512; the deepest row in the
whole family entered 99 rounds, and the LRA majority entered **one**. The five
"other" rows are a different give-up entirely (four `e-matching: instantiation
time budget exhausted`, one `mbqi` declining an uninterpreted sort into the BV
backend) — under load a different rung's give-up prints first. None of them is a
round exit either.

This is the ratio the brief for this lane asked to be published before building:
**177 blocked, 0 reachable by this lever.** It is in the same family as the
143→6, 51→2, 173→10 and 84→49 brackets this project measured in the preceding
week, and it is the most extreme of them.

**The stronger form.** The table classifies by the FIRST give-up line, the
convention `board-six`'s census used; several ladder rungs run the loop, so
that line can belong to a rung that timed out before the loop started — which
is exactly what the five `other` rows are. Scanning the WHOLE trace instead
(`roundprobe.sh`):

    rows                                177
      round budget string ANYWHERE      0     <- the bracket
      fixpoint string anywhere          171
      growth-headroom string anywhere    32
      UNMEASURED (no give-up line)        0

**The round-ceiling give-up does not appear anywhere in any of the 177 runs**,
and the zero is not a grep that missed its subject: every row carries a give-up
line, and 171 carry the fixpoint string the same scan looks for.

Every non-`SHAPE` row was re-run three further times, because at a 24 s budget
1–1.5 % of files flip on ambient load alone and a single pairing is not a
finding. The CLOCK/OTHER split wobbles (4/5, 5/4, 6/3 — both are clock-family
reasons and which prints first depends on load); **`ROUND` is 0 across all 30
re-run solves.**

### 2. The value sweep: flat at zero from the first step

Four arms — the shipped 512, then 2x, 4x, 8x — run **back to back on the same
pinned core for one file before any arm sees the next**, with the arm order
ROTATING per file (`sweep-run.sh`).

| population | n | arm | decided | gained | lost | median ms | total s |
|---|---:|---|---:|---:|---:|---:|---:|
| LRA | 117 | shipped | 0 | 0 | 0 | 106 | 50.9 |
| | | 1024 (2x) | 0 | **0** | 0 | 106 | 49.7 |
| | | 2048 (4x) | 0 | **0** | 0 | 106 | 49.7 |
| | | 4096 (8x) | 0 | **0** | 0 | 106 | 51.4 |
| BV+NRA+UFLIA | 12 | shipped | 0 | 0 | 0 | 2109 | 74.3 |
| | | 1024 (2x) | 0 | **0** | 0 | 2011 | 77.1 |
| | | 2048 (4x) | 0 | **0** | 0 | 2210 | 74.0 |
| | | 4096 (8x) | 0 | **0** | 0 | 2210 | 73.4 |
| AUFLIA | 48 | shipped | 0 | — | — | 10014 | 499.8 |
| | | 1024 (2x) | 0 | **0** | 0 | 10315 | 500.0 |
| | | 2048 (4x) | 0 | **0** | 0 | 10115 | 502.9 |
| | | 4096 (8x) | 0 | **0** | 0 | 10017 | 500.8 |

ADR-1945's QF_UFBV sweep found +31/+44/+45 at 2x/4x/8x and used the *shape* of
that curve — flat after 4x — to decide what shipped. **This curve is flat at
zero from the first step**, which is what a non-binding constraint looks like
and is a different finding from "8x was not enough".

There is no time cost either, and that is the expected consequence rather than a
separate result: a loop that stops at round 1 for a reason unrelated to the
ceiling does the same work whatever the ceiling says.

### 3. The control is not vacuous, and three quarters of the named one was

This lane's brief named QF_UFLIA, QF_UFLRA, NRA and QF_DT as the control —
divisions we decide well. **Three of those four are quantifier-FREE**, so the
e-matching instantiation loop cannot run on them at all. Measured with the route
trail rather than assumed (`route-hit.sh`, `summarize.py control`): the
`q:egraph` rung is ATTEMPTED on **0 of 200 QF_DT files, 0 of 200 QF_UFLIA and 0
of 200 QF_UFLRA**. NRA reaches it on 9 of 200.

That is the hole ADR-1945's lane found in its own control (`ufbv_online` firing
on 0 of 400) reproduced almost exactly, and the reason this ADR states the
number instead of the division names.

The non-vacuous cost control is the **692 files the board says we already
decide** in the same six quantified divisions — same corpus families, same
ladder, same loop, and a verdict to lose. All 692, interleaved per file, arm B
= `AXEYUM_QINST_ROUNDS=4096`:

    same-decided      684        GAINED   0
    same-undecided      8        LOST     0
                                 DISAGREE 0
    median ms     shipped 109    8x 109
    total s       shipped 722.2  8x 722.4
    rows over 20 s  shipped 8    8x 8

**0 lost, 0 gained, 0 sat/unsat disagreement, and the wall clock does not
move.** ADR-1945's cost finding does not reproduce here, and the reason is the
bracket above rather than a difference in method: a loop that stops for a reason
unrelated to the ceiling does the same work whatever the ceiling says. The 8
`same-undecided` rows come back `unknown` on BOTH arms — a board-vs-today
difference at the 1.2 % level, not an arm effect.

### 4. What the 167 fixpoint rows actually look like

The question that replaces the round budget, measured on all 117 LRA rows with
`AXEYUM_QPROBE=1` (`fixpoint-shape.sh`):

    ground-set size at fixpoint:  0 -> 103 rows    12 -> 14 rows
    EMPTY e-graph (ground=0):     103 of 117  (88.0 %)
    >= 1 triggerless universal:    63 of 117  (53.8 %)

**88 % of the LRA family fixpoints with an EMPTY e-graph.** 98 of the 117 are
`LRA/2010-Monniaux-QE`, whose files are a ten-deep alternating `∀∃∀∃…` prefix
over the reals **with no free constant anywhere** — there is not one ground term
for a trigger to match. e-matching is structurally the wrong engine for them;
`q:fourier-motzkin` does not appear in their route trail at all. The remaining
19 are `scholl-smt08`, the same QE shape.

No round count, and no ground-term ceiling, expresses a fix for a query with
nothing to instantiate over.

## Decision

1. **Do not raise `MAX_EXTENDED_INSTANTIATION_ROUNDS`.** It is 512 and no file
   in the ranked family approaches it. The measurement, not the value, is this
   ADR's deliverable.
2. **Each loop exit records which stopping condition fired**, and the give-up
   detail names it (`InstantiationLoopExit`). The `RoundCeiling` arm keeps the
   historical string unchanged, because the historical string was accurate for
   exactly that exit; `Fixpoint` and `GrowthHeadroom` say what they are and
   carry the rounds entered.
3. **`AXEYUM_QINST_ROUNDS`, `AXEYUM_QINST_CADENCE` and
   `AXEYUM_QINST_ROUND_HEADROOM` are levers** over the three round constants,
   wired through `cap_lever!`: unset is the shipped value byte for byte, a
   malformed value panics naming the variable, and each is registered in
   `config_registry` as an `env_override` so `--trace`'s `; config` line shows
   it. The next lane re-asks this question in one environment variable.
4. **A ranked give-up string may not be classified by its wording when more
   than one exit can emit it.** ADR-1950 requires the remaining-budget
   distribution beside a `ROUND`/`CLOCK` claim; this adds that the *producer*
   must distinguish the exits it merges, because a distribution cannot separate
   ROUND from SHAPE — both leave the clock untouched.
5. **A control population must be shown to REACH the code under test**, with
   the number. A quantifier-free division is not a control for a quantifier
   lever, however well we decide it.

## Consequences

- **ADR-1950's counts stand; its `kind` column for this family does not.** The
  177 rows are real and they are the largest family on the board. 167 of them
  are `SHAPE`, not `ROUND`. ADR-1950 anticipated exactly this correction
  mechanism — "a family mislabelled `ROUND` … gets reclassified **by the data**"
  — and this is that reclassification, arriving through a channel it did not
  have: the producer, not the distribution.
- **The next lever for this family is named and sized.** 103 of 117 LRA rows
  fixpoint with `ground = 0`; the population is `2010-Monniaux-QE` +
  `scholl-smt08`, both quantifier-elimination corpora. The candidate is real QE
  / a real-model MBQI, not instantiation at all. Nobody should spend another
  lane-hour on instance selection for this population.
- **The BV and AUFLIA remainders are separate.** BV's 10 rows fixpoint with
  non-trivial ground sets at up to 65 rounds, and AUFLIA's 48 split 40 SHAPE /
  4 CLOCK / 4 other. Those are not the LRA finding and must not inherit it.
- **The three levers cost nothing when unset** — an atomic load at a comparison
  site — and their defaults are pinned as LITERALS as well as against the
  constants, because an A/B that edits both still satisfies "the accessor equals
  its constant".
- **The reported REASON changed for two of three exits; no verdict did.** 117
  pinned LRA rows: 117 `unknown` before, 117 `unknown` after, and the four-arm
  sweep shows 0 conflicting decided verdicts across every arm.

## Alternatives considered

- **Raise the ceiling anyway, since it is free.** It is not free of meaning: a
  bound nobody reaches, raised, becomes a bound nobody can reason about, and the
  next census would still rank the same string. Worse, `512` is the "never hang"
  backstop for a configuration with no wall clock, which is the one property of
  it that is not a preference.
- **Delete the round ceiling.** Same objection, harder: the loop must terminate
  when neither the clock nor the ground cap is configured.
- **Lower the ceiling, since nothing uses it.** Tempting and wrong. The
  truncation test in `qinst_egraph` shows a six-link successor chain needs six
  rounds and an AUFLIA row entered 99; a ceiling chosen from this population
  would be a bound fitted to the files that do NOT reach it.
- **Fix only the give-up strings and leave the levers out.** That answers the
  classification question and leaves the A/B question open, which is how a
  "someone should measure this" survives another six ADRs.
- **Report the 177 as `UNCLASSIFIED` instead.** Wrong direction, the same one
  ADR-1950 declines: these rows ran to the end of their dispatch and carry no
  open segment, so they are rankable. The problem was never that they should not
  be ranked — it is what the ranking claimed, and the fix is to make the
  producer say it.
