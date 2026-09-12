# QF_NIA is not a width problem

Lane `qf-nia-width`, 2026-09-12. Measured at `57f1363e0`.
Decision: [ADR-1921](../09-decisions/adr-1921-the-int-blast-width-escalation-is-measured-and-not-shipped.md).

## The question

`docs/plan/GAP-LOG-2026-09-12.md` sized QF_NIA at **+103** against z3 (we decide
41/200, z3 144, cvc5 87) and said **half the sample is one cap**: of 14 winnable
files classified, **7** gave `bounded integer model overflowed at width 32`. The
ladder bit-blasts integers at `DEFAULT_INT_WIDTH = 32`, finds a bit-vector
model, reads it back as exact integers, replays it against the original
assertions, finds it **false**, and refuses.

That refusal is correct — it is the alternative to shipping a wrong `sat`. The
question is what to do instead of giving up, and the textbook answer is an
escalating width: try 32, and on overflow retry at 64, then 128.

Three things had to be established, and all three are measured below.

1. Does the width explain the gap? The 14-file sample is a sample.
2. Are those files decidable at a larger width at all?
3. What does escalation cost the files that already decide?

**Answers: 21%, no, and nothing.** The escalation decides **0 of 110** winnable
files at the competition budget and **0 additional files of 23** at six times
the budget. It is not shipped.

## Method

**Population.** Not a sample: **all 110** QF_NIA files in
`bench-results/session-20260911-smtlib/head-to-head/QF_NIA.tsv` that we answer
`unknown` and at least one of z3/cvc5 decides. (41 we decide, 110 winnable, 49
nobody decides.) Two further populations for the cost question: the **41**
QF_NIA files we already decide, and **177** already-decided files sampled every
fourth from QF_LIA, QF_UFLIA, QF_IDL, QF_NRA and QF_ABV — the integer-bearing
divisions a wider default would tax.

**The two arms are one binary.** `INT_BLAST_ESCALATION_MAX_WIDTH` ships equal to
`INT_BLAST_MAX_WIDTH`, so the shipped ladder is `[4..16, 24, 32]` exactly as
before; `AXEYUM_INT_BLAST_ESCALATION_MAX_WIDTH=64` appends `40, 48, 56, 64`.
Both arms are therefore the same `target/release/examples/smtcomp_cli`, pinned
to a scratchpad copy so a concurrent lane's rebuild could not swap it mid-sweep.
There is no cross-binary, cross-commit or cross-host confound to argue about.

**Interleaving.** Both arms of a file run back to back inside one worker, so the
pair shares ambient load, and the arm **order alternates by file index**, so a
load trend cannot systematically favour one arm. Three workers on s4, which was
carrying another lane's census throughout — exactly the condition this design is
for. Budget `--timeout-ms 24000` (the competition budget), hard-killed at 45 s.

## Result 1 — the width explains 21% of the gap, not 50%

All 110 winnable files, baseline arm, classified by their `; give-up` line:

| reason | files | share |
|---|---:|---:|
| preprocessed dispatch timeout after reduced solve | 41 | 37% |
| estimated CNF clauses exceeds budget | 30 | 27% |
| **bounded integer model overflowed at width 32** | **23** | **21%** |
| watchdog fired before the worker thread returned | 12 | 11% |
| integer constant does not fit the bounded width 32 | 2 | 2% |
| `distinct` pairwise-expansion limit | 1 | 1% |
| no model within the bounded integer width 32 | 1 | 1% |

Counting every width-shaped reason together — the overflowed replay, the
out-of-range constant, and the in-range `unsat` — the width family is **26 of
110, 24%**. The gap log's `7 of 14` (50%) does not survive the full population.

The class that grew instead is the **CNF clause budget**: 30 files, where the
14-file sample found one. That refusal was already measured by lane
`agent-nia-diagnosis` (`docs/plan/notes/118-nia-diagnosis.md`): lifting the gate
by the estimator's own measured 9.4x over-approximation decides **0 of 49**.

Two caveats on the two load-sensitive rows, stated so nobody quotes them as
load-independent: `Timeout` (41) and `Watchdog` (12) are inflated by the
three-way parallelism, and each inflation can only move files **out of** the
width class, never into it. So 23 is a floor for the width class and 41 a
ceiling for the timeout class. A second, independent sweep of the same 110 files
at four-way parallelism gave 20 / 48 / 8 for overflow / timeout / watchdog —
the same picture with the load-sensitive rows moving and the width row barely
moving.

## Result 2 — escalating to 64 decides nothing

Interleaved A/B, 110 winnable files, 220 solves:

| | baseline (ladder tops at 32) | escalation (tops at 64) |
|---|---:|---:|
| decided | **0** | **0** |
| gains | — | **0** |
| losses | — | **0** |
| `sat`/`unsat` disagreements between arms | — | **0** |
| wall total | 2,242 s | 2,346 s (**+4.6%**) |

What the escalation *does* do is destroy the diagnosis. With the tail armed the
23 precise `bounded integer model overflowed at width 32` lines become
`Timeout` (41 → 59) and `Watchdog` (12 → 17): the wider rungs consume the
remaining budget and the file gives up with a reason that names nothing. An
escalation that decides nothing and blinds the census is worse than no
escalation.

### Is 24 s simply too short for a width-64 blast?

No. The **23 width-family files re-run at 150 s** — 6.25x the competition
budget, hard-killed at 200 s:

| | escalation, 150 s | baseline, 150 s |
|---|---:|---:|
| decided | 3 (2 `sat`, 1 `unsat`) | 3 (2 `sat`, 1 `unsat`) |

**The same three files, with the same three verdicts, in both arms** — verified
by a full diff of the per-file verdict columns
(`bench-results/qf-nia-width-20260912/deep-{escalation,baseline}-150s.tsv`).
Those three are a clock problem, not a width problem; the escalation contributed
**zero** of them. Without the baseline control the probe would have read as
"+3 files from escalation", which is why the control exists.

And of the 20 that stayed `unknown`, **14 report `overflowed at width 64`** —
they climbed the whole tail and the replay still failed at the top rung, which is
also the blaster's hard ceiling.

## Result 3 — the cost to what already works is not measurable

Interleaved A/B on already-decided files. Zero losses and zero disagreements in
both populations; the timing is measured only on files **both** arms decided, so
a flake cannot enter the ratio.

| population | files | losses | disagreements | wall ratio (both-decided) | worst single file |
|---|---:|---:|---:|---:|---|
| QF_NIA already-decided | 41 | **0** | **0** | 0.984 (38 files) | +1.7 s |
| QF_LIA/UFLIA/IDL/NRA/ABV sample | 177 | **0** | **0** | 0.982 (172 files) | +8.2 s |

Both ratios are below 1, which is noise, not a speed-up. That is the expected
shape and it is structural rather than lucky: the ladder returns on its **first**
replay-checked `Sat`, which by construction happens at a width at or below the
historical single width, so a query the ladder decides never builds a tail rung.
`the_armed_tail_only_appends_above_the_historical_width` in `auto.rs` asserts
that prefix property directly.

Both populations also produced apparent "gains" (3 and 3) that are **load
flakes, not escalation wins** — the baseline arm timed out on a file the
escalation arm decided in 6–22 s, on files whose decision happens before any
tail rung exists. They are reported here rather than netted out, because a
measurement that silently absorbs its own noise into the treatment effect is how
a +6 gets claimed for a change that cannot produce one.

## Soundness

426 verdicts were produced across the three A/B populations. Every one was
cross-checked against two independent authorities keyed by **full path**:

- the benchmark's own `(set-info :status …)`, read from the file text — 424 of
  426 verdicts had one (the other 2 declare `unknown`);
- the per-division reference solver's verdict from
  `bench-results/session-20260911-smtlib/board/<div>.tsv` — 393 comparisons.

**0 disagreements. 0 verdicts with no authority.** The checker was verified to
be able to fail: flipping every verdict produces **817** disagreements.

The first version of that checker keyed the reference by **basename** and
reported 24 disagreements — all of them `RC-03.smt2`-shaped collisions between
different benchmark directories. It was a checker manufacturing its own finding,
and it is recorded here because the corrected number would otherwise look like
it never had a competitor.

## Why widening does not help: the wraparound is not in the multiplier

`blast_integers` already emits a **no-overflow side constraint for every
`int_mul`** (`crates/axeyum-rewrite/src/int_blast.rs`,
`mul_no_overflow_constraint`): the product is sign-extended to `2·width` and
required to equal the true wide product, so the SAT search is forced onto
non-wrapping models of every multiplication at every rung.

`IntAdd`, `IntSub`, `IntNeg` and the Euclidean `IntDiv`/`IntMod` construction get
**no such constraint**. So a replay that fails after the mul constraints have
been satisfied is, by construction, an **additive** wraparound — a sum or
difference that left the signed range, not a product that did. That is consistent
with the measurement: 14 files climb to width 64 and overflow there too, because
widening enlarges the range the search may wander into exactly as fast as it
enlarges the range a genuine witness may live in, while the one operator whose
overflow was actually pinned down was already pinned at 32.

The hypothesis this leaves standing is an **additive** no-overflow constraint of
the same shape as the multiplicative one — sound by the same argument, since more
restricting constraints can only shrink the bit-vector model set, `sat` remains
anchored by exact-integer replay, and an in-range `unsat` is already reported as
`unknown`. That is **not measured here** and is a hypothesis, not a result.

## What is not reachable at all

128-bit escalation cannot be tried without other work.
`axeyum_rewrite::MAX_INT_BLAST_WIDTH` is **64**, and `blast_integers` answers a
wider request with `IntBlastError::InvalidWidth`, which every caller maps to a
hard `SolverError` — not to `unknown`. The ceiling is the `i128` model
read-back, so lifting it means a bigint read-back through the whole projection
path, not a constant change. The ladder clamps rather than trusting the lever,
and `the_tail_is_clamped_to_what_the_blaster_accepts` feeds every rung the ladder
can emit to the real blaster rather than asserting the number.

## Provenance

- Corpus: `/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/`
- File list: the 200-file head-to-head sample,
  `bench-results/session-20260911-smtlib/head-to-head/QF_NIA.tsv`
- Per-file data: `bench-results/qf-nia-width-20260912/`
- Host s4, three workers, ambient load from a concurrent lane's census
  throughout; both arms of every pair share that load by construction.
