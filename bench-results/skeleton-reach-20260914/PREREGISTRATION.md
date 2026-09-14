# SKELETON-REACH — pre-registered rules and predictions

**Committed before any measurement in this lane.** Branch base:
`git merge-base main HEAD` is `b32867a21b37dcb0f12c75d81557c8eabf6b25a4`,
which **is** local `main`'s HEAD.

Lane: `skeleton-reach`. Reserved ADR number **2040**.

## What this lane asks

[ADR-2025] shipped the one lever that worked this week: a `q:bool-skeleton`
rung that abstracts every maximal quantified subformula to one opaque Boolean
atom and refutes the quantifier-free remainder. It is worth **+12 on `UFLIA`**
on merged `main`. It left two axes open, and this lane takes both:

1. **Why does the ladder stop at `fd:parse` on `UFNIA`?** Four of its fifteen
   skeleton-unsat rows were classified `RUNG-NEVER-REACHED`, all `UFNIA`.
2. **Where else does the skeleton shape exist, and why did only `UFLIA` move?**
   Per division, is the shape *absent*, *present but not reached*, or *present
   and reached but not refutable*?

## Rules

**R1 — no conversion RATE is pre-registered, and none is inherited.**
[ADR-2025]'s 8/9 and 15/129 were measured on populations selected by outcome
and on one division. Neither transfers. Any rate this lane reports is measured
on the population it is reported for. ([ADR-1980]'s bracket missed 3x this way;
[ADR-2030]'s 21.8 % was 10.2 % at row level.)

**R2 — every bucket is published with its denominator, zeros included, and
NOT-MEASURED is a bucket of its own.** A row the instrument could not process
is never counted as a negative.

**R3 — the `fd:parse` label is not trusted until it is split.** Before any
bucket is reported, it must be shown by an observation INDEPENDENT of the label
whether the bucket is one cause or several: exit code, stderr text, wall clock,
and the presence or absence of every other route entry are each recorded per
row. ([ADR-2020]'s census separator was `;QPROBE` not a bare `;` and truncated
its largest bucket; [ADR-2015] found four loop exits printing no line at all;
[ADR-2030] needed an ordered probe to distinguish "never reached the site" from
"reached it and came out the other side".) If the largest bucket is a single
string covering more than one emit site, it is split before it is sized.

**R4 — the population is re-derived on the current tree, in the same run that
censuses it.** [ADR-2035] found 8 of 22 censused "declining" files were decided
anyway. No row is inherited from a committed list as a *verdict*; committed
lists are used only to name files.

**R5 — a "shape absent" claim needs a positive control in the same sweep.**
The static abstractor must report the shape PRESENT on `UFLIA`, where it is
known present, in the same sweep that reports it absent elsewhere. An empty
result from an instrument never shown to work on this corpus is not a negative.

**R6 — new verdicts are checked against three independent authorities**
(declared `:status`, z3, cvc5) with the **comparable denominator printed beside
any zero** ([ADR-1957]). `z3 -T:` is SECONDS, `cvc5 --tlimit` is MILLISECONDS.
No-opinion counts are reported separately from agreements.

**R7 — Wilson 95 % for every small-n proportion.**

**R8 — if a lever is built, the A/B is interleaved per file**, both arms back
to back on the same pinned core with the order alternating, **one binary and
two env values, never two builds**. Polarity is stated in the runner header.
Every moved row is re-run **3x per arm** and labelled STABLE-GAIN /
STABLE-LOSS / UNSTABLE / FLIP. A **noise floor** is measured on one whole
division at byte-identical configuration, and the band is **assumed non-zero
until measured**. A **control division that must not move** is reported at zero
AND shown non-vacuous: the route binding its undecided rows is named and the
rung is shown to actually execute there. ([ADR-2035]'s control was vacuous.)

**R9 — the ship rule, fixed now so the rule decides and not the author.**
A change ships ON only if, on its target division, it moves **≥ 5 rows net**
with **0 losses, 0 flips, every moved row STABLE-GAIN**, and **0 authority
disagreements at a full comparable denominator**. Fewer than 5 net, or any
loss, flip or disagreement: it does not ship ON. A measured zero is a complete
result and is published as one.

**R10 — any check not finished is reported as "did not run"**, never as a
result and never as an intention.

**R11 — the A/B measures THIS BRANCH.** The post-merge value is predicted
explicitly, with the reason, and the shipped default is *verified* rather than
predicted if anything ships.

**R12 — binary freshness is licensed by `find -newer` over `crates/**/*.rs`,
never by a build's exit status.** Snapshot and target paths here are reused.

**R13 — the abstractor's own liveness is a measured column.** `occ=` and
`atoms=` are recorded per row. `occ=0` is NOT MEASURED (the file has no
quantified subformula the text-level tool can see), never a negative.

**R14 — no waiter greps for a process by a pattern its own command line
contains.** Watch the artifact.

## Predictions

Registered so the measurement can contradict them.

**P1 — the `fd:parse` bucket on `UFNIA` is NOT one cause.** It covers at least
two distinct emit conditions, and at least one of them is not a parse failure
at all. Predicted split: the larger part is a *dispatch-level* stop whose trail
was never mirrored, not an ingest failure. Confidence: moderate — `auto.rs`
already records having found exactly this shape on 70 `QF_DT` files in
September, where "the route trail for every one of them contained a single
`fd:parse` probe" while a route had in fact declined.

**P2 — the `fd:parse` bucket on `UFNIA` is between 5 and 60 of the 147
undecided rows.** Deliberately wide, because nothing in this repository has
sized it.

**P3 — the skeleton shape is PRESENT (≥ 1 skeleton-unsat row) on at most two
divisions besides `UFLIA`, and on `QF_NIA` it is absent by construction**
(quantifier-free: every row must be `occ=0`, which is also this sweep's
negative control on the abstractor).

**P4 — `UFLIA`'s remaining undecided rows still contain skeleton-unsat files**
that the shipped rung does not convert; i.e. the +12 did not exhaust the shape
on its own division.

**P5 — the total additional convertible rows across all six non-`UFLIA` Tier 1
divisions is under 15.** If it is over 15, the "extend it" idea is much bigger
than the brief assumes; if it is 0, the idea is closed.

## Population

`bench-results/tier1-current-20260914/*.tsv` — 200 files per division, 7 Tier 1
divisions, measured on `78ca906c2` (the commit before this lane's base, which
added only those TSVs). Used to NAME files. Verdicts are re-derived (R4).

Corpus root: `/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental`.

## Compute

At most **8 pinned pairs**: s5 cores `{1,3,5,7}` and s6 cores `{1,3,5,7}`.
Divisions run serially within a shard.

[ADR-1957]: ../../docs/research/09-decisions/adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-1980]: ../../docs/research/09-decisions/adr-1980-the-cheap-check-was-the-whole-target-a-dispatch-decline-not-a-datatype-capability.md
[ADR-2015]: ../../docs/research/09-decisions/adr-2015-the-round-head-is-a-symptom-the-ground-checker-is-the-wall.md
[ADR-2020]: ../../docs/research/09-decisions/adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
[ADR-2025]: ../../docs/research/09-decisions/adr-2025-the-refutation-was-available-before-instantiating-and-we-dropped-the-assertion-carrying-it.md
[ADR-2030]: ../../docs/research/09-decisions/adr-2030-the-fallback-was-already-offered-and-the-lemma-batch-is-the-whole-set-at-once.md
[ADR-2035]: ../../docs/research/09-decisions/adr-2035-two-populations-reach-one-boundary-and-a-round-cap-can-convert-neither.md
