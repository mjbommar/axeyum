# GROUND-DECIDE — pre-registration

Branch base: `git merge-base main HEAD` = `4436e9cd5c912c590fa5a2dbfa4c73b8065b3623`,
which **is** local `main`'s HEAD at the time this lane branched.

Written **before** any lever is built or any A/B is run. The census in §1 is a
re-analysis of data another lane already committed
(`bench-results/round-head-20260914/census/`), so it is **observational, not an
experiment** — it is reported with its method rather than pre-registered, and
this file says so rather than pretending otherwise.

ADR number reserved: **ADR-2020**.

## 0. What is already closed — not re-tested here

[ADR-1995] budget policy (0 of 87), [ADR-1956] round ceiling (0 of 177),
[ADR-2005] instance reach (e-matching alone decides 111 of 115),
[ADR-2000] front-door refusal, [ADR-2015] the round head (1 of 209 exits).
This lane targets the component all five point at: **the quantifier-free ground
checker that is handed the instantiated conjunction**.

Two further hypotheses are closed by in-tree evidence found during §1 and are
**not** re-tested:

- **"add only the violated pairs" in the lazy function-consistency CEGAR loop.**
  Measured and rejected before commit on 2026-06-26 (`42fc03e6e`): the narrow
  policy reached **0** UF candidates and timed out after 42 support-conflict
  rounds where all-equal batching reached 1 candidate and 6 lemmas. Any lever
  here must **preserve batching** and bound only its *size*.

## 1. Census method (observational — stated, not pre-registered)

Denominator: the **127 still-failing rows** of [ADR-2015]'s 129 winnable
`UFLIA`/`UFNIA` rows (the 2 rows `main` sometimes decides are excluded, as
[ADR-2015] did).

Records inside `r1_lines`/`r2_lines` are separated by `;QPROBE`, **not** by a
bare `;` — the `why=` detail itself contains `;`. Splitting on `;` truncates the
largest bucket and hides its nested reason; this lane made that mistake first
and caught it by reading the raw line. A `why=` string may additionally **wrap**
another (`the reduced solve's own reason was [Kind] …`) or **append** one after a
stats parenthetical (`…): <inner>`). The census reports the **innermost** cause
and publishes the outer-string census beside it so the difference is visible.

## 2. Pre-registered decision rules for any lever

**R1 — split before censusing.** Any give-up string that covers more than one
call site, or wraps another reason, is split and re-censused before it is used
to size anything. A bucket that was not split is reported as `UNSPLIT`, never
absorbed.

**R2 — publish every cause with the denominator, zeros included.** An omitted
row and a zero row read the same in a table and only one is a measurement.

**R3 — no conversion RATE is pre-registered.** A rate measured on the mixed
blocker population does not transfer to a subset of it ([ADR-1980] missed by 3x
that way). Go/no-go is a **count** on the lever's own population.

**R4 — go/no-go.** Build and ship a lever only if, on a per-file interleaved
A/B over the lane's target division, it moves **≥ 6 rows** from `unknown` to a
decided verdict, **net**, and **every** moved row is STABLE-GAIN under R5.
6 is chosen as **twice** [ADR-2015]'s measured same-arm noise band on this
family (2 files at fixed code; [ADR-2005] independently measured +1/−2/+0).
Below 6, the lane ships **OFF** and reports a clean negative.

**R5 — 3x per arm on every moved row.** Each row that moves is re-run **3 times
per arm** and labelled STABLE-GAIN / STABLE-LOSS / UNSTABLE / FLIP. An UNSTABLE
row is **not** counted toward R4.

**R6 — noise floor on a whole division, same arm, repeated.** Published even
though R5 exists, because R5 only covers rows that moved.

**R7 — interleaved per-file A/B, ONE binary, two env values.** Both arms back to
back on the same file on the same pinned core, order alternating per file. The
runner header states the lever's **polarity** explicitly (which env value is the
shipped arm). Shard configuration is **held fixed across arms** and named in the
report.

**R8 — a control division that must not move**, reported even at zero, and shown
**non-vacuous** by naming the route that binds its undecided rows.

**R9 — every new verdict against independent authorities**, with the
**comparable denominator printed beside any zero**, and no-opinion counts kept
separate from agreements ([ADR-1957]). `z3 -T:` takes SECONDS, `cvc5 --tlimit`
MILLISECONDS.

**R10 — a sat-side reference control is vacuous** ([ADR-1976]). Any rewrite is
controlled on the **unsat** half; for `sat`, model replay against the original
assertions is the evidence, and [ADR-2010]'s limit (the front door's replay does
not cover parser-level rewrites) is respected.

**R11 — Wilson intervals** for every small-n proportion. Never normal.

**R12 — the A/B measures THIS BRANCH.** The report states that and predicts the
post-merge value with its reason.

**R13 — binary freshness is licensed by `find crates -name '*.rs' -newer $BIN`
returning nothing**, not by the build's exit status. Snapshot/target paths are
reused across sessions.

**R14 — any check not finished is reported as "did not run"**, never as a zero
and never as an intention.

## 3. Pre-registered prediction

Recorded so it can be wrong.

The census (§1) shows **70.5 %** of the 78 declining replays are **cheap
refusals by an admission bound**, not exhausted clocks. Refusals are policy, so
they are in principle movable. But every bound in the chain was calibrated
against a *downstream* failure (an unbounded solve, a stack overflow), so
raising one is predicted to **convert refusals into timeouts rather than into
verdicts** on most rows.

**Prediction: a bound-raising lever moves fewer than 6 rows and this lane ships
OFF.** The most likely exception is the lazy function-consistency lemma flood
(uncapped, justified at 6–23 pairs, observed at 17,750), where a **per-round
batch cap** bounds the skeleton without reverting to the policy already rejected
in `42fc03e6e`.

[ADR-1956]: ../../docs/research/09-decisions/adr-1956-do-not-raise-the-instantiation-round-ceiling-zero-of-the-177-rows-reach-it.md
[ADR-1957]: ../../docs/research/09-decisions/adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-1976]: ../../docs/research/09-decisions/adr-1976-qf-nia-is-model-bound-adr-1937-took-the-sat-half-and-the-eager-split-is-worth-four.md
[ADR-1980]: ../../docs/research/09-decisions/adr-1980-the-cheap-check-was-the-whole-target-a-dispatch-decline-not-a-datatype-capability.md
[ADR-1995]: ../../docs/research/09-decisions/adr-1995-the-instantiation-loops-verdict-is-not-monotone-in-its-budget.md
[ADR-2000]: ../../docs/research/09-decisions/adr-2000-the-front-door-refusal-was-not-the-binding-constraint.md
[ADR-2005]: ../../docs/research/09-decisions/adr-2005-the-instances-are-e-matchable-and-we-already-build-them.md
[ADR-2010]: ../../docs/research/09-decisions/adr-2010-the-sat-side-replay-cannot-see-the-parser.md
[ADR-2015]: ../../docs/research/09-decisions/adr-2015-the-round-head-is-a-symptom-the-ground-checker-is-the-wall.md
