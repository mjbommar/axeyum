# ZERO-INST — pre-registration

Branch base: `git merge-base main HEAD` =
`37ff18b568f414dc21e151c3a53292c40fb7fa71`, which **is** local `main`'s HEAD
at the time this lane branched.

ADR number reserved: **ADR-2025**.

Written **before** any lever exists and before any A/B has been run. The
reference measurement in §1 was taken first, is **observational, not an
experiment**, and is reported with its method rather than pre-registered —
this file says so rather than pretending otherwise.

## 0. What is already closed — not re-tested here

Six explanations for the `UFLIA`/`UFNIA` gap are measured and closed, and
this lane re-tests **none** of them:

| | closed by | result |
|---|---|---|
| budget policy | [ADR-1995] | 0 of 87 |
| round ceiling | [ADR-1956] | 0 of 177 |
| instance reach | [ADR-2005] | e-matching alone gets 97 % |
| front-door refusal | [ADR-2000] | blocked at 25x budget |
| the round head | [ADR-2015] | 1 of 209 exits |
| the ground checker's bounds | [ADR-2020] | lever 0 of 129 |

[ADR-2020] closed the last of these on a bound-raising lever and left one
measurement unfollowed: on the 22 files where our ground checker refuses,
cvc5 refuted 21 at a median 70 ms, **nine of them with ZERO instantiation
tuples**, and **eight of those nine are files where we flooded to the 8,192
ground admission cap**. This lane starts there, on a **prior** question to
the five closed ones: *is the refutation already available before
instantiating at all, and do we ever look?*

## 1. Reference measurement (observational — stated, not pre-registered)

Already run and committed (`f370cfdde`) before this file. Method and its
limits:

- The population is the **9** files of [ADR-2020]'s zero-instantiation row,
  derived from its committed
  `ref/cvc5-on-our-skeleton-refusals.tsv` — not re-derived, so it inherits
  that measurement's flag-liveness argument.
- Every probe runs against the **corpus file**, never a variant, except
  where the variant IS the subject.
- `set-info` is dropped from every constructed subset. These benchmarks
  carry `(set-info :status unsat)` and cvc5 turns a correct `sat` on a
  subset into `(error ...)` with a nonzero exit. The first singleton scan
  counted 499 of 589 such verdicts as **errors**; they were `sat` results.
- Every cvc5 option used as a mechanism control is **validated
  individually** and shown to still produce a verdict. cvc5 negates booleans
  as `--no-opt`; the `--opt=false` form is REFUSED, and the first run of
  `strategy-isolate.sh` used it and returned `NONE` in both mechanism
  columns.
- The Boolean-skeleton probe measures the **benchmark**, not cvc5, and is
  confirmed by **two independent solvers**. Abstraction only weakens, so
  only the direction `skeleton unsat ⟹ original unsat` is claimed.

## 2. Pre-registered decision rules for any lever

**R1 — split before censusing.** Any give-up string covering more than one
call site, or wrapping another reason, is split and re-censused before it is
used to size anything. A bucket that was not split is reported as `UNSPLIT`,
never absorbed. ([ADR-2020] walked into this with `;QPROBE` and caught it;
the same trap is assumed present until disproved.)

**R2 — publish every cause with its denominator, zeros included.**

**R3 — no conversion RATE is pre-registered.** The reference measurement
found 8 of 9 skeleton-unsat on a population selected **because** cvc5
refuted it with zero instantiations. That is a rate on a subset chosen by
its outcome, and it does **not** transfer to the 129. ([ADR-1980] missed by
3x this way.) Go/no-go is a **count** measured on the lever's own
population.

**R4 — go/no-go.** Ship a lever only if, on a per-file interleaved A/B over
`UFLIA`+`UFNIA`, it moves **≥ 6 rows** from `unknown` to a decided verdict,
**net**, and **every** moved row is STABLE-GAIN under R5. 6 is twice
[ADR-2015]'s measured same-arm band on this family and six times
[ADR-2020]'s (1 of 129). Below 6 the lane ships **OFF** and reports a clean
negative.

**R5 — 3x per arm on every moved row**, labelled STABLE-GAIN /
STABLE-LOSS / UNSTABLE / FLIP. An UNSTABLE row does not count toward R4.

**R6 — noise floor on a whole division, same arm, byte-identical
configuration.** Published even though R5 exists, because R5 covers only
rows that moved.

**R7 — interleaved per-file A/B, ONE binary, two env values.** Both arms
back to back on the same file on the same pinned core, order alternating per
file. The runner header states the lever's **polarity** explicitly. Shard
configuration is **held fixed across arms** and named in the report.

**R8 — a control division that must not move**, reported even at zero and
shown **non-vacuous** by naming the route that binds its undecided rows.

**R9 — every new verdict against independent authorities**, with the
**comparable denominator printed beside any zero**, and no-opinion counts
kept separate from agreements ([ADR-1957]). `z3 -T:` takes SECONDS,
`cvc5 --tlimit` MILLISECONDS.

**R10 — soundness is checked on the half where it can fail.** This lever can
only ever produce new **`unsat`** verdicts (a Boolean abstraction is a
weakening: it can be `sat` when the original is `unsat`, never the reverse).
So the failure mode is a **wrong unsat**, and a `sat`-side reference control
is vacuous for it ([ADR-1976]). Every new `unsat` is checked against **three**
authorities: the benchmark's own `:status`, z3, and cvc5. **A single
disagreement, from any authority, is a P0 and the lever does not ship** —
regardless of R4.

**R11 — Wilson intervals** for every small-n proportion. Never normal.

**R12 — the A/B measures THIS BRANCH.** The report says so and predicts the
post-merge value with its reason.

**R13 — binary freshness is licensed by `find crates -name '*.rs' -newer
$BIN` returning nothing**, not by a build's exit status. Snapshot paths are
reused; [ADR-2020]'s guard fired twice.

**R14 — any check not finished is reported as "did not run"**, never as a
zero and never as an intention.

**R15 — the abstraction's own liveness is a measured column, not an
assumption.** Any run in which zero quantified occurrences were abstracted
has produced the original file back, and its `unsat` means nothing. The
abstractor exits nonzero in that case and the row is recorded as
`ABSTRACT-FAIL`.

## 3. Pre-registered prediction

Recorded so it can be wrong.

The reference measurement says the refutation of 8 of 9 files is available
in the Boolean skeleton, before any instantiation. Two things can still make
a lever worth zero, and both are predicted to bite partially:

1. **We may already do this and it may already fire**, in which case the
   population is not reachable by adding the check, and the finding is about
   why the existing check does not fire.
2. **The 9 are a subset selected by cvc5's outcome.** The fraction of the
   **129** whose skeleton is unsat is the number that matters, and R3
   forbids predicting it from 8/9.

**Prediction: the skeleton-unsat fraction of the 129 is well below 8/9, and
a pre-instantiation skeleton check moves a NONZERO but SMALL number of
rows — my point estimate is between 4 and 12, i.e. straddling R4's
threshold of 6.** If it lands below 6 the lane ships OFF, and that is a
complete result.

The secondary prediction is about **cost**, not verdicts: the skeleton query
is built from the file's own structure rather than from 8,192 instantiated
ground terms, so if it fires at all it should fire in tens of milliseconds
and the arms' wall clocks should be indistinguishable. A lever that costs
measurable time on files it does not decide is a worse trade than its row
count suggests, and the wall-clock ratio is reported either way.

[ADR-1956]: ../../docs/research/09-decisions/adr-1956-do-not-raise-the-instantiation-round-ceiling-zero-of-the-177-rows-reach-it.md
[ADR-1957]: ../../docs/research/09-decisions/adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-1976]: ../../docs/research/09-decisions/adr-1976-qf-nia-is-model-bound-adr-1937-took-the-sat-half-and-the-eager-split-is-worth-four.md
[ADR-1980]: ../../docs/research/09-decisions/adr-1980-the-cheap-check-was-the-whole-target-a-dispatch-decline-not-a-datatype-capability.md
[ADR-1995]: ../../docs/research/09-decisions/adr-1995-the-instantiation-loops-verdict-is-not-monotone-in-its-budget.md
[ADR-2000]: ../../docs/research/09-decisions/adr-2000-the-front-door-refusal-was-not-the-binding-constraint.md
[ADR-2005]: ../../docs/research/09-decisions/adr-2005-the-instances-are-e-matchable-and-we-already-build-them.md
[ADR-2015]: ../../docs/research/09-decisions/adr-2015-the-round-head-is-a-symptom-the-ground-checker-is-the-wall.md
[ADR-2020]: ../../docs/research/09-decisions/adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
