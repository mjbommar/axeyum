# Pre-registration: scoring one held-out family

**Lane:** `score-the-blind-population`
**Registered at:** 2026-09-01, against `main` at `7e2f859dccd5fae9c8185ec0f6c3a07d7ec16280`
**Status:** REGISTERED BEFORE ANY TARGET STATEMENT WAS INSPECTED.

This document is committed *first*, on its own, and is what makes the
measurement that follows a blind evaluation rather than a story told
afterwards. Anything not written here was decided after seeing the targets and
must be read as such.

## 1. The deficiency, re-measured independently

Joining `artifacts/autogenesis/nursery-v2-extension.json` (500 preregistered
rows) against `artifacts/facts/`:

| partition   | proved | open |
|-------------|-------:|-----:|
| development |    176 |    4 |
| train       |    125 |    5 |
| **held-out**|  **0** |**190**|

The held-out partition exists to answer one question -- *can this system close
propositions it has never seen?* -- and it has never been cashed. Every other
number this project publishes measures capability against targets we chose.

Two structural facts, measured before designing anything:

* The 190 held-out rows are **19 families of exactly 10 rows each**. Family
  size therefore cannot be a selection criterion.
* `scripts/check-autogenesis-holdout-isolation.py` defines
  `SETTLED = {"proved", "computed"}` and **fails if any held-out fact reaches
  either status** (`held_out=206|settled=0|verdict=PASS` at registration time).
  So the repository as it stands has no mechanism for *deliberately* scoring
  the population it built to be scored: every route to a recorded score is,
  today, a gate breach. This is anticipated here, not discovered later, and
  section 6 says what I will do about it.

## 2. Selection rule

> **Take the lexicographically first held-out family name in
> `nursery-v2-extension.json`, skipping any family from which this lane has
> already been exposed to a statement before this document was committed.**

The rule is stated before its output is acted on, is reproducible from the
manifest by anyone, and depends on no property of the propositions -- in
particular not on how hard they look. It mirrors the population's own
`partition_assignment_rule`, which orders by lexicographic module path
precisely because that is a property of the external source rather than of our
capability.

**Disclosure, and the reason for the exclusion clause.** While inspecting the
manifest's *shape* (before this protocol existed) I printed one entry in full
to learn the field names. That entry was
`F:ml430-int-exists-greatest-of-bdd-540c90cf` (`Int.exists_greatest_of_bdd`),
whose statement I therefore saw in truncated form. Its family is
`descent-and-well-ordering` -- which is the lexicographically first held-out
family. Under the manifest's own `family_leakage` policy a route for one member
is evidence about its siblings, so scoring that family would not be a blind
measurement. It is excluded and recorded here rather than quietly skipped. I
considered no proof route for that row and will not.

Applying the rule with that exclusion yields **`integer-absolute-value`**
(10 rows, fragment `Int`, source modules `Init.Data.Dyadic.Basic`,
`Mathlib.Data.Int.Lemmas`, `Mathlib.Data.Int.Order.*`). I have not read any of
its statements at the time of writing.

## 3. How many rows, and in what order

* **m = 10.** The whole family. The denominator is fixed here and does not move.
* **Attempt order: ascending `candidate_id`.** `candidate_id` is a SHA-256
  digest, so the order is fixed, verifiable, and uncorrelated with difficulty.
  It is not open to me to try the easy ones first.

## 4. Outcomes

Every one of the 10 rows gets exactly one of these, and all 10 are published.

| outcome | meaning |
|---|---|
| **CLOSED** | A declaration admitted by `Kernel::add_declaration` whose rendered type is the fact's `formal.statement`, axiom-free, wired into the prelude, with a `checker_command` verified to exit nonzero against a deliberately wrong target. |
| **REFUSED-UNSTATABLE** | The proposition cannot be *stated* in this kernel because a constituent construction does not exist. The missing construction is named. |
| **REFUSED-DIVERGENT** | Statable, but our definition is structurally different from Mathlib's `def`, so under the mirror-flip criterion the mirror is a different proposition. Requires reading Mathlib's source at the pinned commit `c5ea00351c28e24afc9f0f84379aa41082b1188f` and quoting it; an inherited verdict in either direction is not accepted. |
| **FAILED** | Statable and non-divergent, and I did not produce an admitted proof. What it was blocked on is recorded. |
| **NOT-REACHED** | Budget ran out before the row was attempted. Its position in the attempt order is recorded. |

A **REFUSED-UNSTATABLE** or **REFUSED-DIVERGENT** row is an outcome of the
measurement, not an excuse to substitute another row. **A FAILED row is exactly
as informative as a CLOSED one and is the reason the population exists.**

The headline figure is reported as **n CLOSED of m = 10**, with the full
five-way breakdown beside it. `n / (10 - refusals)` may also be reported as a
secondary figure, clearly labelled as secondary; it is not the headline,
because choosing which denominator to publish after seeing the outcomes is
exactly the move this document exists to prevent.

## 5. Stopping rule

I attempt rows in the order of section 3 and stop at the first of:

1. all 10 rows carry an outcome; or
2. **budget:** when roughly 40% of my remaining tool budget is left, I stop
   proving and spend the remainder on recording the score, the zero-diff proof,
   the ledger updates and the report.

On (2), every unattempted row is published as **NOT-REACHED** with its
position. A partial result recorded is the intended outcome of running out of
budget; a truncated attempt list that is never mentioned is not.

## 6. Spending rules I bind myself to

1. **One family is spent: `integer-absolute-value`.** No other held-out family
   is inspected, dispatched against, or reasoned about.
2. **No already-drawn row changes partition or membership.** I will publish a
   zero-diff over all 716 drawn rows (500 in `nursery-v2-extension.json`, 216
   in `nursery-v1.json`) as a SHA-256 over the sorted `(fact_id, partition)`
   pairs, taken at the registration commit and again at the end, **with a
   negative control** that deliberately flips one row's partition and shows the
   digest moves.
3. **No re-draw, no re-scope, no amendment to improve the score.** If a row is
   unclosable, that is the measurement. Under ADR-0542 any repair to a
   preregistered population is an amendment ledger entry, never a deletion.
4. **On the isolation guard.** I expect closing any row to red
   `check-autogenesis-holdout-isolation.py`, whose `SETTLED` rule forbids it. I
   will **not** weaken that guard to let an unrecorded spend through, and I will
   **not** leave a fact `proved` with the gate red and unmentioned. If rows
   close, the score is recorded in an evaluation-record artifact and the
   guard's amendment -- admitting a settled held-out fact **only** when it is
   named by a committed evaluation record that fixed the protocol before the
   outcome -- is proposed in **ADR-1480**, with the guard still refusing every
   other route in. Whether that amendment is adopted is not mine to decide
   unilaterally; if it is not adopted, the score still stands and the facts stay
   `open` with the evidence attached to the evaluation record.
5. **I will publish the failures in the same detail as the successes**, and I
   will not tune the attempt to make the number look better. A low score
   honestly measured is the correct outcome if that is what the system does.

## 7. What this measurement cannot show

* n = 10 rows from one family is a small sample and the families are not
  interchangeable; this scores `integer-absolute-value`, not "the held-out
  population".
* Scoring is done by an agent with the whole repository available, which is the
  condition the system actually operates under -- it is not a measurement of a
  cold, retrieval-free prover.
* Of the 19 held-out families, this scores **one**. Seventeen are untouched
  and stay fully blind; the eighteenth (`descent-and-well-ordering`) carries a
  one-row exposure disclosed in section 2 and is not scored here.
