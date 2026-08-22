# Held-out partition breach: detection, repair, and the gate that was missing

Date: 2026-08-22

Plan: [`226-production-measurement-and-general-producer-plan.md`](226-production-measurement-and-general-producer-plan.md) (P0)
Decision: [ADR-0542](../research/09-decisions/adr-0542-held-out-partition-breach-repair.md)

## What happened

[Doc 16](16-mathlib-frozen-nursery-split-result.md) preregistered 214 Mathlib
propositions as train 78 / development 60 / held-out 76, and the programme
README promises that "every policy improvement is evaluated against immutable
held-out populations."

On **2026-08-21**, commit `6e112b4bc` registered
`authoritative-mathlib-nat-gcd-greatest-kernel-capsule-v1` against
`F:ml430-nat-gcd-greatest-0a04214a` — `partition: held-out`, family
`natural-gcd`, proof shape `natural-gcd:conditional-proposition`. The fact is
`proved`, route `kernel-lean`.

Detected 2026-08-22 while measuring registry coverage for the plan above. It was
not detected by a gate, because no gate looked:

| Instrument | Why it could not see this |
|---|---|
| `check-autogenesis-nursery.py` | validates the manifest's *internal* integrity — no family, shape, source group or component crosses a partition — and never inspects what operations do to the population |
| `validate-autogenesis-operations.py` | mentioned `partition`, `nursery`, `held-out` **zero times** |
| the README guarantee | prose |

## Blast radius

The split key is `<family>:<statement-shape>` and the declared partition unit is
`whole-family-with-source-review-groups-indivisible`, because a feasibility
census showed that broader keys collapse all 214 propositions into one
component. The family is therefore the unit of contamination, not the row:

```text
held-out before   76   natural-binomial 20 · natural-gcd 19 · natural-logarithm 21 · natural-square-root 16
spent             19   natural-gcd  (25% of the partition)
held-out after    57   natural-binomial 20 · natural-logarithm 21 · natural-square-root 16
```

The registry named one held-out fact, but through **eight references across
seven files** — `applicability.fact_ids[]`, `executor.input_fact_id`, and five
plan/admission artifacts. A guard written against `applicability.fact_ids` alone
would have been bypassable the day it was written.

## Repair

Per ADR-0542: `natural-gcd` moves to `development` **as a whole family**, because
splitting it would repair a leakage breach by violating the anti-leakage
invariant the checker enforces. The move is recorded in an `amendments` ledger in
`mathlib-nursery-split-policy-v1.json` carrying the breach's fact id, operation
id, commit and dates; the policy `state` now reads
`preregistered-before-target-outcomes-with-recorded-amendments`, so the artifact
cannot be mistaken for pristine. An amended family assigned back to `held-out` is
a generator error — **the spend is irreversible by construction**, not by
convention.

Train + development rises 138 → 157. Held-out is permanently smaller; no later
work restores it.

## The gate that now exists

`scripts/check-autogenesis-holdout-isolation.py`, registered in
`scripts/check.sh` and the `justfile`, fails if:

1. any held-out fact is `proved` or `computed` — establishing a held-out
   proposition by **any** route spends it, and the operation registry is only
   one way in; or
2. any artifact outside the two files that *define* the population references a
   held-out fact id — walked generically, so a new schema field cannot silently
   reopen the hole.

It fails closed on a missing, unreadable, or **empty** held-out population. A
guard whose subject has vanished otherwise reports the same "no violations" as a
guard that works.

## Evidence

Against pre-repair `HEAD`:

```text
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=76|files_scanned=937|settled=1|references=7|verdict=FAIL
```

Against the repaired tree:

```text
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=57|files_scanned=937|settled=0|references=0|verdict=PASS
```

Six guards were deleted one at a time. Every guard has a nonempty killed-set and
no two share a member, so none can be removed with the suite green. Two guards
are pinned by two tests each; those are facets of one guard, and the mapping is
recorded in the suite's docstring rather than asserted to be one-to-one when it
is not.

## The census, restated on the repaired population

```text
candidates                                                 157
already-established                                         20
no-exact-authoritative-operation                           137
eligible-for-dispatch                                        0
```

**Zero.** This is the plan's central measurement, now produced by the
programme's own census tool rather than an ad-hoc script: 24 registered
operations cover 23 facts, every one of them already established, and not one
row of the evaluation population has an operation that could be dispatched to
it.

## Downstream consequences, stated rather than absorbed

Moving 19 rows into development re-sizes the open evaluation population from 138
to 157, and three artifacts pinned the old number. Two regenerate from committed
inputs and were regenerated here — the dispatch census and the Autogenesis
baseline, **both of which were already stale at `HEAD`** for an unrelated reason
(the capsule burst of 2026-08-21/22 landed nine operations without regenerating
them).

The third does not regenerate cheaply and is left stale **deliberately and
visibly**:

| Artifact | `mathlib-reflexivity-coverage-v1.json` |
|---|---|
| Capture | `/nas3/.../26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1` |
| Streams | 138, one per train/development row at capture time |
| Now needs | 157 |
| Cost | re-elaboration of the added rows in the pinned Mathlib environment |

`create-autogenesis-reflexivity-coverage-input.py` now selects 157 and its
tripwire says 157, so `check-autogenesis-reflexivity-coverage.py` fails with
`proof-free coverage input no longer regenerates` until the capture is rebuilt.
That gate was **already failing at `HEAD`** (`coverage tooling commit is not in
current history`), so this does not newly break a green gate — but the reason
changed, and pinning the input at 138 to keep the old reason would have been
choosing a quiet gate over a true one.

**Follow-up (unassigned):** rebuild the reflexivity coverage capture over the
157-row population. Until then the reflexivity grammar census describes a
population that no longer exists.

## What this does not fix

The gate stops a held-out fact from being *named*. It does not stop a family
being moved out of held-out in order to work on it — the amendment ledger makes
that visible and irreversible, but visibility is not prevention. If that
pattern appears, the next control is a rate limit on amendments, not a stronger
name check.

Nor does it address why single-target capsules keep being registered at all;
that is P2 of the plan, and it is the measurement, not the guard, that will
say whether it stops.
