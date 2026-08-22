# ADR-0542: Repairing a breached held-out partition by whole-family amendment

Status: proposed
Date: 2026-08-22
Index-summary: A held-out family whose blind-evaluation value has been spent moves out of held-out as a whole, recorded in an irreversible amendment ledger and enforced by a fail-closed isolation gate; held-out re-freezes at 57 rows across three families.

## Context

`docs/autogenesis/16-mathlib-frozen-nursery-split-result.md` preregistered 214
Mathlib propositions into train 78 / development 60 / held-out 76. The split key
is `<family>:<statement-shape>` and the declared partition unit is
`whole-family-with-source-review-groups-indivisible`, because a feasibility
census found that joining dependency components with broad statement shapes
collapses all 214 into one component: an equality about Fibonacci recurrence and
an equality about bit operations do not share a proof template merely because
both use `=`. The programme README promises that "every policy improvement is
evaluated against immutable held-out populations."

On 2026-08-21, commit `6e112b4bc` registered
`authoritative-mathlib-nat-gcd-greatest-kernel-capsule-v1` against
`F:ml430-nat-gcd-greatest-0a04214a`, whose partition in the frozen manifest is
**`held-out`**, family `natural-gcd`, proof shape
`natural-gcd:conditional-proposition`. The fact is now `proved` by route
`kernel-lean`.

Nothing detected it, because nothing looked. `scripts/check-autogenesis-nursery.py`
validates the manifest's *internal* integrity — that no family, proof shape,
source group or dependency component crosses a partition boundary — and never
inspects what operations do to the population it describes.
`scripts/validate-autogenesis-operations.py` did not mention partitions at all.
The immutability guarantee existed only in prose, which is the same shape as
this repository's other measured instrument failures: a corpus gate that ran
zero tests for 15 days, a pre-push hook that had never run, 40 of 162 checker
runs exiting 0 on completion alone.

Measured 2026-08-22, the registry named exactly one held-out fact — but through
**eight** distinct references across seven files, including
`executor.input_fact_id` and five plan/admission artifacts. A guard written
against `applicability.fact_ids` alone would have been bypassable the day it was
written.

## Decision

**1. A held-out family whose blind-evaluation value has been spent leaves
held-out as a whole.** `natural-gcd` moves to `development`. Held-out re-freezes
at **57 rows across three families** (`natural-binomial` 20,
`natural-logarithm` 21, `natural-square-root` 16); development becomes 79.

**2. The move is recorded in an amendment ledger, not applied silently.**
`artifacts/autogenesis/mathlib-nursery-split-policy-v1.json` gains an
`amendments` array; each entry carries the family, the direction, the reason,
and a `breach` record naming the fact id, proof shape, operation id, registering
commit and dates. The policy `state` becomes
`preregistered-before-target-outcomes-with-recorded-amendments`, so no reader can
take the artifact for pristine. `scripts/create-autogenesis-mathlib-nursery-split.py`
validates the ledger's shape and copies it into `nursery-v1.json`, so the
manifest a reader actually opens carries the breach.

**3. The spend is irreversible and machine-enforced.** An amended family
assigned to `held-out` is a generator error. A future lane cannot quietly
recycle a spent family back into the blind population.

**4. Isolation is gated from both directions.**
`scripts/check-autogenesis-holdout-isolation.py` fails if any held-out fact is
`proved`/`computed` in the ledger, or if any artifact outside the two files that
*define* the population references a held-out fact id. It walks the JSON
generically rather than checking named fields, and it fails closed on a missing,
unreadable, or empty held-out population.

## Alternatives rejected

**Move only the contaminated proof shape** (`natural-gcd:conditional-proposition`,
9 of the 19 rows). Rejected: the policy's partition unit is the whole family and
`check-autogenesis-nursery.py` enforces
`no-family-may-cross-evaluation-partitions`. This would repair a leakage breach
by violating the anti-leakage invariant — and the family-scoped key exists
precisely because a proof route for one member is evidence about its siblings.

**Delete the 19 rows.** Rejected: it shrinks the evaluation population and hides
the cost. The rows remain fully usable in development, where looking is allowed.

**Leave held-out at 76 and record the contamination in prose.** Rejected: that
is what already failed. The guarantee was prose, and prose is what let a
capsule land against a held-out row for a day without notice.

**Put the guard inside `validate-autogenesis-operations.py`.** Rejected on
operational grounds: that file took 22 commits in the 24 hours this was written,
and a shared-file edit would have collided with an active lane. A standalone
control registered in `check.sh` and the `justfile` is equivalent in force —
`scripts/check-control-registration.sh` is the ratchet that keeps a control from
becoming an orphan.

## Consequences

- Held-out is permanently smaller. **No later work restores it**; that is the
  point of recording the spend rather than absorbing it.
- Train + development rises 138 → 157, so the dispatch census re-sizes. Its
  literal population tripwire moves with it rather than being derived, so an
  unexplained change still stops the census.
- `docs/autogenesis/17-mathlib-nursery-dispatch-baseline.md` records the census
  as it stood on 2026-08-18 (138 candidates). It is a historical result and is
  **not** rewritten; the current census is reported separately.
- The isolation gate is one more control to run, ~1s, in `just check` and
  `scripts/check.sh`.

## Evidence

Mutation-verified 2026-08-22: six guards in the isolation gate deleted one at a
time. Every guard has a nonempty killed-set and no two guards share a member, so
no guard can be deleted with the suite green. Run against pre-repair `HEAD`, the
gate reports `verdict=FAIL` with all eight historical references; against the
repaired tree, `held_out=57|files_scanned=937|settled=0|references=0|verdict=PASS`.

The two generator invariants are likewise controlled: reassigning `natural-gcd`
to held-out and deleting the breach record each produce a distinct named error.

Controls: `scripts/tests/test_check_autogenesis_holdout_isolation.py`,
`scripts/tests/test_create_autogenesis_mathlib_nursery_split.py`.
Plan: `docs/autogenesis/226-production-measurement-and-general-producer-plan.md`.
