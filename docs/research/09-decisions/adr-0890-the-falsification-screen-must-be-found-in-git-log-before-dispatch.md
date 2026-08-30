# ADR-0890: the falsification screen is a receipt committed before dispatch, and ordering is read from git log

Status: accepted
Date: 2026-08-30
Index-summary: D3's counterexample-first screen writes a per-target receipt (git commit + verdict) before a producer may be dispatched at that target; the gate rejects dispatch without a prior clear receipt structurally, and re-checks ordering against real git ancestry when both commits resolve.
Index-status: accepted

Phase: roadmap phase **D3**
Lane: `l3-d3-counterexample-first`
Builds on: [ADR-0752](adr-0752-semantic-controls-are-a-retained-fixture-pack-not-a-review-step.md) (S3, same shape one arrow upstream: theorem statements rather than definitions)

## Context

`docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md`'s D3 phase
sets three exits: a retained false-statement corpus found **before producer
dispatch**; definition mutations that alter at least one reference
observation; and an explicit review obligation for any definition that
cannot be executed. The ordering clause is the one prior phases in this
roadmap do not need to answer, and it is also the one this repository has
gotten wrong before in an adjacent form: `docs/plan/status/README.md`
documents PLAN.md and the ADR index being clobbered because per-lane state
lived in one shared file everyone wrote, and this repository's whole
multi-agent-hygiene section exists because prose ("commit before you check")
does not survive contact with a lane that believes one more check would
complete its report. An ordering rule stated only in prose has the same
failure mode: nothing stops a lane from writing the proof first and the
screen receipt after, and nothing would show that it happened.

This lane's brief cited `docs/research/09-decisions/adr-0870-*.md` and
`artifacts/effort-taxonomy/report.md` as the D0 measurement that chose this
phase. Neither exists anywhere in this tree — checked at `HEAD` and at
`origin/main`, which were the same commit at the time of this ADR, and no
file anywhere mentions either string. This ADR proceeds from the roadmap
document and ADR-0752 instead of fabricating content for the missing
citations; see `docs/plan/status/l3-d3-counterexample-first.md` for the
verification.

## Decision

### 1. A screen produces a receipt, not a log line

`scripts/gen-falsification-screen.py --target <id>` runs one registered
target — a false statement, a definition, or a review obligation — through
the pack and writes `artifacts/falsification/receipts/<id>.json`:

```json
{
  "target_id": "Nat.lor",
  "kind": "definition",
  "verdict": "clear-for-dispatch",
  "detail": { "...": "executed counts, mismatches, mutation results" },
  "git_commit": "<HEAD at screen time>",
  "screened_at": "<UTC ISO timestamp>"
}
```

Three verdicts, one per target kind:

| kind | verdict on success | verdict on failure |
|---|---|---|
| false statement | `reject-before-dispatch` (a counterexample was found) | `NOT-REFUTED` |
| definition | `clear-for-dispatch` (0 mismatches, every mutation moved an observation) | `reject-before-dispatch` |
| review obligation | `review-required`, always | — |

Only `clear-for-dispatch` may back a dispatch. A false statement's *correct*
outcome is still not `clear-for-dispatch` — the whole point of retaining it
is that nothing should ever be dispatched at it, and the receipt schema
enforces that by construction rather than by a reader remembering it.

### 2. Dispatch is refused, structurally, without a prior clear receipt

`--dispatch-demo <id>` (the only writer of
`artifacts/falsification/dispatch-log.jsonl` today, standing in for the
producer-dispatch step D4 will add) reads the receipt file itself before
writing anything, and refuses if it is absent or not `clear-for-dispatch`.
This is enforced twice, deliberately: once here, in the tool that would
write the dispatch record, and again in the gate
(`guard_dispatch_has_receipt`, `guard_dispatch_receipt_is_clear`), because a
future D4 producer-dispatch tool is not obliged to reuse this script and the
gate must not trust that it did.

### 3. Ordering is a property of git log, not of prose

The stronger check: when both the receipt's `git_commit` and the dispatch
entry's `commit` resolve in this repository's history,
`guard_dispatch_ordering` runs

```sh
git merge-base --is-ancestor <receipt-commit> <dispatch-commit>
```

and fails the gate if the receipt commit is **not** an ancestor of (or equal
to) the dispatch commit — i.e. if the screen's own record shows it running
at or after the point work claims to have started from it. `is_ancestor_or_
equal` returns `None`, not `True`, when either SHA does not resolve (a
synthetic test SHA, a shallow clone missing history), and callers never treat
`None` as a pass — the structural check in §2 is what still applies when the
git check cannot run at all.

**Demonstrated, not merely designed, in this lane's own commits.** Every
registered target's receipt was written and committed at `7884497ed`. A demo
dispatch entry for `Nat.lor` was then appended and committed at a strictly
later commit, after this ADR file itself was committed —
`git log --oneline` shows the receipt commit as an ancestor of the dispatch
commit, and `git merge-base --is-ancestor 7884497ed <dispatch-commit>` exits
0. Anyone can re-run that command against this history; it does not depend on
trusting this document.

### 4. The gate re-derives the whole pack every run

`scripts/check-falsification-screen.py` does not read receipts as its source
of truth for whether a false statement is refuted or a definition is
correct — it re-executes `FALSE_STATEMENTS`, `DEFINITIONS`, and
`REVIEW_OBLIGATIONS` from `scripts/falsification_screen_fixtures.py` on every
run, the same discipline ADR-0752 uses for S3's fixture pack. Receipts are
read only for the ordering guards in §2–3. A receipt is evidence that a
screen ran at a point in history; it is never a substitute for re-running the
screen.

### 5. Zero executed cases is always failure, per entry and for the pack

Carried over from ADR-0752 verbatim, applied to both halves of this pack: a
false statement that executed 0 cases, a definition whose reference check
executed 0 cases, or a totals of 0 across either list, fails the gate
regardless of any other guard's outcome.

### 6. A vacuous mutation is reported by name, never silently accepted

A mutation attached to a definition must move at least one observation
relative to the independent reference over the definition's bounded domain.
`guard_mutation_moves_observation` checks this by running the mutation and
comparing, not by trusting a flag the fixture author set. None of the six
mutations in the initial pack are vacuous (each moves at least one
observation on its first divergent point); the guard exists for the one that
eventually will be.

### 7. A mixed-sign Bezout witness pair is a genuine vacuous-witness finding, kept as a record

While building the `Int.bezout_witnesses` fixture, the sign-flip mutation
(`+` instead of `-` in one coefficient update) was tested against four pair
shapes: same-sign `(12, 18)`, mixed-sign `(-12, 18)` and `(12, -18)`, and the
coprime same-sign pair `(7, 5)` against mixed `(-7, 5)`/`(7, -5)`. The mutant
identity **held** at every mixed-sign pair tested — those witnesses do not
discriminate this mutation — and only the same-sign pairs `(12, 18)` and
`(7, 5)` are retained in `_BEZOUT_DOMAIN`. This is recorded in
`falsification_screen_fixtures.py` next to the domain list rather than
silently dropped, per this lane's own governing rule (ADR-0752 §"a control
inherited from a sibling operator can be vacuous"): the vacuity was found by
running the code before trusting a witness, not by inherited assumption.

## Consequences

- 2 retained false statements (both new relative to S3's 13), 6 definitions
  reviewed against independent references with 6 mutations (one per
  definition, each verified to move an observation), 2 review obligations,
  10 receipts, at least 1 demo dispatch entry with a real, `git log`-checkable
  ordering.
- Registered in both `scripts/check.sh` and the `justfile`.
- The pack's shape is pinned in `artifacts/falsification/false-statement-corpus.json`
  and `artifacts/falsification/definitions-registry.json`; a silent change to
  a model is drift, not a fresh baseline.

## What this ADR does not claim

- **The corpus does not cover this repository's definitions.** 6 reviewed
  definitions and 2 false statements is a demonstration of the mechanism with
  real, historically-grounded content, not a census. Growing it is per-family
  work.
- **The git-ordering guard cannot prove a dispatch never happens without any
  receipt tool at all.** It can only check entries that were recorded in
  `artifacts/falsification/dispatch-log.jsonl`. Wiring an actual D4 producer
  dispatcher to write real entries there (or to this schema) is future work,
  named explicitly rather than assumed.
- **Nothing here inspects a kernel proof term.** Like S3, these are semantic
  and structural checks over Python models and bounded domains — cheap, and
  bounded in what they can catch by the same ceiling ADR-0752 states for
  itself.
