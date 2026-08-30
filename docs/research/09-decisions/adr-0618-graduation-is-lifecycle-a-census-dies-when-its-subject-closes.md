# ADR-0618: Graduation is lifecycle; a census dies when its subject closes

Status: accepted
Date: 2026-08-30
Index-summary: A censused fact that closes after the census ran has GRADUATED, not violated it — counted and audited against the census's pinned commit rather than rejected; the failing rules are recomputed freshness ones, and they now report that every frozen statement export names a proved fact, so the mobility census has no subject and regeneration cannot give it one

## Context

`scripts/check-mobility-census.py` had exited 1 for a long time, reddening
`just check` (`step` accumulates failures, it does not abort). Measured on
2026-08-30 at the head of this lane, **127 violations, and 126 of them were the
same sentence**:

```
F:<id> is proved in the ledger; the census is over OPEN facts
```

The census (`artifacts/autogenesis/mobility-census-v1.json`,
[07-mobility-census.md](../../python-2026-08/07-mobility-census.md)) is a
snapshot: for each open fact and each of the nine catalog tactics, does the
tactic's precondition hold at that fact's imported goal? It wrote 152 fact rows.
**126 of those facts have since been proved.** The gate was failing because the
flywheel worked, and a gate that punishes progress gets ignored — which is what
had happened.

That is the presenting problem. It is not the important one.

## The finding the 126 lines were burying

Every quantity below is recomputed here from the ledger, the nursery and the
frozen-export index, not read out of the census:

| | |
|---|---:|
| census rows | 152 |
| … still open | 26 |
| … graduated (open at census time, settled now) | 126 |
| rows the census could EVALUATE | 3 |
| … of those still open | **0** |
| zero-match clusters (the capability backlog) | 1 |
| … naming at least one still-open fact | **0** |
| entries in `agent-frozen-export-index-v1.json` | 4 |
| … whose fact is still open | **0** |

A frozen statement export is the **only** route to an evaluable goal. That is
deliberate and 07-mobility-census.md argues it at length: there is no fallback
that parses `formal.statement` Lean text, because that would make every verdict
rest on a goal nobody pinned — the `explain_corpus` failure in a new place.

So with zero open facts carrying an export, **the mobility census has no
subject left**. Regenerating it would produce `evaluable = 0`, which the
checker's own rule 7 already refuses ("a census that evaluated nothing is not a
census"). The tempting fix — refresh the stale input — does not work here, and
saying so is most of this ADR's value.

## Decision

**1. Graduation is lifecycle, not a violation.** A row whose fact was `open`
when the census ran and is settled now has graduated. It is counted and
reported (`graduated=` on the status line), never rejected.

**2. Graduation is audited, not assumed.** `open_facts` is the denominator of
the census's headline ratio, so padding it with already-closed facts would
inflate the very number the census publishes. Every row's `epistemic_status` is
re-read **at the census's own pinned `git_commit`**, in one
`git cat-file --batch` (measured at 0.01 s for 152 rows), and a row already
settled there is a violation. All 152 rows verify as `open` at `e2714027`.

Three audit states, kept distinct on purpose:

* `ok` — the audit ran.
* `no-git` — no `.git` at all. `git archive` snapshots
  (`scripts/lane-snapshot.sh`) are built and gated exactly that way, and
  `scripts/tests/mutation_controls.py` `copytree`s the tree, so refusing there
  would break two supported workflows. The state is printed on the status line
  rather than swallowed, so a run that *could not* audit never reads as a run
  that audited and found nothing.
* `unreachable` — `.git` is present and the pinned commit is not. A
  **violation**, not a skip. A census pinning a commit nobody can reach cannot
  have its population audited, and "skip when the check is inconvenient" is
  precisely how a checker stops being able to fail.

**3. Three recomputed freshness rules replace the 126 lines.**

* No open, non-held-out fact carries a frozen export → the census has no
  subject, and the message says regeneration will not help.
* Open exports exist and the census evaluated none of them → regenerate.
* An open fact carries an export and has no census row → the one kind of fact
  this census can measure went unmeasured.
* A zero-match cluster whose facts have all settled → a capability backlog of
  closed facts names no capability.

Held-out facts are excluded from all of these before anything is named, so the
"must have a row" rule can never demand the leak that `check_no_held_out`
exists to refuse. That exclusion has its own control, because deleting it would
turn this gate into a held-out-id leak.

**4. The status line carries both.** `open`/`evaluable` are what the census
CLAIMED when it ran; `live`, `graduated`, `live_evaluable`, `live_exportable`
and `audit` are recomputed now. The gap between them is the staleness, and one
number would hide which side of it moved.

## Why not the alternatives

**Suppress the 126 lines.** The obvious fix and the wrong one — it makes the
gate green by making it blind, and it would have hidden the finding above
completely. This repository's signature defect.

**Regenerate the census.** `just mobility-census-regen` already exists; the
premise that there is no refresh path was wrong. It does not help: the output
would be `evaluable = 0`.

**Treat the census as a preregistered blind population, like the nursery.** It
is not one, and this was checked rather than assumed. ADR-0542's concern is
that regenerating a held-out population destroys the evidence. The census
*excludes* held-out facts entirely — they appear only as integers in
`totals.held_out_excluded` and the partition table, never as ids — and the
leakage scan runs live against the current nursery on every invocation. So
regeneration here is honest, and the reason not to do it is that it would not
help, not that it would spend a split key.

**Retire the gate.** Rejected, and it was the option most worth taking
seriously. The census is the only instrument that measures the export
bottleneck, and it is currently reporting that the bottleneck got *worse*: the
route went from 4 exports over 191 open facts to 4 exports over 146, all four
now closed. Deleting the gate would delete the measurement that says so. It
should be retired only if a decision is taken that the frozen-export route is
abandoned — and then the ADR should say that, not this one.

## Consequences

**The gate stays red, and that is the correct state.** It reports three
violations instead of 127, each naming its own remedy: the nursery pin is stale
(the census was computed against a nursery that no longer exists — its held-out
counter is unverifiable, though the leakage scan is live and passes); the
census has no subject; the capability backlog names only closed facts.

Clearing it needs a producer to export a statement for a fact that is still
open. Nothing in the checker can do that, and nothing in the checker should
pretend otherwise.

`test_the_committed_census_passes` was asserting something no longer true and is
replaced by `test_the_committed_census_fails_only_for_known_staleness`, a
ratchet in both directions: a new violation KIND fails it, and so does the
census finally going green — at which point the right edit is to assert 0 again
and delete the known-staleness list.

Coverage measured, not asserted:
`python3 scripts/tests/mutation_controls.py mobility-census` reports **49
mutants, each killed by exactly one test, zero survivors, zero ambiguous
anchors**, over a 60-test suite (was 44, with one failing).
