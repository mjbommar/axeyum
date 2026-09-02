# ADR-1565: the six held-out crossings are a scored evaluation's residue, not a leak — the reclassification is refused, and the seal the nursery gate had quietly lost is restored

Status: accepted
Date: 2026-09-02
Lane: `heldout-never-blind`

Index-summary: This lane was briefed to repair the last red partition gate by
reclassifying held-out → development the families behind the six
`held_out_endpoint: true` edges in
`artifacts/autogenesis/partition-edge-baseline-v1.json`, on the ADR-1450 /
`natural-bit-decode` precedent that a held-out row whose proof cites a drawn
row was never blind. **The reclassification is REFUSED, on two independent
grounds, and the brief's premise is measurably false.** (1) The six edges
resolve — through `check-partition-edges.py`'s own salt, not a
re-implementation — to five rows in ONE family, `integer-absolute-value`, and
that family is exactly the ten rows of `artifacts/autogenesis/holdout-
evaluation-v1.json`, the only scored evaluation record in the tree. A scored
family may not be moved: the move would rewrite the population a committed
evaluation was scored against. (2) The premise inverts the causality. Measured
first-parent: the family was sealed held-out at `94b3e61ee` (2026-08-29
17:22:14); its fact rows were created at `474ed7158` (2026-08-29 23:15:27)
with `depends_on: []` and `epistemic_status: open`; the scoring protocol was
committed at `067d675a3` (2026-09-01 14:03:46); and **every one of the six
edges enters at a single commit, `347785417` (2026-09-01 14:58:17)**, the
scoring lane's closure. The edges did not predate the seal — they were
CREATED BY the evaluation, three days after it, under a protocol committed
first. Blindness here was spent on the books, not leaked. A `held-out ->
train` edge is what proving a held-out row looks like, because a proof cites
the training set; every legitimately scored row will produce them.
**The incidental finding, which is the part with a repair.** Checking the
brief's control — "a held-out row depending on a drawn row must still fail
`check-autogenesis-nursery.py`" — measured that it does NOT. ADR-1564's table
marks `held-out -> train` in bold as a crossing that survives the amendment,
and `check-partition-edges.py` applies it; the nursery gate filtered `entries`
down to the EVALUATED rows before counting a component's partitions, so once
`train` left the evaluation set a `held-out`/`train` component collapsed to
one evaluated partition and raised nothing at all. The seal existed in one of
the two gates that claim it. `crossing_components()` restores it from the
policy's own `blind_partitions`/`training_partitions`, on both report paths;
measured, this adds **zero** new live violations, because the only
cross-partition component containing any held-out row is the one already
flagged. Two mutants: N7 (delete the clause) kills exactly one test, the new
control; N8 (widen it to every training-touching component) kills the control
AND ADR-1564's positive control, which is what shows the seal is
blind-specific rather than merely present. **What stays red, and must:**
`check-autogenesis-nursery.py`, on the same one component of 305 it was red on
before this lane, for the same reason. Nothing was suppressed, amended,
exempted or redacted to make a number move.

Index-status: accepted

## The decision

**The six edges are not repaired, and no family is moved.**

Three repairs were available and two are refused for cause:

| repair | verdict |
| --- | --- |
| move `integer-absolute-value` held-out → development | **REFUSED** — it is the scored family |
| amend the six edges in `partition-edge-amendments-v1.json` | **REFUSED** — ADR-1563's ground still holds; the amendments artifact is inside `check-autogenesis-holdout-isolation.py`'s scan set |
| leave them baselined, and say precisely what they are | **TAKEN** |

The third is not a deferral. The six edges are already recorded, already
ratcheted to shrink-only, and now have a written cause. What was missing was
never an amendment; it was the sentence saying these are an evaluation's
residue rather than a breach — and, as it turned out, a working seal in the
gate that reports on them.

## Why the brief's premise is false, measured

The precedent the brief cited is real and the reasoning is right in its own
cases. The `natural-divisibility`, `natural-parity`, `fermat-numbers` and
`natural-bit-decode` amendments all share one shape: **the spending event
PREDATES the seal.** A declaration was admitted, or a definition landed that
decided a ground equation, days or hours BEFORE the family was preregistered
held-out — so the row was never blind, and `git merge-base --is-ancestor`
confirms the order in each recorded reason.

This family is the opposite order, and the order is the whole argument:

| event | commit | timestamp |
| --- | --- | --- |
| family sealed held-out in `nursery-v2-extension.json` | `94b3e61ee` | 2026-08-29 17:22:14 |
| the five rows created, `depends_on: []`, `open` | `474ed7158` | 2026-08-29 23:15:27 |
| scoring protocol preregistered | `067d675a3` | 2026-09-01 14:03:46 |
| the six `depends_on` edges enter, all at once | `347785417` | 2026-09-01 14:58:17 |

There is no commit between the seal and the protocol in which any of these
rows carries a dependency. The rows were blind for the whole interval the
seal covered, and the protocol was committed before any statement in the
family was read (`artifacts/autogenesis/holdout-evaluation-v1.json`'s
`protocol_commit`, and the protocol note it names).

So the diagnostic "a held-out row's proof cites a drawn row ⇒ it was never
blind" is **sound only for edges that predate the seal**, and it was applied
here to edges that postdate it by three days. Generalised, it would condemn
every held-out row we ever legitimately score, because a proof of anything
cites lemmas, and the lemmas we have are in the training set. That is what a
training set is for — the same argument ADR-1564 made for `development ->
train`, one partition over.

**The check that distinguishes them is a timestamp comparison, and it is
cheap.** A future audit of a `held-out -> X` edge should ask which commit
introduced it and whether that commit precedes the preregistering one, before
reading the edge as a breach.

## The seal the nursery gate had lost

ADR-1564 states the rule and its table marks two rows in bold:

> an edge is a crossing unless it joins a training partition to a NON-BLIND
> evaluation partition, in either direction

`check-partition-edges.py`'s `PartitionRoles.is_crossing` implements exactly
that, blind clause and all. `check-autogenesis-nursery.py` did not. Its leak
check reads:

```python
evaluation = [entry for entry in entries
              if entry["partition"] in partitions_evaluated]
for entry in evaluation:
    component_partitions[by_fact[entry["fact_id"]]].add(entry["partition"])
```

— the filter runs BEFORE the count. While `required_evaluation_partitions`
was `[train, development, held-out]` this was correct by accident: `train`
was evaluated, so a `held-out`/`train` component held two evaluated
partitions and leaked. ADR-1564 removed `train` from that list and the
component collapsed to one evaluated partition. Measured 2026-09-02 on a
synthetic population — one `held-out` row depending on one `train` row, no
other edge — the gate returned `component_split_leaks: []`.

This is the failure mode CLAUDE.md names: **a gate that goes green by losing
its subject.** It did not go fully green, because the live crossing component
also contains `development` rows and so still leaks for the ordinary reason —
which is precisely why nobody saw it. The subject was gone and the verdict
did not move.

`crossing_components()` now applies both rules, reading `blind_partitions`
and `training_partitions` from the policy rather than from a literal, on both
the v1 and the cross-population report paths:

* two distinct evaluation partitions in one component (the original rule), or
* a **blind** row sharing a component with a **training** row.

`longitudinal` is deliberately outside the second rule. It was never in the
evaluated set, so ADR-1564 changed nothing about it, and a component shared
with the longitudinal bootstrap is a separate and separately amendable
violation (ADR-1563) that both paths already raise. Folding it in would report
one finding twice under a rule that did not regress.

### Why this costs nothing, and why that is a measurement rather than luck

The repair adds zero live violations. Enumerated over the weak components of
the drawn population across both manifests, **exactly one** component contains
any held-out row together with a row of another partition, and it is the
305-member one the gate was already red on. Every other held-out row sits in a
component whose partitions are held-out alone.

That is a fact about today's population, not a property, which is the point of
having the guard: the next `held-out -> train` edge lands in a component with
no development row in it, and before this change nothing would have said so.

## The controls

`AmendedPartitionRoleTests` is a BEFORE/AFTER pair over one fixture, and the
new case is a third leg on the same fixture with an ISOLATED component — fused
to the existing `train`/`development` one, it would leak for the ordinary
reason and would pass with the blind seal deleted.

| mutant | kills |
| --- | --- |
| N7 `elif False:` — delete the blind clause | **exactly 1**: `test_a_held_out_train_component_still_leaks_after_the_amendment` |
| N8 `elif partitions & training:` — widen it past `blind` | 2: the new control, and ADR-1564's `test_the_same_component_does_not_leak_once_train_is_a_training_partition` |
| N4 restore the `EVALUATION_PARTITIONS` literal | 2 (was 1): both role-derived cases |

N8 is the one worth reading twice. A guard whose only mutant is `if False:`
is never asked whether it seals the RIGHT pair; N8 asks, and the answer is
that widening the clause re-breaks the crossing ADR-1564 deliberately
legalised.

## Consequences

* The six edges stay baselined at 6, shrink-only, with a recorded cause.
  `check-partition-edges.py --baseline` reports `violations=0` and did not
  need to change.
* `check-autogenesis-nursery.py` stays red on one component. Its
  `LiveManifestTests` case stays red with it — it reproduces the live gate by
  construction, and was already red before this lane, which is why
  `mutation_controls.py` measures `test_nursery_exemption_guards` instead.
* `integer-absolute-value` remains held-out in the manifest and remains SPENT
  for future blind evaluation, as `holdout-evaluation-v1.json` already
  records. Spent is not the same as misclassified, and the two should not be
  merged: a moved family leaves the blind population, a spent one stays in it
  with its result on the books.
* The audit question for the next `held-out -> X` edge is a timestamp
  comparison against the preregistering commit, not the existence of the edge.
