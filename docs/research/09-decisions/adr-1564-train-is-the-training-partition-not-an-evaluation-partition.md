# ADR-1564: train is the TRAINING partition, not an evaluation partition — the list was wrong, so the list changes

Status: accepted
Date: 2026-09-02
Lane: `train-is-not-evaluation`

Index-summary: [ADR-1563](adr-1563-the-bootstrap-lemma-is-not-a-leak-and-the-stale-exemption-is-retired.md)
refused to amend the remaining 153 crossing edges — 147 of them `train <->
development` — on the ground that the committed, `before-target-outcomes`
split policy lists `required_evaluation_partitions: [train, development,
held-out]`, so a development row citing a proved train lemma is a leak by that
policy's own words. That refusal was right about the policy and the policy is
wrong. **Train is the training partition.** Nothing about held-out blindness,
or about development being the tuning set, depends on a development row citing
a proved train lemma; that is what a training set is for, and both properties
that matter are enforced independently
(`check-autogenesis-holdout-isolation.py`, `check-holdout-adjacency.py`,
`check-holdout-closed-evaluation.py` for the blind population;
`check-development-partition.py` for the tuning set). So the preregistered
policy is AMENDED, with a dated `policy_amendments` entry beside a new
`partition_roles` block: `required_evaluation_partitions: [development,
held-out]`, `training_partitions: [train]`, and `blind_partitions: [held-out]`
recording the seal explicitly. Three gates now DERIVE their evaluated set from
that block instead of each holding a literal copy
(`check-autogenesis-nursery.py`, `check-partition-edges.py`,
`nursery-components.py`), and `create-autogenesis-mathlib-nursery-split.py`
carries it into the manifest and REFUSES a role change with no amendment
recorded. Measured: partition-edge **crossing 198 -> 51**, **baseline 153 ->
6** (`shrank_by=147`, the ratchet's refusal-to-grow untouched); nursery
cross-population **5 crossing components -> 1**; component exemptions **5 ->
0**, so ADR-1546's growing-exemption mechanism is now empty rather than
smaller. Two gates changed state to green that this lane did not set out to
fix (`create-autogenesis-mathlib-nursery-split.py --check`,
`nursery-components.py`'s `crossings_now`, which was reporting 198 against the
edge gate's own contract that the two numbers are comparable). **What stays
red, and must:** the nursery gate's cross-population arm, on ONE component of
287 that crosses `development`/`held-out`. It is not amendable and is not
amended — six held-out-endpoint crossings stay baselined per ADR-1563, and a
component exemption may never name a held-out row.

Index-status: accepted

## The decision

`train` is a **training partition**: the population a producer is allowed to
build on. It is not evaluated, so an edge between it and a non-blind
evaluation partition is not a leak.

Everything else stays sealed, and the seal is now written down as data rather
than implied by a list:

| edge | before | after |
| --- | --- | --- |
| `train -> development` | crossing (83 live) | **not a crossing** |
| `development -> train` | crossing (64 live) | **not a crossing** |
| `development -> held-out` | crossing | crossing |
| `train -> held-out` | crossing | **crossing** (blind seal) |
| `held-out -> development` | crossing (4 live) | crossing |
| `held-out -> train` | crossing (2 live) | **crossing** (blind seal) |
| `evaluation -> longitudinal` | crossing, amendable | unchanged (45 amended) |
| `longitudinal -> evaluation` | crossing, NOT amendable | unchanged |

The two rows in bold that stay crossings are the reason `blind_partitions`
exists as its own list. If "is this pair a crossing?" were derived from
`required_evaluation_partitions` and `training_partitions` alone, then
`train <-> held-out` would become an ordinary training pair the moment train
stopped being evaluated — and blindness, once spent, cannot be un-spent. So
the rule is: **an edge is a crossing unless it joins a training partition to a
NON-BLIND evaluation partition, in either direction.** Both gates refuse a
policy whose `blind_partitions` is empty or is not a subset of the evaluation
partitions; unsealing the held-out population is not something a producer can
do by editing a data file.

`held-out -> anything` staying a crossing is the same direction argument
ADR-1563 made for longitudinal: an edge INTO a population every partition
shares carries no information, but an edge OUT of a blind row entangles it
with rows producers work on.

## Why the policy, and not the 147 edges

ADR-1563 stated the alternative and rejected it precisely:

> Writing 64 amendments asserting the opposite would be amending the gate to
> disagree with the preregistered split, at a finer unit than the exemption
> ADR-1546 refused — which is the same act, not a better one.

That is correct, and it is the argument for changing the split rather than
amending around it. The 147 edges are not repairable by any other route:
[ADR-1551](adr-1551-the-family-graph-is-one-blob-and-the-dependency-edge-is-proof-derived.md)
measured that `depends_on` is DERIVED FROM THE ADMITTED PROOF TERM, so it is
not a free variable — 396 of the 398 train/development rows declaring any
dependency are `proved`, and a re-partition that moved rows to break those
edges would be assigning partitions as a function of what we managed to prove,
which is what `split_freeze: before-target-outcomes` forbids. So the three
options were: leave 147 permanent violations baselined forever; amend them one
by one against the policy's own words; or fix the words. Only the third is a
decision anyone can re-derive.

**This is an amendment, not an edit in place.** The split policy is frozen
`before-target-outcomes`, and which partitions are evaluated is part of what
was frozen; editing the list silently would be indistinguishable from having
always meant it, which is exactly the failure ADR-1546 measured on an
exemption re-scoped 228 -> 230 -> 258 -> 274 to fit whatever it had just
failed on. So `create-autogenesis-mathlib-nursery-split.py` now carries a
`PREREGISTERED_PARTITION_ROLES` constant — the shape frozen on 2026-08-18, not
the shape that ships — and `validate_partition_roles` REFUSES any departure
from it that is not accompanied by a dated `policy_amendments` entry with an
authority. It refuses the converse too: `policy_amendments` recorded while the
roles are still the preregistered shape is an amendment that changes nothing,
which is a claim nobody can check.

### A correction to the brief this lane was given

The brief named `artifacts/autogenesis/mathlib-nursery-split-policy-v1.json`
as the file holding `required_evaluation_partitions`. It does not, and did
not: that key lives in `artifacts/autogenesis/nursery-v1.json`'s `policy`
block, emitted there as a hardcoded literal by
`create-autogenesis-mathlib-nursery-split.py:180`. Nor could the amendment be
recorded in the split policy's existing `amendments` list, whose validator
requires every entry to be a held-out family move with an exact key set and
`from == "held-out"`.

So the roles are now a `partition_roles` block in the split policy — the
preregistered authority, where a `before-target-outcomes` decision belongs —
with its own `policy_amendments` ledger beside the family-move one, and the
generator carries the block into the manifest the gates read. That is a
structural improvement over the brief's version rather than a substitute for
it: before this, the split policy did not record which partitions it
evaluated at all.

## What was measured

Every number below is the shipped script's own summary line over the live
tree, before and after, never a re-derivation of its algorithm.

### `scripts/check-partition-edges.py`

```
before  PARTITION-EDGES|manifests=2|drawn=756|crossing=198|amended=45
        |baselined=153|violations=0|not_amendments=5
        |component_exemptions_would_wave=0|unamended_total=153|PASS

after   PARTITION-EDGES|manifests=2|evaluation=development+held-out
        |training=train|blind=held-out|drawn=756|crossing=51|amended=45
        |baselined=6|violations=0|not_amendments=0
        |component_exemptions_would_wave=0|unamended_total=6|PASS
```

`crossing` 198 -> **51**: the 147 `train <-> development` edges are no longer
crossings. The 51 that remain are the 45 amended `evaluation -> longitudinal`
bootstrap edges (ADR-1563, untouched) plus the 6 with a held-out endpoint.
`--record-baseline` reported `edges=6|shrank_by=147`; the refusal to record a
set that is not a subset of the committed one is unchanged and still
mutation-verified (M5).

The summary line now prints the roles it used. A gate whose answer depends on
a policy and does not say which policy it read is one re-record away from
being unfalsifiable.

The 6 baselined edges are `held-out -> development` (4) and `held-out ->
train` (2), still stored with their held-out endpoint as a salted digest
(ADR-1550's amendment), and still structurally un-amendable: an amendment
names its endpoints in plain text and the amendments artifact is inside
`check-autogenesis-holdout-isolation.py`'s scan set.
`check-autogenesis-holdout-isolation.py` reports `references=0|verdict=PASS`
after the re-record.

### `scripts/check-autogenesis-nursery.py`

| | before | after |
| --- | ---: | ---: |
| cross-population violation TYPES | 1 | 1 |
| crossing components | **5** | **1** |
| largest crossing component | 287 (dev/held-out/train) | 287 (dev/held-out/train) |
| v1 arm | green | green |
| exit | 1 | 1 |

Four of the five crossing components were `development`/`train` only and are
gone. The fifth — `1f981290ab63…`, 287 members — crosses
`development`/`held-out` and **stays a violation**. It is reported with a
train member listed too, because the report prints every member's partition;
what makes it a leak is the development/held-out pair alone.

**It is not amended, and this ADR does not amend it.** A component exemption
may never name a held-out row (`validate_exemptions` raises), so the
mechanism is structurally unavailable, which is the correct answer rather than
an obstacle: the fix is a repair of those edges or a decision about the
held-out rows, not a suppression. This is the gate reporting the one thing it
should still be reporting, and it is the same 4 + 2 edges the edge gate holds
baselined.

### Exemptions 5 -> 0

All five remaining component exemptions covered `development`/`train`
components. Under the amended roles each suppresses nothing, which is exactly
what the gate's own `unused_exemptions` criterion calls a violation — the gate
went to **2** violation types for one commit until they were retired. So:

| file | key | entries before | after |
| --- | --- | ---: | ---: |
| `nursery-v1.json` | `component_split_exemptions` | 3 | **0** (key dropped) |
| `nursery-v2-extension.json` | `cross_population_component_split_exemptions` | 2 | **0** |

Deletions only, and each was checked before deletion to reach at most one
evaluation partition (the script asserts it and would refuse otherwise). The
v1 key is dropped entirely because `create-autogenesis-mathlib-nursery-split.py`
— the file's generator — has never emitted it; the v2 seal
(`extension_sha256`) was recomputed with the generator's own `digest`,
`3bab61a4… -> 995bfe29…`, so `gen-autogenesis-nursery-refill.py --check` stays
exit 0. That is the failure ADR-1563 hit and recorded, avoided by doing what
it says.

**ADR-1546's growing-exemption mechanism is now empty, not smaller.** 7 -> 5
was ADR-1563; 5 -> 0 is this. A future exemption is a fresh entry somebody has
to argue for.

## Where the derivation now lives

| script | was | now |
| --- | --- | --- |
| `check-autogenesis-nursery.py` | `EVALUATION_PARTITIONS = {...}` module literal, plus a `validate_policy` asserting the manifest said the same triple | `evaluation_partitions(policy)`; `validate_policy` checks the list is USABLE (non-empty, duplicate-free, real partitions, disjoint from training, non-empty blind subset) |
| `check-partition-edges.py` | every distinct pair of partitions is a crossing | `load_policy` -> `PartitionRoles.is_crossing`, and the roles are printed in the summary |
| `nursery-components.py` | `EVALUATION_PARTITIONS = (...)` module literal; `crossing_edge_count` compared endpoints directly | reads the policy into `Drawn.evaluation_partitions` and publishes it in the census; `crossing_edge_count` calls the EDGE GATE'S OWN `PartitionRoles.is_crossing`, loaded by path |
| `create-autogenesis-mathlib-nursery-split.py` | `"required_evaluation_partitions": ["train", "development", "held-out"]` literal in `build` | carried from the split policy's `partition_roles`, with `validate_partition_roles` gating the departure |

The last row of the third entry is not tidiness. `crossing_edge_count`'s
docstring promised its `crossings_now` was "computed the same way
`check-partition-edges.py` computes it, so [it] can be compared to that gate's
`crossing=`". After the roles changed, that promise was false by 198 to 51 —
two readers of one property disagreeing is a pair of reports describing no
tree at all, which is the reason ADR-1563 made the nursery gate load the edge
gate's own `load_amendments` rather than re-parse the artifact. Same device,
same reason: `nursery-components.py` now reports **51**, and `--record
--remeasure` locked that into the census.

## Checker discipline

Every guard added here was driven to failure, and every mutant kills exactly
one test. Measured with `python3 scripts/tests/mutation_controls.py <family>`
in an isolated scratch root, never in the shared worktree.

### `partition-edges` — 7 new mutants, 33 tests

| mutant | the test that dies |
| --- | --- |
| M17 a training/evaluation pair is not a crossing | `test_a_train_development_edge_is_not_a_crossing_under_the_amended_roles` |
| M18 a BLIND partition is sealed in both directions | `test_a_training_edge_to_the_blind_partition_still_crosses_both_ways` |
| M19 a policy naming no evaluation partition is unanswerable | `test_a_policy_naming_no_evaluation_partition_is_exit_two` |
| M20 `blind_partitions` may not be empty | `test_a_policy_that_seals_no_blind_partition_is_exit_two` |
| M21 training and evaluation are disjoint roles | `test_a_partition_that_is_both_training_and_evaluation_is_exit_two` |
| M22 a manifest with no policy at all is unanswerable | `test_a_manifest_carrying_no_policy_at_all_is_exit_two` |
| M23 two manifests disagreeing about the roles is unanswerable | `test_two_manifests_disagreeing_about_the_roles_is_exit_two` |

M17 is the mutant this ADR exists to make possible: it restores the old rule
(`every distinct pair crosses`) and nothing else in the suite notices, because
every OTHER scenario in the file runs under the **preregistered** policy on
purpose. The fixture helper defaults to
`required_evaluation_partitions: [train, development, held-out]` so each
pre-ADR-1564 scenario keeps its `train -> development` crossing and keeps its
own subject; the ADR-1564 scenarios pass the shipped roles explicitly and
assert the SAME population answers differently. **That contrast is the
measurement.** A suite where every fixture used the new policy could not
distinguish "the roles are read from the policy" from "the literal happens to
have been updated".

M19 and M20's tests assert the MESSAGE, not just exit 2. Four inputs here are
exit 2, and a guard whose test accepts any of them is satisfied by the wrong
refusal — with M19 applied, the empty-evaluation policy still exits 2 through
the blind check, so an exit-code-only test would have survived it.

### `nursery-split-exemption-guards` — 3 new mutants, 20 tests

| mutant | the test that dies |
| --- | --- |
| N4 the evaluated partitions are read from the policy | `test_the_same_component_does_not_leak_once_train_is_a_training_partition` |
| N5 a policy naming no evaluation partition is refused | `test_a_policy_naming_no_evaluation_partition_is_refused` |
| N6 `blind_partitions` may not be empty or foreign | `test_a_policy_that_seals_no_blind_partition_is_refused` |

`AmendedPartitionRoleTests` is a BEFORE/AFTER pair over one fixture:
`test_a_train_development_component_leaks_under_the_preregistered_roles` and
`test_the_same_component_does_not_leak_once_train_is_a_training_partition`
share every fact, every entry and the one `depends_on` edge, and differ only
in `required_evaluation_partitions`. N4 restores the old literal and kills the
second alone.

`test_a_development_held_out_component_still_leaks_after_the_amendment` is the
brief's required control: a synthetic `development`/`held-out` edge fails
BOTH gates after the change — this one in the component gate, and
`test_a_development_to_held_out_edge_still_crosses` in the edge gate.

N1/N2/N3 (ADR-1563's contraction mutants) and the four ADR-1455/ADR-0850
exemption mutants are unchanged at one kill each.

### `mathlib-nursery-split` — 2 new mutants

| mutant | the test that dies |
| --- | --- |
| S1 a role change with no `policy_amendments` entry is refused | `test_changed_roles_without_an_amendment_are_refused` |
| S2 an amendment recorded against unchanged roles is refused | `test_an_amendment_recorded_against_the_preregistered_roles_is_refused` |

S2 is the direction that is easy to leave out. Without it, a lane could record
a `policy_amendments` entry, change nothing, and the file would carry a dated
claim about a change that never happened.

`scripts/check-control-registration.sh`: `controls=NN orphans=0`, exit 0 (see
the lane status doc for the run).

## Consequences

- **`check-partition-edges.py --baseline` is green on a baseline of 6.** New
  crossings still block a push, a merge and both aggregate gates at 0.13 s,
  and the baseline still may only shrink.
- **`check-autogenesis-nursery.py` is still red**, on ONE component instead of
  five, for a reason that is a `development`/`held-out` fusion and nothing
  else. That is the honest remainder and it is what the next lane inherits;
  it is not amendable through any mechanism in this repository, by design.
- **`create-autogenesis-mathlib-nursery-split.py --check` is green**, for the
  first time since the first component exemption was added. ADR-1563 recorded
  that it had been red because `build()` emits no `component_split_exemptions`
  key at all; retiring the last three v1 exemptions removed the divergence.
  The regeneration also landed the `natural-bit-decode` amendment record
  (ADR-0950), which had been in the split policy since 2026-08-30 and had
  never reached the manifest's own ledger. No entry moved partition: the
  generator's `PARTITION_COUNTS` assertion (`train 78, development 120,
  held-out 16`) held before and after.
- **No row moved partition, no held-out fact was touched, and no held-out
  row's outcome is named** in this ADR or in any artifact this lane wrote.
  `check-draw7-frozen-families.py`, `check-holdout-adjacency.py`,
  `check-holdout-closed-evaluation.py`,
  `check-autogenesis-holdout-contamination.py` and
  `check-autogenesis-holdout-isolation.py` are all exit 0, before and after.
- **`check-development-partition.py` stays green** (ADR-1563's grandfather is
  untouched), and it is now the only thing enforcing "development is not what
  a producer is tuned against" — which is the load-bearing half of why train
  can stop being evaluated. It should not be weakened without re-reading this
  ADR.

## Method notes

- Every gate figure is the shipped script's own summary line, run over the
  real tree. The before column was captured on this worktree at
  `596cbf0a2` (main merged) and cross-checked against a `git archive` snapshot
  of the same commit for the two gates that were red for reasons outside this
  lane.
- Both artifact edits were made by script, not by hand: each asserts the file
  round-trips byte-identically through `json.dumps(..., indent=2,
  ensure_ascii=False)` before rewriting it, and the exemption retirement
  asserts, per entry, that the exemption reaches at most one evaluation
  partition before deleting it. A hand edit would have been the only thing in
  this lane nobody could re-derive.
- Not run: `cargo` in any form, `just check`, `scripts/check.sh`. No `.rs`
  file was touched. `scripts/check-generated-artifact-ownership.py` was run
  and is reported in the lane status; it is red on `main` for the same
  artifact both before and after, verified on a snapshot.
