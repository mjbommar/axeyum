# Lane: train-is-not-evaluation — make the split policy say train is the training partition, not an evaluation partition

<!-- plan-section: lane-status -->

**train-is-not-evaluation (`DONE`, train-is-not-evaluation, 2026-09-02).**
[ADR-1564](../../research/09-decisions/adr-1564-train-is-the-training-partition-not-an-evaluation-partition.md)
carries the reasoning. ADR-1563 refused to amend the 147 `train <->
development` crossing edges because the committed, `before-target-outcomes`
split policy lists `required_evaluation_partitions: [train, development,
held-out]`. That refusal was right about the policy; the policy is what
changed.

**The numbers.** Partition-edge `crossing` **198 -> 51**, baseline **153 -> 6**
(`--record-baseline` reported `edges=6|shrank_by=147`; the refusal to record a
non-subset is untouched and still mutation-verified). Nursery cross-population
**5 crossing components -> 1**. Component exemptions **5 -> 0**, so ADR-1546's
growing-exemption mechanism is now empty rather than smaller — 7 -> 5 was
ADR-1563, 5 -> 0 is this. Nursery-components `crossings_now` **198 -> 51**,
which is what makes it comparable to the edge gate's `crossing=` again, as its
own docstring had promised and stopped being true.

**Where the authority now lives.** `mathlib-nursery-split-policy-v1.json`
gains a `partition_roles` block — `required_evaluation_partitions:
[development, held-out]`, `training_partitions: [train]`, `blind_partitions:
[held-out]` — beside a new dated `policy_amendments` ledger citing ADR-1564.
**The brief named the wrong file:** `required_evaluation_partitions` was not in
the split policy at all, it was a hardcoded literal in
`create-autogenesis-mathlib-nursery-split.py:180`, and the split policy's
existing `amendments` list only accepts held-out family moves with an exact
key set. So the roles are now recorded in the preregistered authority (which
previously did not say which partitions it evaluated) and the generator
carries them into the manifest the gates read.

**`blind_partitions` is its own list, and that is the load-bearing detail.**
Derived from the other two, `train <-> held-out` would have become an ordinary
training pair the moment train stopped being evaluated. Blindness once spent
cannot be un-spent, so the rule is *an edge is a crossing unless it joins a
training partition to a NON-BLIND evaluation partition, in either direction*,
and both gates refuse a policy whose `blind_partitions` is empty or is not a
subset of the evaluation partitions.

**Four readers now derive the evaluated set from the policy** instead of each
holding a literal: `check-autogenesis-nursery.py` (both report arms — the
cross-population arm reads the BASE manifest's policy rather than falling
back), `check-partition-edges.py` (`load_policy` -> `PartitionRoles.
is_crossing`, and the summary line prints the roles it used),
`nursery-components.py` (which calls the EDGE GATE'S OWN `is_crossing`, loaded
by path, the same device ADR-1563 used for `load_amendments`), and the
generator.

**WHAT IS STILL RED, and why it is not amended.**
`check-autogenesis-nursery.py`'s cross-population arm, on ONE component of 287
crossing `development`/`held-out` (`1f981290ab63…`). The four
`development`/`train` components are gone. This one is structurally
un-suppressible: `validate_exemptions` raises on an exemption naming a
held-out row, and the six held-out-endpoint edges are un-amendable in the edge
gate for ADR-1563's reason (an amendment names its endpoints in plain text and
the amendments artifact is inside
`check-autogenesis-holdout-isolation.py`'s scan set). It is the gate reporting
the one thing it should still report. `LiveManifestTests.test_committed_
nursery_files_pass_both_gates` fails for exactly this reason, before and after
— verified identical on a `git archive` snapshot of the pre-change tree.

**Two gates changed state to GREEN that were not in scope.**
`create-autogenesis-mathlib-nursery-split.py --check` (1 -> 0) — ADR-1563
recorded it had been red since the first exemption was added, because
`build()` emits no `component_split_exemptions` key at all; retiring the last
three v1 exemptions removed the divergence. Regenerating also landed the
`natural-bit-decode` amendment record (ADR-0950), in the split policy since
2026-08-30 and never in the manifest's own ledger. No entry moved partition —
the generator's `PARTITION_COUNTS` assertion (train 78, development 120,
held-out 16) held before and after. And
`test_create_autogenesis_mathlib_nursery_split` (1 -> 0): its
`test_repository_split_is_exact_and_balanced` had asserted the literal
`{development: 99, held-out: 37, train: 78}` against a live 120/16/78 since
the first held-out amendment. Re-derived from the catalog and the policy's
family mapping — a third computation, not `PARTITION_COUNTS`, which `build`
already checks against and would be vacuous. It had to be fixed:
`mutation_controls.py` refuses a suite whose baseline is not green.

**Gate table, before (`596cbf0a2`, main merged) vs after. Two rows changed and
both went green; nothing regressed.**

| gate | before | after |
| --- | ---: | ---: |
| `check-autogenesis-nursery` | 1 | 1 (5 crossing components -> 1) |
| `check-partition-edges --baseline` | 0 | 0 (baseline 6, not 153) |
| `check-development-partition` | 0 | 0 |
| `gen-autogenesis-nursery-refill --check` | 0 | 0 (seal recomputed) |
| `check-autogenesis-holdout-isolation` | 0 | 0 (`references=0`) |
| `check-holdout-closed-evaluation` | 0 | 0 |
| `check-holdout-adjacency` / `--self-test` | 0 | 0 |
| `check-autogenesis-holdout-contamination` | 0 | 0 |
| `nursery-components --check` | 0 | 0 |
| `mathlib-nursery-split --check` | **1** | **0** |
| `nursery-dispatch-baseline --check` | 1 | 1 (pre-existing) |
| `mathlib-nursery-review --check` | 0 | 0 |
| `propose-nursery-refill` | 1 | 1 (pre-existing) |
| `validate-facts`, `validate-autogenesis-operations` | 0 | 0 |
| `t:test_check_autogenesis_nursery` | 1 | 1 (pre-existing `LiveManifestTests`) |
| `t:test_create_autogenesis_mathlib_nursery_split` | **1** | **0** |
| `t:test_check_autogenesis_holdout_isolation` | 1 | 1 (pre-existing) |
| every other suite in the table | 0 | 0 |

**Mutation, measured not assumed — and the run found four defects reading
would not have.** `partition-edges` 21 mutants / 21 single kills / 33 tests;
`nursery-split-exemption-guards` 9 mutants / 20 tests with N1–N6 one kill each
(the two pre-existing 2-kill mutants sit on both report paths by design and
are identical on a pre-change snapshot); `mathlib-nursery-split` is a NEW
family, 3 mutants / 3 single kills / 8 tests, for a script that had a test
module and no mutation coverage at all. The four defects: **M1 NOT APPLIED**
(its anchor was the line this change rewrote), **M6 SURVIVED** (its test
asserted `"no nursery manifest"`, which the new `load_policy` also prints, so
deleting the guard left the test green on the wrong refusal), **M17 killed the
wrong test**, **N5 SURVIVED** (wrong arm of a compound condition). A fourth
split-generator mutant was **withdrawn rather than reported with `killed 3`**:
all three deaths came from `build`'s own `PARTITION_COUNTS` assertion, not the
guard it named. `check-control-registration.sh`:
`controls=52|orphans=0|py_controls=322|py_orphans=0`, exit 0.

**The measurement that makes the derivation checkable.** Every fixture written
before this decision keeps the PREREGISTERED roles and its `train ->
development` crossing; the new scenarios pass the shipped roles explicitly and
assert the SAME population answers differently. `AmendedPartitionRoleTests` is
a before/after pair over one fixture — same facts, same entries, same
`depends_on` edge, only the policy differs. A suite where every fixture used
the new roles could not tell "read from the policy" from "the literal happens
to have been updated".

**Nothing moved partition, no held-out fact was touched, and no held-out row's
outcome is named** in the ADR or in any artifact this lane wrote. Both artifact
edits were made by script, each asserting its file round-trips
byte-identically before rewriting, and the exemption retirement asserting per
entry that the exemption reaches at most one evaluation partition before
deleting it.

**Did not run:** `cargo` in any form, `just check`, `scripts/check.sh`. No
`.rs` file was touched. `scripts/check-generated-artifact-ownership.py` WAS
run (~4 min): it is red on `drawn-population-component-census-v1.json`'s OWNER
arm both before and after, verified on a `git archive` snapshot of
`596cbf0a2` — pre-existing on `main`, not this lane's, and not repaired by
re-recording the census.

**For the next lane.** The one remaining crossing component is ADR-1546 option
1's work and ADR-1551 recorded why it is hard; what is new is that it is now
the ONLY one, it is `development`/`held-out` rather than a four-partition
blob, and there is no exemption anywhere in the manifests to hide behind.

<!-- plan-section: landed-changes -->

| 2026-09-02 | train-is-not-evaluation | ADR-1564: train is the TRAINING partition; split policy amended with `partition_roles` + `policy_amendments` |
| 2026-09-02 | train-is-not-evaluation | partition-edge crossing 198 -> 51, baseline 153 -> 6 (`shrank_by=147`); nursery crossing components 5 -> 1 |
| 2026-09-02 | train-is-not-evaluation | component exemptions 5 -> 0; `create-autogenesis-mathlib-nursery-split.py --check` green for the first time since exemptions existed |
| 2026-09-02 | train-is-not-evaluation | four readers derive the evaluated set from the policy; 13 new controls, 13 new mutants, 4 mutation defects found by running the families |
