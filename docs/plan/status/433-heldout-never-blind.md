# Lane: heldout-never-blind — the six held-out crossings, identified and refused

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, heldout-never-blind, 2026-09-02).** Briefed to
clear the last red partition gate by reclassifying held-out → development the
families behind the six `held_out_endpoint: true` edges in
`artifacts/autogenesis/partition-edge-baseline-v1.json`. **The reclassification
is refused and no family was moved** ([ADR-1565](../../research/09-decisions/adr-1565-the-six-crossings-are-a-scored-evaluations-residue-and-the-nursery-gate-had-lost-the-blind-seal.md)),
on two independent grounds, the second of which says the brief's premise is
false rather than merely inapplicable.

**(1) It is the scored family — the brief's own stop condition.** Resolving the
six digests through `check-partition-edges.py`'s own `digest_fact_id` and the
committed `held_out_salt` (imported, never re-implemented) gives five distinct
rows in **one** family, `integer-absolute-value`, all in
`nursery-v2-extension.json`. That family's ten rows are exactly the ten
`recorded_scores` of `artifacts/autogenesis/holdout-evaluation-v1.json`, the
only scored evaluation record in the tree. Moving it would rewrite the
population a committed evaluation was scored against.

**(2) The premise inverts the causality, measured.** The reclassification
precedent (`natural-divisibility`, `natural-parity`, `fermat-numbers`,
`natural-bit-decode`) has one shape: the spending event PREDATES the seal. This
family is the opposite order. Sealed held-out at `94b3e61ee` (2026-08-29
17:22:14); rows created at `474ed7158` (2026-08-29 23:15:27) with
`depends_on: []` and `open`; scoring protocol preregistered at `067d675a3`
(2026-09-01 14:03:46); and **all six edges enter at one commit, `347785417`
(2026-09-01 14:58:17)** — the scoring lane's closure, three days after the seal
and 55 minutes after the protocol. The edges were created BY the evaluation.
Generalised, the brief's diagnostic would condemn every held-out row we ever
legitimately score, because a proof cites the training set — which is what a
training set is for. The audit question for a `held-out -> X` edge is a
timestamp comparison against the preregistering commit, not the edge's
existence.

**The finding with a repair.** Checking the brief's control — a held-out row
depending on a drawn row must still fail `check-autogenesis-nursery.py` —
measured that **it did not**. ADR-1564's table marks `held-out -> train` in bold
as surviving the amendment and `check-partition-edges.py` applies it; the
nursery gate filtered `entries` to the EVALUATED rows *before* counting a
component's partitions, so once `train` left the evaluation set a
`held-out`/`train` component collapsed to one evaluated partition and raised
nothing. The seal lived in one of the two gates that claim it. It did not show
up as a green gate because the live crossing component also holds `development`
rows and still leaked for the ordinary reason — the subject was gone and the
verdict did not move. `crossing_components()` restores it from the policy's own
`blind_partitions`/`training_partitions` on both report paths; **zero** new live
violations, because the only cross-partition component containing any held-out
row is the one already flagged.

**Gate table, all run, nothing suppressed.** `check-development-partition` 0 ·
`check-autogenesis-holdout-isolation` 0 (`recorded_scores=10`) ·
`check-holdout-adjacency` 0 · `check-holdout-closed-evaluation` 0 ·
`check-dispatchable-frontier` 0 · `check-draw7-frozen-families` 0
(`moved=0`, `control=FIRES` — 0 is correct, this lane moved nothing) ·
`check-partition-edges --baseline` 0 (`baselined=6 violations=0`;
**baseline stays 6, not 6 → 0**) · `gen-autogenesis-nursery-refill.py --check` 0
· `create-autogenesis-mathlib-nursery-split.py --check` 0 ·
`frontier-shape-census.py --check` 0 (`current`, unchanged — no development row
moved) · `validate-facts.py` 0. **`check-autogenesis-nursery.py` stays 1**, on
the same one component of 305 (`1f981290ab63…`,
`['development','held-out','train']`) it was red on before this lane, for the
same reason; `test_check_autogenesis_nursery.LiveManifestTests` reproduces the
live gate by construction and was already red before this lane, which is why
`mutation_controls.py` measures `test_nursery_exemption_guards` instead.

**Mutation.** N7 (`elif False:`, delete the restored clause) kills **exactly
one** test, the new control. N8 (widen it past `blind` to every
training-touching component) kills two — the control and ADR-1564's positive
control — which is what shows the seal is blind-specific rather than merely
present. N4 now kills 2 where it killed 1.

**For the next lane.** The last red gate is not repairable by reclassification
and should stop being framed that way. Retiring it means either an ADR that
accepts a scored family's residue as a permanent, cause-recorded component
crossing, or a component-level analogue of ADR-1563's per-edge amendment class
keyed to the evaluation record. Do not amend or exempt it without one: an
exemption may never name a held-out row, and this component's held-out members
are all five endpoints.

### The six edges, resolved

Fact ids appear here and nowhere else in this
lane's output. `check-autogenesis-holdout-isolation.py`'s scan set is
`artifacts/**/*.json` plus the episode tree, so `docs/plan/status/` is outside
it (verified: the gate is green at `files_scanned=1114` with this file
present); the amendment precedent likewise carries ids in `nursery-v1.json`, a
`POPULATION_FILES` member the scan excludes. ADR-1565 names no id. No row's
outcome is named here.

All six `from` endpoints are `held-out` in `nursery-v2-extension.json`, family
`integer-absolute-value`, and all six enter at `347785417`.

| # | held-out endpoint | → target | target partition |
| --- | --- | --- | --- |
| 1 | `F:ml430-int-natabs-coe-sub-coe-le-of-le-d2800d86` | `F:ml430-nat-add-comm-56a2d614` | train |
| 2 | `F:ml430-int-natabs-coe-sub-coe-lt-of-lt-e0566dd0` | `F:ml430-nat-add-comm-56a2d614` | train |
| 3 | `F:ml430-int-natabs-emod-two-18514063` | `F:ml430-nat-even-add-one-15b5cb18` | development |
| 4 | `F:ml430-int-natabs-emod-two-18514063` | `F:ml430-nat-even-iff-024826e9` | development |
| 5 | `F:ml430-int-natabs-inj-of-nonneg-of-nonpos-b5d96f53` | `F:ml430-nat-le-antisymm-79dccead` | development |
| 6 | `F:ml430-int-natabs-inj-of-nonpos-of-nonneg-ecdb334a` | `F:ml430-nat-le-antisymm-79dccead` | development |

Five distinct held-out rows, one family, one manifest. Every one is `proved`,
all flipped `open → proved` at `347785417` (2026-09-01 14:58:17), the same
commit that introduced every `depends_on` edge above; each row's file was
created at `474ed7158` (2026-08-29 23:15:27) with `depends_on: []`.

| family | edges | rows | manifest | predating commit? | scored? |
| --- | --- | --- | --- | --- | --- |
| `integer-absolute-value` | 6 | 5 of 10 | `nursery-v2-extension.json` | **no** — edges POSTDATE the seal `94b3e61ee` by 3 days | **YES**, all 10 rows, `holdout-evaluation-v1.json` |

One family, and it is the scored one: both stop conditions in the brief fire on
the same family, so the count of families to move is **0**.

Two of the four targets are themselves ex-held-out rows moved to development by
the 2026-08-30 `natural-parity` amendment, which is why they read as
`development` rather than as a second held-out family.

<!-- plan-section: landed-changes -->

| 2026-09-02 | heldout-never-blind | opened the lane; status stub for the never-blind reclassification |
| 2026-09-02 | heldout-never-blind | resolved the six held-out endpoints to one family via the edge gate's own salt; it is the scored family, so the move is refused |
| 2026-09-02 | heldout-never-blind | measured that the six edges POSTDATE the seal by 3 days and enter at the scoring commit — the brief's premise is false |
| 2026-09-02 | heldout-never-blind | restored the `held-out`/`train` blind seal ADR-1564 dropped from `check-autogenesis-nursery.py`; N7 kills exactly one test |
| 2026-09-02 | heldout-never-blind | ADR-1565 records the refusal, the timeline, and the seal repair |
