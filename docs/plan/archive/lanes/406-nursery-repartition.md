# Lane: nursery-repartition — ADR-1546 option 1, measured and refused: the family graph is one blob and the dependency edge is proof-derived

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nursery-repartition, 2026-09-02).** ADR-1546 left
three repair options for the nursery's fused evaluation partitions; lane
`partition-edge-gate` took option 2 (ADR-1550: the crossing EDGE is the unit,
198 baselined, the baseline may only shrink). This lane took **option 1** —
re-partition the drawn rows by connected component of the declared-dependency
graph. The rule is preregistered in **ADR-1551**, implemented in
`scripts/nursery-components.py`, computed exactly, and **not applied**. Five
measurements, all from the shipped tool over the live tree.

1. **The unit is the FAMILY, not the fact.** The policy declares
   `family_leakage` alongside `split_leakage` and `check-autogenesis-nursery.py`
   enforces both. Contracting families turns 357 fact-level components (352
   already single-partition) into **20**: nineteen are a single isolated
   held-out family, and one blob holds **44 families / 520 of the 716 drawn
   rows** across all four partitions. Option 1's literal form puts 72% of the
   population in one partition.
2. **Two families in the blob cannot move, and 51 of the 198 crossings hang
   off them.** `integer-absolute-value` is held-out (ADR-0542, 6 edges);
   `nat-bootstrap` is pinned to exactly `{F:nat-mul-one, F:nat-zero-add}` by
   `check-autogenesis-nursery.py:426` and 45 drawn rows depend on it. No
   re-partition can touch those 51.
3. **The residual cannot take one partition either.** Cut both pins and 42
   families / 508 rows remain in ONE component; assigning it one partition
   empties one of `required_evaluation_partitions`, which is the gate option 1
   exists to turn green.
4. **The rule's best fixed point is 95 crossings, not zero** — 51 pinned plus a
   44-edge residual cut — and it costs 13 families / **146 rows** changing
   partition, taking train from 208 to **122** while
   `check-dispatchable-frontier.py` is already at 2 against a floor of 10.
5. **The graph is not outcome-blind.** `depends_on` is derived from the
   admitted proof term (`check-fact-depends-derived.py`,
   `admission_dependency_authority: proof-derived-kernel-dependency`), so an
   unproved row has no edges. Over the 508 train/development rows, **396 of the
   398 rows that declare any dependency are `proved`** and 22 of the 25 open
   rows are singletons. Partitioning on it makes a row's partition a function
   of whether we proved it — what `split_freeze: before-target-outcomes`
   forbids.

**`gen-autogenesis-nursery-refill.py` is deliberately NOT changed**, for the
same measurement one step further on. A freshly drawn row is `open` and has no
proof term, so it has no edges: of the **221 open drawn rows, 204 (92.3%) are
in no dependency component at all** — neither depending on a drawn row nor
depended on by one — and only 12 declare any `depends_on` whatever. A generator
that "assigns by component" over that graph puts every new row in its own
singleton, is free to choose any partition it likes, and gains a manifest
sentence saying the assignment is component-based. That is a producer that
cannot fail to produce. The v2 manifest's existing published caveat — "no
dependency-component analysis was run" — is the honest description and stays.
The test the brief asked for (a two-module component landing in ONE partition)
IS written and passes, in the rule's own suite: the rule works, the live graph
refuses it.

**Nothing moved.** No manifest row changed partition, no `amendments` array was
extended, no exemption was added, enlarged or deleted. `nursery-v1.json` and
`nursery-v2-extension.json` are byte-identical to their state at lane start,
and `check-draw7-frozen-families.py` reports `moved=0` with its control firing.
The seven component exemptions are **not deleted**: deleting them makes the
component gate redder on more components, and the re-partition that would have
made deletion safe is the thing that cannot be performed.

The refusal can expire. `scripts/nursery-components.py --check` enforces the
five findings against the live tree (F1 a family holding two partitions, F2 the
blob no longer spanning two evaluation partitions, F3 it containing neither
pin, F4 the 51 pinned crossings gone, F5 the rule reaching zero) and is
registered in `scripts/check.sh` and the `justfile`. Seventeen controls, eleven
mutants, eleven single kills.

**Three findings the next lane should act on.**

- **`check-autogenesis-holdout-isolation.py` is RED on `main`, from
  ADR-1550's own artifact.** `artifacts/autogenesis/partition-edge-baseline-v1.json`
  records the six held-out crossing edges by fact id, and the isolation gate
  counts a held-out fact id appearing in a committed file as a reference:
  `held_out=206 recorded_scores=10 references=6 verdict=FAIL`, all six sourced
  to `partition-edge-baseline-v1.json.edges[].from`. ADR-1550 reports
  `check-merge-hygiene.sh` run end to end but not this gate. Nothing this lane
  wrote contributes — the census artifact names exactly two fact ids, both
  longitudinal.
- **A new `artifacts/autogenesis/nursery*.json` file silently makes two gates
  UNANSWERABLE.** The census was first written as
  `nursery-component-census-v1.json`; `check-partition-edges.py`'s
  `MANIFEST_GLOB` read it as a manifest and printed
  `PARTITION-EDGES|UNANSWERABLE ... entries is not a list`.
  `check-autogenesis-nursery.py` globs the same prefix. Renaming to
  `drawn-population-component-census-v1.json` fixed it; narrowing the glob is a
  change to two gates' subject and was not made here.
- **The cheapest real shrink of the 198 is option 2's shape, not option 1's.**
  45 of the 51 pinned crossings are `depends_on F:nat-zero-add` or
  `F:nat-mul-one` — two settled, published bootstrap lemmas that leak no
  evaluation answer. One per-edge amendment class would take the recorded
  baseline from 198 to 153 with nothing relabelled, and ADR-1550's ratchet
  accepts a shrink.

**Gate table, before and after (identical — this lane changed no subject):**
`check-autogenesis-nursery.py` 1/1 · `check-development-partition.py` 1/1 ·
`check-autogenesis-holdout-isolation.py` **1/1 (pre-existing, see above)** ·
`check-holdout-adjacency.py` 0/0 · `check-draw7-frozen-families.py` 0/0 ·
`gen-autogenesis-nursery-refill.py --check` 0/0 ·
`check-dispatchable-frontier.py` 1/1 (2 against a floor of 10) ·
`check-partition-edges.py --baseline` 0/0 (`crossing=198 violations=0`) ·
`validate-facts.py` 0/0 · `check-generated-artifact-ownership.py` **0** (`guarded=4 producers_run=17 fails=0`, including the OWNER arm's byte-for-byte restore of the census from a perturbed copy) · `check-merge-hygiene.sh` 0 · `check-aggregate-scope.sh` 1 (17 pre-existing one-sided steps, none of them this lane's — the two new steps went into both files). **Not run:** `cargo` in any form, `just check`,
`scripts/check.sh` end to end. No `.rs` file was touched.

<!-- plan-section: landed-changes -->

| 2026-09-02 | nursery-repartition | ADR-1551: option 1 refused on five measurements; the family graph is one 44-family / 520-row blob and `depends_on` is proof-derived |
| 2026-09-02 | nursery-repartition | `scripts/nursery-components.py` — the component census, `--propose` for the rule's cost, `--check` for the five findings; registered in `check.sh` and the justfile |
| 2026-09-02 | nursery-repartition | census artifact registered in `check-generated-artifact-ownership.py`; 17 controls, 11 mutants, 11 single kills |
| 2026-09-02 | nursery-repartition | found: `check-autogenesis-holdout-isolation.py` is red on main from ADR-1550's baseline artifact, and a new `nursery*.json` artifact makes two gates unanswerable |
