# Lane: scored-residue-class — the last red partition gate is green, on a re-derived amendment class

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, scored-residue-class, 2026-09-02).** ADR-1565
identified the last red partition gate's whole subject and named two repairs.
This lane built the second: a component-level analogue of ADR-1563's per-edge
amendment class, **keyed to the evaluation record and never to a fact id**
([ADR-1566](../../research/09-decisions/adr-1566-a-scored-evaluations-residue-is-an-amendment-class-keyed-to-the-evaluation-record.md)).

**The rule as implemented.** `scored-evaluation-residue` is honoured only when
`class_complaint` re-derives all four clauses — none is taken on the
amendment's word, and none is stated in the artifact:

| clause | re-derived from |
| --- | --- |
| (d) keyed to `evaluation_record`, a `record_id` in `holdout-evaluation-v1.json` | the record file |
| (c) the edge runs **from** the blind row to a non-blind one | the live manifests and `policy.blind_partitions` |
| (a) the edge's **blind endpoint** is in that record's `outcomes` **and** in the family the record names | the live manifests (`family`) and the record |
| (b) the record's `state` is `scored`, and its `protocol_commit` is a **strict git ancestor** of the commit that introduced the edge | `git merge-base --is-ancestor` plus the first-parent pickaxe |

Clause (a) is written against the **blind endpoint**, not the edge's source.
Written against the source it would also refuse a reversed edge, and clause
(c)'s mutant would then kill nothing while looking exactly as present.

**No held-out row is named anywhere.** A blind endpoint is written in the
salted-digest form the baseline already uses, and `ClassContext.resolve`
inverts it through the live manifests. `check-autogenesis-holdout-isolation.py`
still scans the amendments artifact (verified: 1121 scan targets, the file
among them) and still reports `references=0`.

**Measured.** `check-partition-edges.py --baseline`: **baseline 6 → 0**,
`violations=0`, `amended=51`, a no-op re-record byte-identical (`317c5f2c…`
twice). `check-autogenesis-nursery.py`: **1 crossing component → 0**, both
report paths, `component_split_leaks: []` and
`evaluation_longitudinal_component_overlap: []` on each. It stands on nothing
suppressed: `component_split_exemptions` and
`cross_population_component_split_exemptions` are both **0 entries**, and the
edge baseline is **0 edges**. The nursery gate honours the class through the
edge gate's own `load_amendments` and a new shared `edge_is_amended`, so what
an amendment covers is decided in one place, not two.

**The one tolerance, and why it is loud.** Clause (b) is a question about the
commit graph, and three real trees have none: `mutation_controls.py` copies the
checkout with `.git` in its `ignore_patterns`, a `git archive` lane snapshot
has no history, and a fixture tree is built from scratch. Refusing there would
make the gate red on a fact about *where it ran*; honouring silently would
claim a clause held that was never asked. So the clause is **skipped and
reported** — a `CLASS-UNVERIFIED` line and a `class_unverified=N` field on both
gates — and M30 is the mutant that asserts availability instead.

**The three seals ADR-1565 restored still hold**, each a synthetic population
differing from the accept case in one thing: an amendment naming a record that
does not exist, an edge INTO the scored blind row, and an edge whose
introducing commit predates the preregistration. All three still fail
`check-autogenesis-nursery.py`; all three are refused by name in the edge
gate's own suite at one mutant kill each.

**Mutation.** `partition-edges`: 42 tests, 28 mutants, **26 kill exactly one**.
M24 (record key) · M25 (scored membership) · M26 (direction) · M27
(preregistration order) · M28 (record state) · M29 (redacted matching) · M30
(the tolerance) are the new ones, one kill each. **M11 kills 2**, and the
second is not an accident: `redacted_key` is one rule with two readers now
(what the baseline records, and which form an amendment may name a blind
endpoint in). Retargeting it at `redacted_row` to force a single kill was tried
and is worse — three kills, two of them for a self-inconsistency the shipped
code cannot have. `nursery-split-exemption-guards`: 26 tests, 11 mutants; **N1
kills 2** (its own accept case and the new class's, which is the positive
control the three seals need); N2/N3/N5/N6/N7 one each; the four pre-existing
2-kill mutants are unchanged.

**Gate table, all run by name, all green.** `check-development-partition` 0 ·
`check-autogenesis-holdout-isolation` 0 (`references=0`, `recorded_scores=10`,
`files_scanned=1114`) · `check-holdout-adjacency` 0 ·
`check-holdout-closed-evaluation` 0 · `check-dispatchable-frontier` 0 ·
`check-draw7-frozen-families` 0 (`new families: []`) ·
`check-partition-edges --baseline` **0** · `check-autogenesis-nursery` **0** ·
`gen-autogenesis-nursery-refill --check` 0 ·
`create-autogenesis-mathlib-nursery-split.py --check` 0 ·
`frontier-shape-census --check` 0 (`current`; regenerated byte-identical) ·
`validate-facts` 0 · `check-control-registration.sh` 0 (`controls=52
orphans=0`).

**For the next lane.** The audit question for the next `held-out -> X` edge is
now executable rather than advisory: which commit introduced it, and does the
preregistering commit strictly precede it. Answer yes and it is one amendment;
answer no and it is a leak to repair or reclassify. Nothing was moved between
partitions, no row's outcome or id appears in any artifact this lane wrote, and
`integer-absolute-value` remains held-out and remains spent exactly as
`holdout-evaluation-v1.json` already records. No cargo work was in scope and
none was run.

<!-- plan-section: landed-changes -->

| 2026-09-02 | scored-residue-class | lane opened; status stub |
| 2026-09-02 | scored-residue-class | ADR-1566: a scored evaluation's residue is an amendment class keyed to the record, never to a fact |
| 2026-09-02 | scored-residue-class | `scored-evaluation-residue` in `check-partition-edges.py`, four re-derived clauses; baseline 6 → 0 |
| 2026-09-02 | scored-residue-class | `check-autogenesis-nursery.py` honours it through the edge gate's own loader and the shared `edge_is_amended`; 1 crossing component → 0 |
| 2026-09-02 | scored-residue-class | fourteen controls incl. the three seals; M24–M30 one kill each; the git-less tolerance is reported, not silent |
