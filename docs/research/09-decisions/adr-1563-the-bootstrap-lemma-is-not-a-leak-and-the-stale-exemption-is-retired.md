# ADR-1563: the bootstrap lemma is not a leak, the stale exemption is retired, and the receipt cannot be

Status: accepted
Date: 2026-09-02
Lane: `partition-gates-green`

Index-summary: Two red partition gates, three repairs, one refusal.
**(1)** 45 of the 198 baselined crossing edges point INTO the two Autogenesis-1
bootstrap lemmas, which ARE the whole `longitudinal` partition. A new per-edge
amendment class `depends-on-longitudinal-bootstrap` covers them; the class is
**re-derived** by `class_complaint` from the live manifests, is
direction-specific (`longitudinal -> evaluation` can never carry it), and
`--record-baseline` now excludes honoured amendments so deleting one turns its
edge back into a violation. **Baseline 198 -> 153.**
`check-autogenesis-nursery.py` contracts the SAME amendments out of its
component adjacency, through the edge gate's own loader rather than a second
hardcoded rule. **(2)** Two component exemptions matched no live crossing
component and are deleted, **7 -> 5**: the 274-member one ADR-1546 measured
growing 228 -> 274, already stale on `main`; and an 11-member one whose
component crossed only because the bootstrap lemmas fused it. `check-autogenesis-
nursery.py`'s v1 arm is green; its cross-population arm went from **3 violation
types to 1**, and within that one type from **3 crossing components to 5** —
the count rose because the 305-member blob was HIDING two dev/train crossings,
and the mass fell (largest component 305 -> 287). **(3)**
`check-development-partition.py` is green. Its one violation could NOT be
retired the ADR-1510 way: `check-autogenesis-fact-operation.py` pins
`operation_sha256 = digest(operation)` inside the evidence of all three facts
the operation admitted (live `cc868669…`, matching; adding one key moves it to
`d610b146…`), so a receipt is immutable by construction. A dated grandfather in
source instead, with both its properties re-derived. **Two handoff corrections,
measured:** the operation landed `9943ae6bd` (2026-08-26), not 2026-08-27, and
was NOT pre-rule — this gate shipped `50307d833` four days earlier and the
facts were already `development`; the gate was red and it landed anyway.
**The refusal:** the remaining 153 crossings are NOT amended. The premise that
"train is the non-evaluation partition" contradicts the committed,
`before-target-outcomes` split policy, whose `required_evaluation_partitions`
is `[train, development, held-out]`; and the 6 held-out-endpoint crossings are
structurally un-amendable, because the amendments artifact is inside
`check-autogenesis-holdout-isolation.py`'s scan set (verified: 1121 targets,
the file among them).

Index-status: accepted

## Context

Two gates were red, and the exit criterion in
[ADR-1546](adr-1546-draw-19-is-refused-and-the-partition-gate-is-held-green-by-a-growing-exemption.md)
asks for every partition gate green with the exemption list shrinking.

[ADR-1550](adr-1550-gate-the-producer-the-crossing-edge-is-the-unit.md) landed
the per-edge ratchet: 198 crossing `depends_on` edges baselined, may only
shrink, honoured amendments are per-edge or not at all.
[ADR-1551](adr-1551-the-family-graph-is-one-blob-and-the-dependency-edge-is-proof-derived.md)
refused re-partitioning by dependency component, because `depends_on` is
derived from proof terms and is therefore not a free variable.

That left `check-autogenesis-nursery.py` red on three violation types in its
cross-population arm (three crossing components, one stale exemption, one
longitudinal overlap) and `check-development-partition.py` red on one producer.

## Decision 1 — the bootstrap lemma is not a leak

`check-autogenesis-nursery.py:426` pins the `longitudinal` partition to exactly
`["F:nat-mul-one", "F:nat-zero-add"]` and raises if it is anything else. Those
two are the axioms-of-the-library: every partition must be free to depend on
them, and none is ever evaluated on them.

Measured over the 198 baselined crossings, by target:

| target | partition | edges in |
| --- | --- | --- |
| `F:nat-zero-add` | longitudinal | 23 |
| `F:nat-mul-one` | longitudinal | 22 |

45 edges, and every edge into `longitudinal` in the whole set goes to one of
those two. An edge into a row that is never a target and that every partition
shares carries no information about the source's partition. It is not a leak.

So `scripts/check-partition-edges.py` grows an amendment **class**,
`depends-on-longitudinal-bootstrap`, with three properties that keep it from
being ADR-1546's growing exemption at a finer unit:

* **The class is re-derived, never asserted.** `class_complaint` reads the
  edge's target partition from the LIVE manifests. An amendment claiming the
  class for a non-longitudinal target is reported and NOT honoured, exactly as
  a missing field is. An unrecognised class name is likewise refused rather
  than skipped as an unknown extra field — a typo must not silently downgrade a
  class-checked amendment to an unchecked one.
* **The direction is half the rule.** Only `to_partition == longitudinal`. The
  reverse — a longitudinal fact whose proof depends on a drawn evaluation fact
  — pulls a drawn result into the regression chain and IS a leak. It can never
  carry this class, which is what keeps the nursery gate's
  longitudinal-overlap check failable in the one direction it can fail
  honestly.
* **`--record-baseline` excludes honoured amendments.** Without this an amended
  edge would sit in both lists, deleting its amendment would change nothing,
  and every class check above would gate nothing observable. With it, the
  amendment is load-bearing: drop it and the edge is a violation against a
  baseline it is no longer in.

Each of the 45 edges is amended individually, with a reason and a date, in
`artifacts/autogenesis/partition-edge-amendments-v1.json`.

**Baseline 198 -> 153** (`shrank_by=45`). The ratchet's refusal to grow is
untouched, and a no-op re-record is still byte-identical (checked:
`529fa8be…` twice).

The remaining 153, by direction:

| from | to | edges |
| --- | --- | --- |
| train | development | 83 |
| development | train | 64 |
| held-out | development | 4 |
| held-out | train | 2 |

### The nursery gate contracts the same amendments, not a second rule

`check-autogenesis-nursery.py`'s `components()` now skips the adjacency of any
edge the edge gate honours, loading them through **the edge gate's own
`load_amendments`** by path rather than re-parsing the artifact. Two readers of
one exemption list that disagree about which entries are valid is a pair of
reports describing no tree at all.

That is also why the contraction is not a hardcoded longitudinal rule in the
nursery gate. A hardcoded rule would make the longitudinal-overlap check
structurally unable to fail — the failure mode CLAUDE.md names — where an
amendment leaves it failable and per-edge deletable. The controls drive exactly
this: `N1` deletes the contraction, `N2` makes it *undirected* (the mutation
that would clear the leaking direction along with the benign one), `N3` lets a
refused amendment read as no amendment. Each kills exactly one test.

## Decision 2 — retire the two exemptions that suppress nothing

The gate's own `unused_exemptions` criterion, acted on rather than reported:

| file | key | members | date | why it suppresses nothing |
| --- | --- | --- | --- | --- |
| `nursery-v2-extension.json` | `cross_population_component_split_exemptions[1]` | 274 | 2026-08-30 | The entry ADR-1546 measured growing 228 -> 230 -> 258 -> 274 against a live component of 305. Stale on `main` independently of this lane. |
| `nursery-v1.json` | `component_split_exemptions[3]` | 11 | 2026-09-01 | Nine facts plus `F:nat-mul-one` and `F:nat-zero-add`; it crossed train/development ONLY because the two bootstrap lemmas fused it. Contract them out and the nine-member residue does not cross at all. |

**Exemptions 7 -> 5** (v1 4 -> 3, cross-population 3 -> 2). Deletions only;
both files round-trip byte-identically through `json.dumps` in their own
format, and the write asserts that before touching either.

The second one is superseded rather than re-scoped, which is what
[ADR-1455](adr-1455-nursery-exemption-guards-and-rescope.md) had to do to
it three days earlier.

### The count of crossing components rose, and that is the honest direction

| | `main` | here |
| --- | --- | --- |
| v1 arm | green | green |
| cross-population violation TYPES | 3 | 1 |
| crossing components | 3 | 5 |
| largest crossing component | 305 (dev/held-out/**longitudinal**/train) | 287 (dev/held-out/train) |
| facts sitting in a crossing component | 319 | 307 |
| stale exemptions reported | 1 | 0 |
| longitudinal-overlap components | 1 | 0 |

Two of the five (4 and 2 members) are NEW rows in the report and were not new
in the tree: the 305-member blob was fusing them through the bootstrap lemmas
and hiding them. That is the shape of "a stable number can be stably wrong" —
a catch-all absorbing items nobody counted — and the repair makes the count
worse and the report true. The mass is the number that fell.

## Decision 3 — the receipt cannot be retired, so it is grandfathered and checked

`authoritative-mathlib-nat-modeq-remainder-family-v1` references three
`natural-modular-equivalence` development facts and no train fact.

**ADR-1510 retirement is not available, and the reason is mechanical.**
`scripts/check-autogenesis-fact-operation.py` computes
`operation_sha256 = digest(operation)` over the whole object and compares it to
what the fact recorded, and separately requires the fact's id to appear in the
live `applicability.fact_ids`. Measured 2026-09-02:

* live digest `cc868669229a7ce96eb8b2991fee1dbf8b994ef23d383128acf7bcc06435a746`,
  which is exactly what all three facts record;
* adding a single `lifecycle` key moves it to `d610b146…`.

So the operation can be neither edited nor deleted without breaking three
`proved` facts' evidence. `gen-obstruction-producers.py` can retire a fulfilled
*contract* because a contract is prospective; an operation is a **receipt**
(ADR-0602) and a receipt is immutable by construction.

**Two corrections to the handoff, both measured.** The operation was registered
`9943ae6bd` (2026-08-26), not 2026-08-27. And it was NOT authored "before any
rule forbade it": `check-development-partition.py` shipped `50307d833` on
2026-08-22, four days earlier and already wired into `check.sh` and the
`justfile`, and all three facts carried `partition: development` in
`nursery-v1.json` at `9943ae6bd`. The gate was red and the operation landed
anyway. This is a grandfather in the literal sense — the rule applied and was
not enforced — not an exemption for a pre-rule landing.

So: `GRANDFATHERED_OPERATIONS`, a **closed list in source**, not a data file. A
producer lane can edit an artifact to clear its own gate; joining a dict in the
gate's source is a reviewed code change with an ADR behind it. Neither property
is taken on the entry's word — `grandfather_holds` re-derives that

1. every development fact the operation covers is SETTLED, so a grandfather can
   never park live development work; and
2. every one of them pins THIS operation in its own evidence — the property
   that makes retirement impossible, which is the actual justification rather
   than a restatement of it.

A failing entry falls through to the same violation the rule always produced,
with the reason printed alongside. An entry that fires on nothing is itself a
violation. And the rule is not weakened for future producers: a new operation
is not in the dict, and property 2 is false for it at registration, when its
targets are open and pin nothing. `test_a_new_development_only_operation_is_
still_a_violation` is that property, driven.

## The refusal — the remaining 153 crossings are not amended

The handoff offered a second amendment class for `development -> train` edges,
on the argument that train is the non-evaluation partition so depending on it
leaks nothing about development outcomes. **That premise does not survive
reading the policy it would amend.** `nursery-v1.json`'s `policy` block, frozen
`before-target-outcomes`, says:

```
"required_evaluation_partitions": ["train", "development", "held-out"],
"split_leakage": "no-declared-component-may-cross-evaluation-partitions"
```

and `check-autogenesis-nursery.py:21` is `EVALUATION_PARTITIONS = {"train",
"development", "held-out"}`. Train IS an evaluation partition here. Writing 64
amendments asserting the opposite would be amending the gate to disagree with
the preregistered split, at a finer unit than the exemption ADR-1546 refused —
which is the same act, not a better one.

The 6 held-out-endpoint crossings are refused for a second, independent reason:
**they are structurally un-amendable through this mechanism.** An amendment
names its endpoints in plain text, and
`artifacts/autogenesis/partition-edge-amendments-v1.json` is inside
`check-autogenesis-holdout-isolation.py`'s scan set — verified by enumerating
`scan_targets()` (1121 files, the amendments file and the baseline among them).
ADR-1550 already paid for this once: its first baseline was six such breaches,
which is why a held-out endpoint is stored there as a salted digest. A
digest-keyed amendment would name an edge nobody could review, which is the one
thing this whole mechanism refuses.

So `check-autogenesis-nursery.py`'s cross-population arm **stays red**, on one
violation type and five components, and the 153 baselined crossings stay
baselined. That is ADR-1546 option 1's work — the re-partition — and ADR-1551
already recorded why it is hard. This ADR shrinks what can be shrunk with a
rule a reader can re-derive and leaves the rest visible.

## Two findings outside the brief

* **`nursery-v1.json` is a generated file whose generator does not know about
  the exemptions it carries.** `create-autogenesis-mathlib-nursery-split.py
  --check` is a registered `check.sh` step, it has been red on `main`, and the
  reason is that `build()` emits no `component_split_exemptions` key at all —
  so the file has been stale against its own generator since the first
  exemption was added. Deleting one made the diff smaller and did not fix it.
  Not this lane's to repair, but nobody should re-scope an exemption believing
  that gate is green.
* **`nursery-v2-extension.json` seals itself**, and the deletion broke that
  seal: `gen-autogenesis-nursery-refill.py --check` was exit 0 on `main` and
  exit 1 here until `extension_sha256` was recomputed with the generator's own
  `digest` (`0eb9f43f…` -> `3bab61a4…`). It was found by running the whole
  partition-gate table against a `main` snapshot rather than only the two gates
  this lane set out to fix.

## Consequences

* `check-development-partition.py`: green.
* `check-partition-edges.py --baseline`: green, on a baseline of 153 rather
  than 198.
* `check-autogenesis-nursery.py`: still red, with a smaller and truer subject —
  1 violation type instead of 3, and the reason for the remaining one recorded
  above.
* The exemption list shrinks (7 -> 5) and the amendment list is 45 entries with
  one re-derived rule rather than 45 judgements.
* Nothing was moved between partitions. No held-out row's outcome is named
  anywhere in this ADR or in any artifact this lane wrote.
