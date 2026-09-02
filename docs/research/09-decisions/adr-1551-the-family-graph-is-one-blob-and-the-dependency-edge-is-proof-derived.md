# ADR-1551: Option 1 is refused — the family graph is ONE blob, and the dependency edge it would partition on is proof-derived

Status: accepted
Date: 2026-09-02
Lane: `nursery-repartition`

Index-summary: ADR-1546 left three repair options for the nursery's fused
evaluation partitions; ADR-1550 took option 2 (gate the producer per crossing
edge, 198 baselined, baseline may only shrink). This lane took **option 1** —
re-partition the drawn rows by connected component of the declared-dependency
graph — preregistered its rule, implemented it, computed exactly what it would
do, and **does not apply it**. Four measurements, each from
`scripts/nursery-components.py` over the live tree. (1) The nursery policy also
declares `family_leakage`, so the assignment unit is the FAMILY, not the fact:
contracting families turns 357 fact-level components (352 already
single-partition) into **20**, nineteen of them a single isolated held-out
family and one blob of **44 families / 520 of the 716 drawn rows** spanning all
four partitions. (2) Two families in that blob cannot move —
`integer-absolute-value` is held-out (ADR-0542) and `nat-bootstrap` is pinned
to exactly `{F:nat-mul-one, F:nat-zero-add}` by
`check-autogenesis-nursery.py:426` — and **51 of the 198 crossings are incident
to them**, so no re-partition can touch those. (3) Cut both pins out and 42
families / 508 rows remain in ONE component; giving it one partition empties
one of `required_evaluation_partitions`, which is the gate option 1 exists to
turn green. (4) The rule's best fixed point moves **13 families / 146 rows**,
takes train from 208 to **122** while the dispatchable frontier is already at 2
against a floor of 10, and still leaves **95** crossings — not zero. And the
decisive one: `depends_on` is DERIVED FROM THE ADMITTED PROOF TERM, so **396 of
the 398 train/development rows that declare any dependency are `proved`** and
an unproved row is a singleton by construction. Partitioning on that graph
assigns a row's partition as a function of whether we proved it, which is what
`split_freeze: before-target-outcomes` forbids. Ships the census tool
(`--check` enforces the five findings the refusal rests on; 17 controls,
eleven mutants, eleven single kills), the artifact, and an incidental defect: a new
`artifacts/autogenesis/nursery*.json` file silently makes
`check-partition-edges.py` and `check-autogenesis-nursery.py` UNANSWERABLE.

Index-status: accepted

## What this lane was sent to do

ADR-1546 measured the v2 nursery's evaluation partitions being fused by
producers, recorded that the component gate had been held green by an exemption
re-scoped 228 → 230 → 258 → 274 in four days, refused draw 19, and left three
repair options. Lane `partition-edge-gate` took option 2 and shipped
`scripts/check-partition-edges.py` (ADR-1550): the unit is one crossing edge,
198 are recorded in `artifacts/autogenesis/partition-edge-baseline-v1.json`,
and the baseline may only shrink.

This lane is **option 1**: "make the draw do component analysis — assign v2
partitions against the declared-dependency graph the way v1 does". The brief
was to preregister a deterministic, outcome-blind rule in this ADR, apply it by
amending the manifests, and drive the recorded crossing count toward zero.

The rule is preregistered below and implemented in
`scripts/nursery-components.py`. It is **not applied**. What follows is why,
measured rather than argued.

## The rule, preregistered

Stated once, in the tool (`RULE`) and here, so the two cannot drift:

- **UNIT.** Contract each `family` to one node. Forced, not chosen: the policy
  declares `family_leakage: no-family-may-cross-evaluation-partitions`
  alongside `split_leakage: no-declared-component-may-cross-evaluation-
  partitions`, and `check-autogenesis-nursery.py` enforces both, so a
  component-based assignment must also be family-respecting. Join two families
  when a drawn row of one declares `depends_on` a drawn row of the other; take
  weak components.
- **PINS.** `integer-absolute-value` (held-out; a held-out row never leaves
  held-out, ADR-0542) and `nat-bootstrap` (longitudinal; pinned to exactly
  `{F:nat-mul-one, F:nat-zero-add}` in `check-autogenesis-nursery.py`) keep
  their partition and are removed from their component. Every crossing edge
  incident to them becomes a per-edge amendment.
- **ASSIGNMENT.** Each residual component takes ONE partition — the one its
  declared dependencies bind it to most strongly — computed by moving the
  single family with the largest crossing-weight gain until no move improves,
  in lexicographic family order, ties keeping the incumbent, subject to `train`
  and `development` each retaining at least
  `policy.evaluation_fact_count.minimum` (100) rows.

It is deterministic (fixed order, fixed tie-break, no seed) and its arithmetic
never reads a proof status or a score. That is not the same as outcome-blind,
and the difference is the fourth finding below.

The rule works. `scripts/tests/test_nursery_components.py` fixes a two-family,
two-module component split across partitions and asserts it lands in ONE
partition with a residual cut of zero — the property option 1 was supposed to
deliver. **The refusal below is a statement about the live graph, not about the
rule being unimplementable.**

## What was measured

`python3 scripts/nursery-components.py --propose`, worktree at `a44a41313`
after `git merge main` (main at `024929ec5`). The tool's `crossings now 198`
is computed independently and agrees exactly with
`check-partition-edges.py`'s `crossing=198`, so neither number is derived from
the other's report.

### 1. The fact-level picture looks tractable and is not

| view | components | already single-partition |
| --- | ---: | ---: |
| `depends_on` over drawn facts | 357 | 352 |
| the same, with families contracted | **20** | 19 |

Fact-level sizes: `{1: 334, 2: 8, 3: 7, 4: 2, 5: 3, 7: 1, 10: 1, 305: 1}`. The
305-member component is ADR-1546's, and its shape is unchanged:
`{development 172, train 126, held-out 5, longitudinal 2}`.

Contract the families — which `family_leakage` forces — and the picture
changes completely:

| family component | families | rows | partitions |
| --- | ---: | ---: | --- |
| the blob | **44** | **520** | development 300, train 208, held-out 10, longitudinal 2 |
| ×19, one apiece | 1 | 10 (one is 16) | held-out |

**Nineteen of the twenty components are a single isolated held-out family.
Everything else — 520 of 716 drawn rows, including every train and every
development row — is one blob.** Option 1's literal form ("a component is
assigned ONE partition") therefore assigns 72% of the drawn population to a
single partition.

### 2. Two families in the blob cannot move, and 51 crossings hang off them

| pin | authority | incident crossing edges |
| --- | --- | ---: |
| `integer-absolute-value` | held-out; ADR-0542, a held-out row never leaves held-out | 6 |
| `nat-bootstrap` | `check-autogenesis-nursery.py:426` pins the longitudinal partition to exactly `{F:nat-mul-one, F:nat-zero-add}` | 45 |
| | **total** | **51** |

`F:nat-zero-add` and `F:nat-mul-one` have in-degree 24 and 22 from drawn rows —
they are `Nat.zero_add` and `Nat.mul_one`, the bootstrap lemmas a quarter of the
nursery rests on. Their rows cannot be relabelled and their in-edges cannot be
removed by relabelling anything else, so **51 of the 198 crossings survive any
re-partition whatsoever.** They are repairable only as per-edge amendments,
which is option 2's mechanism, not option 1's.

The brief anticipated the held-out half of this ("cut that row's edges and
record each cut as a per-edge amendment") and it is the right handling. It does
not anticipate the longitudinal half, which is three quarters larger.

### 3. The residual cannot take one partition either

Remove both pins and **42 families / 508 rows remain in one component.**
Assigning it one partition empties `train` or `development`, and
`check-autogenesis-nursery.py` reports that as `empty-partition:` against
`required_evaluation_partitions: [train, development, held-out]` — the very
gate option 1 exists to turn green.

That check is scoped to `nursery-v1` alone (`build_report`, line 543), which
does not weaken it: **every v1 train family and every v1 development family is
in the blob.** v1's train side is `integer-fibonacci`, `integer-gcd`,
`integer-modular-equivalence`, `natural-factorial`, `natural-fibonacci`; its
development side is `natural-binomial`, `natural-bitwise`, `natural-gcd`,
`natural-logarithm`, `natural-modular-equivalence`, `natural-primes`. All
eleven are blob members, and v1's only family outside it is the held-out
`natural-square-root`. So whichever partition the blob takes, the OTHER one is
empty in v1 and the blocker fires. So option 1's literal form is not merely
unbalanced; it is refused by the gate it is meant to satisfy.

The rule above therefore cuts the residual, and the cost of cutting it is the
next measurement.

### 4. The best the rule can do, and what it costs

`--propose`, floor 100 rows per partition:

| moves | crossings | development rows | train rows |
| ---: | ---: | ---: | ---: |
| 0 (today) | **198** | 300 | 208 |
| 1 | 175 | 310 | 198 |
| 2 | 154 | 320 | 188 |
| 5 | 128 | 331 | 177 |
| 7 | 109 | 351 | 157 |
| 10 | 99 | 371 | 137 |
| **13 (fixed point)** | **95** | **386** | **122** |

Thirteen families move; **146 of the 716 drawn rows change partition**; the
crossing count falls 198 → 95, of which 51 is the pinned floor and 44 the
residual cut. It does not reach zero and cannot: 51 is a hard floor and a
balanced two-colouring of a 42-node graph carrying 323 inter-family edges costs
about 40 more.

Two prices are worth stating separately from the number.

**Train falls from 208 rows to 122.** Train is the population producers author
against. `check-dispatchable-frontier.py` is red at **2** dispatchable against
a floor of 10 and draw 19 was refused (ADR-1546) precisely to refill it.
Shrinking the workable population by 41% to improve a crossing metric moves in
the opposite direction from the thing the refusal of draw 19 was protecting.

**And the split stops being preregistered.** `split_freeze:
before-target-outcomes` is the property that makes a development number mean
anything. Re-labelling 146 rows today, when the outcomes for most of them are
known, replaces a frozen split with one chosen after the fact — whatever the
choosing algorithm looked at.

### 5. The decisive one: the graph is not outcome-blind

The rule's arithmetic never reads `epistemic_status`. The graph it runs on
does, structurally.

`depends_on` on a kernel-route fact is **derived from the admitted proof term**
— `scripts/check-fact-depends-derived.py` reads it out of
`Kernel::theorem_dependencies`, and the policy says so:
`admission_dependency_authority: proof-derived-kernel-dependency`. An unproved
row has no proof term, therefore no derived edges, therefore no component.

Measured over the 508 train/development rows:

| | declares any `depends_on` | declares none |
| --- | ---: | ---: |
| `proved` | **394** | 89 |
| `open` | 2 | 23 |

| | in a component | singleton |
| --- | ---: | ---: |
| `proved` | 358 | 125 |
| `open` | 3 | 22 |

**396 of the 398 rows that carry any dependency at all are proved; 22 of the 25
open rows are singletons.** So a component is, to a very good approximation,
a record of what we have proved and how. Assigning partitions from it assigns a
row's partition as a function of our own results — the exact thing
`split_freeze: before-target-outcomes` exists to prevent. ADR-0615's caveat
that a dependency graph "is not available at draw time" is the same fact seen
from the other end, and ADR-1546 quoted it without following it through to
here: **it is not available at draw time because it is an outcome.**

**And the same measurement refuses the generator change option 1 asks for.**
The brief's fifth deliverable was to make `gen-autogenesis-nursery-refill.py`
assign future draws by component under this rule. A freshly drawn row is `open`
and has no proof term, so it has no edges: measured over the 221 open drawn
rows, **204 (92.3%) are in no dependency component at all** — neither
depending on a drawn row nor depended on by one — and only 12 declare any
`depends_on` whatsoever. A generator that "assigns by component" over that
graph puts every new row in its own singleton and is free to choose any
partition it likes, while the manifest gains a sentence saying the assignment
is component-based. That is a producer that cannot fail to produce, which is
the shape CLAUDE.md names, so the generator is **not changed**. The v2
manifest's existing published caveat — "no dependency-component analysis was
run" — is the honest description and it stays.

This is why the rule is implemented and not run. A deterministic algorithm over
an outcome-derived graph is not an outcome-blind partition; it is an
outcome-dependent partition with a reproducible spelling.

## Decision

**Option 1 is refused, and the refusal is conditional and checkable.** No
manifest row moved partition, no `amendments` array was extended, no exemption
was added, enlarged or deleted. `nursery-v1.json` and
`nursery-v2-extension.json` are byte-identical to their state at the start of
this lane.

Refusing is the cheap half. The expensive half is that the obvious alternative
— apply the rule anyway and take 198 → 95 — is also refused, for finding 5:
it would buy a 52% cut in a metric by making the evaluation split a function of
our own results, and no gate anywhere would report that it had happened.

What ships instead:

- **`scripts/nursery-components.py`.** The census ADR-1546 asserted option 1
  needed and nobody had run. `--propose` computes the rule's assignment and its
  full cost curve without touching a manifest, so whoever holds the authority
  to spend 146 rows can see the exact trade and act in one command.
- **`--check`, which can go red.** The findings above are not left as prose in
  an ADR that accumulates staleness by construction. Five of them are enforced
  against the live tree: F1 a family holding two partitions (the contraction
  stops being forced), F2 the largest family component no longer spanning two
  evaluation partitions, F3 that component containing neither pin, F4 the 51
  pinned crossings disappearing, F5 the rule reaching zero. **Each one firing
  means option 1 has become feasible and this ADR must be re-decided.** A
  refusal nobody can falsify is the growing exemption in a different costume.
- **`artifacts/autogenesis/drawn-population-component-census-v1.json`**,
  registered in `check-generated-artifact-ownership.py` with `--record` as sole
  owner.

## What the next lane should look at instead

Not a recommendation this lane has the authority to make, but the measurements
point somewhere specific:

1. **The 51 pinned crossings are the cheapest real win and they are option 2's
   shape, not option 1's.** 45 of them are `depends_on F:nat-zero-add` or
   `F:nat-mul-one` — dependencies on two settled, published bootstrap lemmas
   that leak no evaluation answer. A single per-edge amendment class for
   "dependency on the Autogenesis-1 longitudinal chain" would take the recorded
   baseline from 198 to 153 with nothing relabelled, and the ratchet in
   ADR-1550 accepts a shrink.
2. **`integer-absolute-value` needs an ADR-0542 decision, not a partition
   change.** It is the only held-out family that appears in any dependency
   component at all, and `depends_on` is proof-derived — the two facts together
   are the breach signature ADR-0542 describes. ADR-1546 already recorded the
   component membership publicly; what is owed is the amendment, and this lane
   does not have the authority to write one against a held-out family.
3. **Option 3 deserves the measurement it never got.** ADR-1546 offered
   "retire the property" as the cheapest of the three. Finding 5 says the
   property `split_leakage` asserts cannot be established at draw time even in
   principle, because the graph it quantifies over does not exist until after
   the outcomes do. That is an argument for option 3 that ADR-1546 did not
   have.

## An incidental defect, found by tripping over it

**A new file matching `artifacts/autogenesis/nursery*.json` silently makes two
gates unanswerable.** The census artifact was first written as
`nursery-component-census-v1.json`; `check-partition-edges.py`'s
`MANIFEST_GLOB` is `artifacts/autogenesis/nursery*.json`, so it read the census
as a manifest and printed

```
PARTITION-EDGES|UNANSWERABLE artifacts/autogenesis/nursery-component-census-v1.json: entries is not a list
```

`check-autogenesis-nursery.py` globs the same prefix. Exit 2 is `cannot
answer`, and in `hooks/pre-push` that blocks — so the failure mode is loud
there and quiet in `check-merge-hygiene.sh`, which reports exit 2 as
`partition_edges=not-answerable` by design. Renaming the artifact to
`drawn-population-component-census-v1.json` fixed it. The general shape is the
one CLAUDE.md names about prefix filters: **a glob over a shared directory is a
literal that anyone can match by accident**, and neither gate can tell a new
manifest from a new artifact that happens to start with the same six letters.
Not repaired here — narrowing the glob is a change to two gates' subject and
belongs to whoever owns them.

## Consequences

- The 198 recorded crossings stand. ADR-1550's ratchet is untouched and
  `check-partition-edges.py --baseline` remains green at
  `crossing=198|violations=0`.
- `check-autogenesis-nursery.py` and `check-development-partition.py` remain
  red, unchanged by this lane, on exactly the subjects ADR-1546 dated. The
  seven component exemptions are neither deleted nor enlarged: deleting them
  makes the component gate redder on more components, and this lane's finding
  is that the re-partition which would have made deletion safe cannot be
  performed.
- `check-dispatchable-frontier.py` stays at 2 against a floor of 10. Draw 19
  still needs authoring and this lane did not unblock it.
- No held-out row's outcome is named here, nothing was dispatched, and
  `check-draw7-frozen-families.py` reports `moved=0` before and after.

## Method notes

- Every number comes from running the shipped script over the real tree and
  reading its own output. The one cross-check that matters — `crossings now
  198` against `check-partition-edges.py`'s `crossing=198` — is between two
  independently written implementations of the same count, neither reading the
  other.
- The epistemic-status tables were computed over the 508 train/development rows
  only. The held-out population is not tabulated here.
- The mutation table is `python3 scripts/tests/mutation_controls.py
  nursery-components`: ten mutants, each killing exactly one of 16 tests. N8
  ("a pinned family is never proposed for a move") SURVIVED its first run — the
  pin was on family NAME and every fixture labelled the pinned families
  held-out or longitudinal, which the partition filter on the next line already
  excluded, so the pin was doing nothing any test could see. The fixture that
  fixes it labels `integer-absolute-value` `development` and pulls it hard
  toward `train`. A guard whose only fixtures make it redundant is the blind
  spot CLAUDE.md names about mutation testing.
- N11 exists because `check-generated-artifact-ownership.py`'s OWNER arm went
  red on the first registration: `size_distribution` was a dict keyed by
  component SIZE, JSON object keys are strings, and a block written in numeric
  order came back re-sorted lexicographically (`"10"` before `"2"`) the moment
  `--record` carried it forward. The artifact was not a fixed point of its own
  writer. The OWNER arm is the only thing in this repository that would have
  found that, and the fixture that now pins it needs components of size 10 AND
  2 — a distribution of `{1: n}` round-trips cleanly under either ordering and
  would have passed forever.
- Not run: `cargo` in any form, `just check`, `scripts/check.sh`. No `.rs` file
  was touched and `shape_search` was not rebuilt — no candidate screening was
  reached, because no candidate was selected.
