# ADR-1550: Gate the producer, not the draw — the partition-crossing EDGE is the unit, and its baseline may only shrink

Status: accepted
Date: 2026-09-02
Lane: `partition-edge-gate`

Index-summary: ADR-1546 measured the v2 nursery's evaluation partitions being
fused by producers and left three repair options open. This takes **option 2**:
refuse at close time any `depends_on` edge whose two endpoints sit in different
evaluation partitions, and run that check where producers actually hit it.
`scripts/check-partition-edges.py` changes the UNIT from a weak component to
one edge — a component grows whenever any member gains an edge, which is why
the exemption covering it was re-scoped 228 → 230 → 258 → 274 in four days,
while an edge never changes shape under the person who reviewed it. Measured on
`main`: **198** crossing edges over 716 drawn facts (train→development 83,
development→train 64, train→longitudinal 26, development→longitudinal 19,
held-out→development 4, held-out→train 2), and the manifests' component
exemptions would wave through **154 of the 198**. The 198 are recorded in
`artifacts/autogenesis/partition-edge-baseline-v1.json`; `--baseline` fails only
on edges outside it, so the gate blocks a new crossing from today while the
re-partition repairs the recorded ones, and `--record-baseline` REFUSES any set
that is not a subset of the committed one. Wired into `hooks/pre-push` (0.13 s),
`scripts/check-merge-hygiene.sh` guard 9, `scripts/check.sh` and the justfile.
Ten mutants, ten single kills. Two incidental findings: a plain pickaxe cannot
attribute an edge that entered through a merge (7 of the 198), and ADR-1546's
two named commits are where the component gate flipped, not where the edges
were added — `42847d62c` touched no fact file at all.

Index-status: accepted

## The decision

ADR-1546 left three options and chose none. The coordinator chose **option 2:
gate the producer, not the draw.** Option 1 (component-aware draws) is a
separate lane's; option 3 (retire the property) is not taken.

This ADR records option 2 as implemented, and adds one rule ADR-1546 did not
state: **the recorded baseline may only shrink.**

## Why the unit had to change

`check-autogenesis-nursery.py` enforces
`split_leakage: no-declared-component-may-cross-evaluation-partitions` over the
weak components of the declared-dependency graph. It is right about its
subject. It is the wrong instrument for a producer, for two reasons that are
measurements rather than preferences.

**It ran in no hook.** `hooks/pre-push` ran `check-settled-fact-statements.py`,
`check-holdout-closed-evaluation.py` and `check-semantic-control-fixtures.py`,
and neither nursery gate. The component gate was registered in
`scripts/check.sh:711` and `justfile:248` — the ~10-minute aggregate — so a
producer could close a fact fusing two evaluation partitions and push it with
the property never evaluated. `--baseline` costs **0.13 s**, so there was never
a cost reason for that placement.

**A component is the wrong thing to exempt.** A component grows whenever any
member gains an edge, so an exemption naming a component's fact-id SET goes
stale on the next producer commit, and the cheapest repair is to enlarge it:
228 → 230 → 258 → 274 members in four days against a live component of 305
(ADR-1546's table, each figure read from the JSON at that commit). A gate whose
largest subject is waved through by an exemption enlarged to fit whenever it
fails cannot fail on that subject.

An **edge** has neither property. It is one string in one fact file, it is what
a producer actually adds, and it does not change shape underneath the person
who reviewed it. So an amendment here names ONE edge, a reason and a date, in
`artifacts/autogenesis/partition-edge-amendments-v1.json` (currently empty).
The manifests' `cross_population_component_split_exemptions` and
`component_split_exemptions` are **refused** as amendments and reported as
`NOT-AN-AMENDMENT` — seven of them. That is not a criticism of what they do for
the component gate, whose unit *is* the component; it is that a fact-id set
says nothing about which edge anybody reviewed.

**That refusal is measurable, not rhetorical.** The gate computes the ordered
pairs those seven exemptions would cover and reports how many live violations
they would suppress: `component_exemptions_would_wave=154` of 198. ADR-1546
could not state that number about the gate it audited, because a component
exemption's effect is not expressible per edge.

## What was measured

Bare audit on `main` at `dae09582d`, 0.12 s without attribution and 26.7 s with
it (198 pickaxe queries):

```
PARTITION-EDGES|manifests=2|drawn=716|crossing=198|amended=0|baselined=0
              |violations=198|not_amendments=7|component_exemptions_would_wave=154|FAILED
```

| from → to | edges |
| --- | ---: |
| train → development | 83 |
| development → train | 64 |
| train → longitudinal | 26 |
| development → longitudinal | 19 |
| held-out → development | 4 |
| held-out → train | 2 |
| **total** | **198** |

`longitudinal` counts as a partition here on purpose: ADR-1546's 305-member
component reached it, and an evaluation fact depending on the longitudinal
regression population fuses the two exactly as a train/development edge does.

Attribution by day: **45** on 08-29, **70** on 08-30, **27** on 08-31, **56** on
09-01. The largest single contributor is 15 edges. This is a steady accrual by
many commits, not two careless ones — which is ADR-1546's structural finding
restated at the edge level.

## The ratchet, and the rule

The 198 are not this lane's to repair; re-partitioning is option 1. So
`--record-baseline` froze them into
`artifacts/autogenesis/partition-edge-baseline-v1.json` (edge set, `edge_count`,
`edge_set_sha256`, the ledger digest they were measured against, the recording
date and commit), and `--baseline` fails only on edges outside it.

**THE BASELINE MAY ONLY SHRINK.** `--record-baseline` refuses to write a set
that is not a subset of the committed one, names the new edges, and writes
nothing. Without that, a lane that hit the gate could clear it in one command
and this would be the growing component exemption again under a new name —
which is the failure this whole ADR is a response to. The refusal is
mutation-verified (M5), and its positive control is a genuinely shrunken set
recording with `shrank_by=1` (a mode that never writes would satisfy the
refusal alone).

A baselined edge that stops crossing is reported as `REPAIRED` so the gain gets
locked in rather than quietly held as headroom for the next crossing.

## Where it runs, and why exit 2 differs between two of them

| caller | form | cost | exit 2 |
| --- | --- | ---: | --- |
| `hooks/pre-push` (L0 block) | `--baseline` | 0.13 s | **blocks** |
| `scripts/check-merge-hygiene.sh` guard 9 | `--baseline` | 0.13 s | reported, does not block |
| `scripts/check.sh`, `justfile` | `--baseline` | 0.13 s | step fails |
| by hand | bare | 26.7 s | — |

Exit 2 is `cannot answer`: no nursery manifest, no fact ledger, or `--baseline`
with no baseline file. In `hooks/pre-push` all three mean a **committed
artifact is missing from the tree being pushed**, which is a thing to stop for.
In `check-merge-hygiene.sh` a coordinator mid-merge can legitimately be looking
at a tree where one side has not landed, so it is reported as
`partition_edges=not-answerable`. Same code, different question, and both are
mutation-verified (M16 for the merge-hygiene arm).

The **bare** audit stays out of both aggregates deliberately. It is red by
construction until the re-partition lands, and a standing red in the aggregate
gate is precisely how the exemption this replaces grew: people learn to scroll
past it.

## Checker discipline

Ten mutants over `check-partition-edges.py`, each killing **exactly one** test
(`python3 scripts/tests/mutation_controls.py partition-edges`), plus M15/M16
for merge-hygiene guard 9. Getting to one kill each changed the FIXTURES, not
the guards: the first draft put a same-partition edge in nine scenarios that
did not need one, and the crossing-detection mutant killed six of them.
`one_crossing_only` now serves every scenario whose subject is not the
partition comparison.

`scripts/tests/test-prepush-l0-gates.sh` derives the L0 gate list from the
hook's own loop and asserts it has at least three entries, that every script it
names exists, and that `check-partition-edges.py --baseline` is one of them
with the flag. All three arms were driven to failure against scratch copies of
the hook before being believed.

The baseline artifact is registered in
`scripts/check-generated-artifact-ownership.py` with `--record-baseline` as
sole owner; `guarded=3 producers_run=14 fails=0`, every arm green including
OWNER's byte-for-byte restore from a perturbed copy. That restore is why the
provenance fields are carried forward whenever the edge set is unchanged: a
field stamped with `today`, or with a live digest of a ledger other lanes edit
hourly, would make the artifact impossible to own.

## Two findings that were not the assignment

**A plain pickaxe cannot attribute an edge that entered through a merge.**
`git log -S` skips merge commits, so seven of the 198 were reported as
`no commit adds this string` while the string is plainly in the committed file.
The first of them, `F:ml430-int-add-comm-c5722728 → F:ml430-nat-add-comm-56a2d614`,
was introduced by the merge `0be9ff41b` and by no other commit in that file's
nine-commit history — verified by walking every one of them and counting
occurrences, not by trusting the pickaxe that had just said nothing.
`--diff-merges=first-parent --no-patch` attributes all 198. Anything else in
this repository that attributes a ledger change by pickaxe is blind to evil
merges in the same way.

**ADR-1546's two named commits are where the gate flipped, not where the edges
were added.** `42847d62c` ("pin the fib corollary statement") touched exactly
one file, `artifacts/ontology/settled-fact-statement-pins.json`, and no fact
file at all; the fib edge it names was added by `c1acb4477`. Nothing in
ADR-1546's conclusion depends on this — both edges are real and were read out
of the ledger directly — but the attribution should not be quoted as
"the commit that added the edge".

## Consequences

- A new partition-crossing `depends_on` edge now blocks a push, a merge and
  both aggregate gates from 2026-09-02, at 0.13 s.
- 198 recorded crossings remain. They are option 1's to repair, and the ratchet
  means the number can only go down. `check-autogenesis-nursery.py` stays red
  on its component view and is untouched by this lane.
- `check-development-partition.py` is untouched and remains red on
  `authoritative-mathlib-nat-modeq-remainder-family-v1`, now at least nine days
  (2026-08-26 to 2026-09-02).
- No fact's partition, no manifest row, and no fact's `depends_on` was changed.
  `nursery-v1.json` and `nursery-v2-extension.json` are byte-identical to
  their state at the start of this lane.

## Method notes

- Every number above comes from running the shipped script over the real tree
  and reading its own summary line, never from re-deriving its algorithm.
- The merge-attribution finding was confirmed by an independent walk over the
  file's whole history counting occurrences of the dependency string, because
  the tool that would normally answer it is the tool that had just been wrong.
- Not run: `cargo` in any form, `just check`, `scripts/check.sh`. No `.rs` file
  was touched. `scripts/check-merge-hygiene.sh` was run end to end (see the
  lane status doc for its line).
