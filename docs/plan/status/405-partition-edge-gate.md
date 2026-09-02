# Lane: partition-edge-gate — ADR-1546 option 2, taken: the crossing EDGE is the unit and its baseline may only shrink

<!-- plan-section: lane-status -->

**Done (`DONE`, partition-edge-gate, 2026-09-02).** ADR-1546 left three repair
options for the v2 nursery's partitions being fused by producers. This lane
implemented **option 2 — gate the producer, not the draw** — and recorded it as
taken in [ADR-1550](../../research/09-decisions/adr-1550-gate-the-producer-the-crossing-edge-is-the-unit.md).
Option 1 (component-aware draws) is untouched and is the next lane's. **No
fact's partition, no manifest row and no fact's `depends_on` was changed**;
`nursery-v1.json` and `nursery-v2-extension.json` are byte-identical to their
state at the start.

**The measurement on `main`** (`scripts/check-partition-edges.py`, bare audit,
0.12 s without attribution / 26.7 s with it):

```
PARTITION-EDGES|manifests=2|drawn=716|crossing=198|amended=0|baselined=0
              |violations=198|not_amendments=7|component_exemptions_would_wave=154|FAILED
```

| from → to | edges | | attribution by day | edges |
| --- | ---: | --- | --- | ---: |
| train → development | 83 | | 2026-08-29 | 45 |
| development → train | 64 | | 2026-08-30 | 70 |
| train → longitudinal | 26 | | 2026-08-31 | 27 |
| development → longitudinal | 19 | | 2026-09-01 | 56 |
| held-out → development | 4 | | | |
| held-out → train | 2 | | largest single commit | 15 |
| **total** | **198** | | | |

**198 violations, 198 in the baseline, and the baseline may only shrink.** The
198 are recorded in `artifacts/autogenesis/partition-edge-baseline-v1.json`;
`--baseline` (0.13 s) fails only on edges outside it, so a NEW crossing blocks
from today while the re-partition repairs the recorded ones.
`--record-baseline` REFUSES to write a set that is not a subset of the
committed one — without that, a lane that hit the gate could clear it in one
command and this would be the growing component exemption under a new name.

**The unit changed from a component to an edge, and that is the whole point.** A
component grows whenever any member gains an edge, which is why the exemption
covering it was re-scoped 228 → 230 → 258 → 274 in four days (ADR-1546). An
edge is one string in one fact file and does not change shape under the person
who reviewed it. So an amendment names ONE edge, a reason and a date
(`partition-edge-amendments-v1.json`, currently empty) and the manifests'
component exemptions are REFUSED as amendments — reported as
`NOT-AN-AMENDMENT`, seven of them. **That refusal is measured, not asserted:**
those seven would wave through **154 of the 198** live violations, a number
ADR-1546 could not state about the gate it audited because a component
exemption's effect is not expressible per edge.

**Where it runs.** `hooks/pre-push` L0 block (0.13 s, listed with the other
three; the property previously ran in NO hook, which is how both 2026-09-01
crossings were pushed); `scripts/check-merge-hygiene.sh` guard 9 under the
ADR-1511 three-outcome pattern; `scripts/check.sh` and the `justfile`. All four
run `--baseline`. The bare audit stays out of the aggregates on purpose — it is
red by construction until the re-partition lands, and a standing red is how the
exemption this replaces grew. **Exit 2 blocks in pre-push and does not block in
merge hygiene**, deliberately: its three causes are all "a committed artifact
is missing", which is a thing to stop a push for and not a thing to stop a
mid-merge coordinator for.

**Checker discipline. Ten mutants, ten single kills**
(`mutation_controls.py partition-edges`), plus M15/M16 for merge-hygiene guard
9 — also one kill each. Getting to one kill each changed the FIXTURES, not the
guards: the first draft put a same-partition edge in nine scenarios that did
not need one and the crossing-detection mutant killed six of them. M1 was also
reported `INCONSISTENT` until `_ctx()` indented gate output in assertion
messages — this gate prints `FAIL:` at line start and the harness parses those
as dead tests. `scripts/tests/test-prepush-l0-gates.sh` derives the L0 list
from the hook's own loop; all three of its arms were driven to failure against
scratch copies before being believed. The baseline is registered in
`check-generated-artifact-ownership.py` as sole-owner: `guarded=3
producers_run=14 fails=0`, OWNER restored a perturbed copy byte-for-byte.

**Two findings that were not the assignment.**

1. **A plain pickaxe cannot attribute an edge that entered through a merge.**
   `git log -S` skips merge commits, so 7 of the 198 came back as "no commit
   adds this string" while the string is plainly in the committed file.
   `F:ml430-int-add-comm-c5722728 → F:ml430-nat-add-comm-56a2d614` was
   introduced by the merge `0be9ff41b` and by no other commit in that file's
   nine-commit history — verified by walking all nine and counting
   occurrences, not by trusting the pickaxe that had just said nothing.
   `--diff-merges=first-parent --no-patch` attributes all 198. **Anything else
   here that attributes a ledger change by pickaxe is blind the same way.**
2. **ADR-1546's two named commits are where the component gate flipped, not
   where the edges were added.** `42847d62c` touched exactly one file,
   `artifacts/ontology/settled-fact-statement-pins.json`, and no fact file at
   all; the fib edge it names was added by `c1acb4477`. Nothing in ADR-1546's
   conclusion depends on this, but its attribution should not be quoted as
   "the commit that added the edge".

**Not run:** `cargo` in any form, `just check`, `scripts/check.sh` (no `.rs`
file was touched and no step this lane added needs a build).
`check-autogenesis-nursery.py` and `check-development-partition.py` were NOT
re-run and are expected to remain red — repairing them is option 1's job, and
this lane deliberately changed nothing they read.

<!-- plan-section: landed-changes -->

| 2026-09-02 | partition-edge-gate | `scripts/check-partition-edges.py`: every `depends_on` edge crossing an evaluation partition, with both partitions and the introducing commit; 198 measured on `main` |
| 2026-09-02 | partition-edge-gate | the baseline ratchet — 198 recorded, `--record-baseline` refuses any set that is not a subset of the committed one (ADR-1550) |
| 2026-09-02 | partition-edge-gate | component exemptions REFUSED as per-edge amendments and measured: they would wave through 154 of the 198 |
| 2026-09-02 | partition-edge-gate | wired into `hooks/pre-push` (0.13 s), `check-merge-hygiene.sh` guard 9, `check.sh` and the justfile; the property previously ran in no hook |
| 2026-09-02 | partition-edge-gate | 10 mutants over the gate + M15/M16 in merge-hygiene, each killing exactly one test; `test-prepush-l0-gates.sh` pins the L0 list |
| 2026-09-02 | partition-edge-gate | a plain pickaxe cannot attribute an edge that entered through a merge — 7 of 198 unattributed until `--diff-merges=first-parent` |
| 2026-09-02 | partition-edge-gate | ADR-1546's `42847d62c` touched no fact file; its two named commits are where the gate flipped, not where the edges were added |
