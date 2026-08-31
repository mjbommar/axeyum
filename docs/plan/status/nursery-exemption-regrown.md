# nursery-exemption-regrown

<!-- plan-section: lane-status -->

**Status: DONE — `check-autogenesis-nursery.py` is green again, and it is
green because the enlarged component was reviewed, not because the checker
was weakened.**

Decision record:
[ADR-0940](../../research/09-decisions/adr-0940-cross-population-exemption-re-scoped-to-228-members.md).

## The task

`python3 scripts/check-autogenesis-nursery.py` was red on `main` on a
cross-population declared-dependency-component crossing. ADR-0850/ADR-0855
built this check to be self-invalidating by design: an exemption names the
exact closed fact-id set of one component, and if the live `depends_on` graph
later grows that component, the recorded digest stops matching and the gate
goes red again, naming the enlarged component in full. That is exactly what
had happened — the job was to review the growth, not to make the gate green
by any means.

## What I re-derived, independently

Computed weakly-connected components over the union of `nursery-v1.json` and
`nursery-v2-extension.json` against the current fact ledger, from scratch
(not inherited from ADR-0925's report, though it agrees):

- 3 components cross evaluation partitions. Two (3 members, 4 members) are
  unchanged and their exemptions still match.
- The third grew **206 -> 228 members**, all `train`/`development`/
  `longitudinal`.

**Held-out involvement: zero, in all three components** — checked directly
against each member's `partition` field, not inferred from family name.

**Why it grew (routine, not a partition-drawing error):** the 22 new members
are `Nat.and*`/`Nat.bitwise*`/`Nat.land*`/`Nat.lor_comm`/`Nat.dist*` facts, all
`epistemic_status: proved`, 0 of 22 referenced by any of the 29 recorded
autogenesis operations, each landed by an ordinary hand-development commit
(`ddb1c6bcd`, `f0ad7113c`, `ef8855a89`, `79d9691c6` — draw-9 status flips and
census closes, all visible in `git log`). They connect into the pre-existing
component only through two already-member arithmetic lemmas
(`F:ml430-nat-add-comm-56a2d614`, `F:ml430-nat-add-assoc-8c87a1f1`) — the
same shape ADR-0850/ADR-0855 already accepted, not a new failure pattern.

ADR-0925 (nursery draw 11) had already measured this exact staleness with
three independent controls and correctly judged the repair out of its own
scope, naming it for "whoever owns that gate next." This lane is that repair.

## What changed

- `artifacts/autogenesis/nursery-v2-extension.json`: the stale 206-member
  `cross_population_component_split_exemptions` entry re-scoped to the exact
  228-member set (`reason`/`authority` updated to record what grew and why;
  `extension_sha256` recomputed with the generator's own digest function).
  The two unaffected exemptions (3 members, 4 members) are untouched. No
  fact, partition, or `epistemic_status` was touched anywhere.
- `scripts/tests/test_check_autogenesis_nursery.py`: new `LiveManifestTests`
  class running `build_report`/`build_cross_population_report` against the
  REAL committed manifests (every other test in the suite is a synthetic
  fixture, deliberately, and none of them would ever catch the committed
  exemption itself going stale — this closes that gap). Also asserts
  `cross_population_component_split_exemptions_unused == []`, catching the
  opposite failure (a dead exemption matching nothing live).
- ADR-0940, recording the full re-derivation, the self-invalidation proof,
  and the draw-11 closed-evaluation review below.

## Self-invalidation proof (not just asserted)

Dropped one member (`F:ml430-nat-dist-comm-1fa29a04`) from the new 228-entry
exemption and re-ran the CLI: it reproduced the full, unexempted 228-member
violation report. Reverted. The mechanism is exactly as fail-closed after
this edit as before it.

## Mutation-verified guard -> test table

| mutation | tests killed |
| --- | --- |
| Revert `nursery-v2-extension.json` to the pre-fix committed state (stale 206-member exemption), leave the new test in place | exactly 1: `LiveManifestTests.test_committed_nursery_files_pass_both_gates` |

Confirmed by running the full 30-test suite both ways
(`python3 -m unittest scripts.tests.test_check_autogenesis_nursery`): 30
passed with the fix in place, 29 passed / 1 error with the stale file
restored, and the one failure is the new test.

## Draw 11's two accepted closed-evaluation violations — checked, not repaired

Confirmed real and checked against the cited precedent (full detail in
ADR-0940):

- `Nat.bit_false_zero`/`Nat.size_one` are genuinely in `natural-bit-decode`,
  which is **held-out** — this is a real spend, and ADR-0925 already says so
  plainly.
- `check-holdout-closed-evaluation.py` (registered in `just check` per
  ADR-0695) is currently RED on this tree: `verdict=FAIL`, `violations=2`,
  naming exactly these two facts. This is a SEPARATE red gate from the one
  this lane fixes, red by design (draw 11 knowingly introduced it and chose
  to document rather than repair).
- The `383-nursery-draw-8.md` citation is accurate but was written for a
  narrower case (a *quantified* statement invisible to the binder-free
  classifier); the general "accept and record" option it states is real, but
  draw 11's phrasing reads more specific to this exact case than the source
  is.
- ADR-0695's own `fermat-numbers` precedent went further than draw 11's
  action: it amended the spent facts OUT of held-out (ADR-0542), not merely
  documented them. Draw 11 explicitly takes the weaker half and defers the
  amendment to a future lane — transparently, not hidden.
- Not repaired here: `check-holdout-closed-evaluation.py`, `artifacts/facts/`,
  and any ADR-0542 amendment are all outside this lane's assigned paths.

## Gates — before and after

| check | before | after |
| --- | --- | --- |
| `python3 scripts/check-autogenesis-nursery.py` | exit 1, cross-population component crossing | exit 0, `AUTOGENESIS_NURSERY_OK\|...\|ready=true\|evaluation=214\|blockers=0` + `AUTOGENESIS_NURSERY_CROSS_POPULATION_OK\|...\|v1=216\|v2=380\|components=317` |
| `python3 scripts/gen-autogenesis-nursery-refill.py --check` | exit 0 | exit 0 (unaffected; `extension_sha256` recomputed correctly) |
| `python3 -m unittest scripts.tests.test_check_autogenesis_nursery` | 29 tests, 0 failures | 30 tests, 0 failures |
| `scripts/gen-adr-index.py --check` | — | fails until regenerated (new ADR file); regenerated, `rows=676, duplicate_numbers=0166,0167` (grandfathered only) |
| `check-holdout-closed-evaluation.py` | exit 1, `violations=2` | unchanged — not this lane's path, reported above |

## What this gate still cannot see

It answers "does the declared-dependency graph respect partition
boundaries", and nothing about whether a partition boundary was drawn well
in the first place — a family that is genuinely contaminated from the start
(the wrong kind of problem entirely, the `Nat.dist` R9 incident's shape)
would pass this exact check as cleanly as the routine growth reviewed here,
because R9/R11/closed-evaluation are separate screens this gate does not run.
