# ADR-0940: The re-grown cross-population exemption is re-scoped, not silenced

Status: accepted
Date: 2026-08-30
Index-summary: `check-autogenesis-nursery.py` was red on `main` because
ADR-0855's 206-member cross-population exemption stopped matching its own
component -- the live component had grown to 228 members via ordinary
proof landings, exactly the self-invalidation ADR-0850/ADR-0855 designed the
mechanism to trigger on. Re-derived the enlarged component independently,
confirmed zero held-out involvement, re-scoped the exemption to the exact
228-member set, and added a regression test against the COMMITTED manifests
so this class of drift is caught before it reaches the gate again.

Related: ADR-0850 (the exemption mechanism), ADR-0855 (the cross-population
form of it), ADR-0925 (nursery draw 11, which measured and reported this same
staleness as pre-existing and out of its scope), ADR-0542 (held-out amendment
ledger, NOT used here -- nothing held-out is involved), ADR-0695 (closed-
evaluation held-out spends, relevant to draw 11's separate finding below)

## Context

`python3 scripts/check-autogenesis-nursery.py` failed on `main` with the
cross-population declared-dependency-component check
(`build_cross_population_report`). ADR-0850 built this check as
self-invalidating by design: an exemption names the exact closed fact-id set
of one weakly-connected component, the digest is recomputed from the live
`depends_on` graph on every run, and if the graph later pulls a new fact into
an exempted component, the recorded digest stops matching and the gate goes
red again -- naming the enlarged, unreviewed component in full. That is
exactly what happened here, and it is the mechanism working as designed, not
a defect in it.

## What was re-derived (not inherited)

Re-computing weakly-connected components over the union of
`nursery-v1.json` and `nursery-v2-extension.json` against the current fact
ledger's `depends_on` edges, independently of any prior lane's report:

- **3 components cross evaluation partitions**, matching the 3 exemption
  entries already recorded in `nursery-v2-extension.json`'s
  `cross_population_component_split_exemptions`.
- Two are unchanged (3 members, 4 members) and their recorded exemptions
  still match exactly.
- The third has grown from **206 to 228 members** (`train`/`development`/
  `longitudinal`). Its recorded exemption (digest `510e9696bc8571c0…`) no
  longer matches the live component (digest `b13fee8fe905f115…`), which is
  the entire failure.

**Held-out involvement: none, in any of the three components.** Every
member's `partition` field was checked directly against the nursery entries
(not inferred from family name); all three components' partition sets are
subsets of `{train, development, longitudinal}`. This is the question that
decides everything for this kind of finding, and the answer is negative.

**The 22 new members**, diffed exactly against the previous 206-member
exemption:

```
F:ml430-nat-and-assoc-273b60d8       F:ml430-nat-and-comm-7525d05a
F:ml430-nat-and-div-two-1a2f7c33     F:ml430-nat-and-le-left-6d04acb7
F:ml430-nat-and-le-right-a3f80076    F:ml430-nat-and-mod-two-eq-one-3e873792
F:ml430-nat-and-one-is-mod-d861e96b  F:ml430-nat-bitwise-bit-4c4b28a8
F:ml430-nat-bitwise-comm-1a273bae    F:ml430-nat-bitwise-swap-7175e90e
F:ml430-nat-dist-add-add-left-92fa4403      F:ml430-nat-dist-add-add-right-6e5d8bbb
F:ml430-nat-dist-comm-1fa29a04       F:ml430-nat-dist-eq-intro-294b44ad
F:ml430-nat-dist-eq-zero-5ae5b706    F:ml430-nat-dist-pos-of-ne-00f5e22f
F:ml430-nat-dist-self-0cfa5426       F:ml430-nat-dist-triangle-inequality-b35e82d3
F:ml430-nat-land-assoc-ad4775b8      F:ml430-nat-land-bit-b9ab7475
F:ml430-nat-land-comm-7e6ad72e       F:ml430-nat-lor-comm-2666d7ef
```

Each was checked directly against `artifacts/facts/*.json`:

- All 22 carry `epistemic_status: "proved"` (not merely `open`).
- 0 of 22 are referenced anywhere in `artifacts/autogenesis/operations.json`
  (29 operations, checked by scanning the full serialized record, not only
  `applicability.fact_ids`).
- `git log` on each fact file shows ordinary hand-development commits:
  `ddb1c6bcd` (`Nat.land_comm`, "one of the 7 fuel-irrelevance was
  blocking"), `f0ad7113c` (`Nat.bitwise_bit`, "the last open `*_bit` family
  member"), `ef8855a89`/`79d9691c6` (draw-9 status flips: "Nat.dist_comm/
  dist_self already existed", "reconcile to Nat.land_*"). None of these
  commits are autogenesis dispatch; all are the ordinary bitwise/parity
  proof work CLAUDE.md's own Gotchas record for this same session.
- The connecting edges into the pre-existing 206-member component are two
  already-arithmetic lemmas: `F:ml430-nat-add-comm-56a2d614` and
  `F:ml430-nat-add-assoc-8c87a1f1`, both already members, both `train`. The
  new `Nat.dist`/`Nat.and`/`Nat.land`/`Nat.lor`/`Nat.bitwise` facts depend on
  ordinary commutativity/associativity of `Nat.add`, which happens to already
  sit inside the exempted component -- the same shape ADR-0850 and ADR-0855
  already accepted twice, not a new failure pattern.

**Verdict on the cause: routine, not a partition-drawing error.** This is
real proof-dependency growth from ordinary hand development (draw 9 and
earlier bitwise/distance work), landing dependency edges the frozen
partition boundary could not have anticipated -- identical in shape to
ADR-0850's original diagnosis and ADR-0855's own restatement of it. It is
not evidence of a family or proof-shape drawn across a boundary that should
never have crossed it.

## Where this was first noticed, and why it was not fixed there

`ADR-0925` (nursery draw 11) measured and reported this exact staleness --
206 -> 228, same 22 members, same cause -- with three independent controls
(`git stash` of the whole draw reproduces the identical violation; removing
the draw's own `FAMILY_MODULES` block and keeping only its incidental
`build_extension` bugfix reproduces it; 0 of the draw's 40 new fact ids
appear in the violation output). That lane correctly judged the repair out
of its own scope (a nursery *draw* edits `gen-autogenesis-nursery-refill.py`'s
two dicts and preregisters new facts; it does not own the exemption
mechanism or `nursery-v2-extension.json`'s exemption list) and left it named
for "whoever owns that gate next." This ADR is that lane.

## Decision

Re-scope the stale exemption entry in
`artifacts/autogenesis/nursery-v2-extension.json`'s
`cross_population_component_split_exemptions` to the exact, current
228-member fact-id set, updating `reason` to record what grew and why, and
`authority` to reference both ADR-0855 (the mechanism) and this ADR (the
re-scoping). No entry is deleted; the two unaffected exemptions are
untouched. `extension_sha256` is recomputed. No nursery entry's partition,
`epistemic_status`, or any other field is touched -- this is exemption-list
maintenance, not a fact-ledger edit, and `artifacts/facts/` is out of this
lane's scope regardless.

This is explicitly **not** an ADR-0542 amendment: no partition moved, no
held-out row is touched, and nothing here is "spent" in ADR-0542's sense.
ADR-0850 already established that a component-split exemption is a narrower,
purely mechanical claim than an amendment, and growing it is the same kind
of action as creating it.

**The self-invalidating property is proven to survive**, not merely
asserted: dropping one member (`F:ml430-nat-dist-comm-1fa29a04`) from the new
228-entry exemption reproduces the full, unexempted 228-member violation
report -- confirmed by direct experiment, then reverted. The mechanism ADR-
0850 built is exactly as fail-closed after this edit as before it.

## A new regression test closes the gap that let this go unnoticed

Every existing exemption test in `scripts/tests/test_check_autogenesis_nursery.py`
(both `NurseryTests` and `CrossPopulationTests`) builds its own tiny synthetic
population specifically so it does not depend on what happens to be committed
today -- which means none of them would ever have caught the COMMITTED
exemption itself going stale. `LiveManifestTests.test_committed_nursery_files_pass_both_gates`
closes that gap: it runs `build_report` and `build_cross_population_report`
against the real, committed `nursery-v1.json` / `nursery-v2-extension.json`
and fact ledger -- exactly `main()`'s own sequence -- and additionally asserts
`cross_population_component_split_exemptions_unused == []`, so a *dead*
exemption (one that no longer matches any live component, the opposite
failure direction) is caught too.

**Mutation-verified**: reverting the exemption edit alone (restoring the
committed pre-fix `nursery-v2-extension.json`, leaving the new test in place)
makes exactly one test fail across the whole 30-test suite --
`LiveManifestTests.test_committed_nursery_files_pass_both_gates` -- confirmed
by running the full suite both ways. No other test is sensitive to this file's
content, which is correct: they are synthetic by design.

## Draw 11's two accepted closed-evaluation violations, checked against precedent

Separately, draw 11 (`882ae1a52`, ADR-0925) accepted two held-out facts in
`natural-bit-decode` -- `Nat.bit_false_zero` (`Nat.bit false 0 = 0`) and
`Nat.size_one` (`Nat.size 1 = 1`) -- as a documented closed-evaluation spend
rather than declining the draw. Checked directly:

- **Both rows are genuinely held-out**, not development or train --
  confirmed by reading `nursery-v2-extension.json`'s entries directly. This
  is a real spend, not a costless one, and ADR-0925 says so plainly ("a
  dispatch lane should not read either as evidence of producer capability if
  solved trivially").
- **`check-holdout-closed-evaluation.py` (the standing gate ADR-0695
  registered in `just check`) is RED on the current tree**, confirmed by
  running it directly: `verdict=FAIL`, `violations=2`, naming exactly these
  two facts. This is a SECOND red gate on `main`, distinct from the one this
  ADR fixes, and it is red by design -- draw 11 knowingly introduced these
  two violations and chose to document rather than repair them.
- **The `383-nursery-draw-8.md` citation is accurate but narrower than draw
  11's prose implies.** The actual sentence
  (`docs/plan/notes/383-nursery-draw-8.md`) is a warning specific to
  `Nat.nthRoot_zero_left` -- a *quantified* statement that reduces to `refl`
  but is invisible to `is_closed_evaluation`'s binder-free classifier -- and
  it offers "choose the construction's equations, or accept and record the
  spend" as the general options for a closed-eval spend found before
  drawing. It does not specifically anticipate a case the classifier DOES
  catch (both `Nat.bit_false_zero` and `Nat.size_one` are binder-free and
  are flagged, `violations=2`, not silently missed), so draw 11's "the exact
  rule ... states for this shape" reads a bit more specific to this case
  than the source text is. The general permission it draws on is real.
- **The `fermat-numbers` / ADR-0695 precedent supports acceptance in
  general, but ADR-0695's own resolution went further than draw 11's.**
  ADR-0695 decision 5 did not stop at "accept and document" -- it amended
  `fermat-numbers` OUT of held-out entirely via ADR-0542. Draw 11 accepts and
  documents but explicitly declines to amend now ("amending a row before it
  is preregistered has no defined meaning in this generator... A future lane
  reaching these two facts in dispatch may reasonably raise an ADR-0542
  amendment"). So draw 11's action is the weaker half of its own cited
  precedent, and it says so.
- Whether that gap between "accept and document" and "accept and repair" is
  itself acceptable is a judgment call ADR-0925 already made transparently,
  with the exact two facts named for whoever amends them -- it is not hidden,
  it is not a checker-that-cannot-fail (the gate DOES fail, loudly, and stays
  failing), and it is outside this ADR's scope (`check-holdout-closed-evaluation.py`,
  `artifacts/facts/`, and any ADR-0542 amendment are explicitly not this
  lane's paths). Recorded here as confirmed, not as fixed.

## Consequences

- `python3 scripts/check-autogenesis-nursery.py` exits 0 again:
  `AUTOGENESIS_NURSERY_OK|...|ready=true|evaluation=214|blockers=0` and
  `AUTOGENESIS_NURSERY_CROSS_POPULATION_OK|...|v1=216|v2=380|components=317`.
- `python3 scripts/gen-autogenesis-nursery-refill.py --check` is unaffected
  (still exit 0) -- confirmed after the edit, since `extension_sha256` was
  recomputed with the generator's own digest function.
- `python3 -m unittest scripts.tests.test_check_autogenesis_nursery` is
  30 tests, 0 failures (29 pre-existing + 1 new).
- `check-holdout-closed-evaluation.py` remains RED (`violations=2`,
  `Nat.bit_false_zero`, `Nat.size_one`), by design, per ADR-0925 -- not
  touched by this ADR, and not this lane's path to fix.
- If either the 3-member or 4-member cross-population component, or this
  228-member one, grows again, the gate goes red again automatically and
  names the enlarged component in full -- proven above by direct
  experiment, not merely asserted.

## Alternatives rejected

- **Widen the exemption to match on a digest of the fact SET without storing
  the members** was never on the table -- ADR-0850 already rejected a bare
  digest as unauditable, and nothing about this growth changes that
  reasoning.
- **Move the newly-joined 22 facts to a different partition to shrink the
  component** was rejected: none of the reasons ADR-0850 gave for declining
  a partition move (no principled correct partition to move to; the crossing
  is a property of the graph, not of any one fact) have changed, and this
  lane's scope explicitly excludes partition moves.
- **Fix `check-holdout-closed-evaluation.py`'s two violations here as well**
  was rejected: it is a different gate, a different fix (an ADR-0542
  amendment or a construction-side repair), and explicitly out of this
  lane's assigned paths. Reported instead, per ADR-0925's own request that
  "whoever owns that gate next" pick it up -- this ADR owns the
  `check-autogenesis-nursery.py` gate specifically, not that one.
