# The eleven narrower-than-replayed model sites, re-verified

Lane SOUND-2 (`AXEYUM_AGENT=SOUND-2-model`), roadmap items 2.10 and 2.11 in
`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`. Measured at
`25f2896e2`, before any code change in this lane.

Roadmap item 2.11 names eleven `file:line` sites where a `Model` emitted after a
successful replay carries fewer components than the state the replay ran
against. This note records what is actually at each of those lines today, and
what the audit found that the row does not say. It is deliberately committed
before the fix, so the fix is measured against a recorded baseline rather than
against a memory of one.

## Method

`Model` (`crates/axeyum-solver/src/model.rs:39-63`) has five components:

| component | in `Model` | in `Assignment` | visible to `Model::to_assignment` |
| --- | --- | --- | --- |
| `entries` (symbol values) | yes | yes (`bindings`) | yes |
| `functions` (UF interpretations) | yes | yes | yes |
| `real_div_zero` | yes | yes | yes |
| `uninterpreted_cardinalities` | yes | **no** | **no** |
| `quantified` (sat certificates) | yes | **no** | **no** |

`Assignment` (`crates/axeyum-ir/src/eval.rs:20-39`) has exactly three:
`bindings`, `functions`, `real_div_zero`. So an `Assignment`-sourced site can
only ever drop those three, and a re-replay against `out.to_assignment()`
(SOUND-1's guard 2) can in principle see all three. A `Model`-sourced site can
additionally drop `uninterpreted_cardinalities` and `quantified`, and guard 2 is
structurally blind to both — this is the row's own note, and it is confirmed:
`to_assignment` (`model.rs:392-405`) copies `entries`, `functions` and
`real_div_zero` and nothing else.

For each site the audit read the model-build loop and the nearest upstream
replay, and recorded which components the build copies.

## The eleven sites as they stand

`Cite` is the line in roadmap row 2.11; `build` is the line of the
`Model::new()` the row is describing.

| # | cite | build | function | source | replay upstream of the build | carries | drops |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | `aufbv.rs:126` | 126 | array+UF elimination model build | `projected: Assignment` | yes, original assertions vs `projected` | entries, functions | `real_div_zero` |
| 2 | `combined.rs:237` | 237 | combined-theory model build | `projected: Assignment` | yes | entries, functions | `real_div_zero` |
| 3 | `abv.rs:263` | 263 | `project_replay_model` | `projected: Assignment` | yes | entries **only** | **functions**, `real_div_zero` |
| 4 | `abv.rs:11091` | **11112** | `model_from_projected_assignment` | `projected: Assignment` | yes (`first_projected_replay_failure`) | entries, functions | `real_div_zero` |
| 5 | `lia.rs:145` | 145 | bounded int-blast readback | `integer_model: Assignment` | yes, original integer assertions | entries **only** | **functions**, `real_div_zero` |
| 6 | `ufbv_online.rs:3168` | 3168 | online AUFBV projection | `projected: Assignment` | yes | entries, functions | `real_div_zero` |
| 7 | `datatype_native.rs:665` | 665 | `project_and_replay` | `assignment: Assignment` | yes | entries **only** | **functions**, `real_div_zero` |
| 8 | `nia_linearize.rs:1837` | 1837 | `replay_sat` (fn at 1826) | `model: &Model` | yes, against `model.to_assignment()` | entries **only** | **functions**, `real_div_zero`, cardinalities, quantified |
| 9 | `lazy_bv.rs:323` | 324 | `restrict_model` (fn at 323) | `model: &Model` | yes, `replay_holds` on `model.to_assignment()` | entries, functions | `real_div_zero`, **cardinalities**, **quantified** |
| 10 | `pbls.rs:1151` | 1152 | `model_from` (fn at 1151) | `asg: &Assignment` | `search.all_satisfied()` over `search.asg` | entries, restricted to `vars` | **functions**, `real_div_zero` |
| 11 | `incremental.rs:7616` | 7617 | `filter_internal_model` (fn at 7616) | `model: &Model` | warm-projection path | entries, functions, **`real_div_zero`** | **cardinalities**, **quantified** |

All eleven still exist and all eleven still emit a model narrower than the state
that was replayed. None had already been fixed. Three cites (`lazy_bv.rs:323`,
`pbls.rs:1151`, `incremental.rs:7616`) name the enclosing `fn` line rather than
the `Model::new()` line — an off-by-one, not drift. One cite has genuinely
drifted: `abv.rs:11091` is inside the replay-repair loop, and the build it
describes is 21 lines below at `abv.rs:11112`.

## What the audit found that the row does not say

1. **`incremental.rs:7616` does NOT drop `real_div_zero`.** Row 2.11 says "most
   drop `real_div_zero`" and then singles this site out for *also* dropping
   cardinalities and quantified. In fact `filter_internal_model` already carries
   `real_div_zero` (`incremental.rs:7626-7628`); cardinalities and quantified
   are the *only* things it drops. The row's framing overstates this site on one
   axis and is exactly right on the other.

2. **Five sites drop `functions`, which the row does not mention at all.**
   `abv.rs:263`, `lia.rs:145`, `datatype_native.rs:665`, `nia_linearize.rs:1837`
   and `pbls.rs:1152` copy symbol entries and stop. This is the SOUND-1b shape
   (`9b259f7c2`: "the preprocessed path dropped UF interpretations from the model
   it emitted"), which produced a caller-visible `Err(UnboundFunction(..))` on
   replay — a strictly louder and more reachable failure than the
   `real_div_zero` fallback. Whether any of the five routes can actually carry a
   UF interpretation is a separate question from whether the build would drop
   one; the build drops one.

3. **The eleven are not the population.** Deriving the site list from the source
   rather than from the row: the `axeyum-solver` crate has 96 `Model::new()` call
   sites outside `model.rs`. Two more in the *same functions as named sites* have
   the same shape and are not in the row —

   - `abv.rs:6633` (lazy-ROW path), replay against the original assertions
     immediately above it, then a build carrying entries and functions and
     dropping `real_div_zero`; the exact twin of site 4.
   - `incremental.rs:7637` (`complete_model_filtered`), building from an
     `Assignment` and carrying entries only.

   The remaining sites were not audited by this lane. "The eleven" should be read
   as a sample SOUND-1 happened to enumerate, not as a closed set.

4. **`pbls.rs:1152` has no assertion replay above it at all.** Its acceptance
   test is `search.total_cost == 0 && search.all_satisfied()` over `search.asg`
   (`pbls.rs:1248-1250`), which is a replay in substance. It is still the
   narrower-than-what-was-checked shape: the emitted model is restricted to
   `vars` and drops both other components.

## Consequence for the fix

Guard 2 (re-replay against `out.to_assignment()`) is a sound *class* guard for
sites 1-7 and 10, whose sources are `Assignment`s and therefore cannot hold a
component `to_assignment` cannot see.

It is **not** sufficient for sites 8, 9 and 11, whose sources are `Model`s.
Adding guard 2 at 9 and 11, whose only remaining loss is cardinalities and
quantified, would install a check that cannot fail on the very defect the site
has — the failure mode `docs/contributor-guide/evidence-and-checker-discipline.md`
rates as worse than no check. Those need a structural carry, not a replay.
