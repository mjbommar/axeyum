# Lane: l3-d2-structural-index — ADR-0717 L3 phase D2, structural theorem and proof index

<!-- plan-section: lane-status -->

**Done, l3-d2-structural-index, 2026-08-30.**
[ADR-0905](../../research/09-decisions/adr-0905-structural-theorem-index-fields-and-signal-separation.md)
records the field provenance and scope cuts.

## What landed

Executed D2 of
`docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md`: a
structural index over `kernel.environment()`, a held-out-excluded join of
Mathlib goal features, fixed queries with committed expected rankings, and
three separately-reported ranking signals.

- `crates/axeyum-lean-kernel/examples/structural_index_extract.rs` — a new
  extractor (does not touch `shape_search.rs`/`shape_index.rs`) that emits
  one JSON record per declaration: namespace, binder-role classification,
  `concl_head`, `type_constants`, `definitions_used`/`theorem_dependencies`/
  `recursors_used` (from existing `Kernel::declaration_type_dependencies`/
  `declaration_dependencies`/`theorem_dependencies`), a heuristic
  `rewrite_direction` for `Eq`/`Iff` conclusions, a `proof_skeleton_digest`,
  and an `external_dependency_fingerprint`. 1,633 declarations extracted
  (base preludes only; `--include-constructed` for `creal`/`complex`/
  `cpoint` was not run for the committed artifact — see scope cuts below).
- `scripts/lib/structural_index.py` — shared query engine + held-out
  exclusion + Mathlib goal-feature projection, imported by both
  `scripts/gen-structural-index.py` and `scripts/check-structural-index.py`
  (the same "one computation, two callers" split `scripts/lib/graph_join.py`
  uses).
- `artifacts/structural-index/{theorems.json,mathlib-goal-features.json,
  held-out-exclusion-manifest.json,queries.json}` — committed artifacts.
  `mathlib-goal-features.json` holds 407 records (Mathlib-sourced,
  non-held-out facts only, out of 543 total Mathlib-sourced entries across
  both nursery files — 136 held out and excluded before any feature was
  built).
- Six guards in `scripts/check-structural-index.py`
  (EMPTY_INDEX, FIXED_QUERIES, HELD_OUT_EXCLUDED, GOAL_FEATURE_NO_LEAK,
  SIGNAL_SEPARATION, ABSENCE_UNANSWERABLE), all mutation-verified 1:1 in
  `scripts/tests/test-structural-index-mutations.sh` (each guard's own
  fixture flips PASS only when that guard's body is stubbed, every other
  fixture stays FAIL).
- Registered as `just structural-index` / `step structural-index` in
  `scripts/check.sh`, append-only (only my own lines added to the `check:`
  recipe dependency list and to `check.sh`'s step sequence).

## The worked example (roadmap's own motivating case)

`Int.prodRange_permute` and `Nat.countRange_permute` (the latter has since
landed in-tree, turning the roadmap's hypothetical into a verifiable pair)
share 23 direct dependencies including `Nat.restrict_injective` and
`Nat.restrict_maps_into`, despite different namespaces and different
conclusion heads (`Eq` over `AxInt.prodRange` vs `AxNat.countRange` in
export form). The fixed query `cross-namespace-shared-machinery`
(`has_dependencies: [Nat.restrict_injective, Nat.restrict_maps_into]`)
returns exactly this pair. `shape_search --concl`/`--hyp` cannot reach this
pair (different conclusion heads); this index does, via the dependency
inverted index over `theorem_dependencies ∪ recursors_used ∪
definitions_used`, not via the `external_dependency_fingerprint` field
(that field is namespace-filtered and is asymmetric for a same-namespace
pair — see ADR-0905 for why the working query uses the unfiltered union).

## Spec fields: built vs skipped

| Spec field | Status | Note |
|---|---|---|
| normalized type shape | built | `type_constants` + `concl_head` + `hyp_heads`(via binders) |
| head relations | built | `concl_head`, per-binder head |
| binders | built (heuristic) | carrier/connective/hypothesis lookup-table classification |
| definitions used | built | `Kernel::declaration_dependencies` filtered to `Definition` |
| theorem dependencies | built | `Kernel::theorem_dependencies` verbatim |
| recursors | built | `Kernel::declaration_dependencies` filtered to `Recursor` |
| rewrite direction | built (heuristic) | node-count comparison of Eq/Iff's last two args; not a rewrite-system analysis |
| proof skeleton | built, SCOPE-REDUCED | a dependency-role fingerprint (sorted role-tagged dependency names), not a term-tree structural hash — see ADR-0905 §2 for why this was enough for the motivating case and why a true term-tree hash was deliberately deferred |
| Mathlib goal-feature join | built | `formal.statement`-only, held-out-excluded, 4-key projection |

## Held-out exclusion: proof of ordering

`scripts/lib/structural_index.py::build_mathlib_goal_features` calls
`select_eligible_mathlib_facts` FIRST (which reads the raw nursery entries
and returns only `{fact_id, family}` pairs for non-held-out,
Mathlib-sourced entries) and the raw entry list is never referenced again
in that function or anywhere downstream. The checker's HELD_OUT_EXCLUDED
guard does not trust this ordering as documentation: it independently
recomputes the held-out `fact_id` set from the same two nursery files (an
authority the artifact under test does not control, mirroring ADR-0800's
MISSING guard) and asserts zero overlap with `mathlib-goal-features.json`'s
`fact_id` column. Mutation-verified: stubbing this guard is the only
mutation that makes the held-out-leak fixture pass.

## Proof-value exclusion

`project_mathlib_goal_features` destructures exactly
`{fact_id, family, goal_head, hyp_count}` from a parsed `formal.statement`
string and asserts its own output key set before returning — mirroring
ADR-0800's `project_type_only`, which destructures rather than nulls so a
future value-bearing field cannot leak through by omission. The
GOAL_FEATURE_NO_LEAK guard independently re-checks every committed record's
key set against `GOAL_FEATURE_KEYS`, so even a future edit to this
projection function that widens its output is caught at the artifact level,
not only at the function level.

## Signal separation: identity vs structural vs lexical

Every query result row carries `identity_match`, `structural_match`, and
`lexical_score` as separate fields — never combined. The committed
demonstration pair: `Nat.crt_self_map_injective_on` (a plausible snake_case
guess) is ABSENT under an identity query (`identity-miss-on-plausible-
guess`, expected `[]`) but FOUND under a lexical query on the same guess
(`lexical-hit-on-same-guess`, expected `["Nat.crtSelfMap_injectiveOn"]`),
because the real kernel name is `Nat.crtSelfMap_injectiveOn` (part
camelCase). The SIGNAL_SEPARATION guard asserts the lexical row never also
claims `identity_match: True` for the same name.

## Absence / unanswerable

`unknown-dependency-is-unanswerable` names one real dependency
(`Nat.restrict_injective`) and one that does not exist anywhere in the
index's dependency vocabulary; `run_query` raises `Unanswerable` rather
than returning an empty match, and the ABSENCE_UNANSWERABLE guard asserts
this. `EMPTY_INDEX` separately fails the whole gate if `theorems.json` is
ever empty.

## Known scope cuts (ADR-0905 §2, "Alternatives")

- **Proof skeleton is a dependency-role fingerprint, not a term-tree
  structural hash.** A true term-tree hash needs its own recursive walker
  over checked proof VALUES (delta-unfolding risk); the roadmap's own
  motivating example turns on shared dependency NAMES, which the existing
  `Kernel::theorem_dependencies`/`declaration_dependencies` accessors
  already supply. A follow-on phase that wants branch-shape-sensitive
  matching extends this index rather than replacing it.
- **Rewrite direction is a heuristic**, not a rewrite-system analysis:
  elaborated node-count of the conclusion's last two applied arguments,
  for `Eq`/`Iff` conclusions only.
- **`--include-constructed` (`creal`/`complex`/`cpoint`) was not run** for
  the committed `theorems.json` — none of the fixed queries need those
  declarations, and building them costs real kernel type-checking time on
  every regeneration. Re-running the extractor with `--include-constructed`
  is a drop-in follow-on; nothing in the schema changes.
- **Mathlib goal-head/hyp-count parsing is a coarse regex heuristic** over
  `formal.statement` text, not a Lean parser; ~21% of features classify as
  `goal_head: "other"` (statements the heuristic could not confidently
  classify — reported honestly rather than guessed).

## Hiding place this index still cannot reach

Hiding place 2 from the roadmap brief — a reusable step built INLINE inside
a larger declaration and never given a name (e.g. `nat_prelude/powsq.rs`'s
`declare_pow_half_split` even/odd split) — has no declaration to index. No
index over `kernel.environment()` can ever see it; this is stated in
ADR-0905 and in the extractor's own module doc, not silently assumed away.
