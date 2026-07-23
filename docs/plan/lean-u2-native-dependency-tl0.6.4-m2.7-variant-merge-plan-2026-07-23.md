# Lean U2 TL0.6.4 M2.7 plan — variant merge and M3 review handoff

Status: **preregistered deterministic offline semantics only; no M2.7 input
authority, accepted parent transfer, merged graph, closed case/variant cell,
M3 review row, native outcome, pair, performance row, or parity credit exists**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parents:
[M2 program](lean-u2-native-surface-classification-tl0.6.4-m2-plan-2026-07-23.md),
[accepted M2.0 result](lean-u2-native-surface-classification-tl0.6.4-m2.0-result-2026-07-23.md),
[M2.1 pre-execution result](lean-u2-native-dependency-tl0.6.4-m2.1-pre-execution-2026-07-23.md),
[M2.2 effective-import correction](lean-u2-native-dependency-tl0.6.4-m2.2-effective-import-r1-plan-2026-07-23.md),
[M2.3 runner plan](lean-u2-native-dependency-tl0.6.4-m2.3-runner-generated-plan-2026-07-23.md),
[M2.4 Lake/project plan](lean-u2-native-dependency-tl0.6.4-m2.4-lake-project-plan-2026-07-23.md),
[M2.5 compiler/runtime/FFI plan](lean-u2-native-dependency-tl0.6.4-m2.5-compiler-runtime-ffi-plan-2026-07-23.md),
and [M2.6 editor/server/RPC plan](lean-u2-native-dependency-tl0.6.4-m2.6-editor-rpc-plan-2026-07-23.md).

## 1. Decision boundary

M2.7 must combine accepted M2.1-M2.6 node, edge, process, artifact, effect,
request, and residual evidence into deterministic case-by-official-variant
closures without allowing storage deduplication, equal commands, equal selected
case lists, or a successful provider to erase a distinct workflow, platform,
configuration, branch, failure, or decline.

The singular rule is:

> The credit unit is one exact case and one exact official variant. Shared
> content may be stored once, but every node, edge, assurance fact, condition,
> decline, and residual retains all owning case/variant identities. No
> aggregate union, intersection, equivalence class, or maximum status can close
> a cell whose own provenance is incomplete.

M2.7 owns:

- validation and transfer of accepted M2.1-M2.6 authorities without running
  their external processes again;
- content-addressed node/edge deduplication with lossless case/variant
  ownership, condition, evidence, and derivation joins;
- exact per-cell direct/transitive surface closure, conditional branch
  accounting, reviewed-decline handling, and residual taxonomy;
- variant delta, union, intersection, and explicitly proved equivalence views;
- deterministic aggregate seals, completeness projections, and the full M3
  review queue; and
- correction overlays, including M2.6's four-case M1 editor/RPC rejection,
  without rewriting historical authorities.

M2.7 does not bind a missing provider, execute Lean/Lake/compiler/server work,
repair or reinterpret a parent, compare official and Axeyum semantics, turn a
decline into support, reduce the declared official matrix, or grant outcome,
pair, performance, population, axis, gate, or parity credit.

## 2. Frozen factored denominator

Accepted M2.0 freezes eight selection rows, 111 official variants, 3,723 case
rows, and **408,374** applicable case/variant cells. The exact factoring is:

| Case class | Cases | Applicable variants per case | Cells |
|---|---:|---:|---:|
| full eight-selection membership | 3,476 | 111 | 385,836 |
| six-selection filtered membership | 202 | 104 | 21,008 |
| three-selection Lake-only membership | 45 | 34 | 1,530 |
| **Total** | **3,723** | — | **408,374** |

The 111 variants span 17 workflow contexts and six event classes, 85 primary
plus 26 rebootstrap phases, and 97 release plus seven sanitizer and seven
reldebug presets. All currently target stage 1; stage remains part of identity
because equality in this pinned matrix is not permission to drop it.

The eight selection rows project to only five distinct selected-ID hashes:

| Selection row | Cases | Official variants |
|---|---:|---:|
| `default-all` | 3,678 | 57 |
| `default-filtered-aec7358564e4` | 3,678 | 8 |
| `default-filtered-bfb0a7b69c6e` | 3,677 | 5 |
| `default-filtered-d1bb9722e72c` | 3,477 | 5 |
| `full-lake-all` | 3,723 | 28 |
| `full-lake-filtered-6325d6cffd5d` | 3,723 | 4 |
| `full-lake-filtered-cbb2894dd43f` | 3,722 | 2 |
| `full-lake-filtered-d803b176baa6` | 3,477 | 2 |

Three pairs have byte-identical selected-ID projections:

- `default-all` and `default-filtered-aec7358564e4`;
- `full-lake-all` and `full-lake-filtered-6325d6cffd5d`; and
- `default-filtered-d1bb9722e72c` and
  `full-lake-filtered-d803b176baa6`.

Those equal hashes authorize shared membership storage only. Their profile,
workflow, job, provider, platform, configuration, phase, environment, and
policy identities remain distinct. M2.7 cannot infer that an apparently
no-op filter, equal command, or equal selected list produces an equivalent
dependency graph or observation.

Every current provider is `unbound`, every resolver/case is `not-run`, both
node and edge registries are empty, and resolved closures/native outcomes/
pairs are zero. These are schema facts, not merge inputs. M2.7 remains
unexecutable as a closure step until each required M2.1-M2.6 parent is accepted.

## 3. Pinned local authority surface

M2.7.1 must reject drift in at least:

| Input | SHA-256 | Required interpretation |
|---|---|---|
| `docs/plan/lean-u2-native-dependency-v1.json` | `46d2c17363bf8e4097d12df20f8ee9ffb86acf647642068d3eacc72e711dd4d6` | accepted M2.0 denominator/schema history |
| `scripts/gen-lean-u2-native-dependency.py` | `e5f835bf4a0dbd4e59e82068b1e57b073f484153333962d1c85e0c308de90b19` | current offline validator baseline |
| `scripts/tests/test_lean_u2_native_dependency.py` | `6f6e157077f7dcd854fdaea998e73aff6b99de30aa23a310129d5ef034c44c93` | current M2.0 mutation boundary |
| `docs/plan/lean-u2-official-ci-profiles-v1.json` | `4817d177828797f9dab9e62cf7647732d2b9c3788db7b7b4e3461bc868948548` | workflow/selection/attempt source authority |
| `docs/plan/lean-u2-native-surface-content-v1.json` | `c83d10ce0f0619d4327dbbd7544bd584360cb080d35778ca7798a5f7da17560f` | immutable M1 source observations |
| `scripts/tests/test_lean_complete_parity.py` | `c8ada5e73fa77ced35878028fea98199551c903f2edf2a67b3f5b930040037dc` | M2.3-M2.6 preregistration checks before this plan |
| `docs/plan/lean-u2-native-dependency-tl0.6.4-m2.6-editor-rpc-plan-2026-07-23.md` | `760661d9f61900b8e309d2286111b411dc7a8b93e555090deceb3fbee4cf9753` | M1 correction overlay and final parent semantics |

These hashes identify the source-first baseline for this plan. M2.7.1 must
separately bind the accepted future result authorities, evidence roots, result
revisions, validators, and logical seals for M2.1-M2.6. A plan or
implementation-readiness file is not an accepted observed result.

The data model follows the same provenance discipline as the W3C
[PROV data model](https://www.w3.org/TR/prov-dm/) and
[PROV notation](https://www.w3.org/TR/prov-n/): derived entities retain the
activities and source entities that produced them. SLSA's
[build provenance](https://slsa.dev/spec/v1.2/provenance) similarly separates
build definition from run details and resolved dependencies. Those standards
are design context, not substitute authorities for Axeyum's exact schema.

## 4. Identity and merge keys

M2.7 retains four nested identities:

1. **Variant key:** target source/release, context, event, job, phase, target
   stage, preset/options, selection row, command, bound provider/executable,
   platform/architecture, configuration, resource lane, workspace/environment,
   cache/network policy, and accepted attempt/evidence identities.
2. **Cell key:** exact `case_id` plus exact `variant_id`; the denominator and
   completeness unit.
3. **Node key:** registered node class plus its complete class-specific
   content/provenance identity. Equal content can share one canonical node, but
   an ownership relation lists every cell and route that reaches it.
4. **Edge key:** registered class, ordered endpoints, direct/transitive role,
   resolver/version, condition/branch, and semantic identity. Evidence and
   ownership remain per cell/variant even when the structural edge is shared.

An observation additionally binds attempt, process epoch, event/span, raw
evidence, and completion identity. An artifact hash alone cannot merge its
producer, route, platform, ABI, loader, request, or effect observations.

Canonical registries sort by type and stable identity. Ownership sets sort by
case then variant; evidence sorts by accepted parent, route, attempt, process,
and event ordinal. Factoring may use sealed references or bitmaps but must
round-trip exactly to all 408,374 cells. Any lossy compaction or order-dependent
join fails closed.

## 5. Assurance algebra is not a total order

M2.0 names `declared-static`, `resolved-static`, `configured`,
`observed-runtime`, `conditional-not-taken`, `provider-unavailable`,
`intentionally-online`, `declined`, and `unresolved`. M2.7 must not choose the
apparently “highest” value and discard the rest.

Within the same exact cell and structural edge:

- static declaration, resolution, configuration, and runtime observation are
  separate provenance dimensions; a later dimension links to rather than
  overwrites its prerequisites;
- compatible repeated evidence unions source pointers and attempts under
  deterministic seals;
- conflicting targets, conditions, states, outputs, or identities create a
  `contradictory-evidence` residual and close nothing;
- `conditional-not-taken` is valid only for a registered branch in a variant
  where that branch is not required and the complementary behavior is bound;
- `intentionally-online` records policy and non-execution, never runtime
  reachability;
- `declined` requires a stable reason, exact owner, reviewer, scope, and
  controls; it never becomes supported behavior;
- `provider-unavailable`, `unresolved`, `not-run`, invalid evidence, or an
  unaccepted parent blocks the cell; and
- evidence from one variant can establish a cross-variant hypothesis but
  cannot change another cell until an explicit equivalence proof is accepted.

Each edge class retains its required assurance vector. Edges marked
`requires_observation=true` cannot close from static/configured evidence;
static-only classes need not invent runtime exercise. All prerequisite links
remain inspectable in the final projection.

## 6. Cell closure and aggregate projections

A cell is `closed-supported` only when its provider/platform/configuration and
all M2.1-M2.6 transfers are accepted, every required node/edge is present with
the class-appropriate assurance, every applicable condition is resolved, all
effects/processes/artifacts/documents are owned and completion-valid, and no
blocking residual remains.

A cell is `closed-declined` only when every missing route is covered by an
accepted reviewed decline. It remains distinguishable from support in every
count and downstream review. `provider-unavailable` is not a decline and cannot
close M2.

A case projection is complete only if every applicable variant cell is either
`closed-supported` or `closed-declined`. It reports supported/declined counts,
not one Boolean that hides the partition. M2 is complete only when all 3,723
cases and 408,374 cells close and all aggregate invariants pass. This still
creates no native outcome or parity pair.

M2.7 may publish these non-crediting views:

- **union:** every structurally distinct node/edge with exact owner sets;
- **intersection:** only compatible structural identities present in every
  named cell, retaining each cell's evidence rather than one representative;
- **delta:** deterministic additions/removals/identity or assurance differences
  between named variants;
- **surface projection:** direct/transitive requirements recomputed from the
  accepted graph, with M0/M1 differences classified rather than overwritten;
- **equivalence class:** variants proven interchangeable for one explicitly
  named projection and mutation set; and
- **coverage cube:** exact observed combinations of workflow, platform,
  configuration, phase, selection, branch, and route.

An intersection is not proof that all variants are complete, and a union is
not one executable configuration. An equivalence class reduces presentation
or storage only; its member cells and denominator remain. NIST's
[combinatorial coverage work](https://www.nist.gov/publications/combinatorial-coverage-measurement)
motivates reporting covered configuration interactions rather than inferring
untested combinations, while the
[Reproducible Builds variation guidance](https://reproducible-builds.org/docs/plans/)
motivates deliberate environment variation rather than erasing it.

## 7. Cross-variant equivalence proof

Two variants can share a projection only after a registered proof binds:

- exact compared fields and deliberately ignored fields;
- provider, executable/dynamic closure, source, platform, configuration,
  environment, workspace, cache/network, command, and resource identities;
- selected case membership and every case-specific graph/evidence digest;
- branch/conditional coverage, outcomes, effects, and terminal evidence;
- a symmetric comparison over the complete named population;
- mutation controls showing every merge-sensitive field breaks equivalence;
  and
- a stable scope, reviewer, result revision, and revocation rule.

Primary and rebootstrap, cached and uncached, normal and fast contexts,
release/sanitize/reldebug, default/full-Lake, Linux/macOS/Windows/aarch64, and
different event/context rows remain distinct unless the exact requested
projection proves equivalence. Matching commands or selected-ID hashes are
insufficient. Provider/platform/configuration fields being unbound is a
blocker, not a wildcard.

If an equivalence later fails, retain the old proof as historical evidence,
revoke only its live use, expand affected member cells, and propagate a
deterministic M3 residual. Do not rewrite prior evidence or silently select a
new representative.

## 8. M1/M2 reconciliation and residual taxonomy

For each cell M2.7 recomputes direct and transitive surfaces from accepted
nodes/edges, then compares them with immutable M0/M1 classifications. M2.6's
overlay rejects the four Lake `json.document-version` editor/RPC projections,
so M2.7 uses the qualified 143-case floor while retaining M1's historical 147.

Every difference receives one typed residual, at minimum:

- `parent-incomplete`, `invalid-evidence`, `unbound-provider`,
  `provider-unavailable`, or `not-run`;
- `unresolved-node`, `unresolved-edge`, `orphan-node`, `unowned-edge`,
  `missing-observation`, or `incomplete-condition`;
- `contradictory-evidence`, `variant-divergence`, `equivalence-unproved`, or
  `equivalence-revoked`;
- `m1-overclassification`, `m1-underclassification`,
  `generated-residual`, or `correction-overlay`;
- `unreviewed-decline`, `intentionally-online`, `normalization-ambiguous`,
  `effect-unaccounted`, or `cleanup-incomplete`; and
- `schema-drift`, `seal-drift`, `ownership-loss`, or `compaction-loss`.

Residuals bind case, variant, graph element/route, parent evidence, severity,
owner, reason, required action, review state, and seal. Counts cannot replace
rows. A residual disappears only through a separately retained resolution that
preserves the original row and derivation.

## 9. Deterministic M3 review handoff

M2.7 publishes one M3 row per case plus drill-down cell rows. Each contains
the exact cell denominator, supported/declined/blocked partition, direct and
closure surfaces, graph roots/digests, assurance vectors, variant deltas,
M0/M1 reconciliation, correction overlays, residuals, parent authorities, and
zero-credit fields.

The review queue orders blocking items before closed rows, then by residual
class/severity, case ID, variant ID, graph type/identity, route, and evidence
ordinal. It separately lists:

1. invalid/unaccepted parents and providers;
2. unresolved, unavailable, contradictory, or incomplete cells;
3. unreviewed/reviewed declines and intentionally-online edges;
4. variant deltas and equivalence hypotheses;
5. M0/M1 corrections and newly discovered surfaces; and
6. closed-supported cells for final sampling and seal review.

M3 acceptance must inspect every row, not only blockers or one representative
per equivalence class. M2.7's queue is a handoff artifact, not M3 acceptance.

## 10. Required schema and controls

M2.7.1 freezes domain-separated variant, cell, node, edge, evidence,
condition, ownership, assurance-vector, decline, residual, equivalence,
projection, review, and aggregate records. Every list and record has a domain-
separated seal; the top record binds parent logical seals, code identities,
ordering rules, denominator expansion, and zero credits.

The implementation must reject at least:

1. any count other than 8 selections, 111 variants, 3,723 cases, and 408,374
   expanded cells with the exact 3,476/202/45 partition;
2. missing, duplicate, reordered, extra, or incorrectly applicable variants;
3. collapse of the three content-equal selection-row pairs;
4. primary/rebootstrap, cached/uncached, event/context, job, stage, preset,
   platform, configuration, provider, lane, command, or policy collapse;
5. an unbound or unavailable provider treated as a wildcard or decline;
6. node/edge content deduplication that loses any owner, condition, resolver,
   route, evidence, or direct/transitive role;
7. an observed edge overwriting static/configuration provenance or evidence
   from one variant promoting another;
8. a total-order/max-state merge, contradictory evidence, or incompatible
   repeated observation;
9. conditional-not-taken without complete branch registration or a taken
   branch credited across another variant;
10. a reviewed decline counted as support, an unreviewed decline closing a
    cell, or intentionally-online treated as observation;
11. a `requires_observation` edge closed statically or a static-only edge
    forced to invent runtime evidence;
12. union/intersection/equivalence projections used as cell completion;
13. asymmetric, partial-population, unbound-field, mutation-free, or stale
    equivalence proof;
14. M2.6's four-case correction lost, M1 history rewritten, or an M0/M1
    difference silently absorbed;
15. orphan/unowned graph elements, incomplete effects/process cleanup, or
    ambiguous normalization;
16. residual count/row mismatch, missing owner/action/review, or disappearing
    unresolved history;
17. unstable ordering, domain confusion, list/record seal drift, or lossy
    factoring/compaction;
18. an unaccepted M2.1-M2.6 parent, wrong containing/result revision, partial
    evidence root, retry, or post-completion mutation;
19. incomplete M3 queue/drill-down projection or skipped equivalence members;
    and
20. any native outcome, pair, performance, complete population/axis/gate, or
    parity credit.

## 11. Source-first sequence and exit

1. **M2.7.0 plan:** this document freezes merge semantics and current read-only
   denominators. It consumes no parent result and runs no external process.
2. **M2.7.1 input authority:** only after accepted M2.1-M2.6 results, freeze
   exact parent revisions/seals, expanded cells, schemas, residual taxonomy,
   equivalence policy, controls, and output roots. All merged/credit fields
   remain empty or zero.
3. **M2.7.2 implementation:** implement offline validation, expansion,
   provenance joins, assurance vectors, closure, projections, residuals,
   mutation tests, and M3 queue rendering; commit and push before use.
4. **M2.7.3 offline projection:** consume only immutable accepted evidence,
   produce canonical output twice, require byte equality, validate every seal
   and denominator, and retain the containing revision. It starts no Lean,
   Lake, compiler, server, test, network, or tracing process.
5. **M2.7.4 result/handoff:** document exact closed/declined/blocked cells,
   variants, surfaces, residuals, equivalence proofs, controls, and nonclaims;
   then hand every row to M3.

Stop if any parent is absent/unaccepted, refs differ, the worktree is dirty,
the denominator or M2.6 correction drifts, any provider/evidence identity is
unbound where required, ownership or branch coverage is lossy, output is not
deterministic, a residual lacks an owner, or any field attempts premature
credit.

M2.7 exits only when all 408,374 cells are losslessly represented and each is
closed-supported or closed-declined; all conditions, provenance, residuals,
equivalence members, and controls validate; every case has a complete M3 row;
and no `not-run`, `unresolved`, `provider-unavailable`, invalid, contradictory,
or silently delegated field remains.

Even that completes only TL0.6.4 M2 dependency/reachability closure. M3 must
review every case and variant before TL0.6.4 can be accepted, and TL0.6.5 must
still execute and compare exact Axeyum behavior. M2.7 alone completes no U2/U5/
U6 population, A0-A11 axis, terminal gate, or Lean parity claim.
