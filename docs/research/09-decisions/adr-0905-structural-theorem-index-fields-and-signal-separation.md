# ADR-0905: The structural theorem index derives dependency/recursor fields from existing kernel accessors, keeps three signal columns apart, and excludes held-out facts before any feature is built

Status: accepted
Date: 2026-08-30
Index-summary: L3 phase D2 structural index — a derived JSON index over `kernel.environment()` (namespace, binder roles, definitions/theorems/recursors used, a dependency-skeleton digest, a namespace-external dependency fingerprint), a held-out-excluded join of Mathlib goal features from the fact ledger's `formal.statement` only, and three separately-reported ranking signals (identity, structural, lexical), never merged into one score.

## Context

`docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md` section D2
calls for indexing Axeyum theorems by normalized type shape, head relations,
binders, definitions used, theorem dependencies, recursors, rewrite
direction, and proof skeleton, and for joining proof-isolated Mathlib goal
features without exposing upstream proof values. Its exit criterion: fixed
queries reproduce exact ranked candidates; held-out facts are excluded before
feature construction; identity, structural, and lexical signals are reported
separately.

The existing retrieval tool, `examples/shape_search.rs` over
`axeyum_lean_kernel::shape_index`, already answers "does a declaration of
this type-shape exist?" via conclusion head, hypothesis heads, and type
constants. CLAUDE.md's retrieval-is-the-bottleneck retrospective documents a
case it cannot reach: `Int.prodRange_permute` was the reusable skeleton a
`Nat.countRange` argument needed, and no name search or shape-search query
finds it, because its conclusion head (`AxInt.prodRange`) differs from the
target's. (That specific instance has since been closed in-tree —
`nat_prelude/count_range_permute.rs`'s `Nat.countRange_permute` now exists —
which turns it into a verifiable pair rather than a hypothetical: both
theorems directly name `Nat.restrict_injective` and
`Nat.restrict_maps_into`, and neither name is under either theorem's own
namespace.)

## Decision

1. **Every derived field comes from an existing, already-tested `Kernel`
   accessor, never a new proof-term walker for the fields that already have
   one.** `Kernel::theorem_dependencies` is direct, self-filtered, THEOREM-only
   dependencies — used verbatim for `theorem_dependencies`.
   `Kernel::declaration_dependencies` (direct, all kinds) is bucketed by
   looking up each dependency's `Declaration` variant to produce
   `definitions_used` (kind `Definition`) and `recursors_used` (kind
   `Recursor`). `Kernel::declaration_type_dependencies` supplies
   `type_constants`. `shape_index::namespace_root` (already public, not
   reimplemented) supplies the namespace used for the external-dependency
   filter below. Only two features have no existing accessor and are computed
   by a new, minimal extractor (`examples/structural_index_extract.rs`):
   binder-role classification (carrier/connective/hypothesis, a coarse lookup
   table over the binder's head constant) and rewrite direction for `Eq`/`Iff`
   conclusions (a heuristic comparing elaborated node count of the
   conclusion's last two applied arguments — never their values, and capped
   and memoized against a shared DAG).

2. **"Proof skeleton" is a dependency-role fingerprint, not a raw proof-term
   hash, and this is a deliberate scope reduction, stated rather than
   implied.** `proof_skeleton_digest` is a SHA-256 over the sorted, role-tagged
   union of `type_constants`, `definitions_used`, `theorem_dependencies`, and
   `recursors_used` (tokens `type:`/`def:`/`thm:`/`rec:` + name). A true
   term-tree structural hash (preserving branch shape and argument order) was
   considered and dropped: it needs its own recursive walker over checked
   proof VALUES, which is exactly where CLAUDE.md's delta-unfolding blowups
   live, and the dependency-role fingerprint is what the roadmap's own
   worked example (`Int.prodRange_permute`) actually turns on — shared
   dependency NAMES, not proof-tree shape.

3. **`external_dependency_fingerprint` is the field aimed at the documented
   miss.** It is `theorem_dependencies ∪ recursors_used ∪ definitions_used`
   filtered to names whose `namespace_root` differs from the declaration's
   own. For `Int.prodRange_permute` and `Nat.countRange_permute` this set
   is non-empty and shares `Nat.restrict_injective`/`Nat.restrict_maps_into`
   even though the two declarations live in different namespaces and have
   different conclusion heads — the exact case a `--concl`/`--hyp` query on
   `shape_index` cannot reach. `scripts/check-structural-index.py`'s fixed
   query Q1 asserts this pair is returned together and fails if either
   dependency name is later renamed without updating the fixture.

4. **Held-out exclusion is a destructuring function, not a filter applied
   later — the same shape ADR-0800 uses for type/value separation.**
   `scripts/gen-structural-index.py`'s `select_eligible_mathlib_facts`
   reads `artifacts/autogenesis/nursery-v1.json` and
   `nursery-v2-extension.json` (never edited by this phase) and returns only
   entries whose `partition != "held-out"`; nothing downstream ever holds a
   reference to the raw entry list. `check-structural-index.py`'s HELD_OUT
   guard re-derives the held-out `fact_id` set independently from the same
   two nursery files and asserts none of those ids, or any Mathlib goal
   feature derived from one of their fact files, appears anywhere in the
   committed `mathlib-goal-features.json` — checked against the external
   nursery files, not against the artifact's own recorded exclusion count,
   for the same reason ADR-0800's MISSING guard reads an external population
   registry rather than the pack's own metadata.

5. **Mathlib goal features never read a proof.** `artifacts/facts/F-*.json`
   entries sourced from the Mathlib nursery carry `formal.statement` as a
   Lean-surface GOAL string with a provenance note that the proof term and
   tactic trace were not consulted (verified by reading
   `F-ml430-nat-sqrt-eq-79ae8eae.json`: `"the proof term and tactic trace
   were not consulted"`). `project_mathlib_goal_features` destructures
   exactly four keys (`fact_id`, `family`, `goal_head`, `hyp_count`) out of a
   parse of that string — never the full statement text, never any
   `evidence`/`provenance` field — mirroring ADR-0800's `project_type_only`:
   a function that cannot leak a field it does not name, checked by a guard
   that asserts the projection file's records have exactly those four keys.

6. **Three signal columns, reported separately, never merged into one
   ranking score.** A query result row carries `identity_match` (exact
   rendered-name equality), `structural_score` (count of matching structural
   predicates: shared external-dependency names, shared concl_head, shared
   recursor), and `lexical_score` (spelling-insensitive name similarity,
   reusing the same normalization CLAUDE.md documents for `CReal` names —
   underscore/camelCase both collapsed). No field combines these; a caller
   that wants one ranking must say so explicitly, and the fixed-query
   fixtures assert each column independently so a future change that
   silently folds lexical matches into the structural count is caught.

7. **Fixed queries commit their exact expected candidate list.**
   `artifacts/structural-index/queries.json` pins query definitions and
   `expected_names` (sorted); `check-structural-index.py` re-runs each query
   against the committed index and diffs the full candidate set, not a
   count — a query that starts returning an extra unrelated match fails
   exactly like one that stops returning the right one.

## Alternatives

**Reimplement a full delta-normalizing proof-term structural hash.** Rejected
for this phase: the fields the roadmap's own motivating example needs
(shared dependency names across namespaces) are already reachable from
existing `theorem_dependencies`/`declaration_dependencies`, and a term-tree
hash adds real kernel-unfolding cost and risk for a signal this phase does
not yet have a query that needs. Left as an explicitly named follow-on in
`docs/plan/status/l3-d2-structural-index.md`.

**Build a Lean-source parser for Mathlib goal features instead of reading
`formal.statement`.** Rejected: the fact ledger already carries exactly the
field needed (a proof-free Lean-surface goal string, with its own provenance
note that the proof was not consulted), and parsing Mathlib source directly
would reintroduce exactly the risk ADR-0800 and this ADR are both built to
foreclose — a wider read surface than the four keys the projection needs.

## Consequences

`crates/axeyum-lean-kernel/examples/structural_index_extract.rs` is a new,
narrowly-scoped example; `shape_search.rs` and `shape_index.rs` are untouched.
`scripts/gen-structural-index.py` / `scripts/check-structural-index.py` /
`scripts/tests/test-structural-index-mutations.sh` own
`artifacts/structural-index/`. A later phase that wants a true proof-tree
skeleton hash, or a richer Mathlib goal-feature set, extends this index
rather than replacing it — the dependency-derived fields and the held-out
exclusion mechanism do not change shape under either extension.
