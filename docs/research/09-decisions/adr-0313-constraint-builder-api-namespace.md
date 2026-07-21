# ADR-0313: Give constraint builders one bounded namespace

Status: accepted
Date: 2026-07-20

## Context

ADR-0312 reduces the warning-denied all-feature `axeyum-solver` root to 77
documented items. A final R4 census asks whether any residual helper family has
independent ownership, with an explicit stop condition against inventing a
miscellaneous namespace.

The residual surface is mostly the intended solver front door: backend traits
and implementations, models and values, incremental state and measurements,
configuration and structural `Unknown`, strategies, model replay, preprocessing,
and direct solve/check functions. Those entries should remain easy to find at
the crate root.

One separate full-only family remains: 12 existing term-construction helpers.
They comprise `distinct`, six Boolean cardinality builders, and five
pseudo-Boolean comparison builders. These functions build constraints in a
caller-owned arena; they do not solve, optimize, project a model, or emit proof
evidence.

Nearby `abduct`, `mbp_lia`, and `mbp_lra` are not constraint-builder siblings:
they derive explanations or project regions from an existing reasoning state.
Likewise, optimization, theory, and SMT-LIB commands already have recorded
owners.

## Decision

**Add a full-only `constraints` facade with cardinality and pseudo-Boolean
submodules plus `distinct`, retain historical root aliases, and end the R4
namespace sweep.**

The canonical paths are:

- `constraints::distinct`;
- `constraints::cardinality::{at_least, at_most, at_most_one, between,
  exactly, exactly_one}`; and
- `constraints::pseudo_boolean::{pb_eq, pb_ge, pb_gt, pb_le, pb_lt}`.

Historical root paths remain callable and type-identical but are hidden from
root rustdoc. No implementation module becomes public and no builder semantics,
accepted sort, error behavior, solver route, or feature selection changes.

## Evidence

- Strict all-feature rustdoc reports 66 documented root items, down from 77.
- The `constraints` subtree contains 14 entries: three top-level entries, six
  cardinality builders, and five pseudo-Boolean builders.
- Minimal `qfbv` remains at 26 documented root items and has no `constraints`
  module.
- Dedicated full-profile compatibility tests compare representative function
  addresses for all three ownership groups against historical root paths.
- All 891 full-profile solver library tests, strict all-target Clippy, and both
  warning-denied rustdoc profiles pass under the bounded one-job configuration.

## Alternatives

- **Leave the 12 builders flat.** Viable but less discoverable: cardinality and
  pseudo-Boolean construction form a clear caller-facing task independent of
  solving.
- **Add abduction and model-based projection.** Rejected: those derive formulas
  or regions from reasoning results rather than construct ordinary input
  constraints.
- **Create a broad `helpers` module.** Rejected: it has no semantic ownership
  and would merely move unrelated residual APIs one level down.
- **Namespace backends or the solver front door in the same change.** Rejected:
  those are the crate's central contracts, already coherent at the root, and
  minimal `qfbv` should not be churned for an all-feature documentation target.

## Consequences

- Constraint construction is discoverable without changing existing callers.
- The residual 66-item full root is intentionally composed of core solver,
  backend, model, incremental, strategy, replay, and small derived-reasoning
  contracts plus already-owned public modules.
- R4 is complete. Further namespace work requires new consumer evidence and a
  separate decision; root-count reduction alone is no longer a reason.
- Artifact-readiness work returns to the next review item: audit loose
  configuration booleans and model invalid states as types, without combining
  that behavior-bearing change with this documentation-only series.
