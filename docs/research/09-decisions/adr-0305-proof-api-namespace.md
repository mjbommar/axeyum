# ADR-0305: Group proof APIs under a compatibility-preserving namespace

Status: accepted
Date: 2026-07-20

## Context

The reviewer-aligned artifact cleanup in
[PLAN.md](../../../PLAN.md) and the
[reconstruction refactor inventory](../08-planning/reconstruction-refactor-inventory.md)
finished R3 by splitting the proof-reconstruction monolith without changing
behavior. R4 then has to address a separate problem: the `axeyum-solver` crate's
all-feature rustdoc root is an undifferentiated public wall.

The current rustdoc census is authoritative and corrects the review's older
approximately-567 estimate:

- all features: 549 root items (312 functions, 147 structs, 56 enums,
  24 constants, 4 traits, 1 type alias, and 5 modules);
- minimal `qfbv`: 36 root items (9 functions, 17 structs, 8 enums, and
  2 traits).

The minimal profile is already coherent, but its nine proof-export functions
and two proof types compete with the ordinary backend/model surface. Under
`full`, checked evidence, Alethe emission, Lean reconstruction, and
faithfulness APIs add another 96 flat proof-facing items. The problem is
documentation and ownership, not an authorization to break existing consumers:
Glaurung's minimal integration imports the historical root paths, including
`export_qf_bv_unsat_proof` and `UnsatProofOutcome`.

This closes the first bounded increment of the review's R7 public-API item. It
does not move certificate implementations between crates, alter a proof rule,
or change solver behavior.

## Decision

**`axeyum-solver` exposes a canonical `proofs` facade while retaining every
historical proof-related root export as a source-compatible, rustdoc-hidden
alias.**

The facade is deliberately hierarchical:

- `proofs::{UnsatProof, UnsatProofOutcome, export_*}` is available in the
  minimal `qfbv` profile;
- `proofs::alethe` owns public Alethe emit/check entry points;
- `proofs::end_to_end` owns the bit-blast/CNF miter certification surface;
- `proofs::evidence` owns evidence production and replay types;
- `proofs::faithfulness` owns term-to-bit-lowering faithfulness checks;
- `proofs::lean` owns Lean reconstruction and kernel-checking entry points.

These are curated re-exports from private implementation modules. The
implementation modules do not become public, and the facade exports no item
that was not already public. Root aliases remain callable and type-identical;
`#[doc(hidden)]` only removes them from the root documentation. Removing those
aliases requires a separately recorded compatibility decision and an explicit
breaking-release migration.

## Evidence

- Strict rustdoc after the change reports 26 minimal-root items, down from 36;
  the new minimal `proofs` page owns the displaced 11 items.
- Strict all-feature rustdoc reports 442 root items, down from 549. The
  `proofs` subtree contains 113 organized entries across its root and five
  submodules.
- Dedicated default-`qfbv` and all-feature API tests compile both the canonical
  paths and the historical root paths and prove that representative exported
  types are identical.
- Glaurung's current dependency is already the minimal profile
  (`default-features = false, features = ["qfbv"]`), and its existing root
  imports remain valid without a coordinated downstream commit.

## Alternatives

- **Delete every non-core root export now.** Rejected: this would be a broad
  source break across Glaurung, workspace consumers, examples, and integration
  tests, mixing migration risk into an artifact-readability increment.
- **Make the existing implementation modules public.** Rejected: that would
  expose private helpers and enlarge rather than curate the supported API.
- **Put all 500-plus items under one `full` or `advanced` module.** Rejected:
  this moves the wall down one level without giving proof, theory, and
  certificate surfaces distinct ownership.
- **Namespace the entire crate in one commit.** Rejected: proof APIs form a
  measured, independently testable first slice; theory and certificate
  groupings need their own consumer and collision census.

## Consequences

- Ordinary rustdoc readers see a materially smaller crate root and one explicit
  proof/evidence hierarchy.
- Existing source keeps compiling, including the minimal Glaurung integration.
- R4 continues with separate `theories` and `certificates` censuses; those
  should use the same curated-facade plus hidden-compatibility-alias pattern
  only where it produces a measured root reduction.
- This commit changes no solver result, accepted term, feature dependency,
  evidence format, deterministic ordering, or trusted-checking boundary.
