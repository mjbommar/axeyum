# ADR-0306: Group specialized certificate catalogs without hiding solver APIs

Status: accepted
Date: 2026-07-20

## Context

ADR-0305 made proof production and reconstruction discoverable under
`axeyum_solver::proofs` while preserving historical root paths. The next R4
census separates two different kinds of remaining root surface:

- general solver and theory entry points, which belong in the later theory/API
  census; and
- narrow checked-certificate catalogs, especially the array micro-scenarios and
  quantified certificate families identified by the architecture review.

After ADR-0305, warning-denied all-feature rustdoc still reports 442 documented
root items. The selected array catalog contributes 31 items. The quantified
catalog contributes 72 certificate types, bounds, constructors, and independent
checkers. Two additional finite-quantifier functions emit Alethe proofs and
therefore belong in the existing `proofs::alethe` namespace instead.

The distinction matters. `check_model` and `check_model_with_assignment` happen
to be implemented beside quantified-SAT certificates, but they are the general
original-term model replay API. Likewise, `check_qf_abv_lazy` and
`check_with_array_elimination` are solver entry points rather than certificate
catalog entries. Hiding either group merely because of its source file would
make the public organization less truthful.

Glaurung selects the minimal `qfbv` feature profile, so none of this full-only
catalog is compiled into that consumer. Full-profile workspace consumers do use
historical root paths, so the organization must remain source-compatible.

## Decision

**Add a full-only `certificates` facade with `arrays` and `quantifiers`
submodules, hide only the corresponding historical root aliases from rustdoc,
and retain general model/theory APIs at the root pending their own census.**

The canonical catalog paths are:

- `certificates::arrays` for checked array/memory certificate structures,
  deterministic constructors, and refutation checkers;
- `certificates::quantifiers` for quantified certificate structures, explicit
  resource bounds, deterministic constructors, and independent checkers.

The finite-quantifier Alethe emitters move to the canonical
`proofs::alethe` facade. Every historical root path remains callable and
type-identical. No implementation module becomes public, and no previously
private item is exported.

## Evidence

- Strict all-feature rustdoc reports 338 documented root items, down from 442.
- The `certificates` subtree contains 105 organized entries: two submodule
  links, 31 array entries, and 72 quantified entries.
- `proofs::alethe` grows from 28 to 30 entries by taking ownership of the two
  finite-quantifier proof emitters.
- The minimal `qfbv` profile remains unchanged at 26 documented root items and
  has no `certificates` module.
- Dedicated all-feature API tests compile canonical and historical paths and
  compare representative type identities and function addresses across both
  catalogs.
- Core `check_model`, `check_model_with_assignment`, and array decision
  procedures remain documented at the root.

## Alternatives

- **Group every type whose name contains `Certificate`.** Rejected: safety,
  interpolation, proof evidence, and domain-specific checked catalogs have
  different consumers and ownership. A name-based sweep would erase those
  boundaries.
- **Move entire source-module export blocks.** Rejected: `quant_sat_cert` and
  `abv` each contain general APIs that do not belong in a certificate catalog.
- **Delete historical root aliases.** Rejected: the readability gain does not
  require a breaking workspace and downstream migration.
- **Move narrow scenarios to another crate now.** Deferred: that is a package
  and dependency decision, whereas a curated facade produces a measurable
  artifact-review improvement without moving trust boundaries or code.

## Consequences

- The documented all-feature crate root is 104 items smaller net of the new
  `certificates` module.
- Certificate families are discoverable by domain without implying that their
  implementations or trusted-checking boundaries changed.
- Existing source continues to compile; future removal of root aliases requires
  an explicit breaking-release decision.
- R4 continues with the separate theory API census. It must preserve the
  distinction between decision procedures, theory state/contracts, and
  certificate/proof objects rather than grouping by source-file accident.
