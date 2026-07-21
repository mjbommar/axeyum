# ADR-0309: Group objective-optimization APIs

Status: accepted
Date: 2026-07-20

## Context

After ADR-0308, warning-denied all-feature rustdoc reports 211 documented
`axeyum-solver` root items. PLAN requires each remaining cross-cutting domain to
be censused independently rather than collected in a miscellaneous facade.

The objective-optimization surface contains 40 existing public entries:

- 6 deterministic, replay-checked model-minimization contracts;
- 5 `MaxSAT` and weighted-`MaxSAT` contracts; and
- 29 scalar, lexicographic, box, and Pareto objective contracts.

Two nearby surfaces do not belong to this ownership boundary.
`PblsBackend`/`solve_local_search` decide satisfiability and are used by
preprocessing; they do not optimize a caller-supplied objective. The
`optimize_smtlib*` functions are textual command front doors and remain with the
separate SMT-LIB census. The `Solver` facade's optimization methods remain
documented on that consumer-facing object.

This surface is full-profile only. Glaurung's production dependency selects
`qfbv`, so it does not compile any of these APIs. Existing full-profile callers
use root paths, making compatibility a required gate.

## Decision

**Add a full-only `optimization` facade with three semantic submodules, hide
the corresponding historical aliases only from rustdoc, and leave SAT decision
backends, SMT-LIB commands, and the general `Solver` facade in their existing
domains.**

The canonical paths are:

- `optimization::models` for replay-checked model minimization;
- `optimization::maxsat` for `MaxSAT` and weighted `MaxSAT`; and
- `optimization::objectives` for scalar, lexicographic, box, and Pareto
  objective optimization.

Every facade entry was already public. Historical crate-root paths remain
callable and type-identical. No optimization algorithm, resource policy, model
replay, solver routing, feature selection, or consumer import changes.

## Evidence

- Strict all-feature rustdoc reports 172 documented root items, down from 211.
- The `optimization` subtree contains 43 entries: three submodule links plus 40
  existing contracts.
- Subtree counts are 6 model-minimization, 5 `MaxSAT`, and 29 objective entries.
- The minimal `qfbv` profile remains at 26 documented root items, exposes only
  the `proofs` module, and has no `optimization` module.
- Dedicated all-feature API tests compare representative type identity and
  function addresses in all three submodules against historical root paths.
- All 891 full-profile solver library tests, strict all-target Clippy, and both
  warning-denied rustdoc profiles pass under the bounded one-job configuration.

## Alternatives

- **Include pseudo-Boolean local search.** Rejected: it is a satisfiability
  backend with no objective contract; source proximity to MaxSAT is not semantic
  ownership.
- **Include SMT-LIB optimization commands.** Rejected: their public contract is
  text parsing and command execution, which belongs to the later SMT-LIB
  front-door census.
- **Hide the `Solver` methods.** Rejected: the object facade is intentionally a
  compact consumer entry point rather than duplicate flat free functions.
- **Delete historical root paths.** Rejected: a breaking migration is not needed
  to establish canonical ownership and improve documentation discovery.

## Consequences

- The documented all-feature root is 39 items smaller net of the new
  `optimization` module.
- Objective users gain one discoverable API tree while all existing imports
  continue to compile.
- The production `qfbv` footprint remains unchanged.
- R4 should next census the SMT-LIB textual front door independently, then
  interpolation and general refutation utilities. Neither belongs under
  `optimization` merely because optimization internally calls solving.
