# ADR-0310: Expose the curated SMT-LIB text-front-door module

Status: accepted
Date: 2026-07-20

## Context

After ADR-0309, warning-denied all-feature rustdoc reports 172 documented
`axeyum-solver` root items. The next independent R4 census covers the SMT-LIB
text front door.

The private `smtlib` implementation module contains exactly 25 public items,
and the root re-export contains exactly the same 25 items:

- 2 outcome/model structures;
- 11 solve, incremental, model, value, assignment, assertion, option, info,
  proof, and unsat-core text-command entry points;
- 2 textual optimization entry points; and
- 10 checked string-route/front-door helpers.

No public constant, internal state, parser helper, or unchecked implementation
detail exists in the module outside that root-owned set. Unlike earlier source
modules whose public items mixed theories, certificates, and instrumentation,
this file boundary already is the semantic boundary.

The surface is full-profile only. Glaurung's production dependency selects
`qfbv`, so it does not compile the SMT-LIB text front door. Existing full-profile
callers use root paths, making source compatibility a required gate.

## Decision

**Make the existing full-only `smtlib` module public, hide its duplicate
historical root aliases only from rustdoc, and keep every internal helper
private.**

The canonical path is `axeyum_solver::smtlib`, including
`smtlib::solve_smtlib`, command-specific solve functions, textual optimization,
and the checked string-route helpers used by the text pipeline.

Every newly reachable module item was already public at the crate root. Root
paths remain callable and type-identical. No parser behavior, command semantics,
string routing, model/proof replay, solver selection, feature boundary, or
consumer import changes.

## Evidence

- Strict all-feature rustdoc reports 148 documented root items, down from 172.
- The public `smtlib` module contains exactly 25 documented entries.
- A source census finds exactly those same 25 `pub` items in `smtlib.rs`; all
  other implementation details remain private.
- The minimal `qfbv` profile remains at 26 documented root items, exposes only
  the `proofs` module, and has no `smtlib` module.
- Dedicated all-feature API tests compare both public structures and
  representative solve, optimize, incremental, and string-route function
  addresses against historical root paths.
- All 891 full-profile solver library tests, strict all-target Clippy, and both
  warning-denied rustdoc profiles pass under the bounded one-job configuration.

## Alternatives

- **Create a second facade such as `text::smtlib`.** Rejected: it adds an
  artificial level when the existing module is already an exact, coherent
  ownership boundary.
- **Re-export only headline solve functions.** Rejected: the command-specific
  functions and checked route helpers are existing supported public contracts;
  omitting them would leave the same flat-root discovery problem.
- **Move string-route helpers under `theories::strings`.** Rejected: these
  helpers operate on parsed scripts and front-door verdict upgrades, not direct
  theory terms.
- **Delete historical root paths.** Rejected: a breaking migration is not needed
  for the documentation and ownership improvement.

## Consequences

- The documented all-feature root is 24 items smaller net of the newly visible
  `smtlib` module.
- Text consumers gain the natural `axeyum_solver::smtlib::*` namespace while all
  existing root imports continue to compile.
- The production `qfbv` footprint remains unchanged.
- R4 should next census interpolation independently, then the remaining general
  refutation/certificate utilities. Neither belongs under SMT-LIB merely because
  the text front door calls it.
