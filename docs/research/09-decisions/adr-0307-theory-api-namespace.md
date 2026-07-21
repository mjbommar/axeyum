# ADR-0307: Group theory contracts without absorbing cross-cutting APIs

Status: accepted
Date: 2026-07-20

## Context

ADR-0305 and ADR-0306 give proof and specialized certificate surfaces canonical
homes while retaining every historical root path. The remaining all-feature
root still contains theory-specific state and direct decision procedures beside
unrelated auto-dispatch, SMT-LIB, optimization, model replay, symbolic execution,
and verification APIs.

A source-module sweep is not a sound classification. For example:

- `auto` contains both the cross-theory front door and quantifier procedures;
- `euf` contains an Ackermann certificate as well as UF and UF/arithmetic
  decision procedures;
- `lra` contains Farkas certificate data, simplex decision procedures, and
  unsat-core extraction; and
- `quant_sat_cert` owns the general original-term `check_model` replay API.

The post-ADR-0306 all-feature root has 338 documented items. A semantic census
identifies 63 documented theory entries across array, arithmetic, datatype,
quantifier, string, UF, and combined-theory ownership. Two additional public
UF/arithmetic metric helpers are already hidden instrumentation; they remain on
their historical paths and do not become canonical facade entries.

Glaurung's production Axeyum dependency selects only `qfbv`, so the full-only
theory surface is absent there. Full-profile workspace consumers use many root
paths, which makes source compatibility a required gate.

## Decision

**Add a full-only `theories` facade with seven semantic submodules, hide the
corresponding historical aliases only from rustdoc, and leave cross-cutting APIs
in their existing domains.**

The canonical theory paths are:

- `theories::arrays` for direct array decision procedures;
- `theories::arithmetic` for integer, real, and nonlinear state/procedures;
- `theories::datatypes` for datatype, enum, and record descriptors/procedures;
- `theories::quantifiers` for quantifier decision procedures;
- `theories::strings` for direct string-theory procedures;
- `theories::uninterpreted_functions` for direct EUF state/procedures; and
- `theories::combination` for shared theory contracts and combined UF/array/
  arithmetic procedures.

The facade does not absorb `check_auto`, `solve`, SMT-LIB front doors,
optimization, interpolation, symbolic execution, BMC/PDR, model replay, proof
production, or certificate constructors. Existing root paths remain callable
and type-identical. No private item becomes public.

## Evidence

- Strict all-feature rustdoc reports 276 documented root items, down from 338.
- The `theories` subtree contains 70 organized entries: seven submodule links
  plus 63 documented contracts and procedures.
- The minimal `qfbv` profile remains at 26 documented root items and has no
  `theories` module.
- Dedicated all-feature API tests compare representative type identity and
  function addresses in every theory submodule against historical root paths,
  including monomorphized generic array/combined procedures.
- The general `check_model`/`check_model_with_assignment`, auto-dispatch,
  SMT-LIB, optimization, proof, certificate, and symexec APIs remain outside
  the theory facade.

## Alternatives

- **Make implementation modules public.** Rejected: this exposes private helpers
  and binds API ownership to current file layout.
- **Put every remaining solver item under `theories`.** Rejected: optimization,
  SMT-LIB, model replay, symexec, verification, proofs, and certificates are
  cross-cutting or consumer-facing domains rather than theories.
- **Group by return type or name prefix.** Rejected: implementation history has
  placed general APIs in certificate-named files and certificate data in theory
  files; names are not an ownership proof.
- **Delete the old root paths.** Rejected: a breaking migration is unnecessary
  for the measured documentation and discoverability gain.

## Consequences

- The documented all-feature root is 62 items smaller net of the new
  `theories` module.
- A reader can find direct theory procedures without navigating certificate and
  application/verification catalogs.
- Existing consumers continue to compile. Removing compatibility aliases still
  requires an explicit breaking-release decision.
- R4's three requested ownership facades are now measured. The next API cleanup
  must census the remaining cross-cutting domains rather than stretching
  `theories`, `proofs`, or `certificates` beyond their recorded meanings.
