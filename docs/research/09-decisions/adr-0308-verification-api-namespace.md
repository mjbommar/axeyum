# ADR-0308: Group verification and symbolic-execution APIs

Status: accepted
Date: 2026-07-20

## Context

ADR-0305 through ADR-0307 give proof, certificate, and direct-theory APIs
canonical homes while retaining every historical crate-root path. Warning-denied
all-feature rustdoc still reports 276 documented root items. The next census
must classify cross-cutting domains independently rather than widening those
three facades.

One coherent 66-item domain spans transition-system verification and the
application-facing machinery built on it:

- 10 bounded-model-checking and k-induction contracts;
- 5 constrained-Horn-clause contracts;
- 6 interpolation-model-checking contracts;
- 9 property-directed-reachability contracts;
- 12 symbolic-execution and symbolic-memory contracts; and
- 24 tiny-BV reference-VM, coverage, and witness contracts.

These are not solver theories: they consume theory solvers to analyze programs
or transition systems. They are also not proof-format APIs, even where a safe
outcome carries a checked certificate. The distinction is exercised by real
workspace consumers: `axeyum-verify` imports transition-system/BMC contracts,
while `axeyum-evm` imports symbolic-execution and symbolic-memory contracts.

Glaurung's production dependency selects only `qfbv`, so this full-profile
application surface is absent from that build. Existing full-profile consumers
use historical root paths, making source compatibility a required gate.

## Decision

**Add a full-only `verification` facade with six semantic submodules, hide the
corresponding historical aliases only from rustdoc, and leave solver/theory,
proof, certificate, optimization, interpolation-construction, and SMT-LIB APIs
in their existing domains.**

The canonical paths are:

- `verification::transition_systems` for BMC and k-induction;
- `verification::horn` for constrained Horn clauses;
- `verification::imc` for interpolation-based model checking;
- `verification::pdr` for property-directed reachability;
- `verification::symbolic_execution` for path and symbolic-memory contracts;
  and
- `verification::toy_bv_vm` for the reference VM and its reachability,
  coverage, test-generation, trace, and witness reports.

Every facade entry was already public. Historical crate-root paths remain
callable and type-identical. No solver behavior, certificate checker, trust
boundary, feature selection, or consumer import changes.

## Evidence

- Strict all-feature rustdoc reports 211 documented root items, down from 276.
- The `verification` subtree contains 72 entries: six submodule links plus 66
  existing contracts.
- Subtree counts are 10 transition-system, 5 Horn, 6 IMC, 9 PDR, 12 symbolic-
  execution, and 24 tiny-BV VM entries.
- The minimal `qfbv` profile remains at 26 documented root items, exposes only
  the `proofs` module, and has no `verification` module.
- Dedicated all-feature API tests compare representative type identity in all
  six submodules and the Horn function address against historical root paths.
- All 891 full-profile solver library tests, strict all-target Clippy, and both
  warning-denied rustdoc profiles pass under the bounded one-job configuration.

## Alternatives

- **Put these APIs under `theories`.** Rejected: transition systems, path
  exploration, coverage, and program witnesses consume theories but are not
  theories themselves.
- **Put safe-result certificates under `proofs` or `certificates`.** Rejected:
  the result types are inseparable from their verification procedures and are
  application-level contracts; their embedded DRAT artifacts still use the
  existing proof facade.
- **Expose implementation modules directly.** Rejected: it would bind public
  ownership to file layout and expose unrelated private helpers.
- **Migrate workspace consumers in the same change.** Rejected: canonical-path
  migration is useful later, but combining it with ownership establishment
  would weaken the source-compatibility gate.

## Consequences

- The documented all-feature root is 65 items smaller net of the new
  `verification` module.
- Verification consumers gain one discoverable, semantically named API tree
  without a breaking migration.
- Existing root imports and the production `qfbv` profile remain unchanged.
- The next R4 census should treat optimization, SMT-LIB, interpolation, and the
  remaining general certificate/refutation utilities as separate domains; none
  belongs in `verification` merely to reduce the root count.
