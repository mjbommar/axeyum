# CAS trace public intake and discovery handoff

This completes the production handoff in LIB-5 T3; it does not replace the
original [trace plan](cas-certified-trace-plan-2026-10-10.md). The current
`complex/cas_bridge_tests.rs` admits a generated identity and rejects altered
claims, but remains test-only. `fact-frontier.py` reports no CAS capability
because its dispatch manifest is absent. Completion is unproven.

## Public kernel boundary

Expose a bounded step-composition interface using the existing Complex ring
proof construction. Keep the kernel's normal dependency graph free of the CAS:
public intake uses plain Rust expression/step data; the external producer adapter
replays CAS bytes and translates source syntax before calling it. A sealed
context constructs the canonical prelude and owns its kernel, preventing caller
substitution of the carrier or equivalence relation.

Bind external original input, claimed result, ordered steps and empty assumption
context. Preserve syntax and check continuity. Reject nonempty/changed contexts;
fractional/wide literals, division, additional variables and unsupported heads
retain explicit reconstruction declines. Preserve the existing bounded integer
fragment; cap expansion/proof work before constructing unary numerals and
report resource exhaustion distinctly.

Return an admission receipt only after `Kernel::add_declaration` succeeds.
Read reached assumptions and actual proof dependencies from the kernel. Do not
raise the CAS certified-function count for a reconstruction/logging interface.
Retain distinct rejected, unsupported, resource-limited and admitted outcomes.

## Producer and discovery connection

Provide a runnable producer adapter and separate serialized replay/admission
mode. Replay must work with trace production disabled. Use a prospective
producer contract with no `proved` field, falsifiable fragment matching and
named non-examples; register the executable CAS capability and dispatch recipe.
A manifest's presence does not supply theorem credit.

Exercise two generated discovery batches: the first produces/adopts a bounded
polynomial identity; the second generates a distinct contextual identity whose
reconstruction consumes the first admitted declaration. The CAS producer reads
source expressions and limits, not earlier proof bodies or proof/value edges.
The checking/reconstruction phase may use admitted library statements. Require
actual kernel dependency on the earlier declaration; two unrelated admissions
cannot close that arrow. Publish checked-trace, reconstructed-step, admitted
statement and reached-assumption counts separately.

## Verification and integration

Allocate a dedicated ADR before adding the public API. Implement in an isolated
continuation; the existing worktree remains frozen for its live baseline gates.
Reuse existing proof builders and public dispatch machinery; avoid copying the
ring decision procedure or introducing a crate before a boundary demands one.

Run discriminating positive/negative public-intake and producer-dispatch tests,
producer-disabled replay, actual two-batch admission/dependency checks, bounded
resource/unsupported controls and private one-guard mutation controls. Measure
kernel work in release first. Confirm nonzero populations and restore mutations
bytewise. Run affected lint, compatibility and aggregate gates on the new source;
passing baseline gates do not cover new production code. Reconcile the final
completion audit, archive finished lanes and integrate only after required gates.
