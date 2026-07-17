# ADR-0216: QF_BV default and explicit consumer profiles

Status: accepted
Date: 2026-07-17

## Context

The artifact review found that the dependency-minimal scalar QF_BV profile was
tested but not selected by a real consumer. `axeyum-solver` defaulted to the
full multi-theory surface, so Glaurung and the browser binding silently compiled
far more code than their direct QF_BV paths used. That made the minimal
pure-Rust deployment claim aspirational rather than a property of shipped
manifests.

A manifest-only switch is not sufficient. Glaurung retained a legacy
`solve_smtlib` reference bridge in the same feature as its direct QF_BV backend.
The browser binding called the same full facade as its only API, was outside the
workspace build gate, and exposed a stale `wasm32` clock-type mismatch in the
proof exporter when built for the actual target.

## Decision

Make `qfbv` the exact default feature of `axeyum-solver`. Every in-tree
multi-theory consumer must disable defaults and opt into `full`; the browser
binding and Glaurung's production backend must disable defaults and opt into
`qfbv`.

Put `axeyum-wasm` in the workspace and keep its public JSON API, but implement
that API as a narrow SMT-LIB parse followed by `SatBvBackend`. Accept only
scalar `QF_BV`, retain single-query push/pop/reset/assumption semantics, and
fail closed on broader declared logics. The binding may depend on the existing
pure-Rust parser, but must not activate the full solver feature. Compile it for
`wasm32-unknown-unknown` in CI.

In Glaurung, keep the direct production feature QF_BV-only and move the legacy
text bridge behind an explicit additive feature that activates `full`. Add a
manifest/dependency-tree firewall so default/profile drift fails the normal
validation gate.

## Evidence

The profile firewall first failed on the former `default = ["full"]`. After
the flip, the explicit and default solver trees contain only the scalar
Axeyum crates (`ir`, `query`, `rewrite`, `aig`, `bv`, `cnf`, and `solver`). The
bench, EVM, property, and verification consumers explicitly select `full`.
Full-facade integration-test crates and the geometry example are also
feature-gated, so the package-default test build exercises enabled-module unit
tests plus the dedicated QF_BV contract instead of failing on unavailable
multi-theory imports. The all-feature workspace gate still compiles and runs
the complete suite.

The browser tests drive real QF_BV SAT and UNSAT scripts through the narrow
binding, check logic/status metadata, and prove a QF_LIA script fails closed.
The first real target build exposed `std::time::Instant` crossing into the
WASM-clock CNF proof API; a target-conditional alias fixes that defect. A
subsequent `cargo build -p axeyum-wasm --target wasm32-unknown-unknown` passes.

Glaurung's ordinary `solver-axeyum` tree activates only the `qfbv` solver
feature and compiles alongside Z3. Its separately selected
`solver-axeyum-text` feature also compiles, preserving the reference path
without hiding its cost.

## Alternatives

- Keep `full` as the default and rely on every lean consumer to remember a
  negative feature flag: rejected because the reviewed consumers already
  demonstrated that this convention drifts silently.
- Remove the named `qfbv` feature because it is dependency-empty: rejected
  because explicit intent is useful in manifests and enforceable by tooling.
- Expand `qfbv` until it includes the full SMT-LIB facade: rejected because it
  would restore the solver-module footprint this decision is meant to exclude.
- Delete the Glaurung text bridge or browser text API: rejected because both are
  useful; a narrow/explicit boundary preserves them honestly.
- Claim browser readiness from a host build: rejected after the actual target
  build found a real clock-type defect.

## Consequences

The default solver crate and Glaurung's production backend now realize the
minimal scalar surface. Full consumers are more verbose but auditable. Adding
a full-only API to a QF_BV consumer becomes a compile failure rather than a
silent footprint expansion.

The browser binding no longer exposes broader logics through its JSON API.
Its SMT-LIB parser still has pure-Rust FP/string parsing dependencies, so this
decision supports a minimal **solver** claim, not an unmeasured minimum bundle
size claim. Browser latency, generated bundle size, and parser-footprint
splitting remain empirical follow-up work under the deployability gate.
