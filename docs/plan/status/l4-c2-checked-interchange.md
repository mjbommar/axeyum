# Status: L4 phase C2 — universal checked interchange for credited roots

<!-- plan-section: lane-status -->

**Lane `l4-c2-checked-interchange`.** DONE for the bounded credited-root
population this lane scoped; wider population growth is future work, not a
gap in what landed.

**Track:** `docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md`,
phase C2
**Phase:** ADR-0915 landed; gate registered in `just check` / `scripts/check.sh`
**Date:** 2026-08-30

## Summary

C2 asks, for every headline theorem representable in the pinned Lean slice:
export the exact reachable Axeyum closure, fresh-reimport or replay it
through an independent path, submit it to pinned Lean's kernel, and bind the
result to the fact receipt, with `missing=0` mandatory.

The credited-root population is ADR-0835's graph join's own
`trust_footprints` dimension: 9 of 446 declarations in
`mathlib-group-defs-v1` carry a Mathlib mirror fact, a resolvable kernel
theorem, and an empty axiom footprint. All 9 were run live against pinned
Lean 4.30.0 (`d024af099ca4bf2c86f649261ebf59565dc8c622`): exported, fresh-
reimported through an independent reader, and submitted to
`Lean.Environment.addDeclCore` via `scripts/lean/replay-lean4export.lean`.
`missing=0`, `accepted=9`, verified end to end, not merely asserted.

## Delivered

- `artifacts/checked-interchange/populations/credited-roots-v1.json` — the
  committed population snapshot (external authority pattern from ADR-0800).
- `artifacts/checked-interchange/census/credited-roots-v1.census.json` — the
  machine-generated credit census, written by the Rust pipeline below.
- `crates/axeyum-lean-import/tests/checked_interchange_credited_roots.rs` —
  the real pipeline: export/reimport/replay/grade over the 9 credited roots,
  plus four adversarial fixtures (wrong proof, wrong goal, no inheritance,
  declined-by-typed-reason) all run live against pinned Lean.
- `scripts/check-checked-interchange.py` — the independent validator, no
  Lean toolchain and no cargo run needed. Seven guards: MISSING,
  STALE_POPULATION, ACCOUNTING, MANDATORY_MISSING_ZERO, BARE_NAME_ACCEPT,
  BARE_TYPE_ACCEPT, DECLINE_PROBE_VACUOUS.
- `scripts/gen-checked-interchange.py` — the thin producer wrapper that runs
  the real pipeline with `AXEYUM_REQUIRE_LEAN=1` forced.
- `scripts/tests/test-checked-interchange.py`,
  `scripts/tests/checked_interchange_mutations.py`,
  `scripts/tests/test-checked-interchange-mutations.sh` — functional tests
  plus the mutation kill table, all 7 guards verified 1:1.
- `docs/research/09-decisions/adr-0915-checked-interchange-credit-is-earned-by-name-and-type-never-either-alone.md`.
- Gate registered as `checked-interchange` in both `justfile` (appended to
  `check:`'s dependency list, own recipe block appended at end of file) and
  `scripts/check.sh` (three `step` lines appended before the `list_only`
  block).

## Identity discipline

Grading a root ACCEPTED requires BOTH: pinned Lean's own `env.constants`
holds a constant of exactly that name, AND the type this kernel checked
renders byte-identically (via `Kernel::render_lean`) to the type the fresh
reimport independently rebuilt from the wire bytes, across two SEPARATELY
CONSTRUCTED `Kernel` instances. Neither condition alone is trusted --
ADR-0716's `Nat.multichoose` measured a real case where an identical name
named a different proposition.

## What is not covered, stated rather than hidden

437 of 446 declarations in `mathlib-group-defs-v1` have no ledger fact at
all and are out of C2's "credited roots" scope by the roadmap's own
phrasing. Extending coverage needs only a wider population snapshot, no new
identity mechanism -- `STALE_POPULATION` already re-derives the set from the
live join rather than trusting a frozen list.

`lean_export.rs`'s own documented residue (binder display names dropped for
alpha-invariance; `letE.nondep`/`isReflexive`/non-mutual `all` emitted in a
fixed conservative form because this kernel never tracks a real value for
them) is not re-derived here -- it is cited as the "cannot express" finding
this format carries, per ADR-0915.

## Remaining work

- [ ] Nothing blocking for the 9-root bounded population. Widening credited
      coverage tracks ADR-0835's own growth as more `ml430` mirrors resolve.
