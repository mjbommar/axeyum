# Lane l3-d1-declaration-spec — L3 phase D1: declarative declaration spec

## Status: in progress (scaffolding committed, generator + Rust interpreter in progress)

Task: `docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md`, phase
D1. See ADR-0965 for the design and TCB argument.

## Plan

- Pilot subsystem: `Nat.squarefreeAux` / `Squarefree`
  (`crates/axeyum-lean-kernel/src/nat_prelude/squarefree.rs`), read-only —
  not edited.
- `artifacts/declaration-spec/schema.json` + `nat-squarefree.json` (the
  pilot spec) + three negative fixtures under
  `artifacts/declaration-spec/negative-fixtures/`.
- `scripts/gen-declaration-spec.py`: validation guards (duplicate name
  in-corpus and cross-prelude, missing/invalid phase, dependency cycle) +
  generated Python types + generated Rust name/equation table.
- `crates/axeyum-lean-kernel/examples/declaration_spec_pilot.rs`: generic
  spec interpreter, builds shadow declarations in the same kernel as the
  hand-built prelude, compares `ExprId` identity and a SHA-256 digest of
  rendered type/value; `--dump-names` mode for the cross-prelude collision
  snapshot.
- `scripts/check-declaration-spec.py`: the gate; registered in `justfile`
  and `scripts/check.sh`.
- `scripts/tests/test-declaration-spec.sh`: mutation-verifies each Python
  guard, one test per guard.

## Landed so far

- ADR-0965.
- This status file.

## Not yet landed (this session, in progress)

- The schema, pilot spec, negative fixtures.
- The generator and gate scripts.
- The Rust interpreter/comparison example.
- `serde_json` dev-dependency in `crates/axeyum-lean-kernel/Cargo.toml`.
- `justfile` / `scripts/check.sh` registration.
- Mutation kill table.

## Measured results

(to be filled in as landed — digest comparison result, guard kill table,
hand-maintained-surface reduction count, autogenesis holdout isolation
before/after.)
