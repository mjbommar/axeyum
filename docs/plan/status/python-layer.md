# Lane: python-layer — PyO3 binding, Python API, agentic frontier loop

<!-- plan-section: lane-status -->

**WIP (agent-python-layer, 2026-08-24).** Strand
[`docs/python-2026-08/`](../../python-2026-08/README.md). Plan 01 is landed
end to end: `crates/axeyum-py` → `axeyum._native` (PyO3 0.29.2, abi3-py312,
no libpython link), root `pyproject.toml`, generated stubs with a drift gate
that fails on zero comparisons, `just py-check`, and a `check.sh` step that
prints SKIPPED (never passed) without `uv`. Plan 02 landed so far:
`axeyum.smt.solve` + `Outcome.replay()` (02-A part), `axeyum.knowledge`
(02-E, 161 tests, validator-mirroring), `axeyum.kernel` (02-C, 57 tests,
epoch-checked handles, 1,207 generated prelude fields; measured nat 235
theorems / 0 axioms, axreal 30). In flight in isolated snapshots:
`axeyum.ir` + `axeyum.solver` (02-A) and `axeyum.cas` + `cas.certify`
(02-B). Next: producer promotion to `src/producers/` and `axeyum.producers`
(02-D), then plan 03 A1 (episode schema + fail-closed checker).
Integration rule learned today: the shared checkout sits on a branch far
behind `main`; move tracked-file edits as patches, verify Rust slices in a
`lane-snapshot.sh` tree, commit from the detached worktree.

<!-- plan-section: landed-changes -->

| 2026-08-24 | `537328b3c` | `axeyum.kernel`: epoch-checked handles, nine preludes with generated field tables, footprints/closures raising on absent names, `add_declaration` with typed `KernelError`, Lean rendering and NDJSON export, identity hashes; 57 tests |
| 2026-08-24 | `df1e7d185` | `axeyum.knowledge`: read-only typed accessors over facts, frontier, operations, overlay, nursery (partition-safe), claims, concepts, pinned `math-education`, autogenesis artifact index; 161 tests mirroring the validators |
| 2026-08-24 | `9dd2dc82a` | Generated native stubs with a drift gate (fails on drift and on zero compared), `just py-check`, conditional `check.sh` step, fleet-hosts `uv` row, Python user guide |
| 2026-08-24 | `a8e8d34a9` | `crates/axeyum-py` binding crate, `axeyum.smt.solve` with `unknown` as a value and `Outcome.replay()`, differential vs `smtcomp_cli`, conftest that fails on zero collected tests |
| 2026-08-24 | `9cfdf86fe` | Python strand: plans 01–03, two measured studies, three API inventories under `docs/python-2026-08/` |
