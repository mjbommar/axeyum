# Lane: python-layer — PyO3 binding, Python API, agentic frontier loop

<!-- plan-section: lane-status -->

**WIP (agent-python-layer, 2026-08-24).** New strand
[`docs/python-2026-08/`](../../python-2026-08/README.md): three plans in
dependency order — `01` binding crate + maturin + stub gate, `02` the typed
Python API over SMT/solver/IR/CAS/kernel/producers/knowledge artifacts, `03`
the pydantic-ai agent with replayable episodes. Measured basis: PyO3 0.29.2
compiles under the workspace `unsafe_code = "deny"` + clippy pedantic; abi3
wheel imports on 3.14.4 with no libpython link; 640 scripts have zero
third-party imports and stay that way. Next: land 01-S1..S3 (crate, errors,
`smt.solve` + replay), then 02 by submodule, each slice gated by
`just py-check` with a nonzero test count.

<!-- plan-section: landed-changes -->

| 2026-08-24 | pending | Python strand: plans 01–03 and the two measured studies under `docs/python-2026-08/` |
