# Lane: python-layer — PyO3 binding, Python API, agentic frontier loop

<!-- plan-section: lane-status -->

**WIP (agent-python-layer, 2026-08-24).** Strand
[`docs/python-2026-08/`](../../python-2026-08/README.md). Plans 01-03 are
complete on `main`; the quality goal (`10-quality-best-practices.md`,
sourced against PyO3 0.29 / maturin / pyo3-stub-gen / Hypothesis guidance)
has landed Q1-Q4: 73 hypothesis property tests against independent
references (which found and fixed a replay that certified an EMPTY
assertion stack on the parser's word-only fallback), 8 Rust-side unit tests,
a `ty` ratchet; the zero-copy audit and `solve_smtlib_with_model` (the
front door now returns its own arena and model -- `smt.solve` 2.22x faster
on `sat`, replay of the deciding run, no second solve), `cast` over
`extract` in 13 `__eq__`s, the CAS detaching, bytes accessors for proofs;
release wheels (abi3 + 3.14t + sdist, smoke-installed before any publish);
the eight open tier-R rows -- `PYTHON_COVERAGE|...|tier_r_unreferenced=0`.
Gate at `7c01fa0bd`: pytest 1,209 passed / 15 skipped, clippy 0 on nightly
and stable. In flight: Q5 typed stubs via pyo3-stub-gen behind an off-by-
default feature, with `stubtest` and an `Any` ratchet. Next: Q6 (derive
`eq`/`hash`/`str`; make `Config`/`Incremental` `Sync` so `unsendable` and
then `gil_used = true` can go).

Detail and older landed rows moved to [`../notes/python-layer.md`](../notes/python-layer.md).

<!-- plan-section: landed-changes -->

| 2026-08-24 | `68f5d61a4` | `axeyum.m`: Mathematica-shaped verbs over the CAS -- parser, variable inference, readable printer; three iterations (equations, assumptions, limits at infinity; systems, definite integrals, Substitute, semantic Equal, mixed int/Fraction arithmetic on `Expr`; Sum, Reduce, Rationalize, NRoots, polynomial toolkit); 19 tests |
| 2026-08-24 | `460bee2db` | Q2: replay of the deciding run's model via `solve_smtlib_with_model` (2.22x on sat), clone audit (12 borrows, 13 `__eq__` via cast), CAS detaches, bytes accessors, benchmarks |
| 2026-08-24 | `d904a5c14` | `axeyum-solver`: `solve_smtlib_with_model` -- the front door returns arena, assertions and model; `solve_smtlib` wraps it; 152-file equality test |
| 2026-08-24 | `68fb060e7` | Q1: 73 hypothesis differentials, 8 Rust unit tests, `ty` ratchet; fixed replay-over-empty-stack on the word-only fallback |
| 2026-08-24 | `a4393ef18` | Q4: the eight open tier-R solver rows as typed ledgers + `get_assertions/get_info/get_option` + `SolveStats`; coverage backlog empty |
| 2026-08-24 | `e0ce50f97` | Q3: release wheels (manylinux 2_28, macOS, Windows, 3.14t, sdist) with a smoke-install gate before publish |
