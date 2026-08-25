# Lane: python-layer — PyO3 binding, Python API, agentic frontier loop

<!-- plan-section: lane-status -->

**WIP (agent-python-layer, 2026-08-24).** Strand
[`docs/python-2026-08/`](../../python-2026-08/README.md). Plans 01-03 and the
quality goal (`10-quality-best-practices.md`) are complete on `main`. Q1-Q8
landed: property-based + Rust-side tests + a `ty` ratchet (Q1, which found a
replay that certified an empty assertion stack); the zero-copy audit and
`solve_smtlib_with_model` ending the double solve (Q2); release wheels with a
3.14t build and a smoke-install gate (Q3); the eight open tier-R rows (Q4);
typed stubs from the Rust signatures via pyo3-stub-gen at 96.9%, stubtest and
an `Any` ratchet (Q5); the CAS long tail -- ntheory / combinatorics / stats /
special / transforms / normal forms / moment provers / ansatz / gf / boolean /
algebraic, 179 items tested against sympy as oracle, three disagreements
argued and pinned (Q8, coverage 302 -> 471); panic-surface hardening -- a
probe took reachable panics 3 -> 0 and crashes 19 -> 2, the rest typed at the
boundary (Q7). Plus `axeyum.m` (Mathematica-shaped verbs) and a runnable
`python/examples/gallery.py`. Coverage `tier_r_unreferenced=0`.

Two known follow-ups, both recorded honestly rather than hidden: several
AGENT/knowledge tests hardcode ModEq fact ids that main's fact growth
(358 -> ~700) removed -- a fact-fixture refresh, not a binding bug; and two
deep-`Clone`/`Drop` segfaults in `Expr` need an iterative Clone in
`axeyum-cas`, out of reach of a boundary guard. Next: Q6 (derive
`eq`/`hash`/`str`; make `Config`/`Incremental` `Sync` so `unsendable` and
`gil_used = true` can go), and those two follow-ups.

<!-- plan-section: landed-changes -->

| 2026-08-24 | `219ce5618` | Q7: panic-surface hardening -- a probe over every callable took panics 3->0, crashes 19->2; preflights + one `catch_unwind` (`InternalError`); a hypothesis no-panic property found the solver-dispatch panic the hand battery missed |
| 2026-08-24 | `e0ce70376` | Q8: the CAS long tail (179 items, 941 tests vs sympy oracle, coverage 302->471, three disagreements pinned) + a runnable demo gallery |
| 2026-08-24 | `f11a74c18` | Q5: typed stubs from the Rust signatures via pyo3-stub-gen (96.9% typed), stubtest + `Any` ratchet gates; found three `axeyum.m` type errors |
| 2026-08-24 | `f11a74c18` | Q5: typed stubs via pyo3-stub-gen behind an off-by-default feature (96.9% typed, allowlisted `Any`s with reasons), `stubtest` + `Any` ratchet gates; three `axeyum.m` type errors found and fixed |
| 2026-08-24 | `68f5d61a4` | `axeyum.m`: Mathematica-shaped verbs over the CAS -- parser, variable inference, readable printer; three iterations (equations, assumptions, limits at infinity; systems, definite integrals, Substitute, semantic Equal, mixed int/Fraction arithmetic on `Expr`; Sum, Reduce, Rationalize, NRoots, polynomial toolkit); 19 tests |
| 2026-08-24 | `460bee2db` | Q2: replay of the deciding run's model via `solve_smtlib_with_model` (2.22x on sat), clone audit (12 borrows, 13 `__eq__` via cast), CAS detaches, bytes accessors, benchmarks |
| 2026-08-24 | `d904a5c14` | `axeyum-solver`: `solve_smtlib_with_model` -- the front door returns arena, assertions and model; `solve_smtlib` wraps it; 152-file equality test |
| 2026-08-24 | `68fb060e7` | Q1: 73 hypothesis differentials, 8 Rust unit tests, `ty` ratchet; fixed replay-over-empty-stack on the word-only fallback |
| 2026-08-24 | `a4393ef18` | Q4: the eight open tier-R solver rows as typed ledgers + `get_assertions/get_info/get_option` + `SolveStats`; coverage backlog empty |
| 2026-08-24 | `e0ce50f97` | Q3: release wheels (manylinux 2_28, macOS, Windows, 3.14t, sdist) with a smoke-install gate before publish |
