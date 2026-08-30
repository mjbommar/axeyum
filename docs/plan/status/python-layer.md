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

Both prior follow-ups are now closed: the AGENT/knowledge fact-fixture drift
was refreshed (targets moved to `nat-modeq-symm/trans` and a nursery-derived
mobility count), and the deep-`Clone`/`Drop` segfault is guarded at the
boundary by a `MAX_EXPR_DEPTH` iterative-depth check that raises
`BudgetExceeded` (an iterative Clone in `axeyum-cas` remains the deeper fix).

Detail and older landed rows moved to [`../notes/python-layer.md`](../notes/python-layer.md).

<!-- plan-section: landed-changes -->

| 2026-08-25 | `be0c67f67` | mobility summary names the dominant unevaluable reason (`unevaluable_no_export`, `unevaluable_top`), so `unevaluable=186` reads as a reachability block not a tactic gap; regenerates the committed census (191->189) that had drifted stale |
| 2026-08-25 | `e27140275` | `--reachable-first`: stably reorder `--next` selection so facts with a frozen export come first (the first 5 eligible had 0); deterministic, population unchanged |
| 2026-08-25 | `b2813872f` | `--skip-unreachable`: preflight the frozen export before spending a model; skips retrieval-miss-only facts at zero cost (~26k tokens/fact saved), opt-in so replays are unchanged; 3 controls |
| 2026-08-25 | `2a2e863f2` | `gen-statement-adapters.py`: proof-free Lean statement adapters from `formal.statement` to expand frozen-export coverage; `--exportable-only` drops arrow-bearing statements lean4export 3.1.0 refuses; verified end to end on s5; 7 controls |
