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

**Frontier reachability (2026-08-25).** Answered "why does the agent attempt
~3 of 146 open facts?" — decomposed into reachability x provability
([`14-frontier-reachability.md`](../../python-2026-08/14-frontier-reachability.md)).
Built `scripts/gen-statement-adapters.py`: generates proof-free Lean statement
adapters from each fact's `formal.statement` so `lean4export` can freeze them
(the only artifact a tier-C producer consumes). Verified end to end on s5
(24 adapters, one `lake env lean` compile, arrow-free ones export to valid
~320KB NDJSON that `import_statement_ndjson` accepts). Measured finding: the
"3" is producer-bound, not export-bound — the refl/symm/trans/comm shapes the
producers close are already proved (498 proved), and every arrow-free *open*
modeq fact is a congruence goal both producers decline. lean4export 3.1.0
silently refuses arrow-bearing statements (exit 1), capping auto-export at
arrow-free shapes. Next: Q6 (derive `eq`/`hash`/`str`; `Config`/`Incremental`
`Sync`); a `ModEq`-unfolding producer to lift the *provability* wall; an
arrow-capable export path.

**Agentic-loop iterations (2026-08-25).** Ran the loop live and improved it
three times: (3) `--skip-unreachable` preflights the frozen export before
spending a model — observed offline over 5 facts, all declined retrieval-miss
after ~26k tokens each because export absence is only found inside the producer
tool, two model rounds in; (4) `--reachable-first` stably reorders `--next`
selection so facts with an export come first (the first 5 eligible had 0); (5)
the mobility summary now names the dominant unevaluable reason, making
`unevaluable=186` legible as a reachability block (`no-frozen-export`), not a
tactic gap. Verified the loop still proves its live frontier (`nat-modeq-symm`,
`nat-modeq-trans`) via `modeq_family`.

<!-- plan-section: landed-changes -->

| 2026-08-25 | `be0c67f67` | mobility summary names the dominant unevaluable reason (`unevaluable_no_export`, `unevaluable_top`), so `unevaluable=186` reads as a reachability block not a tactic gap; regenerates the committed census (191->189) that had drifted stale |
| 2026-08-25 | `e27140275` | `--reachable-first`: stably reorder `--next` selection so facts with a frozen export come first (the first 5 eligible had 0); deterministic, population unchanged |
| 2026-08-25 | `b2813872f` | `--skip-unreachable`: preflight the frozen export before spending a model; skips retrieval-miss-only facts at zero cost (~26k tokens/fact saved), opt-in so replays are unchanged; 3 controls |
| 2026-08-25 | `2a2e863f2` | `gen-statement-adapters.py`: proof-free Lean statement adapters from `formal.statement` to expand frozen-export coverage; `--exportable-only` drops arrow-bearing statements lean4export 3.1.0 refuses; verified end to end on s5; 7 controls |
| 2026-08-25 | `57f3e68b4` `90d6cb5c0` | `14-frontier-reachability.md`: the ~3-of-146 gap decomposed into reachability x provability, measured; finding is the frontier is producer-bound (498 proved, open modeq facts are congruence goals the producers decline) |
| 2026-08-25 | `5c5c2fd04` | fix: a deep `CasExpr` chain raises `BudgetExceeded` (`MAX_EXPR_DEPTH`) instead of segfaulting the process |
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
