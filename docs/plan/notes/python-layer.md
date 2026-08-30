# Notes: python-layer

Detail moved out of [`../status/python-layer.md`](../status/python-layer.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

## Archived landed-changes rows

| 2026-08-24 | `b08986061` | `10-quality-best-practices.md`: sourced practice vs the measured binding; six quality slices |
| 2026-08-24 | `48d7044a2` | Python coverage ledger: 831 of 4,672 public items referenced, 8 tier-R rows open, deferrals with reasons, `09-coverage-plan.md` ordered by consumer value |
| 2026-08-24 | `5b7140d72` | Plan 03 A6: allowlisted metadata fetch with a family-level held-out guard and injection wrapper; cgroup-capped sandboxed `python_exec` with a discriminating self-check; 76 tests |
| 2026-08-24 | `27c601025` | Review fixes: `ReplayUnavailable` and front-door-model replay (P0), forwarding modules for `axeyum.smt/ir/solver` (P1), CI `python` job 3.12-3.14 (P1), nightly clippy green (P1); frontier re-verification opt-in |
| 2026-08-24 | `00a0803f7` | Plan 03 A5: obstruction graph derived from 16 episodes + 11 decline records, 12 clusters / 19 facts, F3 answered both ways; 26 guards |
| 2026-08-24 | `b44cf88da` | Plan 03 A7: mobility census -- three-valued precondition evaluation over every open fact; 4 of 191 evaluable; 4 real catalog reach disagreements reported |
| 2026-08-24 | `2f300656f` | Plan 03 A4: schema v2, deferred checker tools, model-free `Supervise`, independent second-kernel `Check`, holdout gate over episodes; live run proved `Nat.ModEq` refl and symm axiom-free (digests new to the ledger), $1.55; 94 tests |
| 2026-08-24 | `0ba7eaac3` | Frontier agent (plan 03 A2): `[agent]` extra, six read-only partition-filtering tools, `Select -> Gather -> Plan -> WriteEpisode` graph, replay; ten live episodes ($1.635), 8/8 `NoGeneralRoute`; 86 tests |
| 2026-08-24 | `0f64b8951` | Episode schema + fail-closed `check-agent-episode.py` (A1, 15 mutation-verified guards) and tactic catalog v1 with a dispatch-table-rejecting validator (A3, 13 guards) |
| 2026-08-24 | `d27f86f5e` | Producers promoted to `axeyum-lean-import::producers` (byte-identical driver output, committed `proof_sha256` reproduced) and bound as `axeyum.producers` with typed `Declined` reasons; 46 tests |
| 2026-08-24 | `4e56f777a` | `axeyum.cas` (~80 pure functions, `ZeroTest` certificates) and `cas.certify` (groebner, geometry, telescoping, sos, gf2, sturm as producer/certificate/checker triples with report counts; tampered certificates rejected); 350 tests |
| 2026-08-24 | `552c29766` | `axeyum.ir` (epoch-checked `Arena`, full constructor set, trusted `eval`, bv preflight, fp, query) and `axeyum.solver` (`Config`, `CheckResult`, `Incremental`, three-valued `check_outcome`, proofs, cnf); smt sessions; typed `Value` variants; 157 tests |
| 2026-08-24 | `537328b3c` | `axeyum.kernel`: epoch-checked handles, nine preludes with generated field tables, footprints/closures raising on absent names, `add_declaration` with typed `KernelError`, Lean rendering and NDJSON export, identity hashes; 57 tests |
| 2026-08-24 | `df1e7d185` | `axeyum.knowledge`: read-only typed accessors over facts, frontier, operations, overlay, nursery (partition-safe), claims, concepts, pinned `math-education`, autogenesis artifact index; 161 tests mirroring the validators |
| 2026-08-24 | `9dd2dc82a` | Generated native stubs with a drift gate (fails on drift and on zero compared), `just py-check`, conditional `check.sh` step, fleet-hosts `uv` row, Python user guide |
| 2026-08-24 | `a8e8d34a9` | `crates/axeyum-py` binding crate, `axeyum.smt.solve` with `unknown` as a value and `Outcome.replay()`, differential vs `smtcomp_cli`, conftest that fails on zero collected tests |
| 2026-08-24 | `9cfdf86fe` | Python strand: plans 01–03, two measured studies, three API inventories under `docs/python-2026-08/` |

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

## Archived landed-changes rows

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
