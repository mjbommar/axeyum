# Lane: python-layer — PyO3 binding, Python API, agentic frontier loop

<!-- plan-section: lane-status -->

**WIP (agent-python-layer, 2026-08-24).** Strand
[`docs/python-2026-08/`](../../python-2026-08/README.md). Plans 01-03 are
landed on `main` through A7: the binding crate, the seven Python
submodules (1,026 tests), the fail-closed episode checker, the tactic
catalog, the frontier agent, the deferred-approval checker loop that
**closed the loop** (two `Nat.ModEq` facts proved by a model-chosen plan and
re-derived in a second kernel), the obstruction graph (12 clusters / 19
facts; largest removable by an existing capability), and the mobility
census (only 4 of 191 open facts have a frozen export -- the measured
bottleneck). A review's four blockers are fixed: `replay()` never
conflates unavailable with failed and replays the front door's OWN model;
documented submodule imports resolve; a CI Python job on 3.12-3.14; the S1
clippy gate is green on nightly as well as stable. Open for a human: register
an operation for the `Nat.ModEq` family so the two proofs can land in the
ledger; the s5 export step; four real tactic-catalog reach disagreements
(preconditions narrower than their accepted rows); joining the two
obstruction populations (F3).

<!-- plan-section: landed-changes -->

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
