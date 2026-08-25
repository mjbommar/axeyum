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
