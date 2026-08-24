# Lane: python-layer — PyO3 binding, Python API, agentic frontier loop

<!-- plan-section: lane-status -->

**WIP (agent-python-layer, 2026-08-24).** Strand
[`docs/python-2026-08/`](../../python-2026-08/README.md). Plans 01 and 02
are landed on `main` (`smt`, `ir`, `solver`, `cas`/`certify`, `kernel`,
`producers`, `knowledge`; 796 tests). Plan 03: A1 (episode schema +
fail-closed checker, 15 guards each killing one test), A3 (tactic catalog
v1, 9 tactics / 9 precondition shapes / 31 sourced reach rows, validator
fails on a one-shape catalog) and A2 (the frontier agent: six
partition-filtering read-only tools, a dispatch-free `pydantic-graph`
loop, replay with model requests disabled) are landed. **Measured
baseline:** ten live Sonnet-4.5 episodes, $1.635, `checked=12|ok=12`, and
8 of 8 completed plans emitted `NoGeneralRoute` -- the model never claimed
a general route over the current catalog. Next: A4 -- schema v2
(`checker_runs[]`, `ledger_sha256`), the two checker tools behind
`requires_approval`, `Gate`/`Dispatch`/`Check` nodes, and the first
autonomously planned, kernel-checked theorem; then A5 (typed declines to
the AG4.1 taxonomy) and A7 (the mobility census over all open facts).

<!-- plan-section: landed-changes -->

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
