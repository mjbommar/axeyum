# Lane: python-layer — PyO3 binding, Python API, agentic frontier loop

<!-- plan-section: lane-status -->

**WIP (agent-python-layer, 2026-08-24).** Strand
[`docs/python-2026-08/`](../../python-2026-08/README.md). Plans 01 and 02
are landed on `main`: `crates/axeyum-py` -> `axeyum._native` (PyO3 0.29.2,
abi3-py312, no libpython link) with `smt`, `ir`, `solver` (+ `proofs`,
`cnf`), `cas` + `cas.certify` (six producer/certificate/checker routes),
`kernel` (epoch-checked handles, nine preludes), `producers` (promoted from
`examples/` to `axeyum-lean-import::producers`, driver output byte-identical
on the frozen exports), and `knowledge` (validator-mirroring read-only
accessors over every knowledge artifact). Worktree gate at `d27f86f5e`:
clippy 0 warnings, pytest **796 passed / 11 skipped**, stubs `compared=7`,
autogenesis validators OK. Plan 03 in flight: A1 (episode schema +
fail-closed checker with mutation controls) and A3 (tactic catalog v1 whose
validator fails when every entry matches one shape). Next: A2 -- the
`[agent]` extra, six read-only tools, the four-node graph, ten committed
episodes over the 104 open dependency-ready non-held-out facts. Integration
rule learned today: the shared checkout sits on a branch far behind `main`;
tracked-file edits move as three-way merges (`git merge-file`), Rust slices
are verified in `lane-snapshot.sh` trees, commits come from the detached
worktree.

<!-- plan-section: landed-changes -->

| 2026-08-24 | `d27f86f5e` | Producers promoted to `axeyum-lean-import::producers` (byte-identical driver output, committed `proof_sha256` reproduced) and bound as `axeyum.producers` with typed `Declined` reasons; 46 tests |
| 2026-08-24 | `4e56f777a` | `axeyum.cas` (~80 pure functions, `ZeroTest` certificates) and `cas.certify` (groebner, geometry, telescoping, sos, gf2, sturm as producer/certificate/checker triples with report counts; tampered certificates rejected); 350 tests |
| 2026-08-24 | `552c29766` | `axeyum.ir` (epoch-checked `Arena`, full constructor set, trusted `eval`, bv preflight, fp, query) and `axeyum.solver` (`Config`, `CheckResult`, `Incremental`, three-valued `check_outcome`, proofs, cnf); smt sessions; typed `Value` variants; 157 tests |
| 2026-08-24 | `537328b3c` | `axeyum.kernel`: epoch-checked handles, nine preludes with generated field tables, footprints/closures raising on absent names, `add_declaration` with typed `KernelError`, Lean rendering and NDJSON export, identity hashes; 57 tests |
| 2026-08-24 | `df1e7d185` | `axeyum.knowledge`: read-only typed accessors over facts, frontier, operations, overlay, nursery (partition-safe), claims, concepts, pinned `math-education`, autogenesis artifact index; 161 tests mirroring the validators |
| 2026-08-24 | `9dd2dc82a` | Generated native stubs with a drift gate (fails on drift and on zero compared), `just py-check`, conditional `check.sh` step, fleet-hosts `uv` row, Python user guide |
| 2026-08-24 | `a8e8d34a9` | `crates/axeyum-py` binding crate, `axeyum.smt.solve` with `unknown` as a value and `Outcome.replay()`, differential vs `smtcomp_cli`, conftest that fails on zero collected tests |
| 2026-08-24 | `9cfdf86fe` | Python strand: plans 01–03, two measured studies, three API inventories under `docs/python-2026-08/` |
