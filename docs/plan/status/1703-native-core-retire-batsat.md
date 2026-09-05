# Lane: native-core-retire-batsat — retire BatSat; the native CDCL core is the SAT engine

<!-- plan-section: lane-status -->

**Slice 1 of ADR-1703 landed (`WIP`, native-core-retire-batsat, 2026-09-05).**
The in-tree native CDCL core is now the SAT engine on every Axeyum path, and
`rustsat-batsat` is a non-default `batsat-reference` cargo feature used only as
a differential oracle — the role ADR-0002 gives Z3. The default dependency graph
of `axeyum-cnf` contains no `batsat`, `rustsat`, or `rustsat-batsat`; measured
with a positive control, `cargo tree -e normal -p axeyum-cnf` is 5 lines
(`axeyum-aig`, `rustix`) and the same command with `-F batsat-reference` lists
all three.

What unblocked the flip: the native core had no incremental interface, so the
warm path (`IncrementalSat` / `IncrementalCnf`, and through them the LIA DPLL(T)
driver and the warm BV engine) was BatSat-only. `NativeIncrementalCdcl` in
`proof_sat::incremental` supplies it — clauses added between solves, assumptions
per solve, retained learned clauses / VSIDS / phases, a failed-assumption core,
and optional DRAT recording that is off on the warm path.

**Assurance:** the "proofless BatSat UNSAT is lower assurance" boundary in the
trust ledger disappears rather than moves. Every native `unsat` derives the empty
clause from RUP-learned clauses, so a DRAT proof exists by construction. Two
limits are recorded rather than smoothed over: warm-path recording is off by
default (so a warm `unsat` is still stamped `Unchecked` unless asked for), and an
`unsat` under assumptions carries a failed-assumption core, not a refutation.

**Behaviour changes, both deliberate and documented.** The deterministic budget
unit is now the core's *conflicts*, not the adapter's private `within_budget`
polls; the parameter position is unchanged. And `resource_limit = 0` now admits
no search at all rather than "0 conflicts", preserving the "encode but do not
solve" contract the rest of the tree relies on — that one was found by the full
solver unit sweep, not by the targeted per-file runs.

**Next (slice 2):** delete `crates/axeyum-cnf/src/batsat_reference.rs`, the
`batsat-reference` features in `axeyum-cnf` / `axeyum-solver` / `axeyum-bench`,
the three dependencies, and the ~70 historical documentation references. Not
before the native core has carried a full public-corpus run under the new
default.

<!-- plan-section: landed-changes -->

| 2026-09-05 | `317be80fe` | ADR-1703: the native CDCL core is the SAT engine; BatSat is demoted to a non-default `batsat-reference` differential oracle, scheduled for removal in slice 2. |
| 2026-09-05 | `560d781ea` | `NativeIncrementalCdcl`: persistent, assumption-capable native core (add clauses between solves, `analyze_final` cores, retained learned clauses, optional DRAT). `Cdcl` owns its sink; `num_original` becomes a per-clause `learned` flag so an input clause added after learning can never become a `reduce_db` deletion candidate. |
| 2026-09-05 | `f019d503f` | `IncrementalSat` re-based on the native core with its surface unchanged; the adapter moved whole to `batsat_reference.rs` behind a non-default feature; `SatBvBackend` dispatches to the native core unconditionally and `SolverConfig::native_cdcl` becomes a documented no-op; `native_vs_batsat_differential.rs` added (3 tests with the feature, 0 without). |
| 2026-09-05 | `6240f013e` | A zero conflict budget admits no search (restoring the `resource_limit = 0` contract), and `classify_sat_unknown` recognises the native core's budget wording — both caught by the full `-p axeyum-solver --lib --features full` sweep. |
| 2026-09-05 | `9833fadb5` | ADR-1703 cites the gate (b) measurement, run for the first time since ADR-0012 deferred to it: the native core is never worse than BatSat and sometimes better (p4dfa 6 vs 4 decided; Noetzli sample tied), with zero cross-engine disagreements. |
