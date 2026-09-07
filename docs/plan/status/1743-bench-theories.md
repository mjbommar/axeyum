# Lane: bench-theories — criterion benches and hot-path diagnosis for the theory solvers

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, bench-theories, 2026-09-07).** Scope: simplex,
congruence closure, difference logic, the int-blast width ladder,
`eliminate_arrays`, `eliminate_int_divmod` — see the brief and
[docs/research/12-performance/bench-theories-2026-09-07.md](../../research/12-performance/bench-theories-2026-09-07.md)
for the running diary (expectations, results, and where the proxy fixtures
were wrong).

Four new criterion benches landed for the four previously-unbenched routes
named in the brief: `eliminate_arrays`, `eliminate_int_divmod`,
`int_blast_ladder` (all in `crates/axeyum-rewrite/benches/`), and
`dl_negative_cycle` (`crates/axeyum-solver/benches/`, `required-features =
["full"]`). All four build and run clean on s6.

**Headline finding**: congruence closure's superlinear merge-chain cost
(measured ~475x time for 64x chain length) is NOT the proof-forest re-root
walk I first suspected — a new `EGraph::proof_reroot_steps` diagnostic
counter shows that walk is exactly linear. The real cost is
`process_pending`'s `class_declarations` handling: a full clone + full
`sort_unstable` + `dedup` of the merged class's declaration list on every
union that introduces a new declaration, `O(k log k)` per merge with `k`
growing to `N`. A targeted A/B (same chain, same merge count, declarations
kept flat instead of growing) is 72x faster at N=51,200. Not fixed in this
lane — flagged for a follow-up slice. Also found: `blast_integers`'s per-rung
cost is width-invariant (8/16/32/64 all ~41-42 us), so the width ladder's
cost is dominated by rung *count*, not rung width; and this repo's corpus has
no `QF_IDL`/`QF_RDL` file at all and no `QF_ABV` file anywhere near the
read-count scale the array-elimination quadratic bench probes, so neither new
headline bench could be validated against a real corpus file (recorded
explicitly as "did not run", not silently skipped).

Full detail, all numbers, and what was NOT verified (rung counts on a real
`QF_NIA` file; DL front-door vs. engine cost split; a fix for the
`class_declarations` defect) are in the diary linked above.

Gates run and green: `cargo fmt --all --check`; `clippy -D warnings` on
`axeyum-egraph`, `axeyum-rewrite` (`--all-targets --all-features`) and
`axeyum-solver` (`--all-targets --all-features`, exercises the `z3` feature
too); `cargo test -p axeyum-egraph` (35 passed); the three mandatory z3
differential fuzzes (`qf_lra_differential_fuzz` 5 passed,
`simplex_lra_fallback_differential` 1 passed, `qf_uflra_differential_fuzz` 1
passed — all nonzero). Did not run the full `scripts/check.sh`/`just check`
aggregate gate (out of budget); no solver *logic* was changed (only new bench
files, `Cargo.toml` bench registrations, and one diagnostic-only counter in
`axeyum-egraph` with no behavior change, confirmed by the unchanged 35/35
`axeyum-egraph` test pass).

<!-- plan-section: landed-changes -->

| 2026-09-07 | bench-theories | four new criterion benches for the uncovered theory-preprocessing/DL routes; `EGraph::proof_reroot_steps` diagnostic counter; diary with the `class_declarations` quadratic-resort finding (congruence closure) and the width-invariant int-blast-ladder finding |
