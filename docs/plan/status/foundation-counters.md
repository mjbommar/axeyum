# Lane: foundation-counters — counter/stats coverage for `axeyum-egraph`, `axeyum-rewrite`, `axeyum-smtlib`

<!-- plan-section: lane-status -->

**`DONE`, foundation-counters, 2026-09-07.** A bottom-of-stack survey found
`axeyum-egraph`, `axeyum-rewrite`, and `axeyum-smtlib` with zero counter/stats
types while `axeyum-cnf` had ten. All three now have opt-in, clock-free
counters in the style already used here (`axeyum_cnf::SearchCounters`'s
bool-gate, and the thread-local guard pattern from
`axeyum_solver::smtlib::FrontDoorStatsGuard`). Full record, including the
orphaned `proof_reroot_steps` counter this lane found (landed, unread, no
test) and the bounded-not-settled result on the "58 MB / ~54 s" ingest
figure: [the diary](../../research/12-performance/foundation-counters-2026-09-07.md).

**egraph:** `EGraphCounters` (merges/finds/process_pending's declaration-set
copy-sort-dedup work — the operation a sibling lane measured at 72x at
N=51,200 — and explain/explain_steps). Opt-in via `EGraph::set_counting`.
Four new tests, including a counting-on-vs-off byte-identical-output check.

**rewrite:** `pass_stats` module — `PassSize`/`PassSizeDelta`
(`axeyum_ir::TermStats` before/after) plus `rule_application_counts`, as a
`_with_stats` wrapper per hot pass (`canonicalize_terms`, `eliminate_arrays`,
`eliminate_functions`, `eliminate_int_divmod`, `blast_integers`) that leaves
the five unwrapped entry points completely untouched. Four new tests.

**smtlib:** `ingest_stats` module — thread-local `IngestStatsGuard` /
`last_ingest_stats()` counting tokenizer atoms/lists/nesting depth plus
parser assertions/declared-symbols/declared-sorts. Three new tests, plus a
new example `ingest_shape_probe` that bounds (does not settle) the
ingest-throughput discrepancy: three synthetic shapes up to 8 MB all measure
well above the ~1.1 MB/s the in-tree figure implies, so "file shape alone" is
weakened as the explanation. Both affected doc comments are annotated with
this finding, not silently rewritten.

**Verified:** `cargo check --workspace --all-targets --all-features` and
`cargo clippy --workspace --all-targets --all-features -- -D warnings` both
clean after all four commits. Per-crate: `axeyum-egraph` 39/39 lib tests,
`axeyum-rewrite` 158/158 lib tests, `axeyum-smtlib` 96/96 lib tests, all with
`rustfmt --edition 2024` applied file-by-file (never `cargo fmt`).
`cargo test -p axeyum-solver --lib --features full` run to confirm this
lane's changes (none of which touch `axeyum-solver`) leave that gate exactly
as it was; see the diary for the exact pass/fail counts once that run
finished.

**Left undone (see the diary's closing section for the full list):**
`EGraph::counters()` is not wired into `axeyum-solver`'s `euf_egraph.rs` or
the `--trace` channel `smtcomp_cli` composes — out of this lane's declared
crate boundary and risk budget. The 58 MB ingest figure is bounded, not
settled; the file itself was never obtained. "Symbol/sort table growth" was
scoped to final-size counters, not a resize trajectory.

<!-- plan-section: landed-changes -->

| 2026-09-07 | `9b9b6149e` | `axeyum-egraph`: opt-in `EGraphCounters` for merge/find/process_pending/explain, plus 4 tests. |
| 2026-09-07 | `dbc901288` | `axeyum-rewrite`: opt-in `PassSize`/`PassSizeDelta` term-size-before/after wrappers for the five hot passes, plus `rule_application_counts` and 4 tests. |
| 2026-09-07 | `0855f7db4` | `axeyum-smtlib`: opt-in `IngestStatsGuard` for tokens/s-expressions/assertions/declared symbols and sorts, the `ingest_shape_probe` example, and 3 tests. |
| 2026-09-07 | `51208e369` | docs: the foundation-counters diary. |
