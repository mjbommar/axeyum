# Foundation counters: `axeyum-egraph`, `axeyum-rewrite`, `axeyum-smtlib` — 2026-09-07

Lane `foundation-counters`. The bottom of the stack had a real gap: a survey
just before this lane started counted 10 counter/stats types in `axeyum-cnf`,
9 in `axeyum-solver`, 3 in `axeyum-bv`, 1 in `axeyum-ir`, 1 in `axeyum-aig`,
and **zero** in `axeyum-egraph`, `axeyum-rewrite`, and `axeyum-smtlib`. Those
three crates sit under every division: congruence closure, the preprocessing
passes every query pays before a theory solver sees it, and SMT-LIB ingest.

Two measured facts framed the work:

- Congruence closure (`axeyum-egraph`) is superlinear, and a sibling lane
  found the cause — `process_pending`'s declaration-set clone/sort/dedup, not
  the proof-forest walk reading the code suggests — was **72x at N=51,200**,
  found by adding one diagnostic counter rather than by reading.
- Parsing (`axeyum-smtlib`) is 29–60% of ingest and its share tracks file
  **shape**, not size (`bench-primitives-2026-09-07.md`, Findings 2–3). The
  in-tree "58 MB takes ~54 s" figure is ~30x pessimistic against four
  committed files up to 10.5 MB (30–58 MB/s, roughly linear), and the
  discrepancy was left open because the 58 MB file is not in the tree.

## What each crate now counts

### `axeyum-egraph` — `EGraphCounters`

Opt-in via `EGraph::set_counting(bool)` (a plain `bool` field checked at
every increment site, same convention as `axeyum_cnf::SearchCounters`'s
`count_search`), read with `EGraph::counters() -> EGraphCounters`, zeroed
with `EGraph::reset_counters()`. Fields:

- `merge_calls`, `unions`, `redundant_pending` — how much of
  `process_pending`'s worklist was real union-find work versus
  already-equal no-ops.
- `congruence_pending` — pairs enqueued by a post-union signature collision
  (the actual congruence cascade, as opposed to the caller's own asserted
  equalities).
- `finds`, `find_steps` — `find` calls and the union-by-size parent-pointer
  hops they walk (no path compression here, by design, for O(1) undo).
- `declaration_elems_copied`, `declaration_elems_merged`,
  `declaration_dedup_calls`, `max_class_size` — direct visibility into the
  hot spot the sibling lane found: `declaration_elems_copied` is what
  `child_declarations.clone()` pays on every single union regardless of
  outcome, `declaration_elems_merged`/`declaration_dedup_calls` isolate the
  branch that actually resorts and dedups, and `max_class_size` is the
  growth number that predicts how expensive that clone gets.
- `explain_calls`, `explain_steps` — `explain`/`explain_steps` are `&self`
  on purpose (read-only proof-forest walks), so these two live in `Cell<u64>`
  rather than the `&mut self`-side struct; `EGraph::counters()` merges both
  halves into one snapshot.
- `proof_reroot_steps` — the field a prior lane (bench-theories,
  2026-09-07) already added, unconditionally. It had no reader anywhere in
  the tree (checked: zero references outside its own definition/increment/
  accessor) — a counter nothing reads is exactly the "looks like coverage but
  isn't" case the brief warned about. Left unconditional (its existing
  contract), but folded into `EGraphCounters` and now exercised by a test.

**What reads it:** four new unit tests in `crates/axeyum-egraph/src/lib.rs`
(`counters_report_merge_find_and_explain_work`,
`counting_does_not_change_congruence_outcomes`,
`counters_stay_zero_when_counting_is_off`,
`reset_counters_zeroes_gated_fields_only`). No `--trace`-style CLI channel
exists for this crate (it has no binary front door of its own — consumers go
through `axeyum-solver`'s `euf_egraph.rs`), so wiring stops at the crate's own
test suite; the next hop would be exposing `EGraph::counters()` through
`axeyum-solver`'s theory-layer diagnostics, left undone (see below).

### `axeyum-rewrite` — `PassSize` / `PassSizeDelta` / `rule_application_counts`

Each of the five hot passes (`canonicalize_terms`, `eliminate_arrays`,
`eliminate_functions`, `eliminate_int_divmod`, `blast_integers`) already
returns a result type richer than a bare `Vec<TermId>` (ADR-1721/1730) with
its own eliminated-construct and added-constraint counts
(`ArrayElimination::selects`, `FunctionElimination::applications`,
`IntDivModElimination::replacements`/`added_constraints`,
`IntBlasting::restricting_constraints`). This does **not** duplicate any of
that — it adds the one thing none of them reports: the shared
`axeyum_ir::TermStats` term-size footprint before and after.

New module `pass_stats`:

- `PassSize { dag_nodes, tree_nodes, max_depth }` — a projection of
  `TermStats` (already exists in `axeyum-ir`; this module is a thin
  before/after wrapper around it, not a new metric engine).
- `PassSizeDelta { before, after }` plus `dag_node_delta()`.
- One `_with_stats` wrapper per pass (`canonicalize_terms_with_stats`,
  `eliminate_arrays_with_stats`, `eliminate_functions_with_stats`,
  `eliminate_int_divmod_with_stats`, `blast_integers_with_stats`) that calls
  `TermStats::compute` once on the input roots, calls the real pass, and
  once on the output roots.
- `rule_application_counts(&RewriteReport) -> Vec<(RewriteRuleId, u64)>` — a
  deterministic (`BTreeMap`, not discovery-order) per-rule summary of
  `RewriteReport::applications`, which already carries the full log this
  derives from.

**Opt-in means "a separate function", not a runtime flag.** The five
unwrapped entry points are untouched — not one line inside them changed — so
every existing caller pays exactly what it always paid. This is a stronger
guarantee than a boolean gate: it is not merely cheap when off, it is
*absent* when unused.

**What reads it:** four new unit tests in
`crates/axeyum-rewrite/src/pass_stats.rs`. Two assert the wrapper's output is
byte-identical to the unwrapped call (`assert_eq!` on `CanonicalizeTermsOutcome`
and on `.assertions()` slices). Two exercise real shrinkage
(`x = x` canonicalizes to `true`) and real growth (`div`/`mod` linearization,
array Ackermann select-consistency). `rule_application_counts` has its own
test checking the per-rule sum equals the report's total and that the
ordering is already sorted (not incidentally so).

### `axeyum-smtlib` — `ingest_stats` (`IngestStatsGuard` / `IngestStats`)

New module, same convention as `axeyum_solver::smtlib`'s
`FrontDoorStatsGuard` / `cdclt::TheoryLayerStatsGuard` /
`layers::BvLayerStatsGuard`: a thread-local `Cell<bool>` flag, a guard that
flips it and zeroes the accumulators for its lifetime, and a free function
(`last_ingest_stats()`) to read the snapshot. Every increment site is
self-gated (checks `collecting()` internally, so call sites in
`sexpr::read_all`'s hot loop stay one-liners) rather than requiring the
caller to wrap each call — a deliberate deviation from the "if
self.count_search" inline-gate style, made to keep `read_all` under
clippy's `too_many_lines` (it still needed one
`#[allow(clippy::too_many_lines)]`, noted in the source as caused by the
hooks, not new branching).

Counted:

- `atoms`, `lists` — every `SExpr::Atom`/`SExpr::List` the tokenizer emits
  (one gate point, inside the `emit` closure, covers all four emit call
  sites).
- `max_sexpr_depth` — deepest open-paren nesting seen.
- `top_level_forms` — top-level s-expressions `read_all` returns.
- `assertions`, `symbols_declared`, `sorts_declared` — read off the finished
  `Script`/`TermArena` at the end of `parse_script_bounded_inner`
  (`script.assertions.len()`, `script.arena.symbols().count()`,
  `script.arena.uninterpreted_sort_ids().count()`), gated on `collecting()`
  at the call site too (not just inside the record function) because the two
  `.count()` calls are themselves `O(n)` and must not run unconditionally.

**What reads it:** three new unit tests in `ingest_stats.rs`
(`enabling_ingest_stats_counts_real_parse_work`,
`counting_off_leaves_ingest_stats_untouched_by_parsing`,
`counting_does_not_change_parse_output`), and the new example
`crates/axeyum-smtlib/examples/ingest_shape_probe.rs` (below) — a genuine
consumer, not a test double.

## What a counter revealed that reading the code did not

`EGraph::proof_reroot_steps` — a real, already-shipped counter — had **zero
readers** anywhere in the tree outside its own definition, increment site,
and accessor. `grep -rn "proof_reroot_steps"` across `crates/` and `docs/`
returns only the four lines inside `axeyum-egraph/src/lib.rs` itself. This is
exactly the failure mode the brief warns about ("a counter nothing can read
is worse than no counter, because it looks like coverage") — it had landed
with a doc comment and an accessor but no test, no example, no `--trace`
line. This lane added the missing reader (a test asserting it matches the
snapshot) rather than leaving it as a second orphaned counter.

## The ingest-throughput discrepancy: bounded, not settled

`examples/ingest_shape_probe.rs` builds three synthetic shapes — flat
declarations, a ~65k-entry symbol table, and `bvnot` nesting to nine
depths from 1,000 to 1,000,000 — all at a few MB, and reports `parse_script`
throughput plus the new `IngestStats` for each. Measured on this host
(release build):

| shape | bytes | MB/s | notes |
|---|---:|---:|---|
| flat declarations | 4.19 M | ~21 | committed-corpus shape |
| huge symbol table (~65k symbols) | 4.19 M | ~78 | |
| `bvnot` nesting, depth 1k | 8.1 K | ~37 | |
| `bvnot` nesting, depth 10k | 80 K | ~37 | |
| `bvnot` nesting, depth 100k | 800 K | ~23 | |
| `bvnot` nesting, depth 1M | 8.0 M | ~13.5 | |

None of the three shapes reproduces anything near the ~1.1 MB/s the in-tree
"58 MB / ~54 s" figure implies — the slowest measured case here is ~13.5
MB/s, still an order of magnitude faster. Deep nesting shows genuine
super-linear cost (100k→1M is 10x the bytes but ~17x the wall time — some
routine in the pipeline is worse than linear in nesting depth, though the
tokenizer itself stayed iterative and did not overflow the stack even at
depth 1,000,000), but even extrapolating that trend, matching 1.1 MB/s would
need nesting far beyond what any committed or plausible benchmark file
contains.

**Conclusion: bounded, not settled.** The "file shape is the cost" hypothesis
from `bench-primitives-2026-09-07.md` is weakened by this — three shape
candidates tested up to 8 MB all parse well above 1.1 MB/s — which makes the
other two named possibilities (a stale figure, or "reading" in the original
sentence covering more than `parse_script`, e.g. the string-route semantic
phases documented elsewhere at 21–22 s each on a 1.1 MB file) comparatively
more likely. This is recorded as a bound, not a correction: the actual 58 MB
file is still not in the tree, a shape this probe did not try (e.g. extreme
*sharing* — a DAG that unfolds into an astronomical tree, which
`axeyum_ir::TermStats::tree_nodes` exists precisely to detect) is not ruled
out, and the doc comments in `lib.rs`/`parse.rs` were annotated with this
evidence rather than having their number silently changed.

## No-verdict-change / no-default-cost checks

- `axeyum-egraph`: `tests::counting_does_not_change_congruence_outcomes`
  builds the same merge/explain sequence with counting on and off and
  asserts byte-identical `equal`/`explain`/`explain_steps` answers.
- `axeyum-rewrite`: each `_with_stats` test asserts the wrapped pass's own
  output (`CanonicalizeTermsOutcome`, or `.assertions()`) is `assert_eq!` to
  the unwrapped call over the same input.
- `axeyum-smtlib`: `ingest_stats::tests::counting_does_not_change_parse_output`
  compares assertion count, `check_sats`, `logic`, and the full
  `write_script` text between a counted and uncounted parse of the same
  script.
- No clock was added to any default path in any of the three crates. Every
  new field is either gated behind an explicit opt-in (`set_counting`,
  `IngestStatsGuard::enable()`) or reached only through a separate,
  never-called-by-default function (`*_with_stats`).

## SHAs

- `9b9b6149e` — `feat(egraph): opt-in EGraphCounters for merge/find/process_pending/explain`
- `dbc901288` — `feat(rewrite): opt-in term-size before/after for the five hot passes`
- (this doc + `axeyum-smtlib` counters land in the commits that follow; see
  `docs/plan/status/foundation-counters.md` for the final SHA list)

## Left undone

- `EGraph::counters()` is not yet wired into `axeyum-solver`'s
  `euf_egraph.rs` or the `--trace` channel `smtcomp_cli` composes
  (`FrontDoorStatsGuard`/`BvLayerStatsGuard`/`TheoryLayerStatsGuard`). That
  would be the natural next hop — the EUF theory owns the live `EGraph`
  instance during a real solve — but touching `axeyum-solver` was out of
  this lane's declared scope and risk budget (968+ unit tests, the crate
  every other lane also depends on).
- The 58 MB ingest-throughput figure is bounded, not settled (see above); the
  file itself was not obtained.
- `axeyum-rewrite`'s `_with_stats` wrappers are not wired into any solver
  front door either — they are a library-level diagnostic API, reachable
  today only from a test or a caller that imports them directly.
- `sort/symbol table **growth**` (a trajectory over the parse, not just the
  final size) was scoped down to final-size counters
  (`symbols_declared`/`sorts_declared`) — a true growth curve would need
  either periodic sampling or a resize hook inside `TermArena` itself,
  which is out of `axeyum-smtlib`'s crate boundary.
