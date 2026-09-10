# Front end, term IR, and the rewriting / preprocessing pipeline — inventory (2026-09-09)

Everything that happens to a problem before a theory solver sees it: the SMT-LIB
reader and sharing-preserving writer (`crates/axeyum-smtlib/`, minus `regex.rs` /
`regex_membership.rs`, which belong to
[07-strings-and-regex.md](07-strings-and-regex.md)); the typed term IR, arena,
ground evaluator, budget/stop primitives and numeric tower (`crates/axeyum-ir/`);
the query object and its planner (`crates/axeyum-query/`); all sixteen files of
`crates/axeyum-rewrite/`; and the solver-side preprocessing entry points
`preprocess.rs`, `bool_simplify.rs`, `term_walk.rs`, `term_identity.rs`.
Dispatch beyond those four files is
[03-dispatch-routing-and-backends.md](03-dispatch-routing-and-backends.md).
Base commit `ea8515407`. Source-read only; nothing here was confirmed by a build.


> **Superseded in part, 2026-09-09.** This file is a snapshot of the tree at
> `ea8515407`. Since then ADR-1811 landed and there is now ONE word-level
> preprocessing pipeline: `preprocess::reduce_to_fixpoint` +
> `replay_preprocessed_model`. `auto::preprocess_reduce` and
> `dispatch_reduced`'s model-building block are DELETED, so every table row and
> diagram below naming `preprocess_reduce` describes history, not the current
> tree. The front door still runs at round cap 1. See
> [ADR-1811](../research/09-decisions/adr-1811-one-preprocessing-pipeline.md).

## Summary

- **The default `check_sat` preprocessing pipeline is five steps and runs
  exactly once**, not to a fixpoint: `canonicalize_terms` → `propagate_values` →
  `solve_eqs_bounded` → `elim_unconstrained` → `canonicalize_terms`, in
  `auto::preprocess_reduce` (`crates/axeyum-solver/src/auto.rs:2158-2199`),
  gated on `config.preprocess && !has_quantifier` (`auto.rs:1760`).
- **A second, near-identical pipeline exists and iterates up to 8 rounds**:
  `preprocess::check_with_preprocessing`
  (`crates/axeyum-solver/src/preprocess.rs:65-136`, `MAX_PREPROCESS_ROUNDS = 8`
  at `preprocess.rs:32`). It is *not* what the SMT-LIB front door uses. Its only
  non-test in-tree caller is an array-route local-search probe
  (`crates/axeyum-solver/src/abv.rs:3242`). Two implementations of the same
  five-step reduction, with different fixpoint behaviour, is the largest
  structural finding in this area.
- **The default pipeline is guarded by an encoding-size check that can discard
  the whole reduction.** `reduction_shrinks_encoding` (`auto.rs:2233-2264`)
  bit-lowers *both* the original and the reduced query and keeps the reduction
  only if the AIG did not grow; measured counter-examples are tabulated in that
  doc comment (`062-bench_2195`: term DAG 1375 → 1215 while AIG 35 329 → 51 724).
- **The parser is the first preprocessing stage, not a parser.** `Script` has 37
  public fields (`crates/axeyum-smtlib/src/parse.rs:104-356`); at least
  seventeen are source-level analysis products (word skeletons, membership and
  lex problems, length abstractions), and two are *verdicts decided at parse
  time* — `source_string_semantic_unsat` and `source_fp_prefix_monotonic_unsat`,
  the latter returned before `solve` is ever called
  (`crates/axeyum-solver/src/smtlib.rs:2222-2225`).
- **The parser rejects unknown commands rather than ignoring them**
  (`parse.rs:6297`, `SmtError::Unsupported`). The silent-omission cases it does
  have are narrow and listed under *Parser surface* below; the sharpest is
  `set-option`, which the one-shot front door records and never reads.
- Reachability tally for this area (details per table): **WIRED 41**,
  **TEST-ONLY 9**, **NO CALLER FOUND 4**, **FEATURE-GATED 0** at the crate
  level — none of the four crates in scope declares a single cargo feature.
  The whole *solver-side* half (`preprocess.rs`, `auto.rs`, `smtlib.rs`,
  `bool_simplify.rs`, `term_identity.rs`, `term_walk.rs`) is behind
  `axeyum-solver/full`, since `axeyum-smtlib` is an optional dependency.
- **`axeyum-query` is off the shipping path.** `Query` reaches a backend only
  through `SolverBackend::check_query` (`backend.rs:675`), and every caller of
  that method is a test, a bench example, `axeyum-scenarios`, or `axeyum-py`.
  The SMT-LIB front door builds a private `SmtLibSingleQuery`
  (`smtlib.rs:1440`) and calls `solve(arena, &assertions, config)` directly.
- **`pass_stats.rs` (345 lines, 7 public functions) has no caller anywhere
  outside its own `#[cfg(test)]` module.** So do `default_inverters`,
  `alpha_equivalent_to_negation`, and five `budget.rs` types.
- The rewrite manifest is real and enforced at two tiers, but every one of its
  59 shipped rules is `Preservation::Denotation` + `ModelProjection::Identity`
  (`canonical.rs:847-861`), so the manifest's interesting validation arms —
  the ones about equisatisfiable rules — are exercised only by unit tests.
- Model reconstruction is split across three unrelated mechanisms:
  `ModelReconstructionTrail` (the three word-level passes),
  `*::project_model` (arrays, functions), and `IntBlasting::integer_model`.
  No pass in the crate changes models without one of the three or a documented
  reason it needs none — see *Preservation and model routes*.

## The default preprocessing pipeline, in order

Traced from the text front door down. `[full]` marks a step that exists only
under `axeyum-solver/full`.

| # | Step | Function | Site |
|---|---|---|---|
| 0 | Tokenize + read s-expressions (iterative, no recursion) | `sexpr::read_all` | `axeyum-smtlib/src/sexpr.rs:138` |
| 1 | Parse to typed IR; build `Script` (37 fields) under a wall-clock deadline | `parse_script_with_string_bound_within` | `axeyum-solver/src/smtlib.rs:2171` |
| 2 | Source-level word-only fallback, if the bounded encoder declined at parse | `decide_word_only` | `smtlib.rs:2217-2221` |
| 3 | Source FP prefix-monotonic refutation — **a verdict before any solve** | `source_fp_prefix_monotonic_result` | `smtlib.rs:2222-2225` |
| 4 | Source string routes first refusal (word skeleton present) | `source_string_route_verdict` | `smtlib.rs:2234-2239` |
| 5 | Flatten the push/pop stack to one assertion list | `smtlib_single_query` | `smtlib.rs:1761`, `:2240` |
| 6 | `solve` — entry normalizations: counterexample normalization, top-level existential Skolemization | `auto::solve` | `auto.rs:492`, `:507` |
| 7 | Quantifier scan + theory-feature scan | `contains_quantifier_within`, `Features::scan_within` | `auto.rs:1674`, `:1679` |
| 8 | Term-identity refutation (`not (= t t)`, `ite` collapse) | `term_identity::term_identity_refutation` | `auto.rs:1688` |
| 9 | **Gate**: `config.preprocess && !has_quantifier` (`preprocess` defaults `true`) | — | `auto.rs:1760`; default at `backend.rs:392` |
| 10 | `canonicalize_terms` (59 denotation rules, denotation guard on) | `axeyum_rewrite::canonicalize_terms` | `auto.rs:2166` |
| 11 | `propagate_values` (pin `x = c`) | `axeyum_rewrite::propagate_values` | `auto.rs:2172` |
| 12 | `solve_eqs_bounded` (substitute `x := t`, fuel `5_000_000`) | `axeyum_rewrite::solve_eqs_bounded` | `auto.rs:2178`; fuel `solve_eqs.rs:42` |
| 13 | `elim_unconstrained` (peel invertible layers off single-use vars) | `axeyum_rewrite::elim_unconstrained` | `auto.rs:2185` |
| 14 | `canonicalize_terms` again (AC-normalize what substitution un-normalized) | — | `auto.rs:2192` |
| 15 | **Gate**: keep the reduction only if the AIG did not grow | `reduction_shrinks_encoding` | `auto.rs:2233-2264` |
| 16 | Dispatch the reduced query with `preprocess` cleared so step 9 cannot re-enter | `dispatch_reduced` → `check_auto_inner` | `auto.rs:2277-2280` |
| 17 | On `sat`: replay the trail in reverse, then evaluate **every original assertion** | `ModelReconstructionTrail::reconstruct` + `eval` | `auto.rs:2299-2323` |

Deadline checks sit between every pair of steps 10-14 (`auto.rs:2163, 2169,
2175, 2182, 2189, 2195`); a timeout there returns `Unknown`, never a verdict
(`auto.rs:1791`).

**Configuration surface.** One boolean: `SolverConfig::preprocess`
(`backend.rs:188`), default `true` (`backend.rs:392`), builder
`with_preprocess` (`backend.rs:484`). There is no per-pass switch, no ordering
knob, and no way to reach the 8-round loop from the front door. `elim_unconstrained_with`
(`elim_unconstrained.rs:253`) accepts a caller-supplied `InverterRegistry` — the
only pass-level configuration point in the crate — and its sole caller is a bench
example (`crates/axeyum-bench/examples/elim_unconstrained_ablation.rs:170`).

**The other pipeline.** `preprocess::check_with_preprocessing_impl`
(`preprocess.rs:65`) runs the same five steps inside `for _round in
0..MAX_PREPROCESS_ROUNDS` with an early exit when a round eliminates nothing
(`preprocess.rs:89, 133`). It has the same replay discipline
(`preprocess.rs:177-228`) and carries `real_div_zeros` witnesses into the
returned model (`preprocess.rs:225-227`), with a comment stating that dropping
them would produce "a wrong `sat` through the preprocessed path".

> **Corrected 2026-09-09.** This paragraph originally said the `auto.rs` copy
> LACKS the `real_div_zeros` carry and that "neither is a superset of the
> other". Both are false. `auto.rs:2344` carries `real_div_zeros` (since
> 2026-07-25, same comment), *and* `auto.rs:2335` carries function
> interpretations, which `preprocess.rs` does not build at all (zero
> `set_function` calls). The `auto.rs` pipeline is a strict SUPERSET on model
> witnesses. See ADR-1811.

## Inventory

### `axeyum-smtlib` — reader and writer (28,442 lines; 25,207 in scope)

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `sexpr` reader | `src/sexpr.rs` | 384 | Iterative tokenizer + reader; explicit stacks so deep input cannot overflow | WIRED | `parse.rs` calls it; `sexpr.rs:1-4` |
| Typed parser | `src/parse.rs` | 23,668 | SMT-LIB commands, sorts, terms → `TermArena` + `Script`; also builds the string/word/lex/membership source views | WIRED | `smtlib.rs:2171` |
| `Script` | `src/parse.rs:104-356` | — | 37 public fields; 15 `ScriptCommand` variants | WIRED | `smtlib.rs:2189` |
| Writer | `src/write.rs` | 590 | Sharing-preserving export: fan-in > 1 nodes become 0-ary `define-fun` | WIRED | `write_script` re-exported `lib.rs:52`; used by bench + `render` paths |
| `bounded_completeness` | `src/bounded_completeness.rs` | 638 | Syntactic C1∧C2∧C3 test that lets a bounded string `unknown` be upgraded to `unsat` | WIRED | `axeyum-solver/src/smtlib.rs` (`is_bounded_complete`) |
| `ingest_stats` | `src/ingest_stats.rs` | 241 | Opt-in thread-local ingest counters (atoms, lists, depth) | TEST-ONLY | Only caller: `crates/axeyum-smtlib/examples/ingest_shape_probe.rs` |
| `string_literal_code_points` | `src/lib.rs:68` | 8 | The single shared string-literal decoder, public so a certificate uses the same one | WIRED | `lib.rs:57-67` states the rationale |
| `regex`, `regex_membership` | `src/regex*.rs` | 2,780 | Out of scope | — | see [07](07-strings-and-regex.md) |

### `axeyum-ir` — term IR and evaluator (13,831 lines)

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `TermArena` | `src/arena.rs` | 2,290 | Append-only hash-consed arena + typed sort-checked builders | WIRED | Every crate above it |
| `intern_node` | `src/arena.rs:262-271` | 10 | The hash-cons: lookup in `intern: FastMap<TermNode, TermId>`, else push | WIRED | All builders route through it |
| `TermNode` / `Op` | `src/term.rs` | 384 | 10 node variants incl. `WideBvConst`, `WideIntConst` | WIRED | — |
| `Sort` | `src/sort.rs` | 310 | Bool, BitVec, Int, Real, Array, Float, RoundingMode, uninterpreted, datatype | WIRED | `parse_sort`, `parse.rs:6923` |
| `Value` | `src/value.rs` | 1,075 | 12+ variants; `Bv`/`WideBv` and `Int`/`WideInt` are disjoint by construction | WIRED | `value.rs:35-47` |
| Ground evaluator | `src/eval.rs` | 1,741 | `eval`, `eval_with_memo`, `well_founded_default`; the executable semantic reference | WIRED | `auto.rs:2315`, `preprocess.rs:192` |
| `Assignment` | `src/eval.rs:20` | — | Symbol → `Value`, plus function interps and `real_div_zeros` | WIRED | `preprocess.rs:225` |
| `bits` | `src/bits.rs` | 177 | LSB-first value↔bits conversion | WIRED | bit-blaster / model lifter |
| `BIT_VECTOR_WIRE_ORDER` | `src/bits.rs:18` | 1 | The pinned wire-order constant | TEST-ONLY | Only non-def reference: `tests/ir.rs:283` |
| `fast_map` | `src/fast_map.rs` | 139 | `FastMap = HashMap<_,_,FxBuildHasher>`; deterministic by construction | WIRED | `arena.rs:6`, `:28-44` |
| `budget` | `src/budget.rs` | 1,506 | Deterministic work budgets — the stack-wide resource-limit primitive | WIRED (partly) | `WorkMeter`/`Budget`/`EffortPolicy`/`EffortAccount`/`Delayed`/`RoundOutcome` used in `axeyum-cnf`, `sat_bv_backend.rs`, `dpll_t.rs` |
| `budget` unused types | `src/budget.rs:284, 385, 449, 779, 956` | ~200 | `BudgetSplit`, `SchedulePolicy`, `DelayCounter`, `PassBudgetStats`, `BudgetLedger` | TEST-ONLY | No reference outside `axeyum-ir`; `BudgetLedger`'s only use is `budget.rs:1422`, inside the `#[cfg(test)]` module that starts at `budget.rs:1026` |
| `stop` | `src/stop.rs` | 236 | Cooperative stop token shared by theory routes and the CDCL core | WIRED | `axeyum-solver/src/portfolio.rs`, `axeyum-cnf/src/interrupt.rs` |
| `stats` (`TermStats`) | `src/stats.rs` | 117 | Shared DAG-size footprint | WIRED | 20 files outside `axeyum-ir` |
| `rational` | `src/rational.rs` | 1,605 | `i128` fast path + opt-in `wide_*` BigRational promotion (ADR-1702) | WIRED | 238 files |
| `poly`, `poly_big` | `src/poly*.rs` | 1,687 | Univariate polynomial arithmetic for the real-algebraic carrier | WIRED | `poly::` in 73 files; `poly_big::` in 3 |
| `wide`, `int_wide` | `src/wide.rs`, `src/int_wide.rs` | 1,130 | `WideUint` (>128-bit BV), `WideInt` (>`i128` integers) | WIRED | 42 / 17 files |
| `real_algebraic` | `src/real_algebraic.rs` | 639 | Defining polynomial + isolating interval (ADR-0038) | WIRED | 21 files |
| `algebraic_bridge` | `src/algebraic_bridge.rs` | 343 | `impl axeyum_arith::AlgebraicNumber` for `BigAlgebraic` and `RealAlgebraic` | NO CALLER FOUND | Searched `AlgebraicNumber` across `crates/`: the only hits are the trait definition `axeyum-arith/src/lib.rs:1212`, two doc lines, and this file's own impls. Trait-object dispatch could in principle hide a caller, but no `dyn AlgebraicNumber` or generic bound on it exists in the tree. |
| `fmt` (`render`) | `src/fmt.rs` | 200 | Term rendering | WIRED | `smtlib.rs` `get-assertions` path |

### `axeyum-query` — the query object (1,374 lines)

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `Query`, `QueryBuilder` | `src/lib.rs` | 621 | Assertions, assumptions, scopes, labels | WIRED, but off the front door | Only backend consumer is `SolverBackend::check_query` (`backend.rs:675`); the SMT-LIB path uses `SmtLibSingleQuery` (`smtlib.rs:1440`) and calls `solve(arena, &assertions, …)` (`smtlib.rs:2244`) |
| `QueryPlan`, slicing | `src/planning.rs` | 753 | `plan_full`, `slice_for_targets`, `slice_exact_targets`, FNV structural cache key | WIRED via `check_query` only | `sat_bv_backend.rs:613` calls `query.plan_full(arena)`; `slice_*` have no non-test caller |
| `StructuralCacheKey` | `src/planning.rs:42` | — | FNV-1a over the planned term set | WIRED | `axeyum-bench/src/main.rs:46` |
| `QueryReplayFailure` | `src/planning.rs:184` | — | Structured replay failure for a sliced plan | WIRED | `sat_bv_backend.rs:44` |

Consumers of the crate, from `Cargo.toml` and `use` sites: `axeyum-solver`
(`backend.rs:7`, `sat_bv_backend.rs:44`), `axeyum-scenarios` (13 modules),
`axeyum-bench`, `axeyum-py`. Within `axeyum-solver` the only non-test uses are
those two files.

### `axeyum-rewrite` — the sixteen files (16,959 lines)

Every row's reachability was determined by grepping the function name across
`crates/` and excluding `crates/axeyum-rewrite/src/`.

| Pass / file | Path | LOC | What it rewrites | Preservation | Reachability | Caller cited |
|---|---|---|---|---|---|---|
| Canonicalizer | `src/canonical.rs` | 5,290 | 59 local rules: Boolean folds, `eq` reflexivity, AC ordering, constant folding, BV identities | **Denotation** | WIRED | `auto.rs:2166`, `auto.rs:2192`, `preprocess.rs:85`, `preprocess.rs:125`, `incremental.rs:1213/1262`, `quant_bool_model_sat.rs` |
| Constant propagation | `src/propagate_values.rs` | 538 | Pins `(= x c)`, `(= c x)`, bare `p`, `(not p)`; substitutes to fixpoint | Equisat + **trail** | WIRED | `auto.rs:2172`, `preprocess.rs:91` |
| Equation solving | `src/solve_eqs.rs` | 415 | Orients top-level `(= x t)` with occurs-check into `x := t`, substitutes, drops the equality | Equisat + **trail** | WIRED (`solve_eqs_bounded` only) | `auto.rs:2178`, `preprocess.rs:102` |
| `solve_eqs` (unbounded wrapper) | `src/solve_eqs.rs:149` | 3 | `solve_eqs_bounded(_, _, u64::MAX)` | — | TEST-ONLY | Searched `solve_eqs(` workspace-wide: 5 hits, all in `solve_eqs.rs`'s own `#[cfg(test)]` module (`:249, 283, 318, 354, 405`) |
| Unconstrained elimination | `src/elim_unconstrained.rs` | 839 | Replaces the sole parent of a once-occurring variable by a fresh variable, records `x := op⁻¹(u,…)` | Equisat + **trail** | WIRED | `auto.rs:2185`, `preprocess.rs:114` |
| Inverter registry | `src/inverter.rs` | 1,334 | Per-theory inversion rules (`CoreInverter`, `BvInverter`, `ArithInverter`) with the unconstrained-ness predicate injected | supports the row above | WIRED | `InverterRegistry::with_defaults()` at `elim_unconstrained.rs:242` |
| Array elimination | `src/arrays.rs` | 1,076 | `eliminate_arrays`: read-over-write + Ackermann → QF_BV (ADR-0010). `abstract_arrays`: the CEGAR variant | Equisat + `project_model` | WIRED | `abv.rs:540` / `abv.rs:571`; also `aufbv.rs`, `combined.rs`, `proof.rs`, `qfabv_elim_alethe.rs` |
| Function elimination | `src/functions.rs` | 1,225 | `eliminate_functions`: Ackermann reduction of UF applications (ADR-0013). `abstract_functions`: lazy variant | Equisat + `project_model` | WIRED | `euf.rs`, `auto.rs:4349`, `aufbv.rs`, `combined.rs`, `ufbv_online.rs` |
| Datatype simplification | `src/datatypes.rs` | 147 | `select_i(construct_c(…)) → a_i`, `is_c(construct_d(…)) → bool` (ADR-0022) | **Denotation** | WIRED | `datatype_elim.rs`, `datatype_native.rs`, reached from `auto.rs:4575` |
| Quantifier expansion / instantiation | `src/quantifiers.rs` | 1,222 | `expand_quantifiers` (finite-domain), `instantiate_universals`, `instantiate_with_triggers` | Equisat, untrusted; caller replays the original | WIRED | `auto.rs:7325`, `auto.rs:8632`, `auto.rs:8661/8685` |
| Int div/mod elimination | `src/int_divmod.rs` | 842 | Euclidean `div`/`mod`-by-constant and `abs` → fresh vars + linear constraints; `c = 0` → a fresh **unconstrained** var (ADR-1730) | Equisat, fresh symbols only | WIRED | `auto.rs:2728`, `auto.rs:2806`, `nia_linearize.rs`, `evidence.rs` |
| Integer blasting | `src/int_blast.rs` | 634 | Bounded LIA → QF_BV at width ≤ 64 (ADR-0014); `unsat` does **not** transfer | Sat-only after replay; `integer_model` | WIRED | `auto.rs:6553/6597/6686`, `lia.rs`, `combined.rs`, `proof.rs` |
| Derived-BV lowering | `src/lower_bv.rs` | 657 | Derived BV ops → the 17-op bitblast core, for proof emission | **Denotation** | WIRED (evidence path only) | Single caller: `crates/axeyum-solver/src/qfbv_alethe.rs`; not on the decision path |
| α-equivalence / duality | `src/alpha.rs` | 942 | Decides α-equivalence and quantifier-negation duality in one walk | a *checker*, not a rewrite | WIRED (`alpha_equivalent`) | `bool_simplify.rs:20` |
| `alpha_equivalent_to_negation` | `src/alpha.rs:132` | — | The duality half | — | TEST-ONLY | Searched the identifier workspace-wide: the definition, one doc reference, and `alpha.rs`'s own tests (`:377, 582, 602, 608, 624`) |
| Reconstruction trail | `src/reconstruct.rs` | 187 | `ModelReconstructionTrail`: append `Define{sym, definition}` in elimination order, replay in reverse | the composition contract | WIRED | `auto.rs:2299`, `preprocess.rs:185` |
| Pass size stats | `src/pass_stats.rs` | 345 | 7 `*_with_stats` wrappers computing `TermStats` before/after each pass | — | **NO CALLER FOUND** | Searched all seven names (`canonicalize_terms_with_stats`, `eliminate_arrays_with_stats`, `eliminate_functions_with_stats`, `eliminate_int_divmod_with_stats`, `blast_integers_with_stats`, `elim_unconstrained_with_stats`, `rule_application_counts`) across `crates/`: every hit is the definition, the `lib.rs:76-80` re-export, or `pass_stats.rs`'s own `#[cfg(test)]` module |
| Manifest contract | `src/lib.rs` | 1,266 | `RewriteRule`, `RewriteManifest`, `Preservation`, `ModelProjection`, `PreconditionGuard`, `ManifestError` + validation | the contract | WIRED | `canonical.rs:542` |
| `default_inverters` | `src/elim_unconstrained.rs:564` | 3 | Alias returning `InverterRegistry::with_defaults()` | — | **NO CALLER FOUND** | Searched `default_inverters` across the whole repo: only the definition and the `lib.rs:58` re-export. Every real use goes to `InverterRegistry::with_defaults()` (`elim_unconstrained.rs:242`, `elim_unconstrained_ablation.rs:170`) |

### Solver-side preprocessing entry points

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `check_with_preprocessing` | `preprocess.rs:40` | 229 (file) | The 8-round façade wrapper | WIRED (narrowly) | `abv.rs:3242` (local-search probe); `tests/preprocess.rs:14` |
| `preprocess_reduce` | `auto.rs:2158` | 42 | The single-round default pipeline | WIRED | `auto.rs:1766` |
| `term_identity_refutation` | `term_identity.rs:40` | 161 (file) | `not (= t t)` and `ite`-collapse refutations, re-checkable | WIRED, **before** preprocessing | `auto.rs:1688` |
| `bool_simplification_refutation` | `bool_simplify.rs:36` | 308 (file) | Tiny Boolean normalizer producing a re-checkable `false` certificate | WIRED on the **evidence** path only | `evidence.rs:1942`, `evidence.rs:2974`, `reconstruct/direct.rs`. Searched `bool_simplification_refutation(` across `crates/axeyum-solver/src/`: no hit in `auto.rs` — unlike its sibling `term_identity_refutation`, it is not consulted during dispatch |
| `term_walk` | `term_walk.rs` | 183 | `collect_top_binary_conjuncts`, `flatten_binary_spine`, `binary_op_operands`, `flatten_op_spine` — iterative spine walks that replaced a stack-overflowing recursion | WIRED | `flatten_op_spine`: `auto.rs`, `abv.rs`; `flatten_binary_spine`/`binary_op_operands`: the 7 `array_*.rs` routes + `quant_bv_model_sat_cert.rs`; `collect_top_binary_conjuncts`: `evidence.rs` and `term_identity.rs:10` |

## Preservation and model routes

Question: which passes change the model set, and where does the inverse live?

| Pass | Direction it can break | Model route | Where |
|---|---|---|---|
| `canonicalize_terms` | neither (denotation-equal under every assignment) | none needed | manifest forces `ModelProjection::Identity` for every `Denotation` rule (`lib.rs:310-318`) |
| `simplify_datatypes` | neither | none needed | `datatypes.rs:1-18`; a selector over a non-matching constructor is left untouched |
| `lower_derived_bv` | neither | none needed | `lower_bv.rs:1-12`; each rule is an SMT-LIB identity checked by the ground evaluator |
| `propagate_values` | model set (drops symbols) | `ModelReconstructionTrail::define` | `propagate_values.rs:12-18` |
| `solve_eqs_bounded` | model set | `ModelReconstructionTrail::define` | `solve_eqs.rs:14-19` |
| `elim_unconstrained` | model set | trail + `Inversion` from the inverter registry | `elim_unconstrained.rs:24-27`, `inverter.rs:192` |
| `eliminate_arrays` | model set (array vars → fresh scalars) | `ArrayElimination::project_model` | `arrays.rs:141`, second at `:199` for the abstraction |
| `eliminate_functions` | model set (UF apps → fresh scalars) | `FunctionElimination::project_model` | `functions.rs:151`, `:257` |
| `blast_integers` | **`unsat` does not transfer** | `IntBlasting::integer_model` + mandatory replay | `int_blast.rs:14-21`, `:153` |
| `eliminate_int_divmod` | `sat` when the congruence cap fires | *no* projection API — the original symbols survive unchanged, so restriction is the identity; the sat-side risk is handled by `guard_zero_divisor_sat` | `int_divmod.rs:142-235`; guard at `auto.rs:2760`, invoked `auto.rs:2808-2816` |
| `expand_quantifiers` | equisatisfiable, untrusted | none; the caller replays the **original quantified formula** through the enumerating evaluator | `quantifiers.rs:1-11` |
| `abstract_arrays` / `abstract_functions` | abstraction, both directions | CEGAR refinement in the calling route | `abv.rs:701`, `euf.rs`, `ufbv_online.rs` |

The one pass with no reconstruction route and no explicit argument for why none
is needed is `eliminate_int_divmod`. The argument is nevertheless sound and
present in prose: the pass only *adds* fresh symbols and rewrites `div`/`mod`
terms into references to them, leaving every original symbol in place
(`int_divmod.rs:184-192`), and the one direction where the relaxation could
fabricate a verdict — a `sat` above `MAX_CONGRUENCE_GROUPS = 48` — is turned into
a first-class `unknown` by `guard_zero_divisor_sat` (`auto.rs:2760`,
`auto.rs:2808-2816`, ADR-1730). Recording that reasoning in the type, as the
other passes do, would make it checkable rather than readable.

The trust anchor for the whole pipeline is not the passes: it is the final
replay. Both implementations evaluate *every original assertion* against the
reconstructed model and turn any failure into `Err`, never a verdict
(`auto.rs:2313-2323`, `preprocess.rs:191-213`). ADR-1721 records the general
rule — a preprocessing step owes a replacement equality, nothing in the `unsat`
direction, or a per-constraint discharge, depending on which direction it can
break, and a decline is a legal discharge.

## The rewrite manifest: what it promises and what enforces it

The manifest (`lib.rs:211-404`) is the crate's contract type. Each `RewriteRule`
carries a stable ID, prose `precondition`, a machine-checked `guard`, a
`preservation` class, a `projection` obligation, required `tests`, and
`enabled_by_default`.

`RewriteManifest::new` runs `validate_rules` (`lib.rs:288-308`) and refuses:
duplicate IDs, an empty precondition, an empty `RootOperators` list, an empty
test list, and then `validate_projection` (`lib.rs:310-331`), which enforces:

- `Denotation` ⟹ `projection` **must** be `Identity`, else `UnexpectedProjection`.
- `Equisatisfiable` + `Identity` ⟹ `MissingProjection`.
- `Equisatisfiable` + `Required` + `enabled_by_default` ⟹
  `DefaultEquisatWithoutImplementedProjection`. **Not** enabled by default is
  accepted (`lib.rs:328`).
- `Equisatisfiable` + `Implemented` + `enabled_by_default` without
  `RewriteTestRoute::ModelProjectionReplay` ⟹ `DefaultEquisatWithoutProjectionTest`
  (`lib.rs:333-344`).

At runtime the canonicalizer enforces two tiers, selected by `PreconditionPolicy`
(`canonical.rs:328-348`), whose `#[default]` is `Denotational` (`canonical.rs:347`):

1. **Structural, always on.** `manifest.enabled_guards()` (`lib.rs:266`) is
   indexed once per pass (`canonical.rs:1006`) and every committed rewrite is
   checked against its rule's declared operator scope (`canonical.rs:1040`),
   plus sort agreement. Comparison is by operator *variant*
   (`lib.rs:201-208`), so `Extract{hi,lo}` matches any indices.
2. **Denotational, on by default.** Each committed rewrite is evaluated on both
   sides under `DENOTATION_GUARD_SAMPLES = 4` fixed assignments
   (`canonical.rs:312`, built at `canonical.rs:1001`) by the `axeyum-ir` ground
   evaluator — a code path independent of the matcher that decided to fire — and
   a disagreement is a refusal, not a rewrite.

The guard table is derived from the dispatch, not from the prose, deliberately
(`canonical.rs` doc above `default_guard`), and a test drives every default rule
and asserts the operator it actually fired on was in scope
(`guard_table_matches_the_rules_that_actually_fire`).

**What the manifest does not currently exercise.** All 59 shipped rules are
constructed by one helper (`canonical.rs:847-861`) that hard-codes
`preservation: Preservation::Denotation`, `projection: ModelProjection::Identity`,
`tests: [ExhaustiveSmallWidth, OracleDifferential]`, `enabled_by_default: true`.
So `ModelProjection::Required`, `ModelProjection::Implemented`,
`Preservation::Equisatisfiable`, and `RewriteTestRoute::{ModelProjectionReplay,
ProofObligation}` appear in no shipped rule; the four validation arms about them
are covered only by `lib.rs`'s own unit tests (`lib.rs:449-480`). Correspondingly,
the six *equisatisfiable* passes (`propagate_values`, `solve_eqs`,
`elim_unconstrained`, `eliminate_arrays`, `eliminate_functions`,
`blast_integers`) are **not manifest rules at all** — they are separate
functions with their own reconstruction types, outside the contract mechanism.
The manifest governs the canonicalizer; it does not govern the pipeline.

## Parser surface: what is accepted, rejected, and quietly absorbed

**Commands accepted** (`parse.rs:5999-6298`): `set-logic`, `set-info`,
`set-option`, `get-model`, `get-unsat-core`, `get-proof`, `get-assignment`,
`get-unsat-assumptions`, `get-objectives`, `exit`, `get-assertions`,
`reset-assertions`, `maximize`, `minimize`, `get-option`, `get-info`, `echo`,
`get-value`, `check-sat-assuming`, `check-sat`, `declare-fun`, `declare-const`,
`declare-datatype`, `declare-datatypes`, `define-fun`, `define-const`,
`define-sort`, `declare-sort`, `assert`, `push`, `pop`.

**Rejected, not ignored.** Any other head is `SmtError::Unsupported("command
`{other}`")` (`parse.rs:6297`). `reset` is explicitly rejected with a message
pointing at `reset-assertions` (`parse.rs:6081-6088`), because a no-op would
silently keep stale assertions.

**Sorts** (`parse_sort`, `parse.rs:6923-7032`): `Bool`, `Int`, `Real`,
`Float16/32/64/128`, `(_ FloatingPoint eb sb)`, `(_ BitVec w)`, `RoundingMode`,
`(Seq E)`, `(_ FiniteField p)`, `(Array I E)`, declared sorts and `define-sort`
aliases. Three of these are *lowered at parse time*, which is a preprocessing
decision made before the solver is reachable:

- `String` becomes `Sort::BitVec(STRING_TOTAL)` (`parse.rs:6946`) — the packed
  ADR-0029 bounded model, with a well-formedness constraint asserted at declare
  time.
- `RoundingMode` becomes an 8-pattern BV with a `≤ 4` constraint asserted at
  declare time.
- `(Seq E)` becomes a packed BV; the bare `Seq` head is a scoped `Unsupported`.

**Logics.** `set-logic` is stored in `Script::logic` (`parse.rs:6002`) and
validated against nothing at parse time. Dispatch never reads it: searching
`script.logic` across `crates/axeyum-solver/src/` finds two hits, both copying
it into a report struct (`smtlib.rs:1429`, `smtlib.rs:2361`). Route selection is
by `Features::scan_within` over the term DAG (`auto.rs:1679`). In the *session*
front door only, a name that is not shaped like a logic gets an `unsupported`
response (`smtlib.rs:3530-3541`).

**Accepted and silently discarded.** These are the omission cases; none is a
soundness hazard as far as source reading shows, but each is a place where the
tool omits rather than refuses:

| Construct | What happens | Site |
|---|---|---|
| `set-option` in the **one-shot** front door | Recorded into `Script::options` and `ScriptCommand::SetOption`; the one-shot walk matches it in a do-nothing arm | `parse.rs:6032`; `smtlib.rs:1819`, `smtlib.rs:2730`. Only `solve_smtlib_session` acts on it (`smtlib.rs:3543`, `apply_set_option`) |
| `(exit)` | Deliberate no-op, stated as a divergence from `z3 file.smt2`: the parser reads the whole script first, so honouring it would drop trailing commands | `parse.rs:6059-6064`; divergence note `smtlib.rs:3298-3301` |
| `!`-attributes other than `:named` and `:pattern` | The attribute loops step `i += 2` and match only those two keywords; `:qid`, `:weight`, `:no-pattern`, `:lblpos` etc. are skipped without comment | `parse.rs:6307-6316`, `:6319-6333`, `:7769-7803` |
| A `:pattern` group the trigger builder cannot root | The whole group is cleared and dropped, falling back to auto-selection. This one *is* documented as deliberate | `parse.rs:7792-7796`, rationale `:7811-7816` |
| `get-assignment`, `get-unsat-assumptions`, `get-objectives` | Parsed, recorded as `ScriptCommand::UnansweredOutput`, answered `unsupported` in a session and dropped in the one-shot path | `parse.rs:6053-6058`; `smtlib.rs:3563-3570`, `smtlib.rs:1825` |

**Resource behaviour.** `SmtError::DeadlineExceeded` and
`SmtError::ResourceLimit` are distinct from `Syntax`/`Unsupported`
(`axeyum-smtlib/src/lib.rs:87, 105`) and the front door maps both to
`Unknown{kind: ResourceLimit}`, never a verdict (`smtlib.rs:2194-2211`). The
`DeadlineExceeded` doc comment carries an open, unresolved measurement
discrepancy: an in-tree "58 MB / ~54 s" figure (~1.1 MB/s) against 30-58 MB/s
measured on committed files up to 10.5 MB (`axeyum-smtlib/src/lib.rs:74-91`).

## Data flow

```
text
 └─ sexpr::read_all                        iterative; SExpr tree
     └─ parse::parse_script_with_string_bound_within
          ├─ parse_sort           String/Seq/RoundingMode lowered to packed BV here
          ├─ build_term (iterative)  →  TermArena::intern_node (hash-cons)
          └─ Script { arena, assertions, commands, + 17 source-analysis fields }
              ├─ word_only_fallback? ─────────────────► decide_word_only        (verdict)
              ├─ source_fp_prefix_monotonic_unsat? ───► verdict, no solve
              ├─ word_skeleton non-empty? ────────────► source_string_route_verdict
              └─ smtlib_single_query  (flattens push/pop to one Vec<TermId>)
                   └─ auto::solve
                        ├─ normalize counterexamples; skolemize_top_existentials
                        ├─ Features::scan_within  →  route plan
                        ├─ term_identity_refutation                       (verdict)
                        └─ check_auto_with_recorder
                             ├─ [preprocess && !quantifier] preprocess_reduce
                             │      canonicalize → propagate_values →
                             │      solve_eqs_bounded → elim_unconstrained →
                             │      canonicalize          ⇒ (reduced, trail)
                             ├─ reduction_shrinks_encoding? (lowers BOTH to AIG)
                             ├─ dispatch_reduced → check_auto_inner (preprocess=false)
                             │      └─ route-local passes: eliminate_arrays,
                             │         eliminate_functions, eliminate_int_divmod,
                             │         blast_integers, simplify_datatypes,
                             │         expand_quantifiers, instantiate_*
                             └─ on Sat: trail.reconstruct(reverse) → eval(EVERY
                                        original assertion) → Model
```

**Sharing, parse to solve to writer.** One mechanism end to end. The parser
interns every node through `TermArena::intern_node` (`arena.rs:262`), so
structurally equal subterms collapse to one `TermId` at build time, and `let`
bindings and `:named` aliases are bindings of a `TermId`, not textual macros.
The intern table is `FastMap<TermNode, TermId>` = `FxHashMap` (`fast_map.rs:134`),
chosen for determinism by construction rather than a seeded hasher
(`fast_map.rs:16-46`). Rewrites preserve sharing because `replace_subterms`
(`canonical.rs:2814`) and `build_app` (`canonical.rs:2709`) rebuild through the
same builders — `solve_eqs`'s doc calls this out explicitly: substituting
`x := t` shares `t`'s nodes rather than copying them (`solve_eqs.rs:21-23`). The
writer re-derives sharing from fan-in: it counts uses, emits every node with
fan-in > 1 as a 0-ary `define-fun`, and relies on children interning before
parents so ascending `TermId` order is a valid emission order (`write.rs:1-6`,
`:19-60`). One thing deliberately *not* keyed on: quantifier `:pattern`
annotations are a side map the interner ignores, so two quantifiers differing
only in triggers are one term (`arena.rs:47-60`).

## Entry points and public API

| From outside | Function | Path |
|---|---|---|
| SMT-LIB text → verdict | `solve_smtlib`, `solve_smtlib_with_model` | `axeyum-solver/src/smtlib.rs:1954, 1972` |
| SMT-LIB text → ordered response stream | `solve_smtlib_session`, `solve_smtlib_incremental` | `smtlib.rs:3318, 3135` |
| Terms → verdict, with the 8-round pipeline | `check_with_preprocessing` | `preprocess.rs:40` (re-exported `lib.rs:1268`) |
| Text → `Script` | `parse_script`, `parse_script_within`, `parse_script_with_string_bound[_within]` | `axeyum-smtlib/src/lib.rs:44-49` |
| `Script` → text | `write_script`, `sort_text` | `write.rs:19, 305` |
| Build terms | `TermArena` + ~200 typed builders | `axeyum-ir/src/arena.rs` |
| Check a model | `eval`, `eval_with_memo` | `axeyum-ir/src/eval.rs:241, 274` |
| Canonicalize | `canonicalize`, `canonicalize_terms`, `Canonicalizer`, `default_manifest` | `axeyum-rewrite/src/canonical.rs:513, 526, 116, 542` |
| Each elimination pass | see the rewrite table above; all re-exported from `axeyum-rewrite/src/lib.rs:44-87` | |
| Query object | `Query::builder`, `SolverBackend::check_query` | `axeyum-query/src/lib.rs:113`; `backend.rs:675` |

## Tests and gates

| Suite | Path | `#[test]` count | Feature gate | Covers |
|---|---|---|---|---|
| SMT-LIB parser/writer | `axeyum-smtlib/tests/smtlib.rs` | 246 | none | The bulk of parser surface |
| Packed sort widths | `axeyum-smtlib/tests/distinct_packed_sort_widths.rs` | 5 | none | Packed string/seq widths |
| IR core | `axeyum-ir/tests/ir.rs` | 83 | none | Arena, sorts, builders, bit order |
| IR datatypes | `axeyum-ir/tests/datatypes.rs` | 6 | none | Datatype nodes/values |
| Real-algebraic field | `axeyum-ir/tests/real_algebraic_field{,_bignum}.rs` | 20 | none | `RealAlgebraic` arithmetic |
| Sylvester differential | `axeyum-ir/tests/sylvester_determinant_diff{,_bignum}.rs` | 4 | none | Resultant agreement |
| Wide-int eval fuzz | `axeyum-ir/tests/wide_int_eval_fuzz.rs` | 2 | none | `WideInt` evaluator path |
| Unconstrained exhaustive | `axeyum-rewrite/tests/elim_unconstrained_exhaustive.rs` | 16 | none | Every inverter rule at small widths |
| Precondition fuzz | `axeyum-rewrite/tests/precondition_fuzz.rs` | 2 | none | The manifest guard tiers |
| Read-over-write witness | `axeyum-rewrite/tests/read_over_write_witness.rs` | 4 | none | ADR-1721's array witness; the mutation that motivated it |
| Function-abstraction witness | `axeyum-rewrite/tests/function_abstraction_witness.rs` | 6 | none | Ackermann witness |
| Int div/mod witness | `axeyum-rewrite/tests/int_divmod_witness.rs` | 10 | none | Euclidean witness incl. adversarial `from_parts` fixtures |
| Quantifier duality | `axeyum-rewrite/tests/quantifier_duality.rs` | 7 | none | `alpha.rs` |
| Rewrite datatypes | `axeyum-rewrite/tests/datatypes.rs` | 2 | none | `simplify_datatypes` |
| Preprocessing | `axeyum-solver/tests/preprocess.rs` | 12 | **`full`** | `check_with_preprocessing` end to end |
| Warm preprocessing | `axeyum-solver/tests/warm_preprocessing.rs` | 4 | **`full`** | Incremental + canonicalization |
| Rewrite differential | `axeyum-solver/tests/rewrite_differential.rs` | 5 | **`full`** | Canonicalizer against a backend |
| Query planning | `axeyum-solver/tests/query_planning.rs` | 2 | **`full`** | `check_query` + slicing |
| FP preprocessing | `axeyum-solver/tests/fp_preprocess.rs` | 1 | **`full`** | FP lowering |

Unit tests inside `axeyum-rewrite/src` by file: `canonical.rs` 58, `alpha.rs` 25,
`lib.rs` 10, `elim_unconstrained.rs` 9, `propagate_values.rs` 9, `lower_bv.rs` 9,
`functions.rs` 8, `quantifiers.rs` 7, `arrays.rs` 5, `int_blast.rs` 5,
`solve_eqs.rs` 5, `pass_stats.rs` 5, `reconstruct.rs` 4, and **zero** in
`int_divmod.rs`, `inverter.rs`, `datatypes.rs` (each has an integration suite
instead, listed above).

Two things a reader should check before quoting a green run. The five
`axeyum-solver` suites above are `#![cfg(feature = "full")]`, so without
`--features full` they compile to an empty binary and exit 0 — the trap CLAUDE.md
records for `corpus_regression` and `progress_frontier`. And `axeyum-rewrite`'s
three benches (`eliminate_arrays`, `eliminate_int_divmod`, `int_blast_ladder`)
are `harness = false` criterion targets, so they are compiled by
`--all-targets` but run nothing under `cargo test`. `pass_stats.rs`'s five unit
tests are the only thing exercising that module at all.

## Doc drift

### `docs/internals/rewriting.md` (67 lines, last content change 2026-08-07)

Badly stale against a 16,959-line crate. Specific contradictions:

1. **Line 18-19**: *"a rule cannot claim that model reconstruction is required
   while providing no implementation route."* Contradicted by
   `lib.rs:325-328`: `ModelProjection::Required` is accepted whenever
   `enabled_by_default == false`. The real rule is narrower — a *default-enabled*
   equisatisfiable rule needs `Implemented` **and** a `ModelProjectionReplay`
   test (`lib.rs:333-344`).
2. **Line 23**, table cell *"Usually identity"* for `Denotation`. Contradicted
   by `lib.rs:310-318`: a `Denotation` rule with any non-`Identity` projection
   is rejected as `UnexpectedProjection`. It is always identity, enforced.
3. **The machine-checked half of the contract is absent.** `PreconditionGuard`
   (`lib.rs:178-208`), `PreconditionPolicy` (`canonical.rs:328-348`),
   `DENOTATION_GUARD_SAMPLES` (`canonical.rs:312`), `PreconditionAudit` /
   `PreconditionFailure` / `PreconditionViolation` / `RewriteError`
   (`canonical.rs:353-512`) are the enforcement mechanism and the doc's
   "Manifest contract" section lists only the four metadata fields.
4. **Line 33-36**: *"Broader transformations … are separate routes … not
   silently part of the default canonicalizer."* True of the canonicalizer and
   misleading about the product: `propagate_values`, `solve_eqs_bounded` and
   `elim_unconstrained` run on **every default quantifier-free `check_sat`**
   (`auto.rs:2172-2185`, gated by `config.preprocess`, default `true`).
   The doc never states the default pipeline or its order.
5. **Eight of the sixteen files are unmentioned**: `inverter.rs` (1,334 lines,
   the plugin registry that makes `elim_unconstrained` extensible), `alpha.rs`
   (942), `int_divmod.rs` (842), `lower_bv.rs` (657), `int_blast.rs` (634),
   `pass_stats.rs` (345), `datatypes.rs` (147), and `solve_eqs.rs`/
   `propagate_values.rs` appear only inside a list of things that are *not*
   default.
6. **Line 57-59**, the `unsat` obligation, predates ADR-1721 (2026-09-06),
   which replaced "the proof must justify the transformation" with a three-way
   classification (replacement / relaxation / strengthening) and the rule that a
   *decline* is a legal discharge while a *re-derivation* is not. The doc should
   cite it.

### `docs/internals/term-ir.md` (110 lines, touched 2026-09-05)

Mostly current; two contradictions, both about the same landing.

1. **Line 48-50**: *"Integer values are exact within the current `i128`
   reference range, and out-of-range integer evaluation is an explicit
   `ArithmeticOverflow`, never wrapped arithmetic."* Contradicted by
   `Value::WideInt` (`value.rs:39-47`) and `TermNode::WideIntConst`
   (`term.rs:364-372`). The evaluator has a wide-integer detour that computes
   exactly in `BigInt` and demotes (`eval.rs:554-560`); only an operator outside
   `supports_wide_int_path` declines, and it declines with
   `IrError::Unsupported`, not `ArithmeticOverflow` (`eval.rs:561-563`).
2. **Line 77-78**: *"Raising the same ceiling for `Value::Int` and the SMT-LIB
   integer-literal parser is ADR-1702's slice 2, and is not landed."* It has
   landed. `value.rs:39-40` and `term.rs:364-365` both name "ADR-1702 slice 2",
   `TermArena::int_const_big` exists (`arena.rs:1755`), and the SMT-LIB literal
   path calls it (`parse.rs:16055-16060`).

Otherwise accurate: the hash-consing description matches `arena.rs:262-271`, the
user/internal symbol namespace split matches `arena.rs:28-39`, and the LSB-first
convention matches `bits.rs:18`.

### `docs/internals/evaluator.md` (68 lines, touched 2026-09-05)

One contradiction, the same one.

1. **Line 31-34**: *"Concrete `Int` values are `i128`-based, and integer
   arithmetic outside that reference range returns
   `IrError::ArithmeticOverflow`; a solver route must decline …"* Contradicted
   by `eval.rs:548-564`, which routes any `Value::WideInt` operand to
   `apply_wide_int` for the listed operators and returns
   `IrError::Unsupported("integer operand outside the i128 reference range")`
   otherwise. The comment at `eval.rs:548-553` says this guard exists precisely
   because the old behaviour would **panic** on a parsed `2^256` literal.

The five-step replay list (lines 46-52) matches what
`auto.rs:2299-2323` and `preprocess.rs:177-228` actually do, including the
reverse trail replay at step 4.

### `docs/reference/smtlib-support.md` (72 lines, last content change 2026-08-07)

Structurally sound — it correctly defers to the generated conformance matrix and
correctly says `set-logic` is recorded metadata with dispatch by term shape
(line 52, matching `auto.rs:1679`). Two drifts:

1. **Line 47-48**: *"These helpers parse a complete input string and return Rust
   data. They do not emit an ordered SMT-LIB stdout transcript."* Understated.
   `solve_smtlib_session` (`smtlib.rs:3318`) returns an ordered
   `Vec<SmtLibResponse>` including `Echo`, `Unsupported` and per-`check-sat`
   verdicts, honours `set-option` (`smtlib.rs:3543`) and `set-logic`
   (`smtlib.rs:3530`), and its doc comment enumerates three named divergences
   from `z3 file.smt2` (`smtlib.rs:3296-3309`). It is a response *stream*, not
   stdout text — but that is a much smaller gap than the sentence implies.
2. **`solve_smtlib_session` is missing from the front-door table** (lines 35-45),
   which lists nine other entry points. Relatedly, line 27-29 calls the ordered
   session semantics "executable planning evidence, not the current production
   runner"; `solve_smtlib_incremental` is now implemented *as* that walk with
   `SessionPolicy::VerdictsOnly` (`smtlib.rs:3292-3294`), so the prototype and
   the production runner are the same code.

## Gaps and open questions

1. **Why two preprocessing pipelines?** `auto::preprocess_reduce` (one round;
   carries function interpretations AND `real_div_zeros`) and
   `preprocess::check_with_preprocessing_impl` (up to 8 rounds; carries
   `real_div_zeros`, no function carry) implement the same five steps. Neither
   file references the other's round count. **Corrected 2026-09-09:** the
   original text here said `auto.rs` had "no `real_div_zeros` carry" — it does,
   at `:2344`. ANSWERED by ADR-1811, which keeps `preprocess.rs` as the one home
   and lands the merge at cap 1, because `reduction_shrinks_encoding`'s
   calibration rows were measured against a one-round reduction.
2. **`pass_stats.rs` has no consumer.** The module exists to answer "did this
   pass shrink or blow up the shared DAG" and nothing asks. Either a bench
   should call it or it should go; a 345-line module whose only exercise is its
   own five unit tests is a maintenance liability, not an instrument.
3. **`algebraic_bridge.rs` (343 lines) implements a trait nobody consumes.** The
   `AlgebraicNumber` trait exists only in `axeyum-arith/src/lib.rs:1212` and
   these two impls. ADR-1710 §5 is cited as the motivation. Confirming true
   dead-ness would need a check that no generic function in `axeyum-cas` is
   bounded on it — my grep for `AlgebraicNumber` found none, but a re-export
   under a different name would evade that.
4. **How much of `parse.rs` is parsing?** 23,668 lines in one file, with at
   least seventeen `Script` fields that are analysis products rather than parse
   products, and two parse-time verdicts. I did not partition the file by
   function, so I cannot say what fraction is the SMT-LIB grammar and what
   fraction is the source-level string/FP route machinery. A function-level
   line census would settle it and would be the first input to any split.
5. **Whether the ignored `!`-attributes matter.** `:qid` and `:weight` are
   hints, so skipping them is harmless. `:no-pattern` is not a hint — it
   *suppresses* trigger inference — and skipping it can make the e-matcher fire
   on a pattern the author excluded. I found no handling of `:no-pattern`
   anywhere (searched the literal across `crates/`). Whether any corpus file
   uses it, and whether firing an excluded pattern can affect a verdict rather
   than only performance, I could not determine from source.
6. **`axeyum-query`'s intended future.** ADR-0005 accepted it as a Phase 3
   contract boundary, and `Query`/`QueryPlan` are well built (slicing, replay
   failures, structural cache keys), but the shipped text front door does not
   use them. Whether the plan is to route the front door through `Query` or to
   retire the crate is not recorded in any ADR I found.
7. **`solve_eqs`'s unbounded wrapper and `default_inverters`** are two-to-three
   line public aliases with no callers. Harmless, but they are the shape that
   makes a name search return a false positive for "this capability is used".

## ADRs cited

Each was confirmed to resolve to a file in `docs/research/09-decisions/`:
ADR-0005 (Phase 3 query, evidence, and rewrite contracts), ADR-0009
(incremental SAT and solving), ADR-0010 (arrays via eager elimination to QF_BV),
ADR-0013 (uninterpreted functions), ADR-0014 (first arithmetic fragment),
ADR-0022 (first-class datatype sort), ADR-0029 (SMT-LIB string front end),
ADR-0037 (destination-2 reduction over custom core), ADR-1721 (a preprocessing
step owes one of three obligations), ADR-1730 (int div/mod's congruence cap is a
relaxation), ADR-1760 (the front door carries route attribution). ADR-1702 and
ADR-1710 are cited in source comments and referenced above; ADR-0038 likewise.

The author-side view of this pipeline is
[`docs/contributor-guide/adding-an-operator.md`](../contributor-guide/adding-an-operator.md)
(176 lines, nine numbered steps from scope through validation), and
[`docs/contributor-guide/adding-a-rewrite.md`](../contributor-guide/adding-a-rewrite.md)
for a manifest rule. Both exist and both are linked from
`docs/internals/rewriting.md`.
