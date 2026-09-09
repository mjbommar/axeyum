# Solver facade, dispatch, routing, and backends — inventory (2026-09-09)

Scope: the spine that decides which engine runs. Covered paths, all under
`crates/axeyum-solver/`: `src/solver.rs`, `auto.rs`, `strategy.rs`,
`portfolio.rs`, `layers.rs`, `route_trace.rs`, `config_registry.rs`,
`backend.rs`, `capabilities.rs`, `support_matrix.rs`, `combined.rs`,
`combined_theory.rs`, `combined_theory_lia.rs`, `theory_combination.rs`,
`incremental.rs`, `memory_budget.rs`, `live_instruments.rs`, `span_log.rs`,
`lazy_smt_counters.rs`, `error.rs`, `smtlib.rs`, `lib.rs`, `sat_bv_backend.rs`,
`z3_backend.rs`, `lra_route.rs`, and the dispatch-relevant part of `trust.rs`
(lane L8 owns the trust ledger itself). Theory internals belong to lanes L4–L7;
this file names the modules routed to and stops there. Base commit `ea8515407`.

**Feature baseline.** `crates/axeyum-solver/src/lib.rs:70` opens
`macro_rules! full_modules` under `#[cfg(feature = "full")]`; it is invoked at
`lib.rs:251-252`. Roughly 200 modules live inside it, including every file in
this lane's scope except `backend.rs`, `config_registry.rs`, `error.rs`,
`incremental.rs`, `layers.rs`, `lazy_smt_counters.rs`, `live_instruments.rs`,
`memory_budget.rs`, `portfolio.rs`, `sat_bv_backend.rs` and `model.rs`/`proof.rs`
(`lib.rs:48-69`). **`full` is therefore the assumed baseline for every table
below and is not repeated per row.** The `FEATURE-GATED` label is reserved for
gates that are *not* `full`: `z3` (`lib.rs:246-247`, nested inside the macro
body), `bench-internals` (`lib.rs:269-274`), `batsat-reference`. What a
default-profile build can and cannot do is stated once in
[Default-profile build](#default-profile-build).

## Summary

- **The dispatcher is shape-driven, not logic-name-driven.** Route selection
  reads an 11-field boolean `Features` scan of the term DAG
  (`auto.rs:9422-9452`); `(set-logic …)` is parsed and recorded but nothing is
  enforced on it (`smtlib.rs:3339-3341`). There is no route-selection field in
  `SolverConfig` (20 fields, `backend.rs:97-299`) — confirmed by
  `crates/axeyum-bench/examples/route_solo.rs:5-7`, which exists precisely
  because "`SolverConfig` has no route-selection knob".
- **Three nested front doors, in this order:** `solve_smtlib`
  (`smtlib.rs:1972`, 14 front-door stages) → `solve` (`auto.rs:492`, the
  quantified ladder) → `check_auto` (`auto.rs:1110`) →
  `check_auto_with_recorder` (`auto.rs:1665`) → `check_auto_inner`
  (`auto.rs:2353`) → `check_auto_dispatch` (`auto.rs:4529`) → sub-dispatchers.
- **51 distinct route labels** appear in the quantifier-free dispatcher's trace
  vocabulary (49 literal `record_*` names in `auto.rs` plus
  `ufbv-online-cdclt`/`aufbv-online-cdclt` built from a variable at
  `auto.rs:3932-3936`), plus 14 front-door stage constants
  (`route_trace.rs:683-717`) and 8 quantified-ladder stages that are traced
  **only** to stderr (`auto.rs` `qtrace`, see the finding below).
- **The quantified ladder is invisible to `RouteTrace`.** Lines 492–1108 of
  `auto.rs` contain no `RouteTrace`/`Recorder`/`record_*` reference; the eleven
  quantified rungs report through `qtrace` (`auto.rs:233-241`), an
  `AXEYUM_QTRACE`-gated `eprintln!`. A quantified file's route attribution
  therefore names whichever *quantifier-free* sub-route the ladder happened to
  reach.
- **`Solver<B>` is not the dispatcher and never has been.** `Solver::check`
  (`solver.rs:161-163`) calls `self.backend.check(...)` directly; push/pop are a
  `Vec` watermark (`solver.rs:126-142`) and `check_assuming` concatenates
  assumptions onto assertions (`solver.rs:550-562`). Reaching the ladder from
  the facade requires `Solver::check_auto_explained` (`solver.rs:213-218`).
  `solver.rs` was last touched 2026-06-27; `auto.rs` on 2026-09-09.
- **Both "supported logics" declarations are hand-written literals and neither
  is read at solve time.** `SUPPORT_MATRIX` is a 19-row `const` slice
  (`support_matrix.rs:177`); `CAPABILITIES` is a 105-row `const` slice
  (`capabilities.rs:144`). `auto.rs` and `smtlib.rs` contain **zero**
  occurrences of either identifier.
- **The parallel portfolio is off by default.**
  `DEFAULT_INT_LINEAR_PORTFOLIO_WORKERS = 1` (`auto.rs:2948`); at 1 worker
  `dispatch_int_linear_refuters` does not even construct a group
  (`auto.rs:2870`). Threads appear only under `AXEYUM_PORTFOLIO_WORKERS >= 2`,
  over exactly one hard-coded two-arm group (`auto.rs:3023-3032`).
- **`unknown` is produced at 40+ sites and is structurally distinguishable from
  "no route matched" only through the route trace**, not through the
  `CheckResult` value. See [Unknown handling](#unknown-handling).
- **Z3 is clean under ADR-0002.** `grep -n "z3" crates/axeyum-solver/src/auto.rs`
  returns zero hits: there is no Z3 arm in the dispatcher, gated or otherwise.
  The default build pulls no C/C++ dependency (`qfbv = []`).
- **Four `theory_combination.rs` public functions have no caller in the
  workspace** outside their own module and the `lib.rs` re-export. See
  [Reachability tally](#reachability-tally).
- The ladder-budget policy type `LadderSlice` (`auto.rs:1955-2050`) was written
  to delete a "share rounds to zero ⇒ hand the route the whole budget" branch.
  That exact branch still exists at `dpll_lia.rs:617` in
  `online_lia_probe_config`. The policy is not applied uniformly.

## The dispatch decision tree

This is the centerpiece. Read it as: the first predicate that holds and whose
route returns a decided verdict wins; everything else falls through. Every stage
below is cited.

### Stage 0 — the SMT-LIB text front door (`solve_smtlib`)

`solve_smtlib` (`smtlib.rs:1954`) is a projection of `solve_smtlib_with_model`
(`smtlib.rs:1972`), which takes **one deadline for the whole call**
(`smtlib.rs:1977-1979`) and calls `solve_smtlib_at_string_bound`
(`smtlib.rs:2139`) at `DEFAULT_STRING_BOUND = 12` (`smtlib.rs:1985`), then
`apply_string_bound_ladder`.

| # | Predicate | Action | Site |
|---|---|---|---|
| 0.1 | always | parse at `string_bound`, sharing the caller's budget | `smtlib.rs:2170-2172` |
| 0.2 | `SmtError::DeadlineExceeded` / `ResourceLimit` from parse | return `Unknown(ResourceLimit)` — **parse failure is not an error** | `smtlib.rs:2194-2211` |
| 0.3 | any other parse error | `Err(SolverError::Parse)` | `smtlib.rs:2212` |
| 0.4 | `script.word_only_fallback.is_some()` | `decide_word_only`, return | `smtlib.rs:2216-2220` |
| 0.5 | `source_fp_prefix_monotonic_result` matches | return | `smtlib.rs:2221-2224` |
| 0.6 | `prefer_source_string_routes \|\| !word_skeleton.is_empty()` | source string ladder gets first refusal, return on a verdict | `smtlib.rs:2231-2237` |
| 0.7 | otherwise | `solve(&mut script.arena, &query.assertions, config)` — **this is where Stage 1 begins** | `smtlib.rs:2243` |
| 0.8 | result undecided | `StringGate::confirm` | `smtlib.rs:2245-2249` |
| 0.9 | undecided | `apply_source_string_semantic_unsat` | `smtlib.rs:2251-2255` |
| 0.10 | undecided **and** `!source_string_routes_tried` | `apply_word_route` | `smtlib.rs:2258-2268` |
| 0.11 | same guard | `apply_online_string_route` | `smtlib.rs:2273-2283` |
| 0.12 | same guard | `apply_membership_route` | `smtlib.rs:2288-2297` |
| 0.13 | undecided (no source-route guard) | `apply_lex_order_route` | `smtlib.rs:2303-2308` |
| 0.14 | undecided **and** `!source_string_routes_tried` | `apply_length_lia_route` | `smtlib.rs:2313-2323` |
| 0.15 | undecided | `apply_source_string_sat_problem` (bounded concrete witness probe) | `smtlib.rs:2330-2334` |
| 0.16 | undecided **and** reason contains `"no model within the bounded integer width"` **and** `is_bounded_complete(input)` | upgrade `Unknown` → `Unsat` | `smtlib.rs:2348-2352`, predicate at `smtlib.rs:2364-2377` |
| 0.17 | result is the bounded-string-window `Unknown` | re-parse at wider string bounds, accept **only `Sat`** | `apply_string_bound_ladder`, `smtlib.rs:2044-2071` |

Every stage from 0.8 down may only turn an `unknown` into a verdict
(`front_door_undecided`, `smtlib.rs:2094-2105`); a decided verdict is never
overturned. Attribution is recorded per stage under the constants at
`route_trace.rs:683-717`.

### Stage 1 — `solve`: the quantified ladder (`auto.rs:492`)

| # | Predicate | Action / route | Site |
|---|---|---|---|
| 1.0 | `memory_limit_mb` already exceeded | `Unknown(MemoryLimit)`, return | `auto.rs:501-503` |
| 1.1 | always | arm `MemoryWatchdog` for the whole call | `auto.rs:509` |
| 1.2 | `has_quantifier` **and** a ground subset already refutes | `Unsat` | `auto.rs:511-513` |
| 1.3 | quantified | `checked_quantified_fast_path`: canonicalization-discharge, guard vacuity, BV model-sat, Bool model-sat, then five certificate searches (`bv_alternation`, `vacuous_exists`, `bv_paired_exists`, `negated_exists`, `bv_conjunctive`) — any hit ⇒ `Unsat` | `auto.rs:53-104` |
| 1.4 | deadline passed | `Unknown(ResourceLimit)` | `auto.rs:515-517` |
| 1.5 | always | `normalize_top_level_quantified_counterexamples`, then `skolemize_top_existentials` | `auto.rs:527`, `auto.rs:533` |
| 1.6 | `config.lazy_bv && !has_quantifier` | `lazy_bv::solve_lazy_bv_abstraction`, return | `auto.rs:541-544` |
| 1.7 | **`!has_quantifier`** | `check_auto` (**Stage 2**), then `certify_skolemized_negated_universals` | `auto.rs:546-556` |
| 1.8 | quantified | `quant_valid_universal::eliminate_valid_universals`; if all universals gone ⇒ `check_auto` | `auto.rs:571-585` |
| 1.9 | quantified | `quant_vacuous_universal::eliminate_vacuous_universals`; if QF now ⇒ `check_auto` | `auto.rs:596-603` |
| 1.10 | quantified | `quant_eq_partition_search::equality_partition_refutation` ⇒ `Unsat` | `auto.rs:610-613` |
| 1.11 | quantified | `quant_unsat_universal::detect_unsatisfiable_universal` ⇒ `Unsat` | `auto.rs:626-628` |
| 1.12 | quantified | Fourier–Motzkin chain, in order: `eliminate_real_universal` → `eliminate_int_universal_closed` → `eliminate_int_universal_valid` → `eliminate_int_universal_open_gap`. `Unsat` returns; `Rewrite` re-dispatches to `check_auto` when the residual is QF | `auto.rs:651-696` |
| 1.13 | quantified | `finish_quantified_solve_or_induct` (**Stage 1b**) | `auto.rs:709` |

### Stage 1b — `finish_quantified_solve` (`auto.rs:297`)

Order, each rung sharing the one deadline via `config_with_remaining_timeout`:

1. `quant_exists_witness::decide_forall_exists_by_witness` — `auto.rs:308-318`
2. `check_with_quantifiers` (finite-domain expansion) — `auto.rs:324`
3. on unknown/unsupported: `uf_fmf::find_uf_finite_model` **probe** on half the
   remaining budget, on a throwaway `arena.clone()` — `auto.rs:352-368`
4. `mbqi_first_refusal` (1/8 of the remaining budget) — `auto.rs:388-391`
5. `run_egraph_quantified_fallback` (e-matching, full remaining slice) — `auto.rs:392-400`
6. `prove_unsat_by_mbqi` — `auto.rs:406`
7. `uf_fmf::find_uf_finite_model` **full** — `auto.rs:427-437`
8. `nat_induction::prove_by_nat_induction`, last rung — `auto.rs:751` onward

None of these eight rungs records into `RouteTrace`; they emit `qtrace` lines
(`egraph`, `finite-expansion`, `forall-exists-witness`, `mbqi`, `mbqi-quick`,
`nat-induction`, `uf-fmf-full`, `uf-fmf-probe`).

### Stage 2 — `check_auto` (`auto.rs:1110`)

| # | Predicate | Action | Site |
|---|---|---|---|
| 2.0 | memory budget exceeded at entry | `Unknown`, return — deliberately placed **above** the attribution branch so both paths decline identically | `auto.rs:1144-1146` |
| 2.1 | a `RouteAttributionGuard` is live **and** this is the outermost dispatch | delegate to `check_auto_explained` and publish its trace | `auto.rs:1152-1164` |
| 2.2 | otherwise | `check_auto_with_recorder(.., &mut None)` (**Stage 3**) | `auto.rs:1176` |
| 2.3 | result is `Unknown` | `nra_real_root::integer_algebraic_refutation` ⇒ `Unsat` | `auto.rs:1179-1181` |
| 2.4 | still `Unknown` | `try_conjunct_refutation` (≥2 and ≤64 top conjuncts, half the budget split across them) | `auto.rs:1182-1184`, `auto.rs:1244-1265` |
| 2.5 | still `Unknown` | `try_disjunct_refutation` | `auto.rs:1185-1187` |
| 2.6 | still `Unknown` | `try_finite_domain_split` | `auto.rs:1188-1190` |

All four fallbacks are clamped to `fallback_deadline` taken at entry
(`auto.rs:1218-1223`) — a fix for rungs that previously each awarded themselves
a fresh full budget (one file measured at 400 s against a 24 s request).

### Stage 3 — `check_auto_with_recorder` (`auto.rs:1665`)

| # | Predicate | Route | Site |
|---|---|---|---|
| 3.0 | quantifier scan times out | `Unknown(Timeout)` | `auto.rs:1673-1677` |
| 3.1 | `Features::scan_within` times out | `Unknown(Timeout)` | `auto.rs:1678-1682` |
| 3.2 | always | record the `fragment {…}` probe entry | `auto.rs:1683`, `record_probe` at `auto.rs:1823` |
| 3.3 | `features.has_wide_int` | `wide-int-admission` decline — **no route has opted into `>i128` literals** (ADR-1702 slice 2) | `auto.rs:1684-1686`, `auto.rs:1638-1650` |
| 3.4 | `term_identity_refutation` matches | `term-identity-refuter` ⇒ `Unsat` | `auto.rs:1687-1692` |
| 3.5 | always | `dispatch_cas_refuters` → `cas-identity-refuter`, `cas-int-units` | `auto.rs:1693-1695`, `auto.rs:5119` |
| 3.6 | `has_array` | `array_fifo::fifo_ia04_sat_model` ⇒ `Sat` | `auto.rs:1696-1703` |
| 3.7 | `has_array` | `dispatch_array_unsat_refuters` (six sub-refuters, 250 ms slice) | `auto.rs:1704-1710`, `auto.rs:5439-5489` |
| 3.8 | `has_int && !quant && !contains_smtlib_unspecified_arith` | `int-box-eval` | `auto.rs:1711-1718` |
| 3.9 | `has_int && !quant && has_nonlinear_int_product` | early `try_finite_domain_split` | `auto.rs:1729-1743` |
| 3.10 | `config.preprocess && !has_quantifier` | `preprocess_reduce`; adopt only if `reduction_shrinks_encoding`, else dispatch the original; any error degrades to `check_auto_inner` on the unreduced query | `auto.rs:1754-1806` |
| 3.11 | otherwise | `check_auto_inner` (**Stage 4**) | `auto.rs:1808` |

`config.preprocess` defaults to **`true`** (`backend.rs:392`), so 3.10 is the
normal path for a quantifier-free query.

### Stage 4 — `check_auto_inner` (`auto.rs:2353`)

| # | Predicate | Route | Site |
|---|---|---|---|
| 4.1 | `nra_even_power_refutation` matches | `nra-even-power` ⇒ `Unsat` | `auto.rs:2370-2373` |
| 4.2 | always | `fold_to_real_sums`, `eliminate_to_real_const_compare`, `eliminate_to_int_const_compare` | `auto.rs:2381-2385` |
| 4.3 | **no int↔real coercion remains** | `check_auto_dispatch` (**Stage 5**), return | `auto.rs:2394-2405` |
| 4.4 | a coercion remains | `check_with_milp` — mixed-integer branch-and-bound, `MAX_MILP_NODES = 2_000` | `auto.rs:2413-2434`, `auto.rs:2469` |
| 4.5 | MILP declined | `check_auto_dispatch` on the **relaxed** query; a `Sat` is accepted only if it replays against the *original* coupling, else `Unknown(Incomplete)` | `auto.rs:2441-2464` |

### Stage 5 — `check_auto_dispatch` (`auto.rs:4529`), the theory ladder

This is the ordered core. `lift_arith_ite` runs first (`auto.rs:4540`), then a
second `Features::scan_within` on the lifted terms (`auto.rs:4543`).

| # | Guard | Route(s) tried, in order | Site |
|---|---|---|---|
| 5.1 | `features.has_datatype` | `datatype-acyclicity` ⇒ `Unsat`; then `datatype-elim`; on `Unsupported` → `datatype-native`. **Returns unconditionally** — a datatype query never reaches any later stage | `auto.rs:4560-4591` |
| 5.2 | unguarded | `dispatch_difference_logic` → `dl-online`. Budget: `all_but_capped_reserve(1/4, cap 6 s)` (`DL_PROBE_SLICE`, `auto.rs:4502`). A `Sat`/`Unsat` returns; `Unknown` falls through | `auto.rs:4592-4594`, `auto.rs:4424-4466` |
| 5.3 | `has_real && has_int` | `lira-dpll` (`check_with_arith_dpll`); `Unsupported` falls through | `auto.rs:4595-4612` |
| 5.4 | `has_real` | `dispatch_uf_nra` → `uf-nra` | `auto.rs:4613-4624` |
| 5.5 | `has_real && has_nonlinear_real` | `nra-real-root` (`decide_real_poly_constraint`). A `Some(Unknown)` is **terminal for the real branch** except that `dispatch_cas_ideal` gets one chance first | `auto.rs:4638-4666` |
| 5.6 | `has_real` | `dispatch_cas_ideal` → `cas-ideal-refuter` | `auto.rs:4672-4674` |
| 5.7 | `has_real` | `nra::check_with_nra`; `Unsupported` falls through **only when `features.has_function`** — otherwise the error propagates | `auto.rs:4693-4707` |
| 5.8 | unguarded | `dispatch_arith_uf_overbound_probe_before_lia` → `uf-arith-lazy-overbound-pre-lia`. Guards: `has_int && !has_real && !has_array && has_function && has_arithmetic_function`, and `ackermann_congruence_pairs > MAX_ACKERMANN_CONGRUENCE_PAIRS` | `auto.rs:4708-4712`, `auto.rs:3146-3182` |
| 5.9 | `has_int && has_bv_or_float && !has_function && !has_array && !has_uninterpreted_sort && !has_datatype` | `bv2nat-blast` (exact rewrite to pure BV, replay-checked) | `auto.rs:4718-4772` |
| 5.10 | `has_int` | `dispatch_int_linear_refuters` (**Stage 5a**) | `auto.rs:4785-4793` |
| 5.11 | `has_function \|\| has_uninterpreted_sort` | `dispatch_uf_routes` (**Stage 5b**) | `auto.rs:4799-4801`, `auto.rs:5076` |
| 5.12 | `has_array` | `dispatch_abv_online` → `abv-online-cdclt`, budget `all_but_reserve(1/4)` (`ABV_ONLINE_SLICE`, `auto.rs:4941`) | `auto.rs:4803-4807` |
| 5.13 | `has_array` | `dispatch_array_fast_paths` → QF_ALIA/QF_AUFLIA lazy ROW, QF_AX declared-sort lazy ROW, or `dispatch_pure_qf_abv` | `auto.rs:4830-4838`, `auto.rs:5491-5528` |
| 5.14 | `has_array && has_non_bv_array` | `Unknown(Incomplete)` — terminal for non-BV array shapes | `auto.rs:4841-4847` |
| 5.15 | `has_int` | `dispatch_nonlinear_int_tail` (**Stage 5c**), **returns unconditionally** | `auto.rs:4850-4852` |
| 5.16 | fallback | `check_with_all_theories(SatBvBackend, …, DEFAULT_INT_WIDTH)` → `qf-bv`. Two `Err` arms are converted to honest `Unknown`: uninterpreted-sort (`qf-bv-uninterpreted-decline`) and array (`qf-abv-array-decline`) | `auto.rs:4854-4899` |

### Stage 5a — `dispatch_int_linear_refuters` (`auto.rs:2788`)

1. `refute_bv2nat_out_of_range` ⇒ `bv2nat-range` `Unsat` — `auto.rs:2799-2802`
2. `axeyum_rewrite::eliminate_int_divmod` (equisatisfiable), congruence-group
   count retained for `guard_zero_divisor_sat` — `auto.rs:2809-2818`
3. `lia_gcd::prove_lia_unsat_by_diophantine` ⇒ `lia-diophantine` — `auto.rs:2822`
4. `check_with_lia_simplex_within` ⇒ `lia-simplex` — `auto.rs:2830-2837`
5. `should_route_uf_arith_before_lia_dpll` ⇒ record a `lia-dpll` decline and
   return `None` so the UF ladder gets the query — `auto.rs:2845-2860`
6. `int_linear_portfolio_workers() > 1` ⇒ `run_int_linear_group` (two arms,
   `lia-dpll` weight 3 and `int-blast-ladder` weight 1) — `auto.rs:2870-2896`
7. otherwise `check_with_lia_dpll` sequentially ⇒ `lia-dpll` — `auto.rs:2904-2907`

A `lia-dpll` `Unknown` that is *not* a budget kind and `features.has_function`
returns `Ok(None)`, handing the query to the UF ladder (`auto.rs:2925-2929`).

### Stage 5b — `dispatch_uf_routes` (`auto.rs:5076`) and `dispatch_uf_fast_paths` (`auto.rs:3695`)

1. `uf-finite-domain-pigeonhole` — `auto.rs:5092-5103`
2. `dispatch_uf_arith_overbound` → `uf-arith-lazy-overbound`; what happens to its
   `Unknown` is a **policy**, `UfArithOverboundPolicy` (`auto.rs:3260`), selected
   by `AXEYUM_UF_ARITH_OVERBOUND` ∈ {`terminal`,`probe`,`skip`}, default
   `CegarProbe` with reserve `1/4` (`UF_ARITH_LADDER_RESERVE_SHARE`,
   `auto.rs:3318`) — `auto.rs:3744-3747`
3. `lift_uninterpreted_sort_ite` for pure-UF only — `auto.rs:3752-3760`
4. `euf-online` (`check_qf_uf_online_cdclt`) — `auto.rs:3779-3793`
5. `dispatch_ufbv_online` → `ufbv-online-cdclt` or `aufbv-online-cdclt`
   (guard at `auto.rs:3922-3931`) — `auto.rs:3802`
6. `euf-offline` (`check_qf_uf_with_config`) — `auto.rs:3806-3821`
7. `has_int && has_uninterpreted_sort && !has_function` ⇒ `uf-arith-online` — `auto.rs:3829-3836`
8. `has_function && has_arithmetic_function` ⇒ `uf-arith-online` first, then the
   eager `uf-arithmetic` combination. A `Real`-sorted UF `Unknown` is terminal
   (`auto.rs:3874-3880`); a *budget* `Unknown` on non-array integer UF is
   terminal (`auto.rs:3884-3894`); a *logical* `Unknown` falls through — `auto.rs:3838-3901`
9. `dispatch_declared_sort_ufbv_lazy` → `ufbv-declared-sort-lazy` — `auto.rs:3903-3907`

### Stage 5c — `dispatch_nonlinear_int_tail` (`auto.rs:5286`)

1. `nia-square` (`decide_int_square_constraint_explained`) — `auto.rs:5306-5311`
2. `int-real-relax` (`refute_int_via_real_relaxation`), budget `1/6` of the
   remaining deadline (`int_real_relax_budget`, `auto.rs:5279`) — `auto.rs:5355-5372`
3. `nia-linearize` (`check_with_nia`) — `auto.rs:5386-5395`
4. `nia-bounded-blast` (`decide_bounded_int_blast_explained`) — `auto.rs:5404-5414`
5. `dispatch_cas_ideal` → `cas-ideal-refuter` — `auto.rs:5419-5421`
6. `int-blast-ladder` (`dispatch_int_blast_width_ladder`, `auto.rs:7202`) —
   terminal — `auto.rs:5426-5429`

### The features the tree branches on

`Features` (`auto.rs:9422-9452`) is 11 booleans, all derived by scanning the term
DAG within a deadline (`Features::scan_within`, `auto.rs:9455`): `has_real`,
`has_bitblast`, `has_int`, `has_bv_or_float`, `has_datatype`, `has_function`
(an actual `Op::Apply`, not a declaration), `has_uninterpreted_sort`,
`has_array`, `has_non_bv_array`, `has_non_bool_bv_array`, `has_wide_int`. It is
scanned **twice** per dispatch — once at `auto.rs:1678` and again after
`lift_arith_ite` at `auto.rs:4543`.

## Route inventory

`full` is the baseline; only non-`full` gates are called out. Trace-recorded
routes are the ones a `RouteTrace` can name.

### Quantifier-free dispatcher routes (`auto.rs`)

| Route label | Trigger | Target module | Reach |
|---|---|---|---|
| `wide-int-admission` | `features.has_wide_int` | — (declines) | WIRED `auto.rs:1684` |
| `term-identity-refuter` | unguarded | `term_identity` | WIRED `auto.rs:1688` |
| `cas-identity-refuter` | CAS candidate shape | `cas_poly` / `cas_certificate` | WIRED `auto.rs:5133` |
| `cas-int-units` | CAS candidate shape | `cas_poly` | WIRED `auto.rs:5158` |
| `cas-ideal-refuter` | real branch, and int tail | `cas_poly` | WIRED `auto.rs:4673`, `auto.rs:5207`, `auto.rs:5420` |
| `fifo-ia04-sat-witness` | `has_array` | `array_fifo` | WIRED `auto.rs:1698` |
| `array-unsat-refuter` | `has_array` | `abv`, `array_finite`, `euf_egraph` | WIRED `auto.rs:1708` |
| `int-box-eval` | `has_int && !quant` | in-module `decide_int_box_by_evaluation` | WIRED `auto.rs:1716` |
| `finite-domain-split` | nonlinear int product; also post-dispatch | in-module | WIRED `auto.rs:1739`, `auto.rs:1589` |
| `preprocess` | `config.preprocess` | `preprocess`, `axeyum_rewrite` | WIRED `auto.rs:1801` |
| `nra-even-power` | unguarded (inner) | `nra_even_power` | WIRED `auto.rs:2371` |
| `milp` | int↔real coercion present | in-module branch-and-bound over `lra` | WIRED `auto.rs:2417` |
| `coercion-relax` | coercion present, dispatch returned `Sat` | in-module | WIRED `auto.rs:2448` |
| `feature-scan` | scan timed out | — | WIRED `auto.rs:4551` |
| `datatype-acyclicity` | `has_datatype` | `datatype_acyclicity` | WIRED `auto.rs:4567` |
| `datatype-elim` | `has_datatype` | `datatype_elim` | WIRED `auto.rs:4577` |
| `datatype-native` | `datatype-elim` returned `Unsupported` | `datatype_native` | WIRED `auto.rs:4586` |
| `dl-online` | unguarded | `dl_online` | WIRED `auto.rs:4451` |
| `dl-online-extended` | preregistered equality-heavy shape | `dl_online` | WIRED as a budget policy only (`auto.rs:4519`); **never recorded as a trace route** |
| `lira-dpll` | `has_real && has_int` | `dpll_lia` | WIRED `auto.rs:4602` |
| `uf-nra` | `has_real`, UF present | `nra` + `euf` | WIRED `auto.rs:4375` |
| `nra-real-root` | `has_real && has_nonlinear_real` | `nra_real_root` | WIRED `auto.rs:4663` |
| `nra` | `has_real` | `nra` | WIRED `auto.rs:4698` |
| `uf-arith-lazy-overbound-pre-lia` | over-bound int UF+arith, pre-LIA | `euf::try_lazy_arith_for_overbound` | WIRED `auto.rs:3222` |
| `bv2nat-blast` | int + BV, no UF/array/sort/datatype | `bv2nat_blast` | WIRED `auto.rs:4744` |
| `bv2nat-range` | `has_int` | `bv2nat_bound` | WIRED `auto.rs:2800` |
| `lia-diophantine` | `has_int` | `lia_gcd` | WIRED `auto.rs:2822` |
| `lia-simplex` | `has_int` | `lra::check_with_lia_simplex_within` | WIRED `auto.rs:2835` |
| `lia-dpll` | `has_int` | `dpll_lia` | WIRED `auto.rs:2920` |
| `int-blast-ladder` | int tail terminal; also portfolio arm 1 | in-module width ladder → `lia` | WIRED `auto.rs:5428`, `auto.rs:3031` |
| `uf-finite-domain-pigeonhole` | UF present | `ufbv_finite` | WIRED `auto.rs:5099` |
| `uf-arith-lazy-overbound` | over-bound UF+arith | `euf` | WIRED `auto.rs:3661` |
| `euf-online` | UF present | `euf_egraph` | WIRED `auto.rs:3782` |
| `ufbv-online-cdclt` | UF+BV, no int/real/sort/datatype/array | `ufbv_online` | WIRED `auto.rs:3932`+`3947` |
| `aufbv-online-cdclt` | same, with array | `ufbv_online` | WIRED `auto.rs:3931`+`3947` |
| `euf-offline` | UF present | `euf_egraph` | WIRED `auto.rs:3810` |
| `uf-arith-online` | UF+int/real | `uflia_online` / `uflra_online` | WIRED `auto.rs:4214` |
| `uf-arithmetic` | applied arithmetic UF | `uf_arith` / `euf` eager | WIRED `auto.rs:3864` |
| `ufbv-declared-sort-lazy` | declared-sort UF+BV | `ufbv_online` | WIRED `auto.rs:4012` |
| `abv-online-cdclt` | `has_array` | `abv` online | WIRED `auto.rs:5057` |
| `array-fast-path` | `has_array` | `abv` lazy ROW (four sub-routes under one label) | WIRED `auto.rs:4833` |
| `nia-square` | int tail | `nia_square` | WIRED `auto.rs:5309` |
| `int-real-relax` | int tail | `int_real_relax` | WIRED `auto.rs:5365` |
| `nia-linearize` | int tail | `nia_linearize` | WIRED `auto.rs:5392` |
| `nia-bounded-blast` | int tail | in-module bounded blast | WIRED `auto.rs:5411` |
| `qf-bv` | fallback | `combined::check_with_all_theories` + `SatBvBackend` | WIRED `auto.rs:4856` |
| `qf-bv-uninterpreted-decline` | `Err` + `has_uninterpreted_sort` | — | WIRED `auto.rs:4875` |
| `qf-abv-array-decline` | `Err` + `has_array` | — | WIRED `auto.rs:4893` |
| `integer-algebraic-refutation` | post-dispatch `Unknown` | `nra_real_root` | WIRED `auto.rs:1564` |
| `conjunct-refutation` | post-dispatch `Unknown` | recursive `check_auto` | WIRED `auto.rs:1569` |
| `disjunct-refutation` | post-dispatch `Unknown` | recursive `check_auto` | WIRED `auto.rs:1579` |
| `dispatch-early-exit` | trace invariant repair | — | WIRED `auto.rs:1607` |

Budget-policy route names that exist as `LadderSlice` constants but are **never
recorded as trace routes**: `mbqi-quick` (`auto.rs:4075`),
`qinst-egraph-retry` (`auto.rs:4083`), `ufbv-online-probe` (`auto.rs:4059`),
`dl-online-extended` (`auto.rs:4519`). A reader of a route trail will never see
these four names even though each governs a real budget decision.

### Front-door stages (`route_trace.rs:683-717`)

`fd:parse`, `fd:word-only-fallback`, `fd:source-fp-prefix`, `fd:source-string`,
`fd:dispatch`, `fd:string-gate`, `fd:source-string-semantic-unsat`,
`fd:word-route`, `fd:online-string`, `fd:membership`, `fd:lex-order`,
`fd:length-lia`, `fd:source-string-sat-probe`,
`fd:bounded-completeness-unsat` — 14 constants. All WIRED from
`solve_smtlib_at_string_bound` (`smtlib.rs:2185`–`2352`). `fd:dispatch`
(`route_trace.rs:698`) is recorded only when the inner dispatch produced no
attempts of its own.

### Strategies (`strategy.rs`)

| Strategy | Trigger | Target | Reach |
|---|---|---|---|
| `EagerPureRust` | default | `auto::solve` | `strategy.rs:108` |
| `LazyBvAbstraction` | explicit, or `Auto` + heavy ops | `lazy_bv` | `strategy.rs:109-111` |
| `Auto` | explicit | heavy ops ⇒ lazy, else eager with `preprocess(true)` | `strategy.rs:112-124` |
| `Oracle` | explicit | `z3_backend::Z3Backend`, `sat` replayed | **FEATURE-GATED (`z3`)** `strategy.rs:61-62`, `192-207` |

`solve_with_strategy` / `solve_with_portfolio` / `recommended_portfolio` are
**not called by any Rust route** in the workspace. Their only non-test callers
are the Python bindings (`crates/axeyum-py/src/solver/core.rs:230`, `:242-251`).
`recommended_portfolio` never returns `Strategy::Oracle` (`strategy.rs:182-188`).

### Reachability tally

| Class | Count | Examples |
|---|---|---|
| WIRED (reachable from `solve_smtlib` / `solve` / `check_auto`) | 51 QF trace routes + 14 front-door stages + 8 qtrace-only quantified rungs | table above |
| WIRED but runtime-dead at default settings | 1 | `portfolio::FusedGroup` — `auto.rs:2870` requires `AXEYUM_PORTFOLIO_WORKERS >= 2`, default 1 (`auto.rs:2948`) |
| Reachable only from bindings/tests, no Rust route | 3 | `strategy::solve_with_strategy`, `solve_with_portfolio`, `recommended_portfolio` |
| TEST-ONLY | 9 | `combined_theory::{combined_vs_cold_conjunction, combined_theory_propagations, combined_incremental_vs_check, combined_incremental_structure}` (only `tests/uflra_online.rs:749,845,976,1069`); the four `combined_theory_lia` analogues (`tests/uflia_online.rs:1042,1130,1243,1335`); `portfolio::groups_run` (only `tests/portfolio_fused_group.rs`) |
| **NO CALLER FOUND** | 4 | `theory_combination::{shared_terms, propose_interface_equalities, combination_conflict, interface_th_eqs}` |
| FEATURE-GATED, non-`full` | 3 | `z3_backend` (`z3`, `lib.rs:246-247`), `Strategy::Oracle` (`z3`, `strategy.rs:61`), `bench_internals` (`bench-internals`, `lib.rs:269-274`) |

**The NO CALLER FOUND search, stated exactly.** `grep -rn "\b<name>\b"
--include=*.rs .` over the whole tree, excluding `/target/`,
`crates/axeyum-solver/src/theory_combination.rs` (the definition) and
`crates/axeyum-solver/src/lib.rs` (two re-export blocks, `lib.rs:733-734` and
`lib.rs:1489-1490`), returns **zero lines** for
`propose_interface_equalities`, `combination_conflict` and `interface_th_eqs`,
and for `shared_terms` returns only six lines in
`crates/axeyum-solver/src/abduct.rs:306-337`, all of which are a *local
variable* of that name, not the function. Positive control: the same grep for
`classify_interface_equalities`, defined in the same module, finds real callers
at `uflra_online.rs:70`, `:613` and `:916`. `theory_combination.rs` was last
touched 2026-06-19.

## `unknown` handling

`unknown` is a first-class result (`backend.rs:12-15`), carried as
`CheckResult::Unknown(UnknownReason { kind, detail })` (`backend.rs:26-28`,
`backend.rs:32-39`). `UnknownKind` has seven variants (`backend.rs:42-60`):
`Timeout`, `ResourceLimit`, `MemoryLimit`, `NodeBudget`, `EncodingBudget`,
`Incomplete`, `Other`.

**Budget vs logical.** The dispatcher's one structural distinction is
`is_budget_unknown_kind` (`auto.rs:2100-2112`), which treats the five
resource kinds as "this route ran out of budget mid-decision" and `Incomplete`/
`Other` as "this route cannot do this shape". The consequence is a routing
decision, not just a label: a *budget* `Unknown` from `uf-arithmetic` on a
non-array integer query is returned verbatim rather than masked by a
strictly-less-capable fallback (`auto.rs:3884-3894`), and the same rule appears
at `auto.rs:3959-3963` (`ufbv-online-cdclt`) and `auto.rs:5568-5570`
(`dispatch_pure_qf_abv`).

**Can a caller tell "no route matched" from "a route ran and gave up"?**

- From the `CheckResult` alone: **no reliably**. Both surface as
  `Unknown(Incomplete, <free-text detail>)`. The only signal is the `detail`
  string, and it is prose — e.g. `"non-bit-vector array sorts are represented in
  IR, but this shape is outside the current Bool/Int lazy array route"`
  (`auto.rs:4843-4846`) versus `"int↔real coercion relaxation: candidate fails
  the original coupling"` (`auto.rs:2459-2461`). At least one consumer parses
  the detail text as a control predicate: `is_string_window_decline`
  (`smtlib.rs:2072-2090`) and `apply_bounded_completeness_unsat`, which tests
  `reason.detail.contains("no model within the bounded integer width")`
  (`smtlib.rs:2371-2373`) and can **upgrade an `Unknown` to `Unsat`** on that
  substring match.
- From `check_auto_explained` (`auto.rs:1548`): **yes.** Every attempt is
  recorded with a `RouteOutcome`, and `DeclineReason::NotApplicable` (a route
  whose guard failed) is a different variant from
  `DeclineReason::from_unknown(reason)` (a route that ran) and
  `DeclineReason::Unsupported` / `VerifierRejected`. A structural invariant is
  enforced at the boundary: an `Unknown` verdict whose trace contains no
  `Declined` entry gets a synthetic `dispatch-early-exit` decline appended
  (`auto.rs:1601-1609`). That invariant exists because the route-trace tests
  caught a probe-only trace twice on slow runners.
- Note the asymmetry: the *cheap* declines are deliberately silent.
  `dispatch_cas_refuters` records nothing when the route had no candidate shape
  at all (`CasOutcome::NoCandidate`, `auto.rs:5104-5117`), so "no route matched"
  for the CAS family leaves no trace row by design.

**`unknown` is never an error, and errors are converted to it in four places**:
`auto.rs:4858-4877` (uninterpreted sort not bit-blastable), `auto.rs:4879-4894`
(array shape refused by bounded elimination), `smtlib.rs:2194-2211` (parse
deadline/resource limit), and `auto.rs:751-800`'s swallowing of sub-query errors
in the induction rung.

## Backends

### The trait

`trait SolverBackend` (`backend.rs:647-691`) is three methods, two of them
defaulted:

| Method | Line | Default body |
|---|---|---|
| `capabilities(&self) -> Capabilities` | `backend.rs:649` | required |
| `check(&mut self, &TermArena, &[TermId], &SolverConfig) -> Result<CheckResult, SolverError>` | `backend.rs:659` | required |
| `check_query(&mut self, &TermArena, &Query, &SolverConfig)` | `backend.rs:675` | flattens `query.solver_terms()` and calls `check` (`backend.rs:681-682`) |
| `last_stats(&self) -> Option<&SolveStats>` | `backend.rs:688` | `None` |

### Implementors

| Type | Path | Gate | Reach |
|---|---|---|---|
| `SatBvBackend` | `sat_bv_backend.rs:580` | none — default profile | WIRED; constructed by `auto.rs` at 3993, 4735, 4853, 5563, 6672, 6689, 7250 |
| `Z3Backend` | `z3_backend.rs:76` | **FEATURE-GATED `z3`** (`lib.rs:246-247`) | oracle/differential only |
| `LazyBvBackend` | `lazy_bv.rs:373` | `full` | WIRED via `Strategy::LazyBvAbstraction` and `config.lazy_bv`; the struct itself is used by the bench (`axeyum-bench/src/main.rs:1971`) |
| `PblsBackend` | `pbls.rs:1309` | `full` | TEST-ONLY in-tree (`tests/differential_qfbv_backends.rs:202`); declares `complete: false` |
| `ArithDpllBackend` | `abv.rs:2159` | `full` | private adapter, used at `abv.rs:737` |
| `UfliaDpllBackend` | `abv.rs:2181` | `full` | private adapter, `abv.rs:757` |
| `DeclaredSortEufBackend` | `abv.rs:2209` | `full` | private adapter, `abv.rs:792` |
| `IncrementalBvBatchBackend`, `IncrementalBvRawProfileBackend`, `CheckAutoBackend` | `axeyum-bench/src/main.rs:1994`, `:2060`, `:2310` | bench binary | not in the library |

Worth flagging: `ArithDpllBackend`, `UfliaDpllBackend`, `DeclaredSortEufBackend`
and `LazyBvBackend` all report `complete: true` (`abv.rs:2163`, `:2185`,
`:2213`; `lazy_bv.rs:377`) while their routes can return `Unknown`. `Capabilities`
(`backend.rs:630-639`) is three fields — `name`, `produces_models`, `complete` —
and is a pass-through getter on the facade (`solver.rs:107-109`); nothing in the
dispatcher branches on it.

### The Z3 oracle under ADR-0002

`docs/research/09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md`
exists (accepted 2026-06-10). The code matches it:

- `grep -n "z3" crates/axeyum-solver/src/auto.rs` returns **zero hits**. There is
  no Z3 arm in the dispatcher, gated or otherwise.
- The module is gated at `lib.rs:246-247` and the re-export at `lib.rs:1541-1542`.
- The only production-shaped call site is `strategy.rs:199` inside
  `solve_with_oracle` (`#[cfg(feature = "z3")]` at `strategy.rs:192`), reachable
  only through `Strategy::Oracle`, which `recommended_portfolio` never returns
  (`strategy.rs:182-188`) and which `is_pure_rust()` reports `false` for
  (`strategy.rs:82`). Its `sat` is still replayed through the ground evaluator
  (`strategy.rs:201-203`, `replay_sat` at `strategy.rs:210-232`); a replay
  failure is a `SolverError::Backend` soundness alarm.
- Every other caller is a `#[cfg(feature = "z3")]` differential suite (~30
  files, e.g. `tests/differential.rs:9`, `tests/uflia_differential_fuzz.rs:49`)
  or a bench feature (`axeyum-bench/Cargo.toml`, `default = []`).

### No C/C++ in the default build — confirmed from the manifests

`crates/axeyum-solver/Cargo.toml`:

```
default = ["qfbv"]
qfbv    = []                                   # adds NO dependencies
full    = [dep:axeyum-cas, axeyum-egraph, axeyum-fp, axeyum-lean-kernel,
           axeyum-smtlib, axeyum-strings]      # all pure Rust
z3      = ["full", "dep:z3"]                   # the ONLY C/C++ edge
z3-static = ["z3", "z3/gh-release"]
batsat-reference = ["axeyum-cnf/batsat-reference"]   # batsat/rustsat are pure Rust
bench-internals  = ["full"]
```

`default` resolves to `{qfbv}` and `qfbv` is empty, so `cargo build -p
axeyum-solver` with default features pulls `axeyum-aig`, `axeyum-bv`,
`axeyum-cnf`, `axeyum-ir`, `axeyum-query`, `axeyum-rewrite` and nothing else
(plus `web-time` on `wasm32`). `z3` is `optional = true` and `full` does **not**
imply `z3` — the arrow runs the other way. The only C-linking dependency
anywhere in a library manifest is `z3` (→ `z3-sys` → `pkg-config`); the sibling
`axeyum-py` links `libpython` via `pyo3`, but it is not in `axeyum-solver`'s
graph. `deny.toml:36` carves out licences specifically "pulled in by the
z3-static (prebuilt libz3) path", which is the audit trail for the same claim.

## Capabilities and the support matrix

Both are **hand-written `const` literals**, and neither is consulted by the
dispatcher.

| | `SUPPORT_MATRIX` | `CAPABILITIES` |
|---|---|---|
| Declared | `support_matrix.rs:177` | `capabilities.rs:144` |
| Shape | `const &[SupportRow]`, 6 fields (`support_matrix.rs:156-169`) | `const &[Capability]`, 6 fields (`capabilities.rs:125-137`) |
| Entries | 19 | 105 |
| Derived from code? | **No.** No dispatcher call, no feature detection, no probe, no build script | **No.** No enum of supported logics, no probe |
| Rendered to | `docs/research/08-planning/support-matrix.md` via `support_matrix_markdown()` (`support_matrix.rs:533`) | `docs/research/08-planning/capability-matrix.md` via `capability_matrix_markdown()` (`capabilities.rs:2193`) |
| Behavioral check | Partial: `tests/support_matrix.rs` probes ~7 of 19 fragments through `solve_smtlib` (`:90`, `:101`, `:113`, `:124`, `:133`, `:141`, `:184`, `:199`, `:232`) | **None.** `tests/capabilities.rs:13` is a golden-doc compare; `:37` checks non-empty strings and an `ADR-` prefix |
| Read at solve time? | **No** | **No** |

The dispatcher-consultation claim is checkable: `support_matrix` and
`capabilities` appear in `lib.rs` (module declarations at `lib.rs:227` and
`lib.rs:98`) and in `solver.rs:107-108` (which is `backend::Capabilities`, the
runtime self-description, and is a pass-through getter). `auto.rs` and
`smtlib.rs` contain **zero** occurrences of either identifier.

The 12 unprobed `SUPPORT_MATRIX` rows are unbacked assertions: QF_ABV
(`support_matrix.rs:188`), QF_LIA·Diophantine (`:221`), QF_IDL/QF_RDL (`:243`),
QF_NRA and its three extra rows (`:274`, `:286`, `:303`, `:314`), QF_FP (`:342`),
quantifiers (`:353`), datatypes (`:472`), strings (`:483`), optimization
(`:497`), incremental (`:508`).

`capabilities.rs`'s own module doc concedes the gap at `capabilities.rs:13-16`
("The same data is what **should** drive `Unsupported` messages … over time"),
and `scripts/check-capability-routes.py:34-38` states its check "is deliberately
name-only. It does NOT verify that the named function implements what the row
claims."

## Portfolio and parallelism

There are **two unrelated things called a portfolio**, and only one of them can
run threads.

### 1. `portfolio.rs` — the fused group (the real one)

- API is `pub(crate)` except `groups_run()` (`portfolio.rs:149`).
  `FusedGroup::new(arms, workers)` (`:296`), `::run(&self, &TermArena, &[TermId],
  &SolverConfig)` (`:314`).
- **Worker count is not chosen here.** `FusedGroup` only clamps what it is
  handed: `workers.clamp(1, arms.len().max(1))` (`portfolio.rs:299`). There is no
  `available_parallelism` call anywhere in `crates/axeyum-solver/src`.
- `workers == 1` ⇒ `run_reserved` (`portfolio.rs:345-389`): no threads, arms run
  in declared order on the calling thread with weight-proportional budget slices
  plus carry-over, breaking at the first decisive arm.
- `workers > 1` ⇒ `run_raced` (`portfolio.rs:393-516`): `std::thread::scope`
  (`:411`), one named thread per arm with `stack_size(ARM_STACK_BYTES = 256 MiB)`
  (`:178`, `:421-424`), each arm getting its own `arena.clone()` (`:418`), its own
  `StopToken` (`:408`, `:425`), the group's **whole** wall share, and
  `memory_limit_mb / arms.len()` (`:522-525`). Note `workers` is used only as
  `== 1` vs `> 1` — at 2 workers with 3 arms, all 3 threads spawn.
- **Winner**: first `decisive()` arm in **declared index order**
  (`portfolio.rs:534-561`), never finishing order. Two decisive arms that
  disagree is a hard `SolverError::Backend` naming both arms (`:549-558`), not a
  downgrade to `unknown`.
- **Losers** are cancelled cooperatively (`token.request()` on every arm,
  `:479-486`) but the group **drains and joins every arm** (`:471-476`,
  `:493-495`). The join is deliberate: an abandoned arm bounds its time but not
  its memory (`:488-492`).
- **Determinism**: the *verdict* is deterministic given the same multiset of
  decisive arms, and disagreement is an error rather than a coin flip. The
  *attribution and stats are explicitly not* — `portfolio.rs:55-58` says "a route
  trail from a multi-worker group is a record of this run, not a reproducible
  one". Three further consequences visible in code: which arms become decisive
  is race-dependent; a returned `Sat` model's contents depend on which arm won;
  and `auto.rs:2890-2894` returns **early** when a later arm won, skipping the
  `has_function` fall-through and `annotate_lia_budget_before_uf` that
  `first_arm` goes through (`auto.rs:2913-2932`) — a race-selected control-flow
  difference, not merely a race-selected label.

### 2. The int-linear group's wiring (`auto.rs`)

- `DEFAULT_INT_LINEAR_PORTFOLIO_WORKERS = 1` (`auto.rs:2948`), overridden once
  per process by `AXEYUM_PORTFOLIO_WORKERS` into a `OnceLock`
  (`auto.rs:2956-2967`), or per-thread by `IntLinearPortfolioWorkersGuard`
  (`auto.rs:2986-3000`, TEST-ONLY: only `tests/portfolio_fused_group.rs`).
- Exactly **two arms**, compile-time const (`auto.rs:3023-3032`):
  `("lia-dpll", weight 3, check_with_lia_dpll)` and
  `("int-blast-ladder", weight 1, dispatch_int_blast_width_ladder)`. Weights
  matter only at one worker, and at one worker no group is built — so they are
  effectively dead.
- The group's clock is `config_with_remaining_deadline(config,
  dispatch_deadline)` (`auto.rs:2885`); the sequential call is deliberately
  **not** clamped (`auto.rs:2882-2884`).
- `already_recorded = group.is_some()` (`auto.rs:2903`) is what stops `lia-dpll`
  running twice per query — the first version of the wiring did.

### 3. `strategy::solve_with_portfolio` — not this mechanism

`strategy.rs:143-172` is a sequential `or-else` combinator over `Strategy`
values. No threads, no cancellation, no worker count. It has no Rust caller in
the workspace outside tests; its production consumers are the Python bindings.

### Commit `613bc3f35`

`git show --stat 613bc3f35` is **documentation-only**: one file,
`docs/research/12-performance/fused-portfolio-int-linear-2026-09-09.md`,
+39/−31. No code touched. It records the measurement that justifies the group at
`AXEYUM_PORTFOLIO_WORKERS=2`: QF_LIA 119→123 decided over 200 files, QF_IDL
54→56 over 100, **+6 / −0**, zero verdict disagreements. Wall time decomposes so
that the cost lands entirely on files lost either way (QF_LIA +88.8 s across 77
such files) while files that are decided got *faster* (QF_LIA −52.1 s across
119). `docs/plan/STATE-2026-09-09.md:41` records the operational caveat: the +6
requires the env var. The whole module is five commits old
(`df2b4131b`, `53f625c15`, `bfb1b2606`, `1fd16068e`, `c4c6d1cf1`).

### Where parallelism actually exists

`rayon`: zero hits in `crates/axeyum-solver` (it is a dependency of
`axeyum-bench` only). `available_parallelism`: zero hits in `src/`. The only
concurrent *search* is `portfolio::run_raced`. Every other `thread::spawn` in
`src/` is a deep-stack trampoline that spawns one thread and immediately joins
(`reconstruct/arithmetic.rs:181-190`,
`reconstruct/quant_bv_instance_set_lean.rs:2890`, `:3114`, `:3219`, `:3569`) or
lives under `#[cfg(test)]`.

## Incrementality

`trait IncrementalSolver` (`incremental.rs:744-787`) has six required methods and
no defaults: `assert`, `push`, `pop`, `scope_depth`, `check`, `check_assuming`.
The single in-tree implementor is `IncrementalBvSolver`
(`incremental.rs:795-815`, impl at `:4961-4989`).

- **`push`** allocates a fresh activation selector and pushes a `Frame`
  (`incremental.rs:1707-1723`). **`pop`** pops the frame
  (`incremental.rs:1727-1735`) — **no clauses are removed**; deactivation is by
  ceasing to assert the selector.
- **Preserved across a check**: learned clauses, VSIDS activities and saved
  phases (the SAT core persists — `axeyum-cnf/src/lib.rs:668-690`); the AIG and
  the lowering memo; the CNF variable namespace; every frame's clauses across a
  `pop`.
- **Not preserved**: the model. Each check reconstructs and replays it. The only
  retention is the opt-in, off-by-default replay-checked SAT cache
  (`incremental.rs:984-998`, `:159-162`), keyed on exact `(assertions,
  scope_ends, assumptions)` identity (`:215-224`), which declines to cache
  `Unsat` without a source-bound proof and declines `Unknown` (`:203-207`).
- **Assumptions vs assertions**: an assumption gets an *ephemeral* selector for
  one solve (`encode_one_shot_assumptions`, `incremental.rs:3643-3687`), and on
  `unsat` the core returns failed assumptions, which is what makes
  `AssumptionOutcome::Unsat { core }` (`incremental.rs:476-479`) possible. Those
  ephemeral selectors' clauses are **never reclaimed** — ADR-0009 records this
  as a known limitation and the code still has no GC (`fresh_selector` is only
  ever additive, `incremental.rs:1710`, `:3673`, `:3680`).

`docs/research/09-decisions/adr-0009-incremental-sat-and-solving.md` exists
(accepted 2026-06-13). Three divergences from it:

1. ADR-0009 stage 1 specifies a warm wrapper over `rustsat-batsat`; the code is
   re-based onto the in-tree native CDCL core (`axeyum-cnf/src/lib.rs:668-669`,
   "re-based onto the native core by ADR-1703"). The divergence is recorded in
   ADR-1703 but ADR-0009's text was not amended.
2. ADR-0009 §Consequences says "The `Solver` façade's incremental interface is
   now backed by a real incremental engine at the SAT layer." **This is false at
   `ea8515407`.** `Solver::push` is `self.scopes.push(self.assertions.len())`
   (`solver.rs:126-128`), `pop` is `truncate` (`:134-142`), and `check`
   re-submits the whole active set to a one-shot backend (`:161-163`).
   `grep -rn "IncrementalSolver" crates/axeyum-solver/src/*.rs` finds only
   `lib.rs:929` (re-export), `incremental.rs:744` (trait) and
   `incremental.rs:4961` (impl) — there is no path from `Solver` to
   `IncrementalBvSolver`. `solver.rs:9-13` states the one-shot design plainly,
   so the source is self-consistent; it is the ADR that is stale.
3. The warm solver now carries an array/UF layer ADR-0009 never described
   (`Frame::deferred_assertions`, `incremental.rs:797-803`;
   `check_with_memory` re-solves one-shot through `check_auto` under
   `#[cfg(feature = "full")]`, `incremental.rs:1754-1757`). The warm `check`
   path refuses rather than ignores such assertions
   (`SolverError::Unsupported`, `incremental.rs:3762-3768`).

## Errors

`error.rs` (60 lines) is four variants (`error.rs:29-38`):
`NonBooleanAssertion(TermId)`, `Unsupported(String)`, `Backend(String)`,
`Parse(String)`. The module moved out of `backend.rs` to break the
`backend → model → quant_sat_certificates → proof → backend` cycle
(`error.rs:1-20`, `backend.rs:62-65`); the gate is
`scripts/analyze_solver_module_graph.py --check`.

## Budget policy

One type carries every route's claim on the ladder's clock: `LadderSlice`
(`auto.rs:1955-2050`), with `SliceShape::AllButReserve` (a route that decides
most of what it is given keeps everything but a reserve) and
`SliceShape::Fraction` (a speculative probe takes only a slice).
`slice_of` clamps to `[MIN_LADDER_SLICE.min(remaining/2), remaining]`
(`auto.rs:2046-2049`) — the `/2` is load-bearing and its absence was found by a
mutation that made no test fail (`auto.rs:2039-2045`).

| Route | Policy | Constant | Site |
|---|---|---|---|
| `dl-online` | all but `min(t/4, 6 s)` | `DL_LADDER_RESERVE_SHARE = 4`, `DL_FALLBACK_RESERVE = 6 s` | `auto.rs:4491-4503` |
| `dl-online-extended` | all but `min(t/8, 3 s)` | `DL_EXTENDED_*` | `auto.rs:4512-4523` |
| `uf-arith-lazy-overbound` | all but `t/4` (policy `CegarProbe`) | `UF_ARITH_LADDER_RESERVE_SHARE = 4` | `auto.rs:3318` |
| `abv-online-cdclt` | all but `t/4` | `ABV_ONLINE_LADDER_RESERVE_SHARE = 4` | `auto.rs:4938-4942` |
| `int-real-relax` | `t/6` | `int_real_relax_budget` | `auto.rs:5279-5284` |
| `mbqi-quick` | fraction (1/8) | `MBQI_FIRST_REFUSAL_SHARE` | `auto.rs:4075` |
| array unsat refuters | flat `min(t, 250 ms)` | `TIMED_ARRAY_REFUTER_SLICE` | `auto.rs:5484-5489` |

**Finding: the policy is not applied uniformly.** `LadderSlice` exists to delete
a branch that returned the *whole* budget when a route's share rounded to zero
(`auto.rs:1885-1902`). That exact branch is still live in
`dpll_lia.rs:611-618`:

```rust
let share = timeout.checked_div(3).unwrap_or(timeout);
probe.timeout = Some(if share.is_zero() { timeout } else { share });
```

Three env vars change routing policy, each resolved once per process into a
`OnceLock` with a thread-local override for in-process A/B:
`AXEYUM_UF_ARITH_OVERBOUND` (`auto.rs:3364-3376`),
`AXEYUM_ABV_ONLINE_RESERVE` (`auto.rs:5001`), `AXEYUM_LRA_ROUTE`
(`lra_route.rs:149-180`). `AXEYUM_PORTFOLIO_WORKERS` (`auto.rs:2962`) is a
fourth. In every case an unrecognised value silently falls back to the default
so a typo in a sweep script cannot change a verdict.

## Default-profile build

A `cargo build -p axeyum-solver` with default features compiles twelve modules
(`lib.rs:48-69`): `backend`, `config_registry`, `error`, `incremental`,
`layers`, `lazy_smt_counters`, `live_instruments`, `memory_budget`, `model`,
`portfolio`, `proof`, `sat_bv_backend`. The public surface is everything
exported before `lib.rs:954` (where the `full_exports!` macro begins).

**What it can do**: decide scalar QF_BV through `SatBvBackend`
(`sat_bv_backend.rs:580-625`) either directly or through `Solver<SatBvBackend>`;
run the warm `IncrementalBvSolver` with push/pop/assume; export QF_BV DRAT
proofs (`proofs` module, partially gated); read `SolveStats`, `BvLayerStats`,
`LazySmtCounters`, `LiveInstruments`, the config registry and
`peak_resident_bytes`.

**What it cannot do**: there is **no dispatcher at all**. `solve`, `check_auto`,
`check_auto_explained`, `solve_smtlib`, `Strategy`, `RouteTrace`, `SpanLog`,
`SUPPORT_MATRIX`, `CAPABILITIES` and every theory route are inside
`full_modules!` (`lib.rs:70-249`) and simply do not exist. `IncrementalBvSolver::
check_with_memory` has a `#[cfg(not(feature = "full"))]` arm at
`incremental.rs:1758` for exactly this reason. The WASM build takes this profile
(`axeyum-wasm/Cargo.toml:26`: `default-features = false, features = ["qfbv"]`),
so the browser build has the BV backend and none of the routing described in
this file.

`portfolio.rs` is in the default profile only because of one function:
`stop_or_past_deadline` (`portfolio.rs:109-111`), called from 16 sites in
modules that exist by default (`nra.rs:67`, `combined.rs:258`, `dpll_t.rs:340`,
`abv.rs:589`, `cdclt.rs:994`, `dpll_lia.rs:1074`/`1582`/`3772`,
`uflia_online.rs:179`, `uflra_online.rs:97`, `simplex.rs:85`, `lra.rs:55`,
`lra_online.rs:108`, `dl_online.rs:1200`, `optimize.rs:39`, `auto.rs:5576`).

## Data flow

```
SMT-LIB text
  └─ axeyum_smtlib::parse_script_with_string_bound_within   smtlib.rs:2171
     └─ solve_smtlib_at_string_bound  (14 front-door stages) smtlib.rs:2139
        └─ auto::solve                (quantified ladder)    auto.rs:492
           ├─ checked_quantified_fast_path                   auto.rs:53
           ├─ skolemize / valid-universal / vacuous / FM     auto.rs:527-696
           ├─ finish_quantified_solve  (8 rungs, qtrace only) auto.rs:297
           └─ auto::check_auto         (QF front door)       auto.rs:1110
              └─ check_auto_with_recorder                    auto.rs:1665
                 ├─ Features::scan_within                    auto.rs:9455
                 ├─ preprocess_reduce / dispatch_reduced     auto.rs:2158, 2266
                 └─ check_auto_inner                         auto.rs:2353
                    ├─ check_with_milp                       auto.rs:2487
                    └─ check_auto_dispatch  (theory ladder)  auto.rs:4529
                       ├─ dispatch_difference_logic          auto.rs:4424
                       ├─ dispatch_uf_nra / nra              auto.rs:4299
                       ├─ dispatch_int_linear_refuters       auto.rs:2788
                       │     └─ portfolio::FusedGroup        portfolio.rs:296
                       ├─ dispatch_uf_routes                 auto.rs:5076
                       ├─ dispatch_abv_online / array paths  auto.rs:5032, 5491
                       ├─ dispatch_nonlinear_int_tail        auto.rs:5286
                       └─ combined::check_with_all_theories  combined.rs:61
                             └─ SatBvBackend::check          sat_bv_backend.rs:589
```

Every `Sat` that leaves this pipeline has been replayed against the original
assertions by the deciding route; the dispatcher additionally replays after the
coercion relaxation (`auto.rs:2443-2464`) and after `bv2nat-blast`
(`auto.rs:4746-4759`).

## Entry points and public API

Outside the crate, the routing surface is:

| Item | Path | Notes |
|---|---|---|
| `solve_smtlib`, `solve_smtlib_with_model` | `smtlib.rs:1954`, `:1972` | the shipped competition front door; driven by `crates/axeyum-bench/examples/smtcomp_cli.rs:1765` |
| `solve`, `check_auto`, `check_auto_explained`, `unsat_core` | `auto.rs:492`, `:1110`, `:1548`, `:801` | re-exported at `lib.rs:691-693` |
| `Solver<B>` | `solver.rs:56` | facade over a `SolverBackend`; **not** the dispatcher |
| `SolverBackend`, `CheckResult`, `SolverConfig`, `Capabilities`, `SolveStats`, `UnknownKind`, `UnknownReason`, `SolverError` | `backend.rs` / `error.rs` | default profile |
| `SatBvBackend` | `sat_bv_backend.rs:65` | default profile |
| `IncrementalBvSolver`, `IncrementalSolver`, `AssumptionOutcome` | `incremental.rs` | default profile |
| `Strategy`, `solve_with_strategy`, `solve_with_portfolio`, `recommended_portfolio` | `strategy.rs` | Python bindings are the only non-test consumers |
| `RouteTrace`, `RouteAttributionGuard`, `front_door_stage::*` | `route_trace.rs` | opt-in telemetry |
| `UfArithOverboundPolicy(+Guard)`, `AbvOnlineReservePolicy(+Guard)`, `IntLinearPortfolioWorkersGuard` | `auto.rs:3260`, `:4947`, `:2986` | A/B levers |
| `support_matrix::*`, `capabilities::*`, `trust::*` | | reporting ledgers, not consulted at solve time |
| `Z3Backend` | `z3_backend.rs:76` | **FEATURE-GATED `z3`** |

`SolverConfig` has 20 fields (`backend.rs:97-299`) and **none of them selects a
route**. Two defaults are worth naming because they change the tree:
`preprocess = true` (`backend.rs:392`) and `cnf_vivify = true`
(`backend.rs:391`, a no-op unless `cnf_inprocessing: false` at `backend.rs:390`). `native_cdcl`
(`backend.rs:260`) is a documented dead field — "read by nobody"
(`backend.rs:249-260`), retained for ABI compatibility with `axeyum-py`,
`axeyum-bench` and `axeyum-verify` (ADR-1703 slice 2).

## Resource limits and instrumentation

### `memory_budget.rs` — the only hard resource gate besides wall clock

One budget, `SolverConfig::memory_limit_mb` (`backend.rs:109`, default `None` at
`backend.rs:385`), in megabytes, three mechanisms
(`memory_budget.rs:31-136`):

1. **Clause-count proxy** — `MemoryBudget::clause_ceiling` (`memory_budget.rs:302`)
   = `limit_bytes / ENCODING_BYTES_PER_CLAUSE`, with the constant `384`
   (`memory_budget.rs:184`) from a measured bytes-per-clause table
   (`memory_budget.rs:139-183`). It deliberately over-charges so the budget
   refuses early.
2. **Cooperative RSS probe** — `MemoryBudget::exceeded`
   (`memory_budget.rs:318`), Linux only, reading `/proc/self/status` `VmRSS:`
   (`memory_budget.rs:245`, `:266`). **Not `VmHWM`** — `peak_resident_bytes`
   (`memory_budget.rs:485`) is the only `VmHWM` reader and exists for the span
   log's run header, not for enforcement. A probe costs ~9.4 µs
   (`memory_budget.rs:47-52`), which is why there are exactly
   `PROBES_PER_SAT_BV_CHECK = 3` (`memory_budget.rs:194`), pinned by
   `a_check_probes_only_at_phase_boundaries` (`memory_budget.rs:837`).
3. **Sampling watchdog thread** — `MemoryWatchdog::install`
   (`memory_budget.rs:603`), thread `axeyum-memory-watchdog`
   (`memory_budget.rs:657`), 20 ms interval (`memory_budget.rs:390`), parking on
   a condvar when idle, setting a sticky `WATCHDOG_TRIPPED` flag hot paths read
   with one relaxed atomic load (`memory_budget.rs:542`). Nesting handled by
   `WATCHDOG_DEPTH` (`memory_budget.rs:418`) so only the outermost install owns
   the budget. **This mechanism is itself `#[cfg(feature = "full")]`**
   (`memory_budget.rs:390`, `:399`, `:525`, `:542`, `:562`, `:588`, `:667`), so
   a default-profile build gets mechanisms 1 and 2 only.

There is **no global allocator hook**, and the reason is recorded rather than
implied: `impl GlobalAlloc` is `unsafe impl`, and `unsafe_code` is denied
workspace-wide, so it needs an ADR (`memory_budget.rs:17-28`). What is
consequently *not* bounded is stated at `memory_budget.rs:125-136`.

Exceeding always produces `CheckResult::Unknown(UnknownKind::MemoryLimit)` —
never an error, never a panic (`memory_budget.rs:323-334`, `:341`, `:562`).

**Where dispatch consults it** — four sites in `auto.rs`, all cited earlier:
`memory_budget_decline` at `auto.rs:467-470`, called at `auto.rs:500` (phase
`"solve entry"`) and `auto.rs:1145` (phase `"check_auto entry"`), plus
`MemoryWatchdog::install` at `auto.rs:507` and `auto.rs:1153`. The
`check_auto` placement is deliberate and load-bearing: it is **above** the
attribution delegation branch so `check_auto` and `check_auto_explained` decline
identically (`auto.rs:1130-1144`), pinned by
`route_attribution_is_verdict_identical_under_a_memory_budget`
(`tests/route_attribution.rs:147`). `SatBvBackend` probes its own three phase
boundaries (`sat_bv_backend.rs:133`, `:221`, `:2630`).

The limit is also a **sizing input**, not only a gate: Fourier–Motzkin/Farkas
matrix admission (`lra.rs:439-440`, `:482`), the online-LRA admission screen
(`lra_theory.rs:296-306`, ADR-1752), and per-arm division in the portfolio
(`portfolio.rs:522-524`).

**Named gap, from the source itself** (`memory_budget.rs:130-132`): "A route
with NO cooperative check site is still unbounded… nothing enforces that
mechanically." The ten `watchdog_tripped` call sites are `lra.rs:519`, `:1408`,
`:1418`, `:1501`; `lra_online.rs:2185`, `:2235`, `:2295`; `simplex.rs:869`;
`dpll_t.rs:454`; `lra_theory.rs:391`. There is no test that every route has one.

### `route_trace.rs` (`full`) — what the dispatcher records

The recorder is `pub(crate) type Recorder<'a> = Option<&'a mut RouteTrace>`
(`route_trace.rs:607`), driven by `with_recorder` (`route_trace.rs:610`), which
is a no-op when absent. That is *how* verdict invariance is achieved
structurally rather than by testing: one dispatch body, distinguished only by
whether a recorder is threaded (`route_trace.rs:12-25`). `auto.rs` threads
`rec: &mut Recorder<'_>` through roughly 25 helpers. `check_auto_explained`
constructs the only trace (`auto.rs:1552`, passed at `:1554`); `check_auto`
passes `&mut None` (`auto.rs:1176`).

`RouteAttempt { route: &'static str, outcome: RouteOutcome }`
(`route_trace.rs:139-145`). `RouteOutcome` (`:116`) is `Probe(String)`,
`Decided(Verdict)`, `Declined(DeclineReason)`. **`DeclineReason` has five
variants** (`route_trace.rs:61-75`):

| Variant | Line | Means |
|---|---|---|
| `Unsupported` | `:64` | route does not handle this theory/fragment |
| `NotApplicable` | `:66` | probe says the shape does not match; **never ran** |
| `Budget(String)` | `:69` | a deterministic node/CNF/round/width cap was exhausted |
| `Incomplete(UnknownReason)` | `:72` | ran, returned `Unknown` for an incompleteness reason |
| `VerifierRejected(String)` | `:75` | produced a candidate its own re-check rejected |

`from_unknown` (`route_trace.rs:84-93`) maps the five resource `UnknownKind`s to
`Budget` and `Incomplete`/`Other` to `Incomplete`. That mapping is what makes
"no route matched" (`NotApplicable`) separable from "route ran and gave up"
(`Budget`/`Incomplete`/`VerifierRejected`).

**Determinism**: the attempt *sequence* is deterministic; the timing is not, and
the type enforces it — `PartialEq for RouteTrace` compares only `attempts`,
never `elapsed` (`route_trace.rs:197-203`). Pinned by
`tests/route_trace.rs:272` (`trace_is_deterministic_across_runs`) and
`tests/route_trace.rs:229` (`verdict_invariance_over_lcg_corpus`, a 400-query
LCG differential).

### `span_log.rs` (`full`) — post-hoc, not live

**No span is opened anywhere in the dispatch path.** `SpanLog::build`
(`span_log.rs:405`) is a post-hoc derivation: span 0 from the run facts
(`:416-442`), `push_ladder` (`:445`) synthesizing `RouteAttempt` spans from a
`RouteTrace`, `push_instrument_stages` (`:453`) attaching stage spans from
instrument snapshots. Because `RouteTrace` stores durations rather than
instants, route offsets are a **prefix sum**, and the record says so in a
`time_basis` field (`"observed"` / `"prefix-sum"` / `"duration-only"`,
`span_log.rs:55-63`) so a reader cannot mistake a synthesized left edge for an
observed time. It is a flat event log, not a call tree, and
`span_log.rs:3-22` gives the reason: a solve is simultaneously a sequential
ladder of declines, a real nesting inside one route, and a refinement loop, and
a flame graph draws two of the three wrong.

`Span` (`span_log.rs:319-364`) carries `closed_ns: Option<u64>`, whose `None` is
the load-bearing "who held the budget when we died" (`:327-329`), plus
`outcome` distinguishing `Ran`/`Declined`/`Exhausted`/`Killed` (`:161`) and
`bound` (the budget that bit). Schema version pinned at
`SPAN_LOG_SCHEMA_VERSION = 1` (`span_log.rs:98`).

**Emission**: nothing in `axeyum-solver` writes it. The single emitter is
`crates/axeyum-bench/examples/smtcomp_cli.rs`, `write_span_log` (`:1049-1068`),
appending JSONL to the path in `AXEYUM_TRACE_JSON` / `--trace-json`
(`smtcomp_cli.rs:1506`, `:1523`). Write failures go to **stderr only**
(`smtcomp_cli.rs:1046-1048`), so the competition's "verdict is the last line"
contract holds. Run-header provenance comes from `AXEYUM_TRACE_HOST`
(`smtcomp_cli.rs:1666`) and `AXEYUM_TRACE_COMMIT` (`:1667`).

**Reachability**: `full` + WIRED, but only from `smtcomp_cli`. No caller inside
`axeyum-solver` outside `#[cfg(test)]`.

### `live_instruments.rs` (default profile) — the cross-thread board

Not counters: whole typed snapshots in a `Mutex<BTreeMap<&'static str, Slot>>`
(`live_instruments.rs:210-214`), each carrying a `Sampled` provenance
(`:161`) that distinguishes `Complete` from `InFlight`. The doc is explicit
that an in-flight reading is a lower bound and never a denominator (`:30-37`).
The instrument-name vocabulary is closed (`live_instruments.rs:70-160`, 15
names). `install` (`:310`) is RAII; two thread-locals split the fast path so
`publish_live` on an uninstrumented thread is one `Cell` read (`:293-301`).

Reachability: WIRED and env-gated. The only production installer is
`smtcomp_cli.rs:1676`, under `AXEYUM_TRACE=1` or `AXEYUM_TRACE_JSON`
(`smtcomp_cli.rs:1505-1506`, `:1553`). Publishers relevant to this lane:
`route_trace.rs:652` and `:836`, `auto.rs:3487` and `:3523`, `layers.rs:693`,
`lazy_smt_counters.rs:868`/`:905`, `config_registry.rs:8523`,
`sat_bv_backend.rs:168`, `smtlib.rs:1870`.

The reason a live board exists at all: `publish_bv_layer_stats`
(`layers.rs:682`) fires only when a check *returns*, and every lost `sat-bv`
file dies inside bit-blasting or the SAT search
(`live_instruments.rs:97-103`).

### `layers.rs` and `lazy_smt_counters.rs` (default profile)

`layers.rs` gives typed structure to the otherwise-untyped
`SolveStats::backend` string list: `BvLayerStats` for the `sat-bv` pipeline
(`model_replay` split out of `model_lift` on 2026-09-07, `layers.rs:37-50`) and
`TheoryLayerStats` (`layers.rs:782`) for the CDCL(T) stages, produced in
`cdclt.rs:2243-2245`. `lazy_smt_counters.rs` does the same for the
lazy-SMT/DPLL(T) refinement loops. Both are thread-local
(`layers.rs:423`, `lazy_smt_counters.rs:714-728`), armed by a guard
(`layers.rs:469`, `lazy_smt_counters.rs:860`), mirrored cross-thread
(`layers.rs:583`, `lazy_smt_counters.rs:790`), WIRED, and off by default. Worth
noting for the honesty axis: `LazySmtReading` is deliberately three-way
(`lazy_smt_counters.rs:70`) — `None` from `last_lazy_smt_counters()` means
*never enabled*, not "did nothing".

### `config_registry.rs` (default profile) — a description, never the value

The registry is **not a configuration source**. `config_registry.rs:34-38`:
"An entry is a description, never the value itself… nothing in this module is
read by the code an entry describes. Registering a bound cannot change it."
What it catalogues is every governing constant with a dated justification
(`ConfigEntry`, `config_registry.rs:291-318`: `protects`, `on_exceed`,
`signal`, `guarded_by`, `env_override`, `justification`).

**480 entries.** Counted with the registry's own predicate,
`grep -c "    ConfigEntry {" crates/axeyum-solver/src/config_registry.rs` → 480;
cross-checked by `grep -c '        name: "'` → 480. This is the same predicate
`registry_len_matches_its_own_source` (`config_registry.rs:9372`) asserts
equals `REGISTRY.len()`, and it builds its needle by `concat!`
(`config_registry.rs:9378`) to avoid counting itself — after a real
self-counting off-by-one. 93 entries carry `dated(...)` justifications against
`DATED_FLOOR = 77` (`config_registry.rs:8728`), ratcheted upward-only by
`the_dated_count_only_rises` (`:9542`).

**Enforcement.** `every_governing_constant_is_registered`
(`config_registry.rs:9019`) walks `GOVERNED_FILES` (`:8103`, 21 paths), scans
each for constants, and fails unless every one is registered or listed in
`EXEMPT` (`:8311`, 12 classified non-governing constants with reasons). The
reverse direction is `every_entry_names_a_live_constant` (`:8973`), and
`consulted_keys_are_registered` (`:9056`) scans for `note_consulted` call sites.
`SILENT_UNATTRIBUTED` (`:8160`, 111 entries) is a may-not-grow backlog ratchet
against `SILENT_UNATTRIBUTED_MAX = 111` (`:8278`).

**Finding: the dispatcher is not instrumented into its own config trace.**
`grep -c note_consulted crates/axeyum-solver/src/auto.rs` → **0**. The only
`note_consulted` sites are in `nra.rs` (2), `nra_fbbt.rs`, `nra_real_root.rs`,
`nia_linearize.rs` and `simplex.rs` (1 each). So the `consulted=` set on a
`--trace` run never names a dispatch decision, even though `auto.rs` holds the
route-budget constants the registry documents.

**Finding: `active_env_overrides` is blind to unregistered variables by
design.** `config_registry.rs:8642-8645` limits the reported line to variables a
registry entry names. Four dispatch-affecting variables are not registered and
therefore never appear: `AXEYUM_SIMPLEX_PIVOT` (`simplex.rs:241`),
`AXEYUM_OCC_COMPACT` (`sat_bv_backend.rs:1437`), `AXEYUM_NESTED_QUANT`
(`quant_skolemize.rs:145`), `AXEYUM_TIMEOUT_MS` (`smtcomp_cli.rs:1497`, which
sets `SolverConfig::timeout` and therefore every budget in this file).

**Dispatch-relevant environment variables** (18 registered + 4 unregistered
above). The eight that change *routing*, not just a cap:

| Variable | Read at | Effect |
|---|---|---|
| `AXEYUM_PORTFOLIO_WORKERS` | `auto.rs:2962` | sequential ladder vs concurrent two-arm group |
| `AXEYUM_UF_ARITH_OVERBOUND` | `auto.rs:3370` | `terminal` / `probe` / `skip` for the over-bound UF+arith CEGAR |
| `AXEYUM_ABV_ONLINE_RESERVE` | `auto.rs:5007` | whether the array ladder gets a reserve |
| `AXEYUM_LRA_ROUTE` | `lra_route.rs:152` | simplex-vs-FM order, skeleton encoding, cheap-decline fall-through |
| `AXEYUM_NRA_ADMISSION` | `nra.rs:213` | two admission policies differing by 15× (`config_registry.rs:16-17`) |
| `AXEYUM_NRA_FBBT` | `nra_fbbt.rs:251` | FBBT propagation policy |
| `AXEYUM_NIA_REFINEMENT` | `nia_linearize.rs:1319` | NIA refinement policy |
| `AXEYUM_LAZY_SKELETON` | `dpll_t.rs:144` | lazy-SMT skeleton policy |

Caps and admission bounds also overridable: `AXEYUM_MEMORY_LIMIT_MB` (5 registry
entries), `AXEYUM_LIA_WARM`, `AXEYUM_EUF_ONLINE_ATOMS`, `AXEYUM_QINST_RELEVANCE`,
`AXEYUM_QINST_GROUND`, `AXEYUM_UFLIA_INTERFACE_PAIRS`,
`AXEYUM_UFLIA_MAX_BOOLEAN_ATOMS`, `AXEYUM_UFLIA_MAX_OPAQUE_BOOLEAN_ATOMS`,
`AXEYUM_BVE_BUDGET_MULTIPLE`, `AXEYUM_SUBSUME_BUDGET_MULTIPLE`. Diagnostic only:
`AXEYUM_QTRACE` (`auto.rs:235`), `AXEYUM_QPROBE`, `AXEYUM_FLOODPROBE`,
`AXEYUM_TRACE`, `AXEYUM_TRACE_JSON`, `AXEYUM_NIA_DEBUG`, `AXEYUM_UF_FMF_DEBUG`.

Every policy variable is read **once per process** into a `OnceLock` with a
thread-local override for in-process A/B, and every one falls back to the
default on an unrecognised value so a typo in a sweep script cannot change a
verdict (`auto.rs:3364-3376`, `lra_route.rs:143-146`).

## Tests and gates

`crates/axeyum-solver/tests/` holds **302** integration files, of which **297**
carry `#![cfg(feature = "full")]`. The five that do not are `api_namespaces.rs`,
`lean_module_fixtures.rs`, `native_cdcl_baseline.rs`, `qfbv_profile.rs`,
`xor_cdcl_curated_measure.rs`. **A default-feature `cargo test -p axeyum-solver`
therefore compiles essentially none of the dispatch coverage and exits 0.**

| Suite | Lines | Gate | Covers |
|---|---|---|---|
| `tests/route_trace.rs` | 555 | `full` | verdict invariance (`:229`, 400-query LCG differential), trace determinism (`:272`) |
| `tests/route_attribution.rs` | 505 | `full` | ADR-1760 attribution; `route_attribution_is_verdict_identical_under_a_memory_budget` at `:147` |
| `tests/auto.rs` | 228 | `full` | dispatcher behaviour |
| `tests/portfolio_fused_group.rs` | — | `full` | the degeneracy property (`:195-210`: `portfolio_groups_run()` does not move at 1 worker), one `lia-dpll` row per query (`:283-299`) |
| `tests/strategy.rs` | 311 | `full` | `Strategy`, `solve_with_portfolio`, `recommended_portfolio` |
| `tests/support_matrix.rs` | 301 | `full` | golden doc + 7-of-19 behavioral probes |
| `tests/capabilities.rs` | 57 | `full` | golden doc only |
| `tests/deadline_honored.rs` | 484 | `full` | budget discipline |
| `tests/corpus_regression.rs` | 255 | `full` | the committed `:status` corpus |
| `tests/progress_frontier.rs` | 2611 | `full` | the capability ratchet |
| `tests/differential*.rs`, `*_differential_fuzz.rs` (~30 files) | — | **`z3`** | the only checks that compare verdicts against an independent solver; compile to zero tests without the feature |
| `portfolio.rs` `#[cfg(test)] mod tests` | `:563-568` | `full` | 8 tests including declared-order winner (`:833`) and cross-arm disagreement (`:899`) |
| `config_registry.rs` `mod tests` | — | default | `every_governing_constant_is_registered` (`:9019`) and 7 sibling ratchets |

## Doc drift

### `docs/internals/solver-dispatch.md` (235 lines, 2026-09-06)

This is the least-drifted of the five *on the claims it makes*, because it
explicitly declines to state a route order (`solver-dispatch.md:16`, "The
precise route order evolves") and defers coverage to the generated support
matrix (`:69-71`). Every symbol it names still exists — I grepped each of 29
named identifiers individually and all have ≥1 hit. Its problems are one wrong
type name, one misattributed scope, and four material omissions.

| # | Stale line | Source that contradicts it |
|---|---|---|
| D1.1 | `:10` "accepts an arena, assertions, and a `SolveConfig`" | `SolveConfig` has **zero hits** in `crates/axeyum-solver`. `auto.rs:492-496` declares `config: &SolverConfig`. (`grep -rn "SolveConfig" crates/ --include=*.rs` finds only `PlanSolveConfig` in `axeyum-bench/src/main.rs`.) |
| D1.2 | `:221-223` "the quantifier-free dispatcher, which reaches this route as its terminal rung … and nothing running after it" | `auto.rs:3993-3996` scopes "terminal rung" to `dispatch_uf_fast_paths`, not to the dispatcher. `check_auto_dispatch` continues past `dispatch_uf_routes` (`auto.rs:4800`) into the array paths (`:4803`) and the `qf-bv` rung (`:4849-4856`). |
| D1.3 | `:35` "all routes share the caller's remaining deadline"; `:22` the flowchart's sequential `next` edge | `portfolio.rs:40-41` — "`workers > 1` — every arm gets the whole share on its own worker", wired at `auto.rs:2870`. Mitigating: default-off (`auto.rs:2948`), so the sentence still describes the shipped default. |

Omissions, each material to a page whose subject is route contracts:

- **O1.1** the native CDCL(T) bridge (`native_cdclt.rs`, ADR-1704) — a second
  CDCL(T) driver, and the one that produces UNSAT evidence
  (`native_cdclt.rs:1-10`, thread-local artifact channel at `:57-104`). The
  page's UNSAT-assurance bullet (`:209-211`) is where this belongs.
- **O1.2** the fused portfolio (`portfolio.rs`, 968 lines) — including its
  soundness gate, cross-arm disagreement as `SolverError::Backend`
  (`portfolio.rs:60-66`), which is exactly the kind of contract this page is for.
- **O1.3** the memory-budget declines at `auto.rs:500` and `:1145`. The
  "Result discipline" list (`:208-214`) enumerates the ways a result can be
  non-definitive and omits memory entirely.
- **O1.4** the pre-dispatch stage in `check_auto_inner` — `nra-even-power`
  (`auto.rs:2371-2374`) and `milp` (`auto.rs:2415-2436`) can both return a
  definitive verdict *before* `check_auto_dispatch` is reached, and a `sat` on
  the coercion path passes **two** replay gates (`auto.rs:2447-2452`), which the
  flowchart's single `replay` node collapses into one.
- **O1.5** `strategy.rs` (ADR-0019) is never mentioned, and ADR-0019 is cited by
  none of the five docs.

Verified-correct, so as not to overstate: the reserve arithmetic (`:38-43`)
matches `auto.rs:4485-4503` and `dpll_lia.rs:611-618`; the preflight ordering
(`:54-59`) matches `dpll_lia.rs:1378-1397`; "four defaulted hooks" plus "a
fifth, `engine_counters`" (`:113-124`, `:184`) matches exactly five defaulted
methods on `TheorySolver` (`euf_egraph.rs:103`, `:118`, `:137`, `:149`,
`:161`); "all ten existing implementors" (`:116`) matches exactly ten non-test
`impl TheorySolver for` in `src/`.

### `docs/reference/support-matrix.md` (38 lines, 2026-08-07)

**Drift is the doc's entire content.** It claims the matrix keeps six layers
separate:

> `:7-12` — typed IR; ground evaluator; SMT-LIB parser/writer; native oracle;
> pure-Rust decision route; evidence/model/proof support.

`SupportRow` has **four** status fields (`support_matrix.rs:156-169`:
`parser`, `ir`, `solver`, `proof`), and the renderer emits four columns
(`support_matrix.rs:590`: `"| Fragment | parser-accepts | IR-semantics |
solver-decides | proof-supports |"`), matched verbatim by the generated file
(`docs/research/08-planning/support-matrix.md:36`). There is no ground-evaluator
column (it is folded into `IR-semantics`, `support_matrix.rs:65-66`), no writer
column, and **no native-oracle column at all**.

This was stale on the day it was written. `docs/reference/support-matrix.md` was
introduced in `ee12f02aa` (2026-08-07), and
`git show ee12f02aa:docs/research/08-planning/support-matrix.md` already read
`# Support matrix (4-column)` with the identical four-column header. The
reference doc never matched its own cited authority.

Consequential second-order drift: `:30` "an oracle comparison validates a
verdict but is not per-query evidence" instructs the reader to read a column
that does not exist. The oracle/differential axis actually lives in the *other*
ledger as `CheckedBy::DifferentialOracle` (`capabilities.rs:96`), a field of
`Capability` (`capabilities.rs:135`), not of `SupportRow`.

Minor: `:27` teaches "'Done' in one column", a status value absent from all four
enums (`support_matrix.rs:36`, `:67`, `:95`, `:127`); and the command block at
`:17-19` omits the `UPDATE_SUPPORT_MATRIX=1` the failing golden test actually
prints (`tests/support_matrix.rs:29-30`).

### `docs/reference/supported-logics.md` (58 lines, 2026-08-07)

**No drift found.** Every factual claim and all five link targets check out.
In particular `:75-77`, "the SMT-LIB parser records `(set-logic ...)`, but
current solver dispatch is derived from the parsed terms rather than selected or
rejected solely by the declared logic", is exactly true: `smtlib.rs:3530-3542`
only validates `is_smtlib_logic_name` and acks, and grepping `logic` across
`auto.rs` finds only `dispatch_difference_logic` and two test names. The same
six-layer phantom as the support-matrix doc appears once at `:12`
("parser/IR/evaluator/oracle/pure-Rust/evidence layers"), contradicted by
`support_matrix.rs:156-169`. At 58 lines it is materially thinner than the
2026-09 dispatch surface, but thin is not stale.

### `docs/reference/solver-config.md` (101 lines, 2026-09-05)

| # | Stale line | Source |
|---|---|---|
| D4.1 | `:31-33` "`preprocess` defaults on … The other assurance/inprocessing levers in this table default off." | `backend.rs:391` — `cnf_vivify: true`. Changed 2026-09-08, three days after the doc: `backend.rs:158-159` "**On by default since 2026-09-08**". Behaviourally nil while `cnf_inprocessing` is off (`backend.rs:152`), but the sentence is false as written, and this page's own `:93` rule is "Record the complete configuration". |
| D4.2 | source-side mirror | `backend.rs:375-376`'s own `impl Default` doc says "All assurance/perf levers off … **except** word-level `preprocess`" and omits `cnf_vivify: true` four lines below it. A reader reconciling doc and source will trust the wrong one. |
| D4.3 | `:13` "`memory_limit_mb` \| Backend memory budget where supported" | `memory_budget.rs:5-8` — until 2026-08-21 the field had exactly one read in the workspace, `z3_backend.rs` under `#[cfg(feature = "z3")]`. It is now a pure-Rust admission input that gates the front door (`auto.rs:500`), prices LRA/FM admission (`lra.rs:439-440`, `:482`) and is divided per portfolio arm (`portfolio.rs:522-524`). |

Omissions: two public `SolverConfig` fields are absent from every table —
`proof_progress` (`backend.rs:283`) and `check_progress` (`backend.rs:298`),
both with public constructors and builders — on a page whose contract is
"Record the complete configuration, not only timeout" (`:93`). The four
demand-slicing builders/accessors (`backend.rs:518`, `:532`, `:539`, `:545`) are
undocumented. ADR-1762's `config_registry.rs`, which exists precisely to answer
this page's "Reproducibility rules" section, is uncited. And no environment
variable appears anywhere in a document titled "Solver Configuration", despite
`AXEYUM_PORTFOLIO_WORKERS` selecting concurrent dispatch and
`AXEYUM_NRA_ADMISSION` selecting between policies that differ by 15×.

The `native_cdcl` row (`:56`) is fully accurate, including that it is a retired
no-op — pinned by `tests/sat_bv.rs:1304`
(`the_retired_native_cdcl_flag_changes_no_verdict`).

### `docs/internals/architecture.md` (82 lines, 2026-08-07)

**No drift found** in its rules. `:63-64` (no C/C++ in the default build,
native backends as optional oracle leaves) matches
`crates/axeyum-solver/Cargo.toml` and `lib.rs:246-247`; `:65-66`
(`unsafe_code` denied workspace-wide) matches the root `Cargo.toml:97`, and
`memory_budget.rs:22-23` records the policy being *honoured* rather than
waived; `:32-35` (three crates with no workspace dependencies) matches the
manifests; every crate named exists; all six "Read next" links resolve.

Two omissions: `axeyum-arith` (ADR-1710) is in neither the diagram nor the
stage-ownership table despite being consumed by `axeyum-ir`, which *is* in the
diagram; and the "Dispatch and reporting" row (`:54`, "one deadline, route
trace, assurance metadata") predates both the portfolio and the memory watchdog.

### ADR resolution

Both ADRs this brief names resolve:
`docs/research/09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md`
("ADR-0002: Ground-Up Identity, Oracle As Bootstrap Scaffolding", accepted
2026-06-10) and
`docs/research/09-decisions/adr-0009-incremental-sat-and-solving.md`
("ADR-0009: Incremental SAT And Incremental Solving", accepted 2026-06-13).
Every ADR number cited by the five audited docs also resolves to a file
(ADR-0001, ADR-1701, ADR-1703). One link imprecision:
`architecture.md:6` renders `ADR-0001` but hrefs the decisions README rather than
the ADR file.

**ADR-0009 itself is the stalest artifact in this lane.** Its §Consequences
claims "The `Solver` façade's incremental interface is now backed by a real
incremental engine at the SAT layer." At `ea8515407` that is false
(`solver.rs:126-142`, `:161-163`), and the source is the honest half
(`solver.rs:9-13` says the backend is one-shot). Its §Decision also still
specifies `rustsat-batsat` as the warm engine, which ADR-1703 replaced
(`axeyum-cnf/src/lib.rs:668-669`).

## Gaps and open questions

1. **Whether the two front doors really are verdict-identical under a memory
   budget on the full corpus.** `check_auto` vs `check_auto_explained` is pinned
   by an LCG differential (`tests/route_trace.rs:229`) that never sets
   `memory_limit_mb` — `auto.rs:1160-1162` says so, calling the corpus
   "vacuously passing on this axis" — and by one targeted test
   (`tests/route_attribution.rs:147`). What would settle it: run the committed
   `:status` corpus twice, once through each entry point, with
   `--memory-limit-mb` set, and diff the verdicts. `[unverified]` — this is a
   build-and-run task and this inventory is source-reading only.
2. **Whether `dl-online-extended`, `mbqi-quick`, `qinst-egraph-retry` and
   `ufbv-online-probe` are genuinely unreachable as trace labels or merely
   unrecorded.** They exist only as `LadderSlice` route names
   (`auto.rs:4059`, `:4075`, `:4083`, `:4519`) and appear in no `record_*` call.
   Reading the code says they govern real budget decisions but produce no trail
   row; confirming a reader can never see them would take a corpus run with
   `--trace-json` and a grep of the emitted route names.
3. **How often the portfolio's race-selected control-flow divergence
   (`auto.rs:2890-2894` vs `:2913-2932`) actually changes an answer.** The two
   paths differ in whether `annotate_lia_budget_before_uf` and the
   `has_function` fall-through run. The measurement in `613bc3f35` reports zero
   verdict disagreements over 300 files at 2 workers, but it does not isolate
   this branch. What would settle it: instrument both arms of that `if` and
   re-run the 300-file pair.
4. **Whether every route honours the memory watchdog.**
   `memory_budget.rs:130-132` states the gap plainly — a route with no
   cooperative `watchdog_tripped` check site is unbounded and nothing enforces
   otherwise. Ten sites exist, all in the LRA/simplex family. A test in the
   shape of `every_governing_constant_is_registered` would settle it.
5. **Whether the 12 unprobed `SUPPORT_MATRIX` rows are accurate.** Seven of
   nineteen fragments get an engine probe in `tests/support_matrix.rs`; the rest
   are unbacked assertions (QF_ABV, QF_LIA·Diophantine, QF_IDL/QF_RDL, four
   QF_NRA rows, QF_FP, quantifiers, datatypes, strings, optimization,
   incremental). What would settle it: one `solve_smtlib` probe per row, in the
   shape of the seven that exist.
6. **Whether `CAPABILITIES`' 105 rows describe reality at all.** No test probes
   any of them, and `scripts/check-capability-routes.py:34-38` says its own
   check "is deliberately name-only. It does NOT verify that the named function
   implements what the row claims." This is the largest unmeasured claim surface
   in this lane, and it is 105 rows against zero behavioural checks.
7. **What `theory_combination.rs`'s four uncalled functions were for.** The
   module is dated 2026-06-19 and its `classify_interface_equalities` is live in
   `uflra_online.rs`; the other four are not. Whether they are dead or a
   deliberate future boundary is a question for whoever wrote ADR-0005's
   crate-boundary reasoning, not something source-reading can answer.
8. **The `dpll_lia.rs:617` zero-share branch.** It is the exact inversion
   `LadderSlice` was built to delete (`auto.rs:1885-1902`), and the argument in
   `auto.rs` is that the reachable band is six nanoseconds wide for a `/6`
   divisor. For a `/3` divisor of a `Duration` the band is three nanoseconds, so
   it is very likely unreachable in practice too — but nobody has said so in
   writing next to the code, and the `LadderSlice` doc's own conclusion was that
   "a branch that returns the unshared budget is one edit away from being
   reachable."
