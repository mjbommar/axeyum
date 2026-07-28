# Review Diary: glaurung <-> axeyum integration seam

Scope:
- src/symbolic/solver/axeyum_backend.rs (4365 lines)
- src/symbolic/solver/mod.rs (850 lines)
- src/symbolic/solver/z3_backend.rs (347 lines)
- src/symbolic/solver/pipe.rs (289 lines)
- src/symbolic/explore.rs (2024 lines) - solver-facing parts only

Read-only review. Not modifying anything.

## Log

### mod.rs (850 lines)
- Clean trait definitions: Solver (one-shot), IncrementalSolver (assert/push/pop/scope_depth/check/check_assuming).
- WarmAssertionPrefix: Arc-linked-list COW ancestry, ptr_eq-based common_depth. Reasonable, well-documented.
- solve() at 560-715 has heavy #[cfg] branching (z3/axeyum/pipe priority + shadow-diff duplicate-dispatch block ~565-661) -- functionally fine but the shadow-diff block duplicates the "call axeyum, maybe warm, else cold" dispatch (lines 578-586 and 592-600) TWICE (z3_first branching) inline. Minor DRY nit, contained.
- Capture/shadow-split hashing/publishing machinery (258-473) is generic content-addressed file publish -- fine, self-contained, not duplicated elsewhere in scope.
- 3 env vars here: GLAURUNG_SHADOW_DIFF, GLAURUNG_DUMP_QUERIES, GLAURUNG_DUMP_SHADOW_SPLITS (diagnostic-only, opt-in, orthogonal to warm policy).

### z3_backend.rs (347 lines) -- clean, small
- coerce() fn (98-107): zero_ext/extract width normalization. ONE of (at least) FOUR near-identical coerce implementations across the seam (others: axeyum_backend::Translator::coerce @3004, expr.rs::render_shared_coerced @316, expr.rs::render_coerced @415).
- BUG CANDIDATE (width-soundness): `Expr::Const { value, width } => BV::from_u64(ctx, value as u64, width.bits() as u32)` at line 122. `value` is u128 and `Width` goes up to W512 (confirmed in ir/types.rs, used for xmm/simd -- phys_reg_width tests reference Width::W128 for xmm0/v5). Any constant >64 bits silently truncates to its low 64 bits before zero-extending to the declared width -- SOUNDNESS BUG for wide (128/256/512-bit) constants. Contrast with axeyum_backend.rs Translator::translate (2878-2894) which correctly special-cases w>128 via WideUint::from_u128 and masks correctly up to 128. z3_backend has no equivalent wide path.
- Model extraction (line 82) also uses `.as_u64()` -- wide (>64-bit) symbol values silently drop out of the returned model (no error, just missing key). Corroborates the model class of bug the review was primed to look for ("recently found concat-width and extension-width bugs") -- this one is NOT yet fixed here.

### pipe.rs (289 lines) -- clean, u128-safe (parse_bv_literal/parse_model use u128), well tested.

### axeyum_backend.rs (4396 lines: ~3107 non-test + ~1289 test)
Struct/fn inventory: 6 Solver-ish types (AxeyumSolver, AxeyumTextSolver, IncrementalAxeyumSolver,
SnapshotIncrementalAxeyumSolver, LineageIncrementalAxeyumSolver [wraps Snapshot per path_id --
NOT independently duplicated, good], DirectDeltaLineageAxeyumSolver [wraps IncrementalAxeyumSolver
per path_id]). So really TWO parallel warm engines: Snapshot-diff (full-vector re-translate + prefix
diff by TermId equality) vs Direct-delta (index/prefix-identity-tracked incremental assert, only
translates new assertions). Different perf tradeoffs (documented), but outer plumbing (dispatch,
stats, error-reset-on-failure, profiling glue) duplicated between them.

Stats/profile struct count: 9 "*Stats" structs (SnapshotReuseStats, DirectDeltaStats,
WarmPathReuseStats, AutoLineageReuseStats, AdaptiveLineageReuseStats, SerialSiblingReuseStats,
WarmTimeoutColdRetryStats, WarmTimeoutContinuationStats, ReplaySatCacheProcessStats) + 2 giant
profile structs (AxeyumCheckProfile ~30 fields, WarmAxeyumCheckProfile ~50 fields, huge field
overlap: arena_terms/translation_nanos/word_rewrite_nanos/bit_blast_nanos/cnf_encode_nanos/
solve_nanos/model_lift_nanos/replay_nanos/model_extract_nanos/total_nanos duplicated verbatim)
+ DirectTranslationMetrics/DirectCheckMetrics. SnapshotReuseStats and DirectDeltaStats have
near-identical fields (checks/exact_*/prefix_assertions_reused/assertions_added/assertions_popped/
resets_after_error) -- confirmed by `DirectDeltaLineageAxeyumSolver::snapshot_stats()` (1891-1900)
which is a hand-written field-by-field ADAPTER converting DirectDeltaStats -> SnapshotReuseStats
just so callers can share one downstream type. Strong DRY smell.

Env vars (GLAURUNG_AXEYUM_*, all in this file): WARM_REUSE, WARM_OWNER_TRANSFER,
WARM_SERIAL_SIBLING_REUSE, DIRECT_DELTA, WARM_TIMEOUT_COLD_RETRY, WARM_TIMEOUT_CONTINUE,
INTERNAL_AND_FLATTENING, REPLAY_SAT_CACHE, WARM_MAX_LIVE_PATHS, WARM_MAX_ASSERTIONS_PER_PATH,
PROFILE_DIR = 11 vars. Plus mod.rs's 3 = 14 total across the seam.
WarmReusePolicy enum: Off/Snapshot/Lineage/Auto/Adaptive (5 variants) CROSSED with independent
booleans: owner-transfer, serial-sibling-reuse (only meaningful under Adaptive), direct-delta
(orthogonal axis layered onto Lineage/Auto/Adaptive), warm-timeout-cold-retry, warm-timeout-continue,
replay-sat-cache policy, internal-and-flattening. That's a combinatorial config surface, not a
clean orthogonal design -- e.g. warm_serial_sibling_reuse_enabled() (277-282) hard-codes
"only if policy==Adaptive", i.e. one boolean's meaning is conditional on another axis's value.

Boolean env-var parsing: SIX near-identical hand-rolled parsers repeating the same
None/off/false/"0"/on/true/"1"/_ match ladder: parse_warm_timeout_cold_retry (201-206, terser
variant), parse_warm_timeout_continue (212-223), parse_direct_delta (245-250, terser variant),
parse_warm_owner_transfer (264-275), parse_warm_serial_sibling_reuse (284-295), and the `enabled`
match inside parse_replay_sat_cache_policy (304-313). Two default-false ones (direct_delta,
warm_timeout_cold_retry) use a shorter matches!+is_some_and pattern; four default-true ones
repeat the full 8-arm match verbatim except for which text values map which way. Textbook
extract-a-helper case: `fn parse_bool_env(value: Option<&str>, default: bool) -> bool`.

Dispatcher god-function: `check_warm_thread_local_selected` (2097-2293, ~200 lines) is the single
worst offender for "large function" -- nested match over 5 policy variants x direct-delta bool x
auto-admission x adaptive-pressure-expansion x serial-sibling-reuse fallback, with duplicated
"fetch stats before/after, record delta, bump WARM_PATHS_CREATED/CLOSED, debug_assert_eq!(created,
reserved)" boilerplate appearing twice (once for direct=true block ~2208-2269, once for direct=false
~2270-2287) almost verbatim.

Error handling: 0 unwrap() in production code (all 28 unwrap() hits are in the #[cfg(test)] module,
confirmed via line-range check). 12 expect() calls, ALL in production code, ALL carry
invariant-justification messages -- not lazy but still panics-on-violated-invariant. 6 of the 12
cluster inside DirectDeltaLineageAxeyumSolver::check_path/transition_and_check (1644, 1668, 1693,
1735, 1740, 1799) -- all guarding "path exists because `created` was already checked/materialized
earlier in this same function", i.e. the invariant is carried by control flow across a 150-line
function rather than by the type system (e.g. an owned struct/enum state machine). A future edit
that reorders these checks panics the whole analysis process instead of returning SolveResult::Error.

Translator (2847-3029): correctly mirrors z3_backend's coerce+width discipline, has the right
comments explaining the exclusive/inclusive Extract hi convention and the coerce necessity
(matches the "recently found concat/extension width bugs" framing in the prompt) -- this part
looks like the FIXED code, i.e. today's translate() is in good shape. Wide (>128 bit) constant
correctly special-cased via WideUint; z3_backend has NOT been given the equivalent treatment (see
z3_backend finding above) -- an asymmetry between the two backends.

check_warm_thread_local (2059-2095) doing 3 concerns (dispatch, cold-retry-on-timeout, metering) is
comparatively fine at ~35 lines.

### explore.rs (solver-facing slice)
- State carries warm_path_id/warm_retain_assertions/warm_assertion_prefix (386-397), correctly
  threaded through root/fork/fork_transferring_warm_owner/fork_branch_successors.
- solve_traced (498-531) and solve_probe_traced (535-580) are ~95% duplicated: build args, call
  solve_for_path_delta, update warm_retain_assertions on synced, fetch last_solve_timing, build a
  WarmReplayCheck, call trace.check(...). Only difference: probe clones+pushes into a local `probe`
  Vec instead of mutating st.constraints, and pops the trace afterward. Should factor a shared
  `solve_delta_traced(st, asserts_slice, ...)` helper.
- warm_owner_transfer_enabled/warm_serial_sibling_reuse_enabled (314-337) are thin #[cfg] wrappers
  forwarding into axeyum_backend -- fine, expected leakage of a feature-gated backend concept into
  the generic explorer; kept minimal.
