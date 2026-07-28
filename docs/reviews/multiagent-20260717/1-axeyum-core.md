# axeyum-solver core review diary

Scope: crates/axeyum-solver/src/{reconstruct,abv,int_reconstruct,incremental,nra_real_root,backend,model,smtlib}.rs

## File sizes (wc -l), full dir for context
- reconstruct.rs: 18517
- abv.rs: 14953 (biggest, 547KB)
- int_reconstruct.rs: 8876
- incremental.rs: 7821
- nra_real_root.rs: 7544
- capabilities.rs: 1773, auto.rs: 6688, qinst_egraph.rs: 7113 -- not in primary scope but noted as also huge.

## Coarse unwrap/expect/panic/as-cast counts (grep -c) in target files
- reconstruct.rs: unwrap=1 expect=32 panic=0 unreachable=2 as-casts=7
- abv.rs: unwrap=785 expect=60 panic=153 unreachable=0 as-casts=11  <-- huge outlier
- int_reconstruct.rs: unwrap=1 expect=7 panic=0 unreachable=3 as-casts=12
- incremental.rs: unwrap=19 expect=13 panic=0 unreachable=9 as-casts=2
- nra_real_root.rs: unwrap=54 expect=1 panic=10 unreachable=1 as-casts=6
- backend.rs / model.rs: clean (0/0/0)
- smtlib.rs: unreachable=1, as-casts=2

## reconstruct.rs
- 463 total fn definitions in one file. mod-level, huge.
- 43 functions named `reconstruct_*_to_lean_module` (grep -c), e.g. lines 3105 (arith_dpll), 3162 (bounded_int_blast), 3200 (nra_even_power), 3231 (array_axiom), 3259, 3282, 3305, 3328, 3343, 3372, 3401, 3428, 3455, etc.
- reconstruct.rs:3162-3195 (`reconstruct_bounded_int_blast_to_lean_module`) and reconstruct.rs:3200-3231 (`reconstruct_nra_even_power_to_lean_module`) are near-byte-identical: fetch cert -> map_err into ReconstructError::MalformedStep w/ rule string -> build "assume"/refuter axiom pair -> require_infers_false -> render_ctx_module. Only the certify-fn name, rule string literals, and error text differ. Classic table-driven-dispatch candidate: a `reconstruct_generic_refutation_to_lean_module(rule: &str, cert_check: impl FnOnce(...) -> Option<Cert>)` would collapse ~40 functions x ~30 lines = ~1200 lines into one generic + a small table.
- ReconstructCtx impl block: struct def 182-298, impl 314-764 (~450 lines) -- large impl, needs closer read for single-fn size.
- mod declared inline at top (line 49) `mod quant_bv_instance_set_lean;` -- suggests some Lean-reconstruction submodules already exist; the god-file could have followed the same submodule pattern for `reconstruct_*_to_lean_module` family (one module per theory-fragment or a data table) but didn't.

## reconstruct.rs (deep dive)
- reconstruct.rs:3805-4136 `reconstruct_proof_fragment_to_lean_module` -- 331-line function, a giant `match fragment { ProofFragment::X => { ...12 near-identical lines... } }` over ~35+ enum variants. Each arm: build SolverConfig w/ timeout+resource_limit -> call a `find_*`/`*_refutation` search fn -> `.map_err(...MalformedStep{rule: "...", detail: format!(...)})?` -> `.ok_or_else(declined)?` -> call the matching `reconstruct_*_to_lean_module`. e.g. arms at 3888 (ClosedUniversalCounterexample), 3907 (BvClosedUniversalCounterexample), 3926 (BvVacuousExistsUniversalCounterexample), 3946 (BvAlternationCounterexample), 3965 (BvPairedExistentialTransfer), 3984-4074 and more. This is THE central DRY/god-function issue in the file: ~35 arms x ~10-15 lines boilerplate =400+ lines that could be a data table `[(rule_name, search_fn, reconstruct_fn, timeout, resource_limit)]` driven by one generic helper. Combined with the 43 `reconstruct_*_to_lean_module` (see above) leaf functions that also share an identical skeleton (get-cert -> map_err -> ok_or_else -> build assume/refuter axiom pair -> require_infers_false -> render_ctx_module), this whole file is dominated by copy-pasted per-theory-fragment glue rather than a trait/table abstraction. A `ProofFragmentHandler` trait or a static dispatch table keyed by `ProofFragment` would cut this file by an estimated 30-40%.
- reconstruct.rs:11679-11794 (~115 visible, gap-detected 242) `fn bv_bit` -- large recursive match over AletheTerm ops (bvnot/bvand/bvor/bvxor/bvxnor/bvadd/bvneg/extract/sign_extend...) for per-bit reconstruction. Long but this one is legitimately complex bit-blasting domain logic with good doc comments; lower priority than the dispatcher duplication above. Still a candidate to split by op-family into helper fns for readability.
- reconstruct.rs:16812-17027 `reconstruct_sos_rational_weight` (215 lines) and reconstruct.rs:17027-17249 `reconstruct_sos_rational_weight_gt` (222 lines) are near-twin functions (strict `p<0` vs `p>0` SOS certificate reconstruction) sharing almost the entire skeleton (fetch cert -> check strict_lt()/negation -> rational_squares() -> clear_rational_sos_denominators -> cert_poly_to_rexpr...). Should share one parameterized helper (bool `strict`) instead of two 200+-line clones.
- reconstruct.rs: 32 `.expect(...)` calls -- need spot check whether these are truly invariant-guaranteed or reachable on malformed/adversarial proof input (proof reconstruction from potentially external/generated Alethe proofs is exactly where "should never happen" reasoning tends to be wrong). See below for spot-checks.

## abv.rs (14953 lines, 547KB) -- highest-risk file by raw stats -- REVISED after boundary check
- IMPORTANT CORRECTION: `mod tests { ... }` starts at abv.rs:11442 and runs to EOF (14953) -- i.e. **3512 of 14953 lines (23%) are a single embedded test module**. Re-scoped counts:
  - Production code (lines 1-11441): unwrap=0, expect=0, panic=0. Genuinely clean on this axis.
  - Test module (lines 11442-14953, 3512 lines): unwrap=785, expect=60, panic=153. All the scary raw numbers live in tests (fuzz/property-style helpers with messages like "x should be a symbol", "expected replay helper to accept the candidate" -- lines 11475, 11499, 11519, 11523, 11614, 11691, 11707, 11734-12678+ repeatedly). Using panic! instead of assert!/unwrap-with-context in test helpers is a minor style nit, not a soundness bug.
  - Net effect: abv.rs's real problem is sheer SIZE + a 3.5k-line monolithic test module glued to the end of an already-15k-line file, not runtime-panic risk. The test module alone is bigger than most whole files in this crate and should live in its own `abv/tests.rs` (or split by sub-theory: array-elim tests, store-chain tests, swap-chain tests, etc.), and the production 11.4k lines should also be split (it already has natural seams: array-elimination core ~36-536, const-array-default-mismatch/store-chain-readback/cross-store-array-disequality certificate families ~536-1875, swap-chain/XOR-swap reasoning, memcpy/sort/fifo pattern families -- each looks like it could be its own module akin to the already-separate `array_binary_search.rs`, `array_memcpy.rs`, `array_fifo.rs`, `array_xor_swap.rs` siblings sitting right next to it in `src/`). It's odd that some array patterns got their own file (array_memcpy.rs, array_fifo.rs, array_xor_swap.rs, array_sort2.rs, array_write_chain.rs) while abv.rs accumulated others (const-array-default-mismatch, store-chain-readback, cross-store-array-disequality, symmetric-swap-chain, two-byte-memcpy-ish helpers) inline -- inconsistent module boundary, i.e. the split pattern the codebase already uses elsewhere was not applied consistently here.
  - `pub fn X_refutation()` thin wrapper + `pub fn X_refutation_within(..., deadline: Option<Instant>)` pattern repeats ~5x (e.g. abv.rs:564/571, 674/681, 793/800) -- consistent and fine (not a smell), just noting the convention.

## Self-acknowledged complexity: clippy::too_many_lines / too_many_arguments allow-attributes
Grepped `#[allow(clippy::too_many_lines)]` etc. across the 8 target files -- this is essentially the codebase admitting "this function is too long" and suppressing the lint instead of splitting:
- reconstruct.rs: 12 occurrences
- abv.rs: 23 occurrences
- int_reconstruct.rs: 19 occurrences
- incremental.rs: 6 occurrences
- nra_real_root.rs: 3 occurrences
- smtlib.rs: 2 occurrences
- backend.rs / model.rs: 0
Total 65 across scope. This is strong, citable, quantified evidence that "large file / long function" is a known, tolerated pattern rather than an oversight -- worth flagging as a policy issue (either raise the lint threshold formally in `Cargo.toml`/`clippy.toml` with justification, or actually split the flagged functions).

## int_reconstruct.rs (8876 lines, ALL production -- no test module found in-file)
- Same family-of-near-duplicate-declined-helpers pattern as reconstruct.rs's dispatcher, but worse: at least 6 near-identical one-line "decline" helper functions that only differ by an embedded rule-name string:
  - int_reconstruct.rs:1740 `residue_decline` -> `ReconstructError::UnsupportedTerm{ term: format!("integer Euclidean residue: {detail}") }`
  - int_reconstruct.rs:2257 `affine_growth_decline` -> same shape, "integer affine growth: {detail}"
  - int_reconstruct.rs:3439 `eq_partition_decline` -> "single-pivot equality partition: {detail}"
  - int_reconstruct.rs:3529 `cover_decline` -> "quantified counterexample cover: {}" (also takes `impl Into<String>` instead of `&str` -- inconsistent signature vs the other 5)
  - int_reconstruct.rs:5406 `nested_xor_decline` -> "nested-XOR reconstruction: {detail}"
  - int_reconstruct.rs:5504 `closed_cex_decline` -> "closed-universal counterexample: {detail}"
  Trivial fix: one `fn decline(kind: &str, detail: impl Into<String>) -> ReconstructError` called as `decline("integer Euclidean residue", detail)`, removing 6 near-duplicate fns (and the signature inconsistency).
- `impl IntReconstructCtx` is split into THREE non-contiguous blocks in the same file: int_reconstruct.rs:174 (to ~1365), :5606, and :6652 (to ~7671), with ~4000 unrelated lines of free functions (partition/cover/nested-xor logic) interleaved between them. This makes "what does IntReconstructCtx actually do" impossible to answer by reading one contiguous region -- a real cohesion/organization smell for a god-context-object file. `#[allow(clippy::too_many_lines)]` appears right before `reconstruct_int_euclidean_residue_to_lean_module` at int_reconstruct.rs:1746 confirming self-acknowledged oversized function (that function itself int_reconstruct.rs:1551-~1740 is ~190 lines).
- Each theory sub-fragment (euclidean-residue, affine-growth, equality-partition, counterexample-cover, nested-xor, closed-universal-counterexample, diophantine) gets its own private micro-namespace of helper fns with a shared prefix (`cover_*`: at least 20 functions 3535-4884; `partition_*`: ~15 functions 2329-3439) all living in the same 8876-line file. Same conclusion as abv.rs: natural module boundaries exist (per-fragment) but were not taken; this should be `int_reconstruct/{residue,affine_growth,eq_partition,cover,nested_xor,closed_cex,diophantine}.rs` behind a small dispatcher, mirroring `quant_bv_instance_set_lean` which IS already split out as its own module (reconstruct.rs:49 `mod quant_bv_instance_set_lean;`) -- so the codebase knows the pattern, it's just inconsistently applied.

## reconstruct.rs / int_reconstruct.rs: casts
- `as` casts are NOT a live soundness concern in the scoped files on closer read (refined grep for actual numeric type suffixes): reconstruct.rs has 2 (`len() as i128`, safe), nra_real_root.rs has 2 (loop bound / exponent, safe, small magnitudes), abv.rs's casts are all inside its test-only fuzzer helpers (14862-14919, PRNG state manipulation, not production). int_reconstruct.rs and incremental.rs have none. This contradicts the initial coarse grep (which matched substrings like "class"/"was") -- worth noting for accuracy: **no width-truncation soundness issue found in this pass** in the 8 scoped files.

## nra_real_root.rs (7544 lines; test mod at 7078-7544, ~466 lines of tests; ~7077 lines production)
- Structurally the best-organized of the big 5: many small, focused functions (Sturm sequences, root isolation, CAD cell decisions) with real domain documentation. Still large enough to warrant a split by concern (root isolation vs multivariate CAD vs univariate decision), and still carries 3 `#[allow(clippy::too_many_lines)]`.
- Real DRY finding: a whole "strict" vs "nonstrict" (and further "_algebraic") twin/triplet family duplicating the same CAD (cylindrical algebraic decomposition) traversal:
  - nra_real_root.rs:2894 `decide_strict_cad_two_var` vs nra_real_root.rs:3206 `decide_nonstrict_cad_two_var` -- read both in full: near-identical bodies (coprime_split the component polys, guard via debug_assert on Cmp variants, then `for &(elim,keep) in &[(v1,v0),(v0,v1)] { try strict_cad_along / nonstrict_cad_along }`). Only the debug_assert predicate and the inner along-fn differ.
  - nra_real_root.rs:2934 `strict_cad_along` vs nra_real_root.rs:3247 `nonstrict_cad_along` -- same shape, presumably same duplication (not fully diffed line-by-line but signature/doc pattern matches).
  - nra_real_root.rs:3074 `decide_strict_cell` vs nra_real_root.rs:3386 `decide_nonstrict_cell` vs nra_real_root.rs:3469 `decide_nonstrict_cell_algebraic` -- a 2x/3x fork of the same cell-decision logic by strictness+domain.
  - nra_real_root.rs:4305 `decide_strict_cad_nvar` vs nra_real_root.rs:4517 `decide_nonstrict_cad_nvar` vs nra_real_root.rs:4601 `decide_nonstrict_cad_nvar_algebraic` -- the n-var generalization repeats the same strict/nonstrict/algebraic fork again.
  This is a systemic pattern (not a one-off): the "strict vs nonstrict" axis is a boolean/enum (`Cmp` already exists at nra_real_root.rs:144 with Lt/Gt/Ne/Eq/Le/Ge variants) that's been resolved at the FUNCTION level (copy-paste per branch) rather than threaded as a parameter or via a small `CellDecider` trait/closure. Given CAD is the algorithmic core of this file, collapsing these families would likely cut nra_real_root.rs by 15-25%.
- 12 production `.unwrap()`s, mostly narrow patterns like `*vars.iter().next().unwrap()` (2588, 3750, 4438, 4789) / `*comp_vars.iter().next().unwrap()` (2588) immediately after a `.len()==1` or non-empty check earlier in scope -- looked locally justified in the couple sampled but repeated 4x near-identically across the strict/nonstrict twins (same root cause as the DRY finding above: duplicated call sites duplicate the same unwrap pattern).

## incremental.rs (7821 lines; test mod at 7649-7821, ~172 lines tests; ~7648 production)
- Cleanest of the 5 large files by raw error-handling stats: 0 unwrap, 12 expect, 7 unreachable, all in production code, and all sampled instances are locally justified by nearby invariant-establishing code (e.g. `pop()` at incremental.rs:1694 correctly guards `frames.len() > 1` before popping, matching the `.expect("base frame always present")` callers).
- DRY nit: the exact literal `.expect("base frame always present")` appears 10 times (e.g. incremental.rs:1359, 1384, 1397, 1427, 1442, 1483, 1494, 1500, 1540, 1545) always as `self.frames.last()/last_mut().expect("base frame always present")`. Trivial fix: add `fn base_frame(&self) -> &Frame` / `fn base_frame_mut(&mut self) -> &mut Frame` private helpers once and call them; currently every call site re-derives the same invariant-message pair, so a future change to the invariant (e.g. frames becoming allowed to be empty) would need 10 coordinated edits instead of 1.
- unreachable! at incremental.rs:322 (`CheckResult::Sat(_) => unreachable!()`) is genuinely exhaustiveness-driven (reached only after a `let-else` already destructured the Sat arm above) -- fine, no message needed but a short one would help future maintainers.

## backend.rs (526 lines) -- clean, best-organized file in scope
- `SolverBackend` trait (backend.rs:482) is small, well-documented, minimal surface (capabilities/check/check_query/last_stats) -- no leaky abstraction found.
- `SolverConfig` (backend.rs:113-265) is a flat struct with 17 independent fields, almost all `bool` or `Option<T>` experimental feature levers (prove_unsat, cnf_inprocessing, cnf_vivify, preprocess, profile_bit_demand, demand_bit_slicing, range_demand_slicing, incremental_positive_and_flattening, xor_cdcl_fallback, lazy_bv, native_cdcl, lazy_bv_abstract_ite, ...) built via a fluent `with_*` builder (backend.rs:298-443). Documentation is unusually good (each field explains soundness/trust implications) but the type design has a real gap: backend.rs:201-210 documents `demand_bit_slicing: bool` and `range_demand_slicing: Option<RangeDemandPolicy>` as two SEPARATE fields controlling the same axis (which bit-lowering strategy to use), and the doc comment literally admits: *"Enabling both demand modes is a configuration error rather than an implicit precedence rule."* -- i.e., the type system allows an invalid state (both set) that is only a runtime/logical error, not a compile-time impossibility. This should be a single enum, e.g. `enum BitLoweringMode { Eager, DemandSliced, RangeSliced(RangeDemandPolicy) }`, making the "config error" state unrepresentable. This is the clearest boolean/optional-soup-that-should-be-an-enum instance found in the whole scoped review.
- Otherwise this file is a good model for what the other files in scope should look like: small, single-purpose, well-doc'd, no unwrap/expect/panic.

## model.rs (336 lines) -- clean, no issues found worth flagging.

## smtlib.rs (2437 lines) -- brief look only (time-permitting tier)
- 1 unreachable!, 2 as-casts (smtlib.rs:512 `ch as u32` over `n.to_string().chars()` -- safe, digit chars), 2 `#[allow(clippy::too_many_lines)]`. Not deeply reviewed given time budget; no major red flags surfaced in the structural pass.

(diary complete for this pass)

