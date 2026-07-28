# Axeyum quantitative breadth sweep -- 2026-07-17

Workspace: /home/mjbommar/projects/personal/axeyum (20 crates under crates/)
Totals: 686 .rs files, 476,303 lines. 61 files > 1500 lines. READ-ONLY sweep.

## 1. Top 25 largest .rs files (lines)

| # | Lines | File |
|---|-------|------|
| 1 | 18,517 | crates/axeyum-solver/src/reconstruct.rs |
| 2 | 14,953 | crates/axeyum-solver/src/abv.rs |
| 3 | 11,598 | crates/axeyum-smtlib/src/parse.rs |
| 4 | 8,876 | crates/axeyum-solver/src/int_reconstruct.rs |
| 5 | 7,909 | crates/axeyum-bench/src/main.rs |
| 6 | 7,821 | crates/axeyum-solver/src/incremental.rs |
| 7 | 7,544 | crates/axeyum-solver/src/nra_real_root.rs |
| 8 | 7,113 | crates/axeyum-solver/src/qinst_egraph.rs |
| 9 | 7,057 | crates/axeyum-fp/src/lib.rs |
| 10 | 6,688 | crates/axeyum-solver/src/auto.rs |
| 11 | 5,652 | crates/axeyum-solver/tests/symbolic_execution.rs |
| 12 | 5,245 | crates/axeyum-cnf/src/lib.rs |
| 13 | 5,179 | crates/axeyum-smtlib/tests/smtlib.rs |
| 14 | 4,989 | crates/axeyum-solver/src/ufbv_online.rs |
| 15 | 4,859 | crates/axeyum-bv/src/lib.rs |
| 16 | 4,556 | crates/axeyum-cnf/src/alethe.rs |
| 17 | 4,429 | crates/axeyum-solver/src/reconstruct/tests.rs |
| 18 | 4,169 | crates/axeyum-solver/src/array_axiom.rs |
| 19 | 4,155 | crates/axeyum-solver/src/dpll_lia.rs |
| 20 | 4,010 | crates/axeyum-rewrite/src/canonical.rs |
| 21 | 3,867 | crates/axeyum-solver/src/lra_online.rs |
| 22 | 3,665 | crates/axeyum-solver/src/reconstruct/quant_bv_instance_set_lean.rs |
| 23 | 3,535 | crates/axeyum-solver/src/evidence.rs |
| 24 | 3,446 | crates/axeyum-solver/tests/lean_crosscheck.rs |
| 25 | 3,320 | crates/axeyum-bench/src/bin/glaurung-ordered-trace.rs |

61 files exceed the 1500-line large-file threshold (all flagged candidates).

### Spot-reads of top 8
- **reconstruct.rs (18,517)**: Alethe->Lean proof reconstruction (EUF). 446 fns,
  23 structs, 0 inline `#[test]` (tests split to reconstruct/tests.rs, 4,429
  lines). Content after line ~12,929 is `#[cfg(test)]`-gated *helper* scaffolding
  carrying 15 `#[allow(dead_code)]` markers. Many small step-emitter fns -- the
  bigness is fn count, not one giant fn.
- **abv.rs (14,953)**: QF_ABV eager array elimination. 317 fns, 44 structs, 53
  inline tests interleaved from line 1,461 on -- mixed prod/test file.
- **smtlib/parse.rs (11,598)**: SMT-LIB 2 parser. 289 fns; contains the single
  longest fn in the workspace, `apply_op` at line 10,315 (801 lines), plus
  `parse_command` (249) and `parse_term` (201). Big match-dispatch tables.
- **int_reconstruct.rs (8,876)**: Diophantine refutation -> Lean. 248 fns, ZERO
  tests in-file (tested externally). Repetitive `reconstruct_int_*_to_lean_module`
  family (351/279/243/230/211-line fns).
- **bench/main.rs (7,909)**: monolithic benchmark harness binary -- 236 fns, 30
  structs, 37 tests inline from line 6,600; CLI+corpus walk+stats in one file.
- **incremental.rs (7,821)**: incremental BV solver front end. 239 fns, only 5
  inline tests starting line 7,648.
- **nra_real_root.rs (7,544)**: exact single-var polynomial NRA. 220 fns, 31
  tests from line 7,068.
- **qinst_egraph.rs (7,113)**: e-matching quantifier instantiation. 188 fns, 59
  tests interleaved from line 1,178.

## 2. Function-size hotspots (heuristic brace scan; 16,400 fns measured)

35 fns > 200 lines; 8 fns > 400 lines. Worst offenders:

| Lines | Location | fn |
|-------|----------|----|
| 801 | axeyum-smtlib/src/parse.rs:10315 | apply_op |
| 745 | axeyum-evm/src/symbolic.rs:457 | run_from |
| 577 | axeyum-solver/tests/symbolic_execution.rs:804 | tiny_bv_assembly_imports_memory_program_and_replays (test) |
| 571 | axeyum-lean-kernel/src/int_prelude.rs:206 | build_int_prelude |
| 540 | axeyum-bench/src/bin/glaurung-ordered-trace.rs:608 | load |
| 479 | axeyum-solver/tests/evidence.rs:1668 | produce_evidence_certifies_small_array_axiom_unsats (test) |
| 449 | axeyum-lean-kernel/src/arith_prelude.rs:164 | build_arith_prelude |
| 446 | axeyum-ir/src/eval.rs:462 | apply |
| 378 | axeyum-lean-kernel/src/prelude.rs:169 | build_logic_prelude |
| 351 | axeyum-solver/src/int_reconstruct.rs:1905 | reconstruct_int_affine_growth_to_lean_module |
| 340 | axeyum-rewrite/src/lib.rs:382 | default_rules_fire_on_focused_examples (test) |
| 330 | axeyum-solver/src/reconstruct.rs:3805 | reconstruct_proof_fragment_to_lean_module |
| 320 | axeyum-verify-macros/src/parse.rs:1458 | lower_method_call |
| 310 | axeyum-solver/src/auto.rs:2368 | check_auto_dispatch |
| 300 | axeyum-solver/src/abv.rs:7420 | note |
| 289 | axeyum-solver/src/nra.rs:164 | check_with_nra_impl |
| 284 | axeyum-rewrite/src/canonical.rs:303 | default_rules |
| 266 | axeyum-solver/src/evidence.rs:2352 | produce_evidence |

Corroborated by 102 `#[allow(clippy::too_many_lines)]` suppressions (see section 6).

## 3. Panic/unwrap density per crate

Raw totals (incl. tests), then prod/test split (heuristic: everything after the
first `#[cfg(test)]` in a file, plus tests/ and benches/, is "test").

| Crate | unwrap | expect | panic! | unreach! | todo!/unimpl! | PROD unwrap | PROD expect | PROD panic |
|-------|-------:|-------:|-------:|---------:|--------------:|------------:|------------:|-----------:|
| axeyum-solver | 15,781 | 2,679 | 1,048 | 84 | 0 | 535* | 305 | 10 |
| axeyum-rewrite | 1,245 | 25 | 2 | 6 | 0 | 0 | 24 | 0 |
| axeyum-scenarios | 808 | 17 | 30 | 12 | 0 | **788** | 16 | 1 |
| axeyum-ir | 478 | 77 | 32 | 9 | 0 | 1 | 56 | 25 |
| axeyum-cnf | 344 | 90 | 73 | 5 | 0 | 0 | 34 | 0 |
| axeyum-smtlib | 296 | 98 | 15 | 8 | 0 | 0 | 47 | 0 |
| axeyum-fp | 271 | 11 | 65 | 3 | 0 | 0 | 0 | 0 |
| axeyum-verify | 256 | 165 | 117 | 9 | 0 | 57 | 56 | 26 |
| axeyum-bv | 250 | 52 | 0 | 34 | 0 | 0 | 52 | 0 |
| axeyum-lean-kernel | 152 | 92 | 62 | 7 | 0 | 137* | 65 | 59 |
| axeyum-strings | 21 | 176 | 28 | 1 | 0 | 0 | 14 | 0 |
| axeyum-bench | 86 | 76 | 1 | 3 | 0 | 0 | 9 | 0 |
| axeyum-query | 50 | 5 | 0 | 0 | 0 | 0 | 5 | 0 |
| axeyum-verify-macros | 18 | 5 | 4 | 2 | 0 | 18 | 5 | 4 |
| others (aig/egraph/evm/property/property-macros/wasm) | <=19 ea | -- | -- | -- | 0 | ~0 | <=11 | 0 |

*Correction after drill-down: the solver "prod" 535 is dominated by
`src/reconstruct/tests.rs` (520 unwraps; a test file living under src/, gated by
the parent's `#[cfg(test)] mod`). True solver prod unwraps ~ 15 (12 in
nra_real_root.rs, all guarded-invariant style e.g. `len()>1` before
`last().unwrap()`). Likewise lean-kernel's 137 are in `src/*/**_tests.rs` files;
true prod ~ 1-3.

Genuine non-test unwrap hotspots:
- crates/axeyum-scenarios/src/*.rs -- 788 (arena-builder `.unwrap()` chains in
  scenario constructors, e.g. identities.rs:24-28). Crate is itself a
  test-workload generator, so severity moderated but panics would kill runs.
- crates/axeyum-verify/src/reflect/mir.rs -- 28 (arena op unwraps while lowering
  rustc MIR, runtime input -> panic surface).
- crates/axeyum-verify/src/reflect/llvm.rs -- 20 (same pattern).
- crates/axeyum-verify-macros/src/parse.rs -- 18 (proc-macro; panics become
  compile errors, semi-acceptable).
- axeyum-ir prod panic! = 25, axeyum-verify prod panic! = 26,
  lean-kernel prod panic! = 59 (kernel invariant violations).

Zero `todo!` / `unimplemented!` in the entire workspace.

## 4. Unsafe inventory

- **Zero `unsafe` blocks, fns, or impls in the whole workspace** (regex
  `unsafe (fn|impl|{)` -> 0 hits; all 35 textual "unsafe" hits are identifiers,
  comments, or lint attrs).
- Workspace-level `[workspace.lints.rust] unsafe_code = "deny"` in root
  Cargo.toml; 6 crates additionally `#![forbid(unsafe_code)]`:
  strings, verify-macros, egraph, evm, lean-kernel, verify.
- No SAFETY comments needed; nothing to audit. Exemplary.

## 5. TODO/FIXME/HACK/XXX (all of them -- 10 real markers, 0 FIXME/HACK)

| Location | Text |
|----------|------|
| axeyum-ir/src/value.rs:598 | TODO(P2.7 A.1b): Seq handling (non-scalar sibling guards) |
| axeyum-ir/src/value.rs:632 | TODO(P2.7 A.1b): Seq handling (mirror) |
| axeyum-ir/src/value.rs:673 | TODO(P2.7): empty non-string sequences precise sort |
| axeyum-solver/src/string_theory.rs:67 | incrementality TODO |
| axeyum-solver/src/string_theory.rs:269 | tight core is an optimization TODO |
| axeyum-solver/src/auto.rs:5912 | TODO(P2.7 A.1b): no sequence feature/route yet |
| axeyum-solver/src/evidence.rs:3500 | Seq no-op for now (TODO P2.7 A.1b) |
| axeyum-property/src/reproduce.rs:90,97 | generated-code `// TODO` placeholder (by design) |
| axeyum-lean-kernel/src/lean_pp.rs:126 | export slice TODO (Lean inductive regen) |

All tagged to plan phases (P2.7/A.1b); no untracked debt markers. XXX hits were
false positives (test strings "XXX").

## 6. Allow-attribute suppressions

485 total `#[allow(...)]` across workspace. By crate: solver 277, fp 50,
rewrite 37, smtlib 24, ir 20, bench 20, lean-kernel 15, verify 11.
Top kinds: too_many_lines 102(+10 combined), many_single_char_names 98,
too_many_arguments 65(+8), similar_names 26, cast_precision_loss 23.
`#[allow(dead_code)]`: 26 hits; **cluster of 15 in
crates/axeyum-solver/src/reconstruct.rs** (lines 8516-18508) on cfg(test)-shared
helpers -- flagged as the one real dead-code cluster.

## 7. Duplication signals

- `fn collect_top_conjuncts(arena, term, out)` -- **17 identical copies** across
  axeyum-solver/src (array_finite, set_cardinality, auto, array_xor_swap,
  array_sort2, quant_affine_growth_cert, quant_nested_xor_cert, nra_even_power,
  array_binary_search, bv_uf_local, array_write_chain, array_memcpy,
  term_identity, quant_residue_cert, array_axiom, ufbv_finite,
  bv_forall_nonconstant).
- `fn contains_quantifier(arena, term)` -- **16 copies** (quant_* modules,
  reconstruct/quant_bv_instance_set_lean, rewrite/quantifiers, skolem_alethe...).
- `*_online.rs` family (lia/lra/ufbv/uflia/uflra, 15,724 lines combined):
  uflia_online vs uflra_online share 53 of 87 distinct fn names -- parallel
  copy-adapted theory solvers. `fn propagate` in 8 files, `fn solve` 18,
  `fn check` 19 across src.
- Repeated literal test block: `panic!("the BV system is unsafe (42 reachable)...")`
  duplicated in 4 test files (pdr_lia, pdr_lra, imc_lia, imc_lra).
- axeyum-solver has 155 src modules, many being per-pattern "cert" modules with
  the same skeleton (collect conjuncts -> match pattern -> emit cert).

## 8. Test ratio per crate (src lines vs tests/+benches/ dir lines; inline #[cfg(test)] not separated)

| Crate | src | tests dir | ratio |
|-------|----:|----------:|------|
| axeyum-solver | 208,668 | 104,619 | 0.50 (plus heavy inline tests; 264 test files) |
| axeyum-strings | 7,210 | 6,513 | 0.90 |
| axeyum-verify | 3,902 | 8,240 | 2.11 |
| axeyum-property | 2,970 | 2,237 | 0.75 |
| axeyum-smtlib | 14,411 | 5,179 | 0.36 |
| axeyum-evm | 3,456 | 1,719 | 0.50 |
| axeyum-ir | 9,283 | 2,753 | 0.30 |
| axeyum-fp | 7,057 | 948 | 0.13 (+55 inline tests) |
| axeyum-cnf | 23,083 | 756 | 0.03 (inline-test heavy: 344 unwraps in cfg(test)) |
| axeyum-lean-kernel | 15,674 | 482 | 0.03 (tests in src/*/**_tests.rs modules) |
| axeyum-rewrite | 10,988 | 52 | 0.005 (1,245 inline-test unwraps -> inline heavy) |
| axeyum-bench | 11,229 | 0 | inline only (37 tests in main.rs) |
| axeyum-scenarios | 7,702 | 0 | inline only |
| axeyum-aig/egraph/query/bv | 1,015-4,859 | 0 | inline only |
| axeyum-wasm | 72 | 0 | none |

Note: several crates keep tests inline or in src/-embedded _tests.rs modules, so
tests-dir ratio understates coverage; solver alone has ~104k dedicated test
lines plus large inline suites. Overall test volume is high.

## Ranked top-10 quantitative concerns (S1 worst)

1. S2 file-size -- axeyum-solver/src/reconstruct.rs: 18,517 lines / 446 fns,
   0 inline tests, 15 dead_code allows. Split into submodule tree (a
   reconstruct/ dir already exists -- finish the migration).
2. S2 duplication -- collect_top_conjuncts x17 + contains_quantifier x16
   identical copies in axeyum-solver/src. Hoist both into a shared term-utils
   module (~33 deletions, one canonical impl).
3. S2 function-size -- apply_op, axeyum-smtlib/src/parse.rs:10315: 801 lines in
   one fn inside an 11,598-line parser. Split per-theory op tables.
4. S3 panic surface -- axeyum-scenarios: 788 non-test `.unwrap()` on arena
   builders (e.g. identities.rs:24-28). Thread `?`/expect with context; a bad
   width panics the whole workload generator.
5. S3 file-count/size -- 61 files > 1500 lines (9 files > 7,000). Adopt a
   per-module size budget; worst crate axeyum-solver (155 modules, 208k src
   lines).
6. S3 duplication -- *_online.rs solver family: 15,724 lines, uflia/uflra share
   53/87 fn names. Extract a generic theory-online skeleton
   (trait + shared CDCL(T) loop).
7. S3 panic surface -- axeyum-verify/src/reflect/{mir.rs (28), llvm.rs (20)}
   unwraps while lowering compiler output (runtime input). Convert to
   Result-returning lowering.
8. S3 lint-suppression mass -- 485 #[allow] total; 102 too_many_lines + 65
   too_many_arguments concentrated in solver (277). These are the mechanical
   echo of items 1/3/5; burn down alongside splits.
9. S4 mixed prod/test files -- abv.rs (14,953 lines, 53 interleaved tests from
   line 1,461) and qinst_egraph.rs (59 tests from line 1,178) interleave test
   modules mid-file; move to trailing tests module or _tests.rs for reviewability.
10. S4 test copy-paste -- identical BMC/PDR/IMC guard blocks (e.g. the
    42-reachable panic string x4) across pdr_lia/pdr_lra/imc_lia/imc_lra tests;
    a shared tests/common transition-system fixture would cut ~hundreds of lines.

Positives worth stating: 0 unsafe blocks + workspace deny(unsafe_code);
0 todo!/unimplemented!; only 10 TODOs, all phase-tagged; true production
unwrap count outside scenarios/verify is near zero (guarded-invariant style);
test volume is very high (~110k+ dedicated test lines).
