# Deferred, off-by-default, and unreachable: a code survey

**Date:** 2026-09-10
**Lane:** SWEEP-1-deferred
**Status:** survey only — nothing in this document was fixed. It is a
dispatch list.

## Why this exists

Drilling into why z3 refutes a QF_UF benchmark in 0.04 s that we took 75 s
on, the cause was one sentence in a doc comment on
`crates/axeyum-solver/src/euf_egraph.rs`'s `EufTheory::propagate`:

> Sound EUF theory propagation: the unassigned equality atoms whose two sides
> are **already congruent** ... each entailed `true` ... (Disequality
> entailment — an atom forced `false` — needs the fuller "distinct classes"
> analysis and is deferred.)

We propagated equalities true and never propagated anything false.
Implementing the deferred half took conflicts from 94,100 to 623 (z3 needs
559) and the solve from 75.6 s to 19.8 s.

Three more of the same shape landed the same day: a feature documented "off
by default" that had been on since 2 August; four tuning constants labelled
"zero effect" that were the live ones; and `RestartPolicy::mode_switching` /
`PhasePolicy::scheduled`, implemented and tested and unreachable from the
CDCL(T) driver because `set_policies` had only two callers.

This survey looks for the rest, and ranks by whether a cost is **measurable**.

## The ranked list

Rank is (does it sit on a shipping path) x (can I name the observation that
prices it) x (is the deferred half already half-built). "Shipping path" means
a non-test, non-example caller chain from a public entry point. **Nothing
below was compiled, benchmarked, or executed** — every "observation" is a
proposal, not a result, except where a number is quoted from an in-tree
document and attributed.

### Tier A — the deferred half is already built, and a counter already prices it

| # | site | what is deferred / unreached | shipping path | the observation that would price it |
|---|------|------------------------------|---------------|--------------------------------------|
| A1 | `crates/axeyum-solver/src/reconstruct.rs:1762` | Scan order. `datatype_structural_refutation` is tested **before** `has_datatype`: <br>`} else if crate::datatype_acyclicity::datatype_structural_refutation(arena, assertions).is_some() {` <br>`    ProofFragment::DatatypeStructural` <br>`} else if has_datatype {` <br>`    ProofFragment::Datatype` <br>`DatatypeStructural` is on the **StructuralAttestation** list (`reconstruct.rs:1267`) — a contentless `axiom P` / `axiom Not P` module. `Datatype` is the branch that reaches the four **axiom-free** Lean reconstructors at `reconstruct.rs:2310-2322`. `datatype_acyclicity.rs:1-3` says it covers *"acyclicity (occurs-check), constructor distinctness, constructor injectivity, and constructor exhaustiveness"* — the same axioms `reconstruct/datatype.rs:133/263/633/999` discharge with a real proof. Verified by reading both sites. | yes: `prove_unsat_to_lean_module` -> `scan_proof_fragment` | **The best hit in the survey.** Lean parity is *every unsat carries a machine-checkable proof*, and this routes an entire fragment family to a proof-free attestation because one arm is ordered ahead of another. Run a QF_DT corpus through `prove_unsat_to_lean_module` and bucket by `LeanModuleContent::of_module_source` (`reconstruct.rs:1247`) — occurs-check and distinct-constructor files should come back `structural-attestation`. Swap the two arms and count how many move to `theory-reconstruction`. Both the artifact and the marker (`STRUCTURAL_ATTESTATION_MARKER`, `reconstruct.rs:1207`) are already machine-readable per module. |
| A2 | `crates/axeyum-cnf/src/xor_propagate.rs:94` | `/// Only implied *units* are applied; implied *equalities* are left for a later substitution slice.` The Gaussian solve computes the implied equalities in full; `:115` keeps only `sol.implied_equalities().len()` and applies units only. | yes: `axeyum-solver/src/sat_bv_backend.rs:1682-1686` builds `InprocessSchedule { xor_propagate: true, .. }`; `inprocess.rs:1165` calls it. Live on the `prove_unsat` route. | **The counter is already wired and already emitted on every shipping inprocess run**: `inprocess.rs:1173` does `observer.count("xor_equalities_available", ..)`. Read it off any QF_BV bench run with `--prove-unsat`; the value is the number of variable merges being discarded. The substitution machinery it would need also already exists (`axeyum-cnf/src/decompose.rs`, equivalent-literal substitution + `CnfAssignment` reconstruction). Structurally the closest match to the EUF case: computed, discarded, priced by a counter that is already running. |
| A3 | `crates/axeyum-solver/src/string_theory.rs:270` | `/// A tight core is an optimization TODO.` — `check_conflict` returns the **entire active equality + disequality set** as the conflict clause rather than a minimized core. | yes: `StringTheory::assert` -> `check_conflict`, driven by `cdclt::CdclT` on every QF_S / QF_SLIA query | Structurally the EUF case again: an unminimized conflict clause is a weak learned clause, and weak learned clauses show up as a conflict-count blowup. Count `SearchCounters::conflicts` (`axeyum-cnf/src/proof_sat.rs`) on the string corpus before and after minimizing — the same instrument that priced the EUF fix at 94,100 -> 623. |
| A4 | `crates/axeyum-cnf/src/xor_matrix.rs` (1,595 LOC), exported at `lib.rs:169` | `IncrementalXorMatrix` / `XorMatrixStep`: a complete Gaussian-on-trail propagator **with row-provenance reasons** (`:85`, `:852`). `xor_cdcl.rs:51` defers exactly this: *"This watched-literal scheme is sound but incomplete versus full Gaussian elimination ... A complete Gaussian-on-trail propagator (with row-provenance reasons) for the implications this misses is a later enhancement."* | **no shipping caller**: `rg -n '\b(IncrementalXorMatrix\|XorMatrixStep)\b' -g '*.rs' -g '!target/**' -g '!references/**' .` returns 3 sites — the `lib.rs` re-export and `crates/axeyum-cnf/benches/xor_matrix_gauss.rs`. Nothing in any crate's `src/`. | Complete propagator sitting beside an incomplete one; conflict count is the price. `solve_with_xor_cdcl_conflicts` (`xor_cdcl.rs:196`) and `_reductions` (`:207`) are already instrumented, and `crates/axeyum-solver/tests/xor_cdcl_curated_measure.rs::xor_cdcl_vs_batsat_on_curated_multipliers` (`#[ignore]`d, 2M-conflict budget) exists to answer "did xor_cdcl decide something batsat did not". Benches `xor_matrix_rref` / `xor_matrix_assign_backtrack` already exist. |
| A5 | `crates/axeyum-solver/src/capabilities.rs:489` and `:613` | `"Propagation under-approximated (deferred); non-LRA atoms decline gracefully"` and `"Propagation deferred; non-LIA atoms decline gracefully"`. Verified verbatim at both lines. | yes: these are the shipped capability records for the online LRA and LIA theories | **The same sentence, in the same position, as the EUF one.** Soundness-neutral: under-approximate propagation costs search, never a verdict. Observation is identical to the EUF fix's — conflicts per solve on QF_LRA / QF_LIA. If those theories expose no conflict counter, instrument the propagation boundary named at `config_registry.rs:4528` (`deferred_feasibility_conflict`). |
| A6 | `crates/axeyum-solver/src/string_theory.rs:62` | `/// The word core's derived Facts over sub-components still do not propagate because most do not coincide with a tracked atom.` — derived facts are computed, then dropped. | yes, same theory and driver | Instrument derived `axeyum_strings::Fact`s per solve against how many reach a tracked atom. A high derived-but-dropped ratio is the "compute it and throw it away" shape. |
| A7 | `crates/axeyum-solver/src/config_registry.rs:4134` (`AXEYUM_LAZY_SKELETON`) | The default is `cold`. The registry entry's own text records that `warm` **was measured 3-4x faster** on the propositional half (`1,211 -> 263 ms`, `1,674 -> 570 ms`, `480 -> 122 ms`) and **decided nothing new** (2 of 16 either way, the same two files), with the arms pinned to agree round-by-round by `the_warm_and_cold_arms_agree_round_by_round`. | yes: env-selected, default `cold` | The default rests on the **absence of a wider measurement** ("16 files of one division is not a basis for that"), not on a negative result — which is the opposite of row D1. The observation is the division-wide A/B: one binary, `AXEYUM_LAZY_SKELETON=warm` vs unset, wall clock per file across every lazy-SMT division. Counter: `lazy_smt_counters.rs::record_skeleton`, plus `nra_hist` / `nra_max_round`. |
| A8 | `crates/axeyum-smtlib/src/bounded_completeness.rs:64`, decline list at `:418`, cap at `:57` | `is_bounded_complete` gates an `unknown -> unsat` **upgrade**, and declines on any `let` (line 418 of the rejected-construct list), any `Int`/`Real` `declare-fun`, and any integer literal >= `MAX_SAFE_INT_LITERAL = 1 << 20`. `let` is ubiquitous in real SMT-LIB text. Verified: the decline list and the cap both read as described. | yes, **front door**: `crates/axeyum-solver/src/smtlib.rs:2397` `apply_bounded_completeness_unsat`, which fires on `Unknown` with `UnknownKind::Incomplete` and detail `"no model within the bounded integer width"`, then calls `is_bounded_complete(input)` and returns `Unsat`. Verified by reading the function. | Every declined query here is an `unknown` that is **provably an `unsat`** — a lost decision on the parity metric, recovered by widening the test rather than by any solver work. Run the QF_S / QF_SLIA corpus, count queries ending `Unknown` with that exact detail whose only C3 failure is a `let` or a literal in `[2^20, 2^31)`. Existing harnesses that would move: `crates/axeyum-solver/tests/bounded_completeness_unsat.rs` and the adversarial `crates/axeyum-solver/tests/bounded_completeness_fuzz.rs` (the guard that must keep holding). |
| A9 | `crates/axeyum-egraph/src/lib.rs:1025`, `:1036`, `:1018` | `EGraphCounters` collection is opt-in and **nothing outside the crate ever opts in**. `set_counting`, `reset_counters` and `proof_reroot_steps` have zero call sites outside `crates/axeyum-egraph/`, so `count_ops` is `false` for the lifetime of every shipping e-graph and `counters()` always returns zeros. Verified: `rg -n '\bset_counting\b' crates/` outside `axeyum-egraph` returns nothing; positive control `ematch_many_candidates_indexed` returns two external hits in `qinst_egraph.rs`. | the consumer exists: `crates/axeyum-solver/src/qinst_egraph.rs:5438`, `:5880` | `lib.rs:379` states the exact question the instrumentation exists to answer and it is **currently unanswered on any real run**: *"forest re-root walk actually `O(1)` amortized, or does it revisit a growing chain"*. This is the same shape as the `TheoryEngineCounters` that priced the EUF fix — one `set_counting(true)` in the solver's e-graph bridge plus a bench-lane dump of `proof_reroot_steps` turns a dark instrument on. Cheapest item in Tier A by far. |

### Tier B — on a shipping path, cost is real, the measurement needs building

| # | site | what is deferred / unreached | shipping path | the observation that would price it |
|---|------|------------------------------|---------------|--------------------------------------|
| B1 | `crates/axeyum-solver/src/string_theory.rs:64` | `/// The word core is not incremental: the theory re-runs the refuter from scratch on each representable assertion ... This is correct but not cheap; a backtrackable word core is the incrementality TODO.` | yes, same route as A3 | Wall time inside `StringTheory::assert` as a share of total solve on the string corpus. `cargo test -p axeyum-solver --features full --test qf_slia_fixed_splice` and the `:status` corpus sweep both exercise it. |
| B2 | `crates/axeyum-solver/src/backend.rs` — `lazy_bv`, `lazy_bv_abstract_ite`, `xor_cdcl_fallback`, `incremental_positive_and_flattening` | Four `SolverConfig` bools, all `default = false`, that **nothing outside tests and the Python bindings ever sets true**. `axeyum-bench` has `--inprocess`, `--vivify`, `--native-cdcl`, `--prove-unsat` and **no flag for any of these four**. | partly: reachable from `axeyum-py` (`crates/axeyum-py/src/solver/results.rs:146-152`) and `scripts/prove-tock-log2.py`; **not** from `axeyum-bench`, which is the instrument for the Z3 head-to-head claim | The parity benchmark structurally cannot exercise three implemented solver routes. Add the flags and re-run `just bench-public-qfbv-sat-bv-compare` per arm. For `xor_cdcl_fallback` specifically, seven counters are already stamped — `xor_cdcl_fallback_fired`, `_unsat`, `_sat`, `_unknown`, `_no_xor`, `_skipped_size`, `_unsat_drat_checked` (`sat_bv_backend.rs:1753-1822`) — and every `_unsat` / `_sat` is an `Unknown` the shipping route returns today. Admission is bounded by `XOR_CDCL_FALLBACK_MAX_CLAUSES`, so the downside is capped. Prior art exists for `lazy_bv` (`docs/research/05-algorithms/lazy-bitblasting-p21-findings.md`) — read it before assuming this is unmeasured. |
| B3 | `crates/axeyum-solver/src/backend.rs:390` + `:475` | `cnf_vivify` defaults to **`true`**, but its own doc says *"A no-op unless `with_cnf_inprocessing` is also on"* — and `cnf_inprocessing` defaults to **`false`**. The shipped default of `cnf_vivify` is inert. | yes: this is the default config every route builds | The "constant labelled zero-effect that is live / live constant that is zero-effect" shape, inverted. Assert it: flip `cnf_vivify` with `cnf_inprocessing` off and require byte-identical CNF. Then price inprocessing itself with `--inprocess` on the micro corpus. |
| B4 | `crates/axeyum-solver/src/euf.rs:748` | `/// for an arithmetic-sorted function the witnessing model is not yet built (scalar-keyed function tables) so 'sat' degrades to a sound CheckResult::Unknown — never a wrong answer.` | yes: `check_with_uf_arithmetic`, from the QF_UFLIA / QF_UFLRA dispatch | A **lost decision**, not a slow one — directly on the parity metric. Count `Unknown` verdicts on satisfiable QF_UFLIA / QF_UFLRA benchmarks; the `progress_frontier` ratchet already carries uflra/uflia families to read the delta from. |
| B5 | `crates/axeyum-solver/src/incremental.rs:1740` and `crates/axeyum-solver/src/bmc.rs:151` | `check_with_memory` *"re-solves all active assertions one-shot via the full pure-Rust dispatcher, so it does not yet reuse the warm CNF for deferred theory constructs"*. `bounded_model_check_with_memory` therefore **discards the warm solver at every depth**. | yes: `axeyum-evm` symbolic execution and every BMC over symbolic memory | The A/B is already built and the docs assert the arms agree on array-free input: run `bounded_model_check` (warm) against `bounded_model_check_with_memory` (cold) on an array-free system at increasing depth. The gap is the price. ADR-0030 follow-up. |
| B6 | `crates/axeyum-rewrite/src/arrays.rs:105` | `/// Read-over-write is already applied (stores are eliminated) in this abstraction; only select congruence is deferred.` `abstraction()` returns the relaxation with **no select-consistency lemmas**. | shipping surface; the lazy consumer lives in `axeyum-solver`. The adjacent `selects()` accessor already returns exactly the `(array, index, fresh result)` triples a lemma generator needs — **half-built**. | Strong match on the "state exists and is under-used" axis. Count how many select pairs a candidate model violates per refinement round on QF_ABV — i.e. how many lemmas the lazy loop re-derives. |
| B7 | `crates/axeyum-solver/src/ufbv_online.rs:5` | `/// base selects and reads through stores receive fresh scalar results, while store hit/miss axioms are deferred.` | yes: the canonical online QF_UFBV / QF_ABV / QF_AUFBV combination over `cdclt::CdclT` | Deferred axioms admit models the array semantics forbid, which the driver must refute by search. Count CDCL(T) conflicts and refinement rounds on the QF_AUFBV slice against the eager `check_with_array_elimination` route (ADR-0010) on the same files. |
| B8 | `crates/axeyum-bv/src/lib.rs:64`, `:406` | *"All other operators are conservative barriers that retain the existing full-width lowering."* Add/mul/div have no bit-local demand rule, so `((_ extract 0 0) (bvadd x y))` materialises the whole adder. | yes: demand lowering on the bit-blasting route | **An existing test already pins the gap**: `crates/axeyum-bv/src/lib.rs:4626`, `demanded_lowering_uses_conservative_full_arithmetic_barrier`, asserts `term_bits_lowered > term_bits_demanded`. A ripple-carry rule for `bvadd` flips that to `==` on that exact test. Corpus counters: `BitDemandStats::{term_bits_available, term_bits_demanded, term_bits_lowered}`. Costs most on the quadratic multiplier/divider circuits (`bv/src/lib.rs:100`). |
| B9 | `crates/axeyum-solver/src/word_reconstruct.rs:34-39` | Three declared string conflict classes decline: variable-prefix cancellation (`x ++ "a" = x ++ "b"`), the self-loop / length family (`x = "a" ++ x`), and regex-derivative emptiness. | yes: `WordEquation` is declared `TheoryReconstruction` (`reconstruct.rs:1323`), so a declined shape becomes a hard `Err` from `prove_unsat_to_lean_module` | **The size-measure argument the self-loop family needs already exists** for datatypes (`reconstruct/datatype.rs:999`, `recursive_datatype_size`). `Str = List Char` is a recursive inductive; the measure transfers. Cheapest of the three. Observation: bucket QF_S / QF_SLIA unsat files by which `word_reconstruct` arm fires. `word_reconstruct/tests.rs:178` and `:192` are the two pinned declines and are the counters. |
| B10 | `crates/axeyum-solver/src/reconstruct.rs:3408` + `crates/axeyum-solver/src/reconstruct/arithmetic.rs:4766` | The SOS route's fallback renders an attestation instead of a proof — *"The module contains none of the reasoning it attests to"*, byte-identical across two different queries. Cause at `reconstruct.rs:1332`: only `is_single_square_lt_zero` is accepted; general SOS *"needs the degree-2 ring normalizer and is a later slice"*. The same missing normalizer declines non-unit Farkas multipliers on the `la_generic` path. | yes | `ProofFragment::Sos` self-declares `TheoryReconstruction`, so the fallback raises `ReconstructError::ModuleContentMismatch` — already instrumented. Count those errors per QF_NRA corpus run; each is an SOS query with a valid Rust certificate and no Lean proof. **One deferred component, two measurable decline sites.** |
| B11 | `crates/axeyum-solver/src/capabilities.rs:769` | `"INTEGER difference logic (QF_IDL) is NOT covered: it routes through ArithDpll, which has no theory reconstruction and declines"` | yes: `scan_proof_fragment` -> `ProofFragment::ArithDpll` -> the shared attestation emitter | QF_IDL vs QF_RDL through `prove_unsat_to_lean_theory_module`: QF_RDL returns modules, QF_IDL returns `Err` on 100 % of unsats, from the same scan. The `lean_crosscheck` family `qf_rdl_difference` (`capabilities.rs:771-775`) is the harness; it has no QF_IDL sibling. |
| B12 | `crates/axeyum-solver/src/qfdt_simp_alethe.rs:890`, `:1155` | `prove_qf_dt_distinct_alethe_carcara` and `prove_qf_dt_injective_alethe_carcara` — implemented, tested, **no dispatch caller**. Every non-test reference is a `lib.rs` re-export (`:333`, `:1286`). | **no shipping caller found**: `rg -n 'prove_qf_dt_(distinct\|injective)_alethe_carcara' -g '*.rs'` returns the two definitions, two re-exports, two capability rows, two comments, and the two test files | The "implemented, tested, unreachable from the driver" shape. Two Carcara certificate producers exist and no query can emit them. Count Alethe/Carcara artifacts per QF_DT corpus run bucketed by producer; these read 0 against passing tests. Compare `prove_qf_dt_unsat_alethe_via_simplification` in the same re-export block — the delta is the measurement. |
| B13 | `crates/axeyum-solver/src/datatype_native.rs:468` | `"datatype fields; array/UF datatype fields are not yet supported"` | yes: the native datatype route's admission test | Count admission declines on QF_DT / QF_UFDT attributable to this message. An admission decline is a lost decision or a slower route. |
| B14 | `crates/axeyum-cnf/src/xor_extract.rs:66` | *"The other gate kinds. The encoder already plans NOT-ITE, NOT-AND and AND-tree gates and counts them in `CnfEncodingStats`; only XOR is recorded here, because only XOR has a consumer today."* Corroborated: `crates/axeyum-aig/src/lib.rs:742` has `detect_xor_gate` and no `detect_and_gate` / `detect_ite_gate`. | yes: gate-hint recording on the encode path | Three counters are **already populated on every encode**: `CnfEncodingStats::{not_ite_gates, not_and_gates, and_tree_gates}` (`axeyum-cnf/src/lib.rs:2627-2631`). Their ratio to `xor_gates` on a bit-blasted corpus is the size of the un-hinted population. |
| B15 | `crates/axeyum-rewrite/src/int_divmod.rs:471-485` | `MAX_CONGRUENCE_GROUPS = 48`. Above 48 distinct zero-divisor dividends the pass emits `ZeroDivisorCongruence::Omitted` and `sat_transfers` goes false — a forced `unknown` on the sat side. The doc names the fix: *"the follow-up to make it unconditional is to route `_/0` through the lazy-CEGAR UF congruence path."* | yes: `eliminate_int_divmod` -> `crates/axeyum-solver/src/preprocess.rs`; `sat_transfers` is the caller-side guard (ADR-1730) | Count `ZeroDivisorCongruence::Omitted` over QF_NIA / QF_LIA, plus the **max** distinct-zero-divisor-dividend count per instance. The doc asserts ">48 is pathological"; that claim is exactly what the counter prices. `crates/axeyum-rewrite/tests/int_divmod_witness.rs` is the existing faithfulness harness. |
| B16 | `crates/axeyum-smtlib/src/parse.rs:9853`, `:9914`, `:9979` | `str.replace_all`, `str.replace_re`, `str.replace_re_all` are wired **ground-only**; every symbolic operand is a clean `Unsupported` -> `unknown`. The decline text names the bounded sub-case itself: *"whose round count is bounded only when `len(a)` is concrete"*. | yes: the `str.*` dispatch table; `SmtError::Unsupported` propagates to `CheckResult::Unknown` via `axeyum-solver/src/smtlib.rs` | The three decline strings are unique and greppable — count them as `unknown` reasons over QF_SLIA. **The recoverable slice is precisely measurable**: instances with a symbolic subject and a constant pattern, which the comment says is the bounded case. |
| B17 | `crates/axeyum-smtlib/src/parse.rs:7811`, `:7743` | `build_trigger_term` declines the **whole trigger group** on any non-`apply` root — an interpreted operator, an indexed identifier, a `define-fun` macro, a nested binder, a literal — plus anything past `MAX_TRIGGER_DEPTH = 32`. The quantifier then gets *no* trigger, not a degraded one. | yes: quantifier parsing -> `axeyum_rewrite::instantiate_with_triggers`, called from `crates/axeyum-solver/src/auto.rs:9090` and `:9117`. A declined group silently degrades to the enumerative route at `auto.rs:9061`. | Counter on `build_trigger_term` returning `None` over UF / AUFLIA, split by reason (interpreted op / indexed id / macro / depth). Then compare instance counts from `instantiate_with_triggers` against the enumerative fallback on the same queries. `quantifiers.rs:336` (`CHAIN_INSTANCE_CAP = 4096`) is the other end of the same measurement. |
| B18 | `crates/axeyum-rewrite/src/arrays.rs:393`, `:427` | `"eager array elimination supports only bit-vector-indexed, bit-vector-valued arrays"` and `"bounded extensionality currently supports only bit-vector-indexed arrays"`. Mirror-image gap on the parser side: `parse.rs:18946` `"eqrange currently supports only Int-indexed arrays"`. | yes, and broadly: `eliminate_arrays` is called from `abv.rs:20`, `abv/array_elim_certificate.rs:198`, `euf.rs:2005`/`:2162`, `qfabv_elim_alethe.rs:117`, `quant_finite_cert.rs:265`, `uflra_interpolant.rs:95`, `uflia_interpolant.rs:101`. An `Unsupported` from either site kills the whole ABV route. | Count `ArrayElimError::Unsupported` with each exact message over QF_ALIA / AUFLIA / QF_AUFLIA, where **Int-indexed arrays are the norm**. `crates/axeyum-solver/src/abv/instruments.rs:83` already instruments `abstract_arrays` vs `eliminate_arrays`; the decline counter belongs in the same struct. |
| B19 | `crates/axeyum-smtlib/src/regex.rs:70-75` vs `crates/axeyum-strings/src/regex/membership.rs:44` | `MAX_NFA_STATES = 256`, justified *"Generous enough for the curated corpus's regexes"* — a curated corpus, not SMT-COMP. It also governs `re.inter` (product NFA) and `re.comp`/`re.diff` (subset construction over a 256-byte alphabet, which blows 256 states almost immediately). The sibling engine's cap for the same job is `DEFAULT_MAX_STATES = 20_000`. | yes: `compile_regex` <- `str.in_re` / `str.replace_re` / `str.replace_re_all` | **A 78x spread between two caps on the same job is itself the measurement.** Count the decline string over SMT-COMP QF_S regex families and record the *distribution* of realized NFA sizes, not just the over-cap count. The `re.comp` / `re.diff` sub-count is the interesting one. |

### Tier C — real, lower expected value, or the deferred thing is a measurement rather than a diff

| # | site | what is deferred / unreached | shipping path | the observation that would price it |
|---|------|------------------------------|---------------|--------------------------------------|
| C1 | `crates/axeyum-solver/src/reconstruct.rs:1257-1285` | 29 of 65 fragments funnel through one shared emitter whose *"output does not depend on the query at all beyond the generated constant names"* — `LraDpll`, `ArithDpll`, `BoundedIntBlast`, `BvAbstraction`, `BoolEufOnline`, `SetCardinality`, `FiniteDomainEnum`, the six concrete-program fragments, and others. | yes: `prove_unsat_to_lean_module` | The largest coverage hole by fragment count, and the doc is honest about it (`reconstruct.rs:1163`: *"an artifact that cannot fail is not thereby a proof"*), which makes it measurable. Observation: the `theory-reconstruction : structural-attestation` ratio over the full corpus from `LeanModuleContent::of_module_source`. `capabilities.rs:463` records one such count — *"5 attestations, 17 declined, 0 failures"* over 135 bound instances (2026-08-18) — a single-family sample, not a corpus number. |
| C2 | `crates/axeyum-solver/src/config_registry.rs:2825` (`INT_REAL_RELAX_BUDGET_SHARE`) | `guarded_by: "nothing: see the note"`, and the note: *"When the shrunk share underflows to zero the code returns the caller's config UNCHANGED — the full, unshrunk timeout — rather than skipping the refuter or clamping to a floor. The sharing policy is bypassed silently at exactly the small-budget end where starvation matters most."* | yes | The literal "named guard does not actually guard" shape: the guard field says `nothing`, and the divisor stops dividing where division matters. Counter: budget-share computations that underflow to zero, at `auto.rs::decide_int_box_by_evaluation`'s caller. On a short-deadline corpus (`--timeout 1s`) that is the bypass rate. |
| C3 | `crates/axeyum-solver/src/config_registry.rs:2836` (`MAX_BOUND_PROP_ROUNDS`) | *"`for _ in 0..256 { .. if !changed { break } }` — reaching the cap without a fixpoint hands the caller partial bounds with no indication the fixpoint was not reached. The incompleteness is invisible."* | yes | Soundness-neutral (declines downstream are sound), but the decline is unattributable. Counter: loops exiting on the cap rather than on `!changed`. `RouteOutcome::Declined(DeclineReason::Incomplete)` (`route_trace.rs:123`) is the existing sink for the attribution. |
| C4 | `crates/axeyum-solver/src/backend.rs:70`, `crates/axeyum-bv/src/lib.rs:140` | Both sparse BV lowering modes are off by default: *"They are not used by `lower_terms` or `lower_terms_demanded`; callers must select this policy explicitly while the Glaurung acceptance gate is being calibrated."* `RangeSliced` is not bound in Python at all (`axeyum-py/src/solver/results.rs:139` errors). | `with_bit_lowering_mode` / `with_demand_sliced_lowering` / `with_range_demand_slicing` are called only from `axeyum-bench/src/main.rs:4649-4654` and `examples/qfbv_sat_attribution.rs:95` | **The deferred thing is the measurement, not the code.** Counters exist (`RangeDemandDecision`, `estimated_bits_avoided`, `analysis_work`, `range_merges`, `range_promotions`) and the bench already has a `--range-demand-slicing` policy A/B (`axeyum-bench/src/main.rs:8004-8025`). The stated blocker is the ADR-0157 real-corpus / Glaurung acceptance gate — a run. |
| C5 | `crates/axeyum-cnf/src/proof_sat.rs:599` | *"The rephase schedule and the target-mark release are implemented and tested, but changing two heuristics at once makes neither measurable; this default flips only when the measurement says it should."* `SearchPolicies::default()` is still `tiered()` + `pinned()` + `luby()`; `scheduled_phase()`, `releasing_phase()`, `legacy_clause_db()`, `ema_restart()` have **no non-example, non-test constructor**. | partly fixed today: `axeyum-solver/src/native_cdclt.rs:624` now routes `search_profile: configured_search_profile()`, but that arm is "`Shipped` unless asked" — the default does not flip | `crates/axeyum-cnf/examples/clause_db_policy_ab.rs` is a ready-made five-arm A/B harness. The in-tree evidence for one arm is `phase_policy.rs:59` — *"`PhasePolicy::releasing` was 48 % better on one and 21 % worse on the other"* — a two-instance sample, too small to flip a default. Run the existing harness wider. |
| C6 | `crates/axeyum-cnf/src/inprocess.rs:1538` | `// Conservative: discard the (unverifiable) strengthening and proceed on the pre-vivify formula.` A whole vivify pass is thrown away when its DRAT does not step-check. Live: `vivify_step_guard: true` in the shipping schedule. | yes | `observer.count("vivify_drat_step_checked", ..)` at `:1535` is the discriminator — every `0.0` is a discarded pass; `vivify_clauses_strengthened` / `vivify_literals_removed` quantify the loss. **This is a correct fail-safe, not a deferral**; the cost is real only if the counter fires. Cheap to check, low expected value. |
| C7 | `crates/axeyum-solver/src/reconstruct/bitblast.rs:1454`, `:1674`, `:1733` | *"the `cong`/`trans`/`bitblast_*` term-equality steps are deferred (never consumed by the refutation, so never forced into the `False` term)."* | yes: `reconstruct_bitwise_clausal`, from the `QfBv` fragment | **Not a hole today — an unguarded invariant.** The deferral is conditional on those steps never being consumed. Observation: a counter of `Ok(None)` returns at `:1674` that are later referenced as a resolution premise. Today it must be 0; a bit-blast emitter change that makes it non-zero turns this into a silent hole, and nothing asserts otherwise. |
| C8 | `crates/axeyum-ir/src/value.rs:649`, `:688`, `:731`; `crates/axeyum-solver/src/auto.rs:10018`; `crates/axeyum-solver/src/evidence.rs:4893` | Five `TODO(P2.7 A.1b)` sites for `Seq` handling; `auto.rs` says *"no sequence feature/route exists yet"*. `evidence.rs:4893` classifies `Seq` as theory-free and says so. | precondition currently holds: no front-end produces `Seq` | Not a perf hit — a missing logic fragment, priced by corpus coverage, not a counter. If a `Seq`-producing front-end lands, `evidence.rs:4893` silently misclassifies. A `debug_assert!` on that arm would price it at zero; there is none. |
| C9 | `crates/axeyum-solver/src/config_registry.rs:3081`, `:3135`, `:3248`, `:2709`, `:2722` | Five budget-share constants self-labelled unmeasured: *"value unchanged and unmeasured"*, *"STILL unmeasured"*, *"cites no measurement at all"*. `:3248` explicitly refuses to launder a date. | yes | Per-rung budget-consumption histogram on QF_UFLIA / QF_UFLRA. `dated_count` / `undated_count` (`config_registry.rs:9615`) and `config_trace_line` are the existing artifacts; `scripts/check-config-registry-staleness.py` leads with the ratio. The discipline is working here — the labels are honest; the values are still unmeasured. |
| C10 | `crates/axeyum-solver/src/config_registry.rs` | **262 entries carry `guarded_by: ""`**, against 488 total `guarded_by` occurrences. The module's own contract (`:62`) is *"`Signal::None` iff `guarded_by` is enforced"*, and `:60-63` warns that `protects` / `on_exceed` on those rows are *"human judgement… not a verified property"* with a measured **~70 % independent agreement** (`:66-74`). | registry surface | Not a specific hole — the **denominator** for C2, C3 and C9. Extend the two-reader agreement study (10 constants, 7 agreements) to a larger sample of the 262. That number bounds how much of the registry can be trusted when picking what to measure next. |
| C11 | `crates/axeyum-rewrite/src/pass_stats.rs` (whole module) | Opt-in term-size diagnostics for every rewrite pass. All seven public fns (`rule_application_counts`, `canonicalize_terms_with_stats`, `eliminate_arrays_with_stats`, `eliminate_functions_with_stats`, `eliminate_int_divmod_with_stats`, `blast_integers_with_stats`, `elim_unconstrained_with_stats`) are re-exported at `lib.rs:77-79` and called **only from this module's own inline tests**. | **no shipping caller found** for any of the seven (control: the same loop over `propagate_values` returns 5 files, `solve_eqs_bounded` returns 5) | `crates/axeyum-solver/src/preprocess.rs:221` runs `canonicalize -> solve_eqs -> elim_unconstrained -> re-canonicalize`, and its own doc (`:168`) says *"One pass is not enough … the encode budget on real corpora"*. `PassSizeDelta` is exactly the "did this pass shrink, grow, or blow up the shared DAG" number. Swap the four `preprocess.rs` call sites to the `_with_stats` variants and emit the deltas in `axeyum-bench`: a per-pass DAG-size profile that does not currently exist. |
| C12 | `crates/axeyum-rewrite/src/lib.rs:135`, `:157` | The equisatisfiable / model-projection half of the rewrite manifest is validated and dead. `ModelProjection::Required` (*"Projection is required but not yet implemented; rule must remain off by default."*) and `::Implemented`, `Preservation::Equisatisfiable`, and `RewriteTestRoute::ModelProjectionReplay` are constructed **only in tests**; `RewriteTestRoute::RandomEvaluator` and `::ProofObligation` have zero construction sites anywhere. Pinned by `default_manifest_enables_only_denotation_identity_projection_rules` (`lib.rs:483`). | manifest surface | **The genuinely equisatisfiable passes are not in the manifest at all** — `abstract_arrays`/`eliminate_arrays`, `abstract_functions`/`eliminate_functions`, `eliminate_int_divmod`, `elim_unconstrained` — so none of them passes through the projection guard that exists for exactly that case. Observation: `default_manifest().rules().len()` against the count of equisatisfiable passes in `preprocess.rs`. Registering one as `Equisatisfiable` + `Implemented` makes `lib.rs:483` fail, which is the measurable trigger. |
| C13 | `crates/axeyum-rewrite/src/elim_unconstrained.rs:562` | `default_inverters()` has **zero callers including tests** (only the definition and the `lib.rs:58` re-export). The pass calls `InverterRegistry::with_defaults()` directly. The doc at `:245` says the caller-supplied-registry entry point is *"how the ablation is run"* (an empty registry makes the pass a no-op), and **no shipping or bench code runs that ablation**. | the entry point exists; the ablation does not | The value of the whole inverter registry (`CoreInverter`, `BvInverter`, `ArithInverter`) is unmeasured. Run the corpus once with `InverterRegistry::new()` and once with defaults through `elim_unconstrained_with`; diff `UnconstrainedElimination::eliminated` and end-to-end solve time. `config_registry.rs:1541` already registers this module as a tuning knob. |
| C14 | `crates/axeyum-smtlib/src/parse.rs:20027` | `// Int↔Real coercions. Constant operands fold exactly; symbolic operands need cross-sort (Nelson-Oppen) reasoning and are not yet supported.` — but the code still **builds** `int_to_real` / `real_to_int` / `real_is_int` for the symbolic case, so the failure surfaces downstream as an unattributed backend `unknown`. | yes: arithmetic dispatch, every QF_LIRA / QF_UFLIRA query with a mixed-sort coercion | **Because the parser does not decline here, this needs a counter at the build site, not a grep of decline strings.** Count non-constant `to_real` / `to_int` / `is_int` arguments in QF_LIRA / AUFLIRA and how many of those instances end `unknown`. |
| C15 | `crates/axeyum-rewrite/src/quantifiers.rs:339`, `:335` | `peel_universals` declines non-prenex assertions and existential residuals; `CHAIN_INSTANCE_CAP = 4096` leaves longer chains uninstantiated (a sound `unknown`). | yes: `instantiate_universals` <- `auto.rs:9061`; `instantiate_with_triggers` <- `auto.rs:9090`, `:9117` (the latter re-runs after Skolemization, the partial mitigation already in place) | Two counters, and they separate two different fixes: (a) assertions where `peel_universals` returns `None` *after* the Skolemization retry, (b) chains exceeding the cap. On UF / AUFLIA that is "we cannot express it" versus "we chose not to expand it". |
| C16 | `crates/axeyum-rewrite/src/alpha.rs:132` | `alpha_equivalent_to_negation` — decides `left ≡ ¬right` up to α-renaming including the `∀x.P ↔ ¬∃x.¬P` dualities. Implemented, property-tested, re-exported at `lib.rs:44`, and **called by nothing outside its own test module** (control: `alpha_equivalent`, same file, same export line, has callers). | **no shipping caller found** | Where it would pay is complementary-literal / tautology detection over quantified assertions in `preprocess.rs`. Measurable as assertions dropped as `true`/`false` by a duality check on UF / AUFLIA. `ALPHA_EQUIVALENCE_STEP_BUDGET` is the cost bound to record alongside. |

### Tier D — traps: looks like a lead, is not

| # | site | why it is not a lead |
|---|------|----------------------|
| D1 | `crates/axeyum-solver/src/qinst_egraph.rs:265-282`, `:336-380`, `:393-402` | `RelevanceCriterion::EqualityOnly` ships; `BooleanUnits` is implemented (`BooleanUnitValuation`), tested, and used by **no shipped arm**. Three further levers ship inert: `rank_by_residual: false`, `max_residual_width: usize::MAX` (*"declines nothing, which is shipped"*), `evict_entailed: false`. Perfect surface match to the motivating incident. **ALREADY MEASURED.** `docs/research/12-performance/uf-instance-selection-2026-09-09.md` ran all seven arms; every one decided **0 of 32**, and its conclusion is *"no arm of this policy can lift it"*. The live finding in that doc is different: the shipped criterion is blind on 85.6 % of scored candidates and the fix is a criterion the equality core cannot express, not a lever. **Do not dispatch this as an unexploited win.** |
| D2 | `crates/axeyum-cnf/src/xor_dpll.rs` (662 LOC), `crates/axeyum-cnf/src/xor_search.rs` (881 LOC) | Exported, tested, no shipping caller — but `config_registry.rs:1394` says `xor_dpll` is *"explicitly the correctness-first (not production) decider for the CDCL(XOR) integration slice"*, i.e. a deliberate differential oracle. `xor_search::xor_implications` is superseded, not pending: `xor_cdcl.rs:33` rejected it because *"its reasons are a connected-component over-approximation"*. Both are scaffolding for A4. |
| D3 | `crates/axeyum-bv/src/lib.rs:91` `lower_terms_profiled` | Genuinely no shipping caller, and already flagged in-tree (`docs/solver-inventory-2026-09/01-sat-core-and-cnf.md:172`, "TEST/BENCH-ONLY"). But the production path does not go dark on profiling — `sat_bv_backend.rs:198` handles `BitLoweringMode::Eager if config.profile_bit_demand` through the deadline-carrying variant. A redundant duplicate, not a lost capability. |
| D4 | aggregate: 1,274 `pub`/`pub(crate)` fns across `crates/*/src` with **zero** non-test callers outside their own file (318 referenced at most once even inside their defining file) | A **population**, not a finding. Most are legitimate public API — accessors, certificate checkers. The useful cut is builder `with_*` methods and policy enum variants whose only non-test constructor is a test; B2 and B3 came out of that cut. Method and false-positive classes are documented under "Method" below. |
| D5 | `crates/axeyum-egraph/src/fast_map.rs:55` | `#[allow(dead_code)] pub(crate) type FastSet<T>` — declared, unused. The sibling `FastMap` is live and the module documents the FxHash swap as measured and verdict-invariant *for the map*, so the `HashSet` sites in `lib.rs` are still on SipHash. The only literal dead-code marker in that slice, and the measurement protocol already exists. Low cost; listed for completeness. Note this file is **untracked in the working tree** at the time of the survey — it may belong to a lane in flight. |

### Stale claims found along the way

Four sites document a deferral that **no longer exists**, and in doing so they
explain away the decline whose real cause is A1's scan order:

- `crates/axeyum-solver/src/qfdt_simp_alethe.rs:37`, `:611` — *"the fragment
  dispatch does not yet route a datatype is-tester proof to a datatype
  reconstructor"*. Contradicted by `reconstruct.rs:2310`, which calls
  `reconstruct_qf_dt_tester_to_lean_module`; `capabilities.rs:1086-1104`
  already grades that route `Assurance::Checked` with a `lean_crosscheck` gate.
- `crates/axeyum-solver/src/qfdt_simp_alethe.rs:865`, `:1130` — distinctness
  and injectivity "deferred too". Contradicted by `reconstruct.rs:2312`, `:2318`.
- `crates/axeyum-solver/src/capabilities.rs:1199`, `:1222` — *"the Lean/kernel
  reconstruction route is deferred (Carcara-only)"* for distinctness and
  injectivity. Same contradiction.
- `crates/axeyum-solver/src/capabilities.rs:1100` — *"injectivity Lean route is
  deferred (needs noConfusion beyond ι)"*. `reconstruct/datatype.rs:633` does
  injectivity with ι + congruence and **no** `noConfusion`.
- `crates/axeyum-solver/src/config_registry.rs:1407` — *"Not yet called from
  production dispatch (only tests)"* about `xor_gauss_drat_refutation`. Stale in
  letter (`sat_bv_backend.rs:1874` is a `src/` caller) and right in effect (that
  caller is behind B2's `xor_cdcl_fallback: false`).

A sixth, in a different crate: `crates/axeyum-smtlib/src/regex.rs:57` lists
`(re.loop …)` / `(_ re.^ n)` under **"Declined (clean `Unsupported`, never a
wrong verdict)"** — contradicted by shipping code in the same file, which
implements both: `:704` `expand_loop(n, Some(n), rest)` for `"re.^"`,
`loop_index` at `:716`, `MAX_LOOP_EXPANSION = 256` at `:732`, and `expand_loop`
at `:738`. Only the over-cap case declines. (The `str.indexof_re` half of the
same sentence is genuine — `parse.rs:7588` declines it as a cvc5 extension.)

`capability_matrix_markdown()` (`capabilities.rs:2188`) is golden-tested against
`docs/research/08-planning/capability-matrix.md`, so three of these publish a
**false capability boundary** in a generated document. A stale registry note is
the same failure mode as the "off by default since August" incident.

## Counts — the scale, not an implication

Canonical sweep: `crates/` only, `-g '*.rs'`, excluding `**/tests/**`,
`**/tests.rs`, `**/*_tests.rs`, `**/examples/**`, `**/benches/**`. Case
insensitive. `target/`, `references/`, `.git/` and `docs/` are outside
`crates/` and so excluded by construction. Counts are **matching lines**, not
distinct findings.

| pattern id | regex | hits |
|---|---|---|
| P01 | `deferr` | 356 |
| P02 | `\b(is\|are) deferred\b` | 29 |
| P03 | `we defer\|defers this\|defer(red)? (this\|that\|it)` | 1 |
| P04 | `not yet\|does not yet\|do not yet` | 153 |
| P05 | `left for\|left to a\|future work\|a later slice\|follow-?up slice` | 76 |
| P06 | `for now` | 9 |
| P07 | `TODO` | 11 |
| P08 | `FIXME` | **0** |
| P09 | `\bXXX\b` | **0** |
| P10 | `\bHACK\b` | **0** |
| P11 | `unimplemented!\(\|todo!\(` | 1 (a doc comment asserting there is none) |
| P12 | `allow\(dead_code\)` | 99 |
| P13 | `incomplete` | 473 |
| P14 | `under.?approximat\|over.?approximat` | 107 |
| P15 | `conservativ` | 236 |
| P16 | `does not handle\|cannot handle\|not handled\|only handles\|handles only` | 36 |
| P17 | `never propagat\|only .{0,30}\btrue\b` | 55 |
| P18 | `off by default\|disabled by default\|opt.in` | 155 |
| P19 | `no effect\|zero.effect\|no measurable\|declines nothing\|inert` | 75 |
| P20 | `unmeasured\|unverified\|untuned\|not measured` | 112 |
| P21 | `a guess\|guessed\|arbitrar\|hand.?picked\|transcribed` | 946 |
| P22 | `no caller\|never called\|not wired\|unreachable from\|no shipping caller` | 41 |
| P23 | `degrade[sd]? to` | 151 |
| P24 | `declin[a-z]* rather than` | 128 |
| P25 | `first slice\|this slice\|initial slice` | 300 |
| P26 | `bails? to\|gives? up\|punt` | 48 |

Interpretation, so the numbers are not read as 3,400 defects:

- **P01 (356) is dominated by a feature name.** "Deferred" in this codebase
  mostly means the *deferred explanation handle* in `cdclt.rs`, the *deferred
  candidate pool* in `qinst_egraph.rs`, and `deferred_final_check` in
  `lra_online.rs` — implemented features, not omissions. P02 (`is deferred` /
  `are deferred`, 29) is the sub-pattern that actually marks an omission, and
  it is where rows 8, 9 and 12 came from.
- **P21 (946) is almost entirely `Arbitrary` (proptest) and `arbitrary`
  precision.** Not triaged. Reported as a raw count only.
- **P13 (473), P15 (236), P23 (151), P24 (128)** are dominated by *sound
  decline* documentation — the codebase's normal way of saying "returns
  `unknown` rather than guessing". That is correct behaviour, not a defect,
  and each one has a real cost only where a counter exists to price it.
  Rows 6 and 11 are the two I could attach an observation to; the rest were
  not individually triaged.

## Positive controls for every zero-return pattern

An empty `rg` is not a negative result. Each pattern that returned zero above
was proved to work by finding it somewhere the exclusions removed:

- **P08 `FIXME` = 0.** Control: the same regex over the whole repo returns
  `docs/reviews/multiagent-20260717/4-axeyum-breadth.md`. The pattern
  matches; there is genuinely no `FIXME` in `crates/*/src`.
- **P10 `\bHACK\b` = 0.** Same control, same file, same conclusion.
- **P09 `\bXXX\b` = 0 in the filtered set.** Control: unfiltered over
  `crates/` the same regex returns 23 lines, all in test files. The word
  boundary and the pattern both work.
- **P11 `unimplemented!(` / `todo!(` = 1.** Control: `panic!\(` with the same
  `!\(` construction matches in 694 files, so `rg` is matching `!(` correctly.
  The single hit is `crates/axeyum-arith/src/lib.rs:20`, a module doc asserting
  *"there is no `todo!()`"* — i.e. the crates genuinely contain no
  `unimplemented!()` or `todo!()` macro call.

Further zero-return checks from the sub-surveys, each with its control:

- **`set_counting` / `reset_counters` / `proof_reroot_steps` outside
  `crates/axeyum-egraph/` = 0.** Control: unfiltered, each returns 9 hits inside
  `axeyum-egraph/src/lib.rs`; and `ematch_many_candidates_indexed` — an
  e-graph method that *is* consumed externally — returns two hits in
  `crates/axeyum-solver/src/qinst_egraph.rs`. Re-verified by hand for row A9.
- **`alpha_equivalent_to_negation` outside `crates/axeyum-rewrite/` = 0.**
  Control: `alpha_equivalent`, same file and same export line, returns hits.
- **`RewriteTestRoute::(RandomEvaluator|ProofObligation)` = 0.** Control:
  `RewriteTestRoute::ExhaustiveSmallWidth` returns 4.
- **`IncrementalXorMatrix` / `XorMatrixStep` in any `src/` = 0.** Control: the
  unfiltered search returns 3 sites — the `lib.rs` re-export and the criterion
  bench.
- **`TODO|FIXME|HACK` in the front-end/rewrite slice = 0** (with `-w`).
  Control: the same command over all of `crates/` returns 11. An earlier run
  without `-w` returned 3 — all false positives on `\uXXXX` escapes in
  `regex_membership.rs`, which is why the word boundary matters.
- **`guarded_by: "…untested|not enforced|by convention|reviewer…"` = 0** in
  `config_registry.rs`. Control: `guarded_by: "…nothing|declin…"` returns 9. No
  entry admits "untested" in those words; the one honest admission is
  `"nothing: see the note"` at `:2825` (row C2).
- **`structural_attestation` / `lean_module_content` in `evidence.rs` and
  `capabilities.rs` = 0.** Control: the same pattern on `reconstruct.rs`
  returns 12. **This is itself the finding behind rows A1, C1 and B11**: the
  attestation-vs-reconstruction distinction exists only in `reconstruct.rs` and
  is surfaced in neither the evidence artifact nor the capability ledger, which
  is why none of those rows has a standing counter.
- **One zero-return that was a false alarm, not a finding**: `axeyum_strings::infer`
  outside `axeyum-strings` = 0, but `infer::infer` *is* reached internally —
  `arrange.rs:70` -> `solve_word_equations` -> `crates/axeyum-solver/src/string_theory.rs:1188`.
  Discarded. Recording it because an unfiltered zero here would have read as a
  dead 1,000-line inference engine.

`rg` here is ripgrep 14.1.1 (the bundled binary), **not** the interactive
`grep`, which on this host is ugrep 7.8.4 and disagrees with GNU grep on
escapes. Every count above was produced by `rg`.

## Coverage: five passes, and where each one is thin

This survey was run as five passes with different file sets. The pattern
batteries and per-slice counts differ, so **do not add the counts together** —
they overlap and use different exclusions.

| pass | file set | size | its own thin spot |
|---|---|---|---|
| whole-tree | all of `crates/` | 2,199 files, 1.89 M lines | pattern-level only; no per-crate triage outside the solver |
| solver core | `axeyum-solver/src` theory, dispatch, incremental, bmc, string | — | did not triage `capabilities.rs` or `config_registry.rs` (delegated) |
| SAT / bitblast | `axeyum-cnf/src`, `axeyum-bv/src`, `axeyum-aig/src` | 37 files, 60,428 lines | did not enumerate all ~300 `pub` items for callers; spot-checked the enum/builder/module surfaces instead |
| reconstruction | `reconstruct*`, `word_reconstruct*`, `qfdt_simp_alethe.rs`, `capabilities.rs`, `config_registry.rs`, `evidence.rs` | 50,696 lines | **did not enumerate the ~134 `declin` hits in `reconstruct/quant_bv_instance_set_lean.rs`** — the highest-density decline file in the slice and the one sampled least. Plausibly holds Tier-A/B candidates. Also did not audit 10 of the 11 `note: "FINDING` registry entries beyond their one-line summaries. |
| front end / rewrite | `axeyum-smtlib/src`, `axeyum-rewrite/src`, `axeyum-strings/src`, `axeyum-search/src`, `axeyum-arith/src`, `axeyum-egraph/src` | 63 files, 79,553 lines | no systematic per-`pub fn` sweep of `parse.rs` (24 k lines, mostly private fns behind one dispatch `match`) or of `axeyum-strings/src/regex/`; ~350 of 393 `declin` hits sampled rather than read |

One crate is reported **clean rather than as a finding**: `axeyum-search` has
zero reverse dependencies (`grep -l axeyum-search crates/*/Cargo.toml` returns
only itself) but is examples-driven by design — 23 files in its `examples/`,
and every module is referenced by an example or by `lib.rs`.
`compose::compose_cover_proof` is reached through `harness.rs:637`.

`crates/axeyum-cas`, `crates/axeyum-lean-kernel`, `crates/axeyum-evm`,
`crates/axeyum-verify`, `crates/axeyum-machine`, `crates/axeyum-py` were **not
triaged at all**. They are in the whole-tree counts because they live under
`crates/`; no candidate from them was worked up.

## What I did NOT check — report these as "did not run"

- **Enum variants were not scanned mechanically for unreachability.** The
  script covers `fn` definitions only. `RestartPolicy::mode_switching` — one of
  the four finds that motivated this survey — is an enum variant, so **the
  single most productive shape from today's incidents is not covered by this
  survey's mechanical pass**. Rows D1, C12 and C5 were found by hand. This is
  the largest known gap and the obvious next sweep.
- **`struct` fields and `const`s were not scanned** for
  set-but-never-read / read-but-never-set. Rows B2 and B3 came from enumerating
  `SolverConfig` specifically; no other config struct was enumerated.
- **P21 (946 hits) was not triaged**, so the "constant whose doc says it is a
  guess" category is effectively **unsearched** — the pattern is swamped by
  `Arbitrary` (proptest). A narrower pattern is needed.
- **P12 (99 `allow(dead_code)`) was not triaged**, beyond noting that
  `crates/axeyum-solver/src/reconstruct/arithmetic.rs` carries 14 and
  `crates/axeyum-lean-kernel/src/simp/list.rs` carries 24.
- **`docs/` was not swept.** The brief allows a smaller docs pass; it did not
  run.
- **`#[cfg(test)] mod tests` blocks live inside shipping `.rs` files**, and the
  `tests/`-dir and `*_tests.rs` globs cannot exclude them. The whole-tree
  unreachability script brace-matches them out; the per-slice comment counts do
  not, and were hand-triaged instead. Treat the per-slice raw counts as upper
  bounds.
- **No `cargo`-based reachability analysis was run** (`cargo udeps`,
  `-W dead_code`, coverage instrumentation) — the lane was told not to build.
  Every reachability claim here is grep-based over source text and can miss
  macro-generated, trait-object-dispatched, or derive-generated call sites.
- **Nothing was compiled, benchmarked, or executed.** Every "measurement that
  would price it" is a proposal. The only real measurements quoted are row
  D1's (from `docs/research/12-performance/uf-instance-selection-2026-09-09.md`),
  row A7's (from the `config_registry.rs:4134` entry itself), and row C5's
  (from `phase_policy.rs:59`) — each attributed, none re-derived.

## Method for the unreachability pass

`scratchpad/SWEEP-1/unreach3.py`: walk every `.rs` under `crates/`, split
into three populations — **shipping** (`src/*.rs` with `#[cfg(test)]` blocks
brace-matched out, excluding `tests.rs` / `*_tests.rs`), **test** (everything
removed by that split, plus `tests/` dirs), and **other** (`examples/`,
`benches/`, `python/`, `scripts/`, `render/`, `artifacts/`). Tokenize each
file once into an identifier `Counter`. For each `pub fn` in shipping code,
report it when its identifier appears **zero** times in shipping code outside
its own defining file.

Known false-positive classes, not filtered out: trait-method implementations
called through a `dyn`/generic bound; methods invoked via a macro that
constructs the name; `pub` API deliberately exported for downstream
consumers. Treat the 1,274 as a population to cut, never as a defect count.

## Where the next lane should start

**A1** is the one to dispatch first. It is a two-arm scan order in
`reconstruct.rs:1762`, it is verified by reading both sites, and it decides
whether an entire fragment family gets a real axiom-free Lean proof or a
contentless attestation — which is the headline metric, not a speed number.
Its four "deferred" notices are stale and were actively hiding it.

**A9** is the cheapest: one `set_counting(true)` in the solver's e-graph
bridge turns on an instrument that has been dark on every shipping run, and
the question it answers is written down at `crates/axeyum-egraph/src/lib.rs:379`.

**A2 and A4** are one afternoon in `axeyum-cnf`: a counter that is already
running says how much A2 costs, and A4's replacement is 1,595 lines that
already exist and are already benched.

**A3, A6 and B1** are one file, one theory, and the closest structural match
to the EUF incident — an unminimized conflict core, derived facts computed and
discarded, and a theory that re-runs from scratch on every assertion.

**D1 is the trap.** It looks like the best candidate in the list and it has
already been measured to zero across all seven arms. Read
`docs/research/12-performance/uf-instance-selection-2026-09-09.md` before
touching `qinst_egraph.rs`'s relevance policy.

The next *sweep* — not the next fix — should be enum variants and struct
fields. This survey's mechanical pass covers `fn` definitions only, and the
motivating incident was an enum variant.
