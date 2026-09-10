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

Rank is by (does it sit on a shipping path) x (can I name the observation
that prices it) x (is the deferred half already half-built). "Shipping path"
means a non-test, non-example caller chain from a public entry point.

| # | site | what is deferred / unreached | shipping path | the observation that would price it |
|---|------|------------------------------|---------------|--------------------------------------|
| 1 | `crates/axeyum-cnf/src/xor_propagate.rs:94` | `/// Only implied *units* are applied; implied *equalities* are left for a later substitution slice.` — the Gaussian solve computes the implied equalities in full, then `xor_propagate.rs:115` keeps only `sol.implied_equalities().len()` and applies units only. | **yes**: `axeyum-solver/src/sat_bv_backend.rs:1682-1686` builds `InprocessSchedule { xor_propagate: true, .. }` -> `inprocess.rs:1165` calls `xor_propagate`. Live on the `prove_unsat` inprocessing route. | **The counter is already wired and already emitted on every shipping inprocess run**: `inprocess.rs:1173` does `observer.count("xor_equalities_available", ..)`. Read it off any QF_BV bench run with `--prove-unsat`; a non-trivial value is the exact number of variable merges being discarded. The substitution machinery it needs also already exists (`axeyum-cnf/src/decompose.rs`, equivalent-literal substitution + `CnfAssignment` reconstruction). This is the closest match in the whole survey to the EUF case: computed, discarded, and priced by a counter that is already running. |
| 2 | `crates/axeyum-cnf/src/xor_matrix.rs` (1,595 LOC), exported at `lib.rs:169` | `IncrementalXorMatrix` / `XorMatrixStep` — a complete Gaussian-on-trail propagator **with row-provenance reasons** (`xor_matrix.rs:85`, `:852`). It is a literal description of the enhancement `xor_cdcl.rs:51` defers: *"This watched-literal scheme is sound but incomplete versus full Gaussian elimination ... A complete Gaussian-on-trail propagator (with row-provenance reasons) for the implications this misses is a later enhancement."* | **no shipping caller**: `rg -n '\b(IncrementalXorMatrix\|XorMatrixStep)\b' -g '*.rs' -g '!target/**' -g '!references/**' .` returns 3 sites — the `lib.rs` re-export and `crates/axeyum-cnf/benches/xor_matrix_gauss.rs`. Nothing in any crate's `src/`. | Same shape as EUF: a complete propagator sitting beside an incomplete one, conflict count as the price. `solve_with_xor_cdcl_conflicts` (`xor_cdcl.rs:196`) and `solve_with_xor_cdcl_reductions` (`:207`) are already instrumented; the corpus test `crates/axeyum-solver/tests/xor_cdcl_curated_measure.rs::xor_cdcl_vs_batsat_on_curated_multipliers` (`#[ignore]`d, 2M-conflict budget) exists to answer exactly "did xor_cdcl decide something batsat did not", and missed row-combination parities are what limits it. Benches `xor_matrix_rref` / `xor_matrix_assign_backtrack` already exist. |
| 3 | `crates/axeyum-solver/src/string_theory.rs:270` | `/// A tight core is an optimization TODO.` — `check_conflict` returns the **entire active equality + disequality set** as the conflict clause instead of a minimized core. | yes: `StringTheory::assert` -> `check_conflict`, driven by `cdclt::CdclT` on every QF_S / QF_SLIA query | This is structurally the EUF case: an unminimized conflict clause is a weak learned clause, and weak learned clauses show up as a conflict-count blowup. Count `SearchCounters::conflicts` (`axeyum-cnf/src/proof_sat.rs`) on the string corpus before/after minimizing, exactly as the EUF fix was priced (94,100 -> 623). |
| 4 | `crates/axeyum-solver/src/string_theory.rs:62` | `/// The word core's derived Facts over sub-components still do not propagate because most do not coincide with a tracked atom.` — derived facts are computed and then dropped. | yes: same theory, same driver | Instrument how many `axeyum_strings::Fact`s are derived per solve vs how many reach a tracked atom. A high derived-but-dropped ratio is the same "we compute it and throw it away" shape the EUF propagate had. |
| 5 | `crates/axeyum-solver/src/string_theory.rs:64` | `/// The word core is not incremental: the theory re-runs the refuter from scratch on each representable assertion ... This is correct but not cheap; a backtrackable word core is the incrementality TODO.` | yes, same route | Wall time inside `StringTheory::assert` as a share of total solve on the string corpus. `cargo test -p axeyum-solver --features full --test qf_slia_fixed_splice` and the `:status` corpus sweep both exercise it. |
| 6 | `crates/axeyum-solver/src/backend.rs` — `lazy_bv`, `lazy_bv_abstract_ite`, `xor_cdcl_fallback`, `incremental_positive_and_flattening` | Four `SolverConfig` bools, all `default = false`, that **nothing outside tests and the Python bindings ever sets true**. `axeyum-bench` has no CLI flag for any of them (it has `--inprocess`, `--vivify`, `--native-cdcl`, `--prove-unsat`, but not these). | partly: reachable from `axeyum-py` (`crates/axeyum-py/src/solver/results.rs:146-152`) and `scripts/prove-tock-log2.py`; **not** reachable from `axeyum-bench`, which is the instrument for the Z3 head-to-head claim | Add the four flags to `axeyum-bench`'s arg parser and re-run `just bench-public-qfbv-sat-bv-compare` per arm. Today the parity benchmark structurally cannot exercise three implemented solver routes. (Prior art exists — `docs/research/05-algorithms/lazy-bitblasting-p21-findings.md` — check it before assuming this is unmeasured.) |
| 7 | `crates/axeyum-solver/src/backend.rs:390` + `:475` | `cnf_vivify` defaults to `true`, but its own doc says *"A no-op unless `with_cnf_inprocessing` is also on"* — and `cnf_inprocessing` defaults to `false`. The shipped default of `cnf_vivify` is therefore **inert**. | yes, this is the default config every route builds | This is the "zero-effect constant that is actually live / live constant that is actually zero-effect" shape, inverted. Assert it: a test that flips `cnf_vivify` with `cnf_inprocessing` off and requires byte-identical CNF. Then price inprocessing itself with `--inprocess` on the micro corpus. |
| 8 | `crates/axeyum-solver/src/euf.rs:748` | `/// for an arithmetic-sorted function the witnessing model is not yet built (scalar-keyed function tables) so `sat` degrades to a sound `CheckResult::Unknown` — never a wrong answer.` | yes: `check_with_uf_arithmetic`, reached from the QF_UFLIA / QF_UFLRA dispatch | A **lost decision**, not a slow one — directly on the parity metric. Count `Unknown` verdicts on satisfiable QF_UFLIA/QF_UFLRA benchmarks in the public corpus; the `progress_frontier` ratchet (`cargo test -p axeyum-solver --test progress_frontier --features full`) already has uflra/uflia families to read the delta from. |
| 9 | `crates/axeyum-solver/src/incremental.rs:1740` and `crates/axeyum-solver/src/bmc.rs:151` | `check_with_memory` *"re-solves all active assertions one-shot via the full pure-Rust dispatcher, so it does not yet reuse the warm CNF for deferred theory constructs"*. `bounded_model_check_with_memory` therefore **throws away the warm solver at every depth**: `/// This first slice re-solves each depth one-shot ... so it trades the warm-solver speedup for memory support.` | yes: `axeyum-evm` symbolic execution and every BMC over symbolic memory | The A/B is already built and the docs assert the arms agree: run `bounded_model_check` (warm) against `bounded_model_check_with_memory` (cold) on an **array-free** system at increasing depth. The gap is the price of the deferred warm-array path. ADR-0030 follow-up. |
| 10 | `crates/axeyum-solver/src/ufbv_online.rs:5` | `/// base selects and reads through stores receive fresh scalar results, while store hit/miss axioms are deferred.` | yes: the canonical online QF_UFBV / QF_ABV / QF_AUFBV combination over `cdclt::CdclT` | Deferred axioms mean the theory admits models the array semantics forbid, which the driver must then refute by search. Count CDCL(T) conflicts and refinement rounds on the QF_AUFBV slice; compare against the eager `check_with_array_elimination` route (ADR-0010) on the same files. |
| 11 | `crates/axeyum-rewrite/src/arrays.rs:105` | `/// Read-over-write is already applied (stores are eliminated) in this abstraction; only select congruence is deferred.` — `abstraction()` returns the relaxation with **no select-consistency lemmas**, for a lazy consumer to refine. | shipping *surface*; the lazy consumer lives in `axeyum-solver`. The adjacent `selects()` accessor already returns exactly the triples a lemma generator needs — the deferred half is **half-built**. | This is the strongest structural match to the EUF case: the state exists (`selects()`) and is under-used. Price it by counting how many select pairs a candidate model violates per refinement round on QF_ABV, i.e. how many lemmas the lazy loop is re-deriving. |
| 12 | `crates/axeyum-solver/src/qinst_egraph.rs:265-282`, `:336-380`, `:393-402` | `RelevanceCriterion::EqualityOnly` ships; `RelevanceCriterion::BooleanUnits` is implemented (`BooleanUnitValuation`) and tested and used by **no shipped arm**. Three more levers ship inert: `rank_by_residual: false`, `max_residual_width: usize::MAX` (*"declines nothing, which is shipped"*), `evict_entailed: false`. | yes: `SHIPPED_RELEVANCE_POLICY`, selected unless `AXEYUM_QINST_RELEVANCE` names another arm | **ALREADY MEASURED — do not dispatch as an unexploited win.** `docs/research/12-performance/uf-instance-selection-2026-09-09.md` ran all seven arms and every one decided 0 of 32; its conclusion is *"no arm of this policy can lift it"*. Listed here because the *shape* matches perfectly and the next reader will otherwise re-find it. The live finding in that doc is different: the shipped criterion is blind on 85.6 % of scored candidates, and the fix is a criterion the equality core cannot express, not a lever. |
| 13 | `crates/axeyum-solver/src/datatype_native.rs:468` | `"datatype fields; array/UF datatype fields are not yet supported"` | yes: the native datatype route's admission test | Count admission declines on the QF_DT / QF_UFDT corpus attributable to this message. An admission test that declines is a `unknown`/fallback, i.e. a lost decision or a slower route. |
| 14 | `crates/axeyum-solver/src/qfdt_simp_alethe.rs:37`, `:611`, `:865`, `:1130` | `/// is-tester collapse is deferred**: the fragment dispatch does not yet route a` datatype ... and three further deferred collapses (distinctness, injectivity, `select`-fold). This is the **`set_policies` shape**: the collapse is implemented; the dispatch does not route to it. | dispatch-level: verify the caller chain before dispatching a fix | Coverage, not speed: these are Alethe/Lean reconstruction steps, so the observation is declined-vs-reconstructed counts on the QF_DT evidence artifacts. |
| 15 | `crates/axeyum-solver/src/capabilities.rs:919`, `:1100`, `:1199`, `:1222` | `"the Lean reconstruction path does not yet cover opaque-application congruence"`; two routes recorded as `"Lean/kernel reconstruction route is deferred (Carcara-only)"`; one `"route is deferred (needs noConfusion beyond ι)"`. | yes: these are shipped capability records, so they describe what the product claims | "Lean parity" is *every unsat/valid carries a machine-checkable proof*. Each of these is a named hole in that claim. Price by the count of unsat results on the relevant fragments that produce Carcara-only or no evidence. |
| 16 | `crates/axeyum-ir/src/value.rs:649`, `:688`, `:731`; `crates/axeyum-solver/src/auto.rs:10018`; `crates/axeyum-solver/src/evidence.rs:4893` | Five `TODO(P2.7 A.1b)` sites for `Seq` handling; `auto.rs` says *"no sequence feature/route exists yet"*. | yes, but the capability is absent rather than deferred-in-place | Not a perf hit — a missing logic fragment. Priced by corpus coverage (how many benchmarks name `Seq`), not by a counter. Listed for completeness; low rank because nothing is half-built. |
| 18 | `crates/axeyum-bv/src/lib.rs:64`, `:406` | *"All other operators are conservative barriers that retain the existing full-width lowering."* — add/mul/div have no bit-local demand rule, so `((_ extract 0 0) (bvadd x y))` materialises the whole adder. | yes: demand lowering on the bit-blasting route | **An existing test already pins the gap**: `crates/axeyum-bv/src/lib.rs:4626`, `demanded_lowering_uses_conservative_full_arithmetic_barrier`, asserts `term_bits_lowered > term_bits_demanded`. A ripple-carry bit-local rule for `bvadd` flips that `>` to `==` on that exact test. Corpus counters: `BitDemandStats::{term_bits_available, term_bits_demanded, term_bits_lowered}` (`bv/src/lib.rs:437-440`); AIG size falls out as CNF variables, which `cnf_variable_budget` admits on. Costs most on the quadratic multiplier/divider circuits (`bv/src/lib.rs:100`). |
| 19 | `crates/axeyum-cnf/src/xor_extract.rs:66` | *"The other gate kinds. The encoder already plans NOT-ITE, NOT-AND and AND-tree gates and counts them in `CnfEncodingStats`; only XOR is recorded here, because only XOR has a consumer today."* Corroborated on the AIG side: `crates/axeyum-aig/src/lib.rs:742` has `detect_xor_gate` and no `detect_and_gate` / `detect_ite_gate`. | yes: gate-hint recording on the encode path | Three counters are **already populated on every encode**: `CnfEncodingStats::{not_ite_gates, not_and_gates, and_tree_gates}` (`axeyum-cnf/src/lib.rs:2627-2631`), beside `xor_gates`. Their ratio to `xor_gates` on a bit-blasted corpus is the exact size of the un-hinted population. |
| 20 | `crates/axeyum-solver/src/config_registry.rs:1407` | *"Not yet called from production dispatch (only tests), but governs the function's own contract regardless."* — now **stale in letter**: `xor_gauss_drat_refutation` does have a `src/` caller (`sat_bv_backend.rs:1874`), which is itself unreachable because of row 5's `xor_cdcl_fallback: false`. | registry surface | A registry note that is factually stale is the same failure mode as the "off by default since August" incident. The counter is `xor_cdcl_fallback_unsat_drat_checked` (`sat_bv_backend.rs:1792`) — the difference between an unchecked XOR-Gaussian UNSAT and a DRAT-certified one, named in `capabilities.rs:171` as the evidence string for the ADR-0035 XorGaussian trust hole. It reads zero on every default run today. |
| 21 | `crates/axeyum-solver/src/backend.rs:70`, `crates/axeyum-bv/src/lib.rs:140` | Both sparse BV lowering modes are off by default: *"The defaults are intentionally conservative and experimental. They are not used by `lower_terms` or `lower_terms_demanded`; callers must select this policy explicitly while the Glaurung acceptance gate is being calibrated."* `RangeSliced` is not even bound in Python (`axeyum-py/src/solver/results.rs:139` errors). | `with_bit_lowering_mode` / `with_demand_sliced_lowering` / `with_range_demand_slicing` are called only from `axeyum-bench/src/main.rs:4649-4654` and `examples/qfbv_sat_attribution.rs:95` | **The deferred thing here is the measurement, not the code.** Counters exist (`RangeDemandDecision`, `estimated_bits_avoided`, `analysis_work`, `range_merges`, `range_promotions`, `bv/src/lib.rs:420-432`) and the bench already has a `--range-demand-slicing` policy A/B (`axeyum-bench/src/main.rs:8004-8025`). The stated blocker is the ADR-0157 real-corpus / Glaurung acceptance gate — a run, not a diff. |
| 22 | `crates/axeyum-cnf/src/proof_sat.rs:599` | *"The rephase schedule and the target-mark release are implemented and tested, but changing two heuristics at once makes neither measurable; this default flips only when the measurement says it should."* `SearchPolicies::default()` is still `tiered()` + `pinned()` + `luby()`. `scheduled_phase()`, `releasing_phase()`, `legacy_clause_db()`, `ema_restart()` have **no non-example, non-test constructor** — every `SearchPolicies::` hit outside `proof_sat.rs` is `crates/axeyum-cnf/examples/clause_db_policy_ab.rs:209-227`. | partly fixed today: `axeyum-solver/src/native_cdclt.rs:624` now routes `search_profile: configured_search_profile()`, but that arm is "`Shipped` unless asked" — the default does not flip | `crates/axeyum-cnf/examples/clause_db_policy_ab.rs` is a ready-made five-arm A/B harness. The in-tree evidence for one arm is `phase_policy.rs:59` — *"`PhasePolicy::releasing` was 48 % better on one and 21 % worse on the other"* — a two-instance sample, too small to flip a default. This is "run the existing harness on a wider corpus", not a code item. |
| 23 | `crates/axeyum-cnf/src/inprocess.rs:1538` | `// Conservative: discard the (unverifiable) strengthening and proceed on the pre-vivify formula.` — a whole vivify pass is thrown away when its DRAT does not step-check. Live: `vivify_step_guard: true` in the shipping schedule (`sat_bv_backend.rs:1682-1686`). | yes | `observer.count("vivify_drat_step_checked", ..)` at `inprocess.rs:1535` is the discriminator — every `0.0` is a discarded pass — and `vivify_clauses_strengthened` / `vivify_literals_removed` (`:1550-1556`) quantify the loss. **This is a correct fail-safe, not a deferral**; the cost is real only if the counter shows it fires. Cheap to check, low expected value. |
| 24 | aggregate: 1,274 `pub`/`pub(crate)` fns across `crates/*/src` with **zero** non-test callers outside their own file | Script: `scratchpad unreach3.py` (method below). 318 of them are referenced at most once even inside their defining file. Highest test-reference counts include `axeyum-solver/src/incremental.rs:1123 simplify_memory_for_warm_assertion` (64 test refs, 0 shipping refs outside its file) and `axeyum-solver/src/backend.rs:467 with_cnf_inprocessing` (15 test refs). | mixed — most are legitimate public API (accessors, certificate checkers) | This is a **population**, not a finding. The useful cut is: a builder `with_*` or a policy enum variant whose only non-test constructor is a test. Rows 4 and 5 came out of this cut. Someone should re-run the cut restricted to `with_*` methods and to enum variants (the script covers fns only — **enum variants were not scanned; that check did not run**). |

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

`rg` here is ripgrep 14.1.1 (the bundled binary), **not** the interactive
`grep`, which on this host is ugrep 7.8.4 and disagrees with GNU grep on
escapes. Every count above was produced by `rg`.

## What I did NOT check — report these as "did not run"

- **Enum variants were not scanned for unreachability.** The unreachable
  script (below) covers `fn` definitions only. `RestartPolicy::mode_switching`
  — one of the four finds that motivated this survey — is an enum variant, so
  the single most productive shape from today's incidents is **not covered by
  this survey's mechanical pass**. Row 10 was found by hand, not by the script.
  This is the largest known gap.
- **`struct` fields and `const`s were not scanned** for
  set-but-never-read / read-but-never-set. Rows 4 and 5 were found by hand
  from `SolverConfig` specifically; no other config struct was enumerated.
- **P21 (946 hits) was not triaged.** The "constant whose doc says it is a
  guess" category is therefore effectively **unsearched** — the pattern is
  swamped by `Arbitrary`. A narrower pattern is needed.
- **P12 (99 `allow(dead_code)`) was not triaged**, beyond noting that
  `crates/axeyum-solver/src/reconstruct/arithmetic.rs` carries 14 of them and
  `crates/axeyum-lean-kernel/src/simp/list.rs` carries 24.
- **`docs/` was not swept.** The brief allows a smaller docs pass; it did not
  run.
- **Nothing here was compiled, benchmarked, or executed.** Every "measurement
  that would price it" is a proposal, not a result. The one number in this
  document that is a real measurement is row 10's, and it is quoted from
  `docs/research/12-performance/uf-instance-selection-2026-09-09.md`, not
  re-derived.
- **`crates/axeyum-cas`, `crates/axeyum-lean-kernel`, `crates/axeyum-evm`,
  `crates/axeyum-verify`, `crates/axeyum-machine` were not triaged.** They are
  in the counts because they are under `crates/`, but no candidate from them
  was worked up.

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

Rows 1, 2 and 3 (`string_theory.rs`) are one file, one theory, and the
closest structural match to the EUF incident: a conflict clause that is not
minimized, derived facts that are computed and discarded, and a theory that
re-runs from scratch on every assertion. Row 9 (`axeyum-rewrite/src/arrays.rs`)
is the closest match on the "state exists and is under-used" axis — `selects()`
already returns exactly what a lemma generator needs.

Row 10 is the trap: it looks like the best candidate in the list and it has
already been measured to zero. Read
`docs/research/12-performance/uf-instance-selection-2026-09-09.md` before
touching `qinst_egraph.rs`'s relevance policy.
