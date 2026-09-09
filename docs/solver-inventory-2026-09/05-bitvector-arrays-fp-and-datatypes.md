# Bit-vectors, arrays, floating point, and datatypes — inventory (2026-09-09)

Scope: bit-vector satellite routes (`lazy_bv.rs`, `uninterpreted_bv.rs`,
`bv_uf_local.rs`, `bv2nat_blast.rs`, `bv2nat_bound.rs`, `bv_defined_enum.rs`,
`toy_bv_vm.rs`, `symexec.rs`), the array/ABV subsystem (`abv.rs` + `abv/`,
`aufbv.rs`, `array_axiom.rs`, `array_finite.rs`, and seven `array_*.rs`
scenario-shaped files), UF+BV combination (`ufbv_finite.rs`, `ufbv_online.rs`),
datatypes/enums/records (`datatype_elim.rs`, `datatype_native.rs`,
`datatype_acyclicity.rs`, `enums.rs`, `records.rs`), counting and
optimization (`cardinality.rs`, `set_cardinality.rs`, `pb.rs`, `pbls.rs`,
`distinct.rs`, `maxsat.rs`, `optimize.rs`) — all under
`crates/axeyum-solver/src/` — plus `crates/axeyum-fp` (IEEE 754 builders) and
`crates/axeyum-evm` (an EVM symbolic executor). Base commit `ea8515407`. Eager
bit-blasting itself (term → AIG → CNF, `axeyum-bv`/`axeyum-cnf`) and
`bv_forall_nonconstant.rs`/`bv_interpolant.rs` (quantifiers/interpolation) are
other lanes' territory, cross-referenced only.

**Feature baseline, stated once.** Every file in this scope is declared inside
the `full_modules!()` macro (`crates/axeyum-solver/src/lib.rs:73-232`,
invoked at `lib.rs:252`), gated `#[cfg(feature = "full")]`. `axeyum-solver`'s
own default is `default = ["qfbv"]` (`Cargo.toml:40`) — none of this scope
compiles in the crate's own default build. Six consumer crates
(`axeyum-bench`, `axeyum-verify`, `axeyum-evm`, `axeyum-property`,
`axeyum-py`, `axeyum-machine-evidence`) depend on `axeyum-solver` with
`features = ["full"]`; `axeyum-wasm` uses `qfbv` only, so none of this scope
reaches the WASM build. Per the coordinator's calibration, the tables below do
**not** repeat "full" per row; `FEATURE-GATED` is reserved for gates other
than `full` (`z3`, `bench-internals`) found within this scope.

## Summary

- **My scope is essentially all reachable.** Of 38 tallied components, 36 are
  `WIRED` (with a cited caller), 2 are `TEST-ONLY`, 0 are `NO CALLER FOUND`.
  This is a different picture from a "dead module" audit — see Reachability
  tally below and the reason it comes out this way.
- **`axeyum-fp` (8,257 lines, one file) is WIRED, not a dead builder
  library** — the single most important finding in this lane. It is wired
  through two independent paths: (1) `crates/axeyum-smtlib/src/parse.rs` (a
  **non-optional** dependency of the SMT-LIB parser) calls `axeyum_fp::*`
  builders at **parse time** — 37 call sites, `parse.rs:16246-19876` — so
  `fp.*` SMT-LIB terms become ordinary `BitVec` IR terms before
  `axeyum-solver`'s own dispatcher ever sees them; (2)
  `crates/axeyum-solver/src/lib.rs:912-913` re-exports `axeyum_fp as fp`
  directly for callers building FP terms themselves. There is no FP theory
  solver anywhere in the stack — FP is eliminated to BV in the parser, and the
  existing replayed BV path does the rest, exactly as ADR-0023 specifies.
- **`axeyum-evm` is a downstream consumer, not solver code.** One-directional:
  `grep -rn "axeyum_evm\|axeyum-evm" crates/axeyum-solver/src/
  crates/axeyum-solver/Cargo.toml` is empty. It is a real external exerciser of
  `symexec.rs`'s `SymbolicExecutor`/`SymbolicMemory` (array+BV theory), the
  same relationship `axeyum-scenarios` has to the solver (ADR-0008), applied
  to EVM bytecode.
- **Array handling is four layered routes, not two.** Eager read-over-write +
  Ackermann (ADR-0010, the shared canonical implementation lives in
  `axeyum-rewrite::eliminate_arrays`, called from both `abv.rs` and
  `aufbv.rs`) is the always-correct fallback; a lazy select-congruence CEGAR
  (`check_qf_abv_lazy`) and a lazy-ROW-plus-extensionality CEGAR
  (`check_qf_abv_lazy_row` → `abv/lazy_ext.rs`) sit above it as sound
  refinements; a bank of narrow checked-refutation recognizers
  (`array_axiom.rs`, `array_finite.rs`, and the seven `array_*.rs` files) runs
  as a cheap pre-solve pass. All four are dispatched from `auto.rs` and/or
  `evidence.rs`.
- **All seven `array_binary_search.rs`/`array_bv_abs.rs`/`array_fifo.rs`/
  `array_memcpy.rs`/`array_sort2.rs`/`array_write_chain.rs`/
  `array_xor_swap.rs` files are SOLVER CODE, not benchmark/scenario
  encodings**, despite scenario-shaped names — each is a narrow checked
  refutation recognizer called from `evidence.rs`/`reconstruct.rs` (and, for
  `array_fifo.rs`, also `auto.rs`). None is referenced from
  `crates/axeyum-bench` or `crates/axeyum-scenarios` — the opposite of what a
  scenario-generator file would show.
- **Datatypes run a three-stage cascade in one dispatch block**
  (`auto.rs:4558-4589`, `features.has_datatype`): structural acyclicity check
  first (`datatype_acyclicity.rs`), then elimination
  (`datatype_elim.rs`), then native tag/field expansion
  (`datatype_native.rs`) on elimination's `Unsupported`. `enums.rs`/
  `records.rs` are unrelated, standalone public builders (BV-encoded
  enum/record constructors), not participants in the `Sort::Datatype`
  pipeline.
- **`optimize.rs`/`maxsat.rs`/`pbls.rs` are all reachable from the public
  `Solver<B>` API**, but by three different mechanisms: `optimize.rs` via 11
  direct `Solver<B>` methods implementing OMT as iterated sound feasibility
  decisions (exponential-then-binary search over the objective bound, no
  native theory); `maxsat.rs` via `Solver::max_satisfiable`, itself a thin
  reduction to `optimize::maximize_bv` (no core-guided/branch-and-bound
  machinery); `pbls.rs` via both an internal preprocessing fast-path
  (`preprocess.rs:145`, opt-in) and a direct re-export — the only one of the
  three that is a genuine standalone search procedure (WalkSAT-family SLS).
- **UF+BV is one online CDCL(T) decision procedure plus a cheap fast-path**,
  not two alternates: `ufbv_online.rs` (`check_qf_ufbv_online_cdclt`/
  `check_qf_aufbv_online_cdclt`) is the actual QF_UFBV/QF_AUFBV decision
  procedure; `ufbv_finite.rs` is a narrow pigeonhole/cardinality UNSAT
  fast-path tried earlier and reused throughout certificate construction.
- **The SMT-LIB totality convention (`bvudiv x 0` = all-ones, `bvurem x 0` =
  `x`) has one source of truth**: `axeyum-ir`'s ground evaluator
  (`eval.rs:601-602` narrow path, `eval.rs:1359-1360` wide path). None of the
  8 BV-satellite files reimplement division/remainder semantics; they all
  route replay/rebuild through `axeyum-ir`'s `eval`/term builders, so no
  inconsistency was found *within this scope*. I did not independently verify
  the CNF-level divider circuit in `axeyum-bv` (lane L1's territory) matches
  the same convention structurally — flagged as a gap.
- **A real soundness asymmetry exists for FP**, recorded in ADR-0028: because
  FP arithmetic has no first-class IR op, the ground evaluator replays the
  *same lowered circuit* the solver decided over — "model replay cannot catch
  a wrong FP circuit... the solver and the replay check share the bug." FP
  assurance rests on differential validation against native `f32`/`f64` (and
  `rustc_apfloat` for wide formats), not on the replay-is-the-soundness-anchor
  pattern the rest of this scope relies on. A real historical bug (`fma`
  sign-extension, 2026-06-14) illustrates this: replay agreed with the wrong
  answer; only the independent oracle caught it.
- **Doc drift found**: ADR-0010 ("not by a lazy array decision procedure
  (yet)") is stale — lazy CEGAR routes shipped later
  (`capabilities.rs:284-296`). CLAUDE.md's crate description of `axeyum-fp`
  ("depends only on `axeyum-ir`") is stale — `crates/axeyum-fp/Cargo.toml`
  also depends on `axeyum-arith` (ADR-1710). Minor: `underspecified-operator-
  fuzz-coverage.md` cites `eval.rs:533-534` for `bvudiv`/`bvurem`; current
  lines are `601-602`.

## Reachability tally

| Group | Files | WIRED | TEST-ONLY | FEATURE-GATED (non-`full`) | NO CALLER FOUND |
|---|---:|---:|---:|---:|---:|
| BV satellite routes | 8 | 7 | 1 (`toy_bv_vm.rs`) | 0 | 0 |
| Array/ABV subsystem | 15 | 14 | 1 (`abv/tests.rs`) | 0 | 0 |
| UF+BV combination | 2 | 2 | 0 | 0 | 0 |
| Datatypes/enums/records | 5 | 5 | 0 | 0 | 0 |
| Counting/optimization | 7 | 7 | 0 | 0 | 0 |
| `axeyum-fp` (crate) | 1 | 1 | 0 | 0 | 0 |
| **Total** | **38** | **36** | **2** | **0** | **0** |

`axeyum-evm` is not tallied above — it is a consumer crate, not a component of
this scope; see its own row below.

Why so little dead code, unlike other audited areas of this codebase: nearly
every file in this scope is called from one of two crate-wide hubs —
`auto.rs`'s theory dispatcher or `evidence.rs`'s certificate-construction
pass — both of which are themselves reached from the crate's public
`produce_evidence`/`Solver::check`/`solve_smtlib` entry points. A module that
is *not* reachable from either hub tends to stand out immediately as an
orphaned re-export (none were found here); the two `TEST-ONLY` cases are
self-declared test infrastructure, not orphaned production code.

## Inventory

### BV satellite routes

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---:|---|---|---|
| `lazy_bv` | `lazy_bv.rs` | 429 | ADR-0019 lazy abstraction-refinement (CEGAR): abstracts `bvmul`/`bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/`bvsmod` as fresh vars, solves the shrunk problem eagerly, replays, refines on mismatch | WIRED | `strategy.rs:108,111-112,183` (`solve_with_strategy`); `auto.rs:541` (opt-in via `SolverConfig::lazy_bv`, default `false`, `backend.rs:398`) |
| `uninterpreted_bv` | `uninterpreted_bv.rs` | 433 | Encodes uninterpreted sorts as fixed-width BV (domain size = distinct-symbol count) so the BV backend can decide EUF/UF fragments | WIRED | `euf.rs:653,659` |
| `bv_uf_local` | `bv_uf_local.rs` | 624 | Small-width local BV enumeration deriving equalities that feed UF congruence refutation | WIRED | `evidence.rs:1798,3058,4277`; `reconstruct.rs:1697`; `reconstruct/direct.rs:736,742` |
| `bv2nat_blast` | `bv2nat_blast.rs` | 554 | Rewrites linear `bv2nat` integer atoms into exact BV atoms at a computed non-overflowing width (ADR-0029 gap-10 closure); declines outside its exact fragment | WIRED | `auto.rs:4733` |
| `bv2nat_bound` | `bv2nat_bound.rs` | 118 | Abstracts `bv2nat(b)` to a fresh Int with the sound range fact `0 <= n <= 2^W-1`; used only to discharge `unsat` | WIRED | `evidence.rs:4560`; `auto.rs:2722` |
| `bv_defined_enum` | `bv_defined_enum.rs` | 868 | Bounded finite-scalar enumeration after applying required top-level definitions/domain restrictions (BV + float-as-bitpattern, ADR-0026); replays via the ground evaluator | WIRED | `evidence.rs:1753,2103,3072,4283`; `reconstruct.rs:1631,1770`; `reconstruct/direct.rs:678` |
| `toy_bv_vm` | `toy_bv_vm.rs` | 2445 | Small reference BV register-machine: lifts instructions to terms, explores CFG via `symexec`, extracts/replays concrete witnesses. Doc comment self-classifies: "a reusable library version of the toy target used by the symbolic-execution tests, not a production binary lifter" | TEST-ONLY | Public re-export at `lib.rs:801-811`, but only callers are `tests/symbolic_execution.rs` and a type-identity check in `tests/api_namespaces.rs:301,316-317`; searched `axeyum-scenarios/`, `axeyum-bench/`, `axeyum-py/` for `toy_bv_vm`/`TinyBv` — zero hits |
| `symexec` | `symexec.rs` | 1741 | `SymbolicExecutor`: DFS path exploration over a warm `IncrementalBvSolver`, path-condition assume/branch/backtrack, model extraction; `SymbolicMemory` builds `select`/`store` terms and routes unreduced array/UF terms to the one-shot full dispatcher | WIRED | Public re-export `lib.rs:792-799`; real external caller `crates/axeyum-evm/src/lib.rs:43` and `src/symbolic.rs:51-52,235,320` (`SymbolicMemory::from_array`, `SymbolicExecutor::with_config`) |

Decision-site detail for the eager/lazy question (BV): `strategy.rs:106-122`
(`solve_with_strategy`) matches on `Strategy`: `EagerPureRust` →
`auto::solve` (hand-off to lane L1's `axeyum-bv`/`axeyum-cnf`);
`LazyBvAbstraction` → `lazy_bv::check_lazy_bv_abstraction`; `Auto` (the
default portfolio member) → `if lazy_bv::has_heavy_ops(...) { lazy } else {
eager }` (`strategy.rs:111-121`). `has_heavy_ops` (`lazy_bv.rs:256-258`) is a
pure structural scan for the six nonlinear BV ops — presence/absence, no cost
heuristic. `recommended_portfolio` (`strategy.rs:172-184`) applies the same
gate to order strategy attempts. Independently, `auto.rs:536-541` inside
`check_auto` has its own `SolverConfig.lazy_bv` opt-in trigger (default
`false`), re-entering `lazy_bv::solve_lazy_bv_abstraction`. These are two
distinct entry points into the same module; which one a default `Solver::check`
call reaches depends on which backend/strategy is selected — that selection
logic is `strategy.rs`/`auto.rs` territory, only partly in this lane's scope.

### Array/ABV subsystem

ADR-0010 (`docs/research/09-decisions/adr-0010-arrays-via-eager-elimination.md`,
confirmed real) is the array-elimination decision: "decide QF_ABV in the pure-
Rust backend by eagerly eliminating arrays to QF_BV before bit-blasting — not
by a lazy array decision procedure (yet)." The "yet" resolved: lazy CEGAR
routes exist and are `Assurance::Validated` (`capabilities.rs:284-296`) — see
Doc drift.

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---:|---|---|---|
| `abv` | `abv.rs` | 10,979 | Array elimination front door: eager (`check_with_array_elimination`, `abv.rs:39`, wraps `axeyum_rewrite::eliminate_arrays` via `eliminate_arrays_counted`, `abv.rs:536-540`) + lazy select-congruence CEGAR (`check_qf_abv_lazy`, `abv.rs:89`) + lazy-ROW CEGAR (`check_qf_abv_lazy_row`, `abv.rs:672`, uses `axeyum_rewrite::abstract_arrays`) + small checked refutations | WIRED | `auto.rs:5564` calls `check_qf_abv_lazy_row`; `lib.rs:658-663` re-exports under `theories::arrays` |
| `abv/lazy_ext` | `abv/lazy_ext.rs` | 442 | Lazy extensionality CEGAR: diff-skolem witnesses + on-demand select-congruence, engaged when eager and lazy-ROW both decline on a true (non-substitutable) array-equality shape | WIRED (escalation stage) | `abv.rs:713` (`check_qf_abv_lazy_row_inner` calls `lazy_ext::check_qf_abv_lazy_ext`) |
| `abv/array_elim_certificate` | `abv/array_elim_certificate.rs` | 386 | `ArrayElimUnsatCertificate`/`certify_array_elim_unsat` — checkable UNSAT certificate for the eager elimination route | WIRED | `abv.rs:10972`; `certificates::arrays` at `lib.rs:437-440` |
| `abv/instruments` | `abv/instruments.rs` | 348 | `AbvStats`/`AbvStatsGuard` — route-trace counters (route entry as well as return, unlike the plain `RouteTrace`) | WIRED (instrumentation) | `abv.rs:10973-10974`; `note_abv` called at `abv.rs:683,686`; consumed by `docs/research/12-performance/qf-abv-route-attribution-2026-09-08.md`'s measurement (see Gaps) |
| `abv/tests` | `abv/tests.rs` | 3,668 | 56 `#[test]` fns covering the `abv` subsystem | TEST-ONLY | `mod tests;` at `abv.rs:10979` |
| `aufbv` | `aufbv.rs` | 141 | QF_AUFBV front door: composes `axeyum_rewrite::eliminate_arrays` then `axeyum_rewrite::eliminate_functions`, solves the QF_BV residual, projects the model back (functions first, then arrays), and replay-checks every original assertion (the soundness anchor) | WIRED | `lib.rs:725,1007` (`check_with_arrays_and_functions`) |
| `array_axiom` | `array_axiom.rs` | 4,450 | Checked recognizer bank, five array-axiom schemas; self-documented as "a bridge for repeated corpus shapes, not a general array-elimination certificate" (`array_axiom.rs:5`) | WIRED (pre-solve fast-path) | `evidence.rs:3108` (`direct_pre_solve_array_report`), `:4301`; `reconstruct.rs:1778`; gated by `PRE_SOLVE_ARRAY_AXIOM_DAG_LIMIT` (`config_registry.rs:4310-4321`, value 256 term-DAG nodes) |
| `array_finite` | `array_finite.rs` | 654 | Finite-domain array extensionality + Bool-array read-collapse refuters (bound `MAX_FINITE_ARRAY_EXT_READS=16`) | WIRED | `auto.rs:5463`; `evidence.rs:4287-4291`; `reconstruct.rs:1786-1789`; also used inside `array_axiom.rs:1135,3139` |
| `array_binary_search` | `array_binary_search.rs` | 542 | Checked recognizer: 16-element sorted array + 5-probe binary search | WIRED, SOLVER CODE | `evidence.rs:2014,4334`; not referenced by `axeyum-bench`/`axeyum-scenarios` |
| `array_bv_abs` | `array_bv_abs.rs` | 347 | Checked BV-abstraction over-approximation refuter | WIRED, SOLVER CODE | `evidence.rs:1951,4313` |
| `array_fifo` | `array_fifo.rs` | 1,050 | Checked FIFO-equivalence (shift-register vs. circular-queue, 5 cycles) refuter + SAT model | WIRED, SOLVER CODE | `evidence.rs:2023,4337`; also reached from `auto.rs` |
| `array_memcpy` | `array_memcpy.rs` | 548 | Checked 2-byte memcpy refuter | WIRED, SOLVER CODE | `evidence.rs:1969,4316` |
| `array_sort2` | `array_sort2.rs` | 749 | Checked 2-element bubble/selection-sort refuters | WIRED, SOLVER CODE | `evidence.rs:1978,1987,4319-4324` |
| `array_write_chain` | `array_write_chain.rs` | 454 | Checked aligned write-chain commutation refuter | WIRED, SOLVER CODE | `evidence.rs:1960,4340` |
| `array_xor_swap` | `array_xor_swap.rs` | 848 | Checked XOR-swap permutation refuters (two variants) | WIRED, SOLVER CODE | `evidence.rs:1996,2005,4326-4332` |

**Solver-vs-scenario verdict**: all seven `array_binary_search.rs` through
`array_xor_swap.rs` files are **solver code** (checked refutation
recognizers matched against a specific generated proof-obligation shape),
not benchmark/scenario encodings. The "generated" language in their doc
comments describes the corpus shape each recognizer targets, not that the
file itself generates scenarios. `grep -rln` for each module path under
`crates/axeyum-bench/src` and `crates/axeyum-scenarios/src` returned nothing
for any of the seven — a real scenario-generator file would be referenced
*from* those two crates, and none is.

**Architectural note**: there is one shared canonical ADR-0010 implementation
(`axeyum_rewrite::eliminate_arrays`/`abstract_arrays`, in `axeyum-rewrite`,
outside this lane's scope), called from both `abv.rs` (with instrumentation
and further lazy escalation on top) and `aufbv.rs` (composed with function
elimination). `abv.rs` is not a competing reimplementation of ADR-0010 — it is
the orchestration and certificate layer built on the same core.

### UF+BV combination

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---:|---|---|---|
| `ufbv_finite` | `ufbv_finite.rs` | 556 | Finite-domain cardinality/pigeonhole UNSAT fast-path for QF_UFBV, tried before the online procedure; also reused to build/check UNSAT certificates for whichever route found the refutation | WIRED | `auto.rs:5097` (`dispatch_uf_pigeonhole` → `finite_domain_pigeonhole_refutation`); `evidence.rs:1649,1657,2981,4252,4255`; `reconstruct.rs:1822`, `reconstruct/direct.rs:24,499` |
| `ufbv_online` | `ufbv_online.rs` | 4,997 | The actual QF_UFBV/QF_ABV/QF_AUFBV decision procedure: EUF congruence (`euf_egraph::EufTheory`) driven in lockstep with `IncrementalBvSolver` via `cdclt::CdclT`, lazy row abstraction for arrays, lazy Ackermann for UF | WIRED | `auto.rs:3939-3941` (`dispatch_ufbv_online`, guarded: function symbols present, BV-or-array present, no int/real/uninterpreted-sort/datatype); `auto.rs:5051` (`dispatch_declared_sort_ufbv_lazy`) |

Tests: `ufbv_online_differential_fuzz.rs`, `aufbv_online_differential_fuzz.rs`,
`array_valued_uf_online.rs`, `structural_array_projection_online.rs` exercise
`ufbv_online`; `ufbv_finite.rs` has 4 inline `#[test]`s but no dedicated
integration-test file was found directly (only indirect exercise via
`evidence.rs`/datatype test files, not independently confirmed).

### Datatypes, enums, records

ADR-0022 (`docs/research/09-decisions/adr-0022-first-class-datatype-sort.md`,
confirmed real) records the two-step plan: elimination first, native theory
second, matching what the dispatcher does.

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---:|---|---|---|
| `datatype_acyclicity` | `datatype_acyclicity.rs` | 715 | Structural UNSAT certificates: occurs-check cycles, two-constructor clashes, injectivity-vs-disequality — a sound cheap fast-path that never wrongly says unsat | WIRED, tried first | `auto.rs:4565`, before either elimination or native, inside the `features.has_datatype` block (comment `auto.rs:4558-4563`) |
| `datatype_elim` | `datatype_elim.rs` | 71 | Tier-1 route: read-over-construct elimination via `simplify_datatypes`, then hands off to `auto::solve`; on residual `is-c`/`select` content on free variables returns `Unsupported` | WIRED | `auto.rs:4575` (`check_with_datatype_elimination`), guarded by `features.has_datatype`; falls through to native internally at `datatype_elim.rs:43` |
| `datatype_native` | `datatype_native.rs` | 751 | Tier-2 fallback: eager tag/field expansion (ADR-0022 step B) for free datatype variables elimination could not remove | WIRED | Reached two ways: from inside `datatype_elim.rs:43`, and from `auto.rs:4585` on elimination's `Err(SolverError::Unsupported(_))` |
| `enums` | `enums.rs` | 205 | `EnumSort`/`EnumVar`: standalone builder for enumerated sorts (`k` nullary constructors) lowered to `BitVec(ceil(log2 k))` — no new IR sort, no new decision procedure | WIRED (public API), not part of the `Sort::Datatype` pipeline | `lib.rs:685,1118`; no caller inside `datatype_elim.rs`/`datatype_native.rs`/`auto.rs` (`grep -rn "enums::" src/` → only the two `lib.rs` re-exports); exercised by `tests/enums.rs`, `tests/api_namespaces.rs` |
| `records` | `records.rs` | 224 | `RecordSort`: standalone builder for fixed-width records, `concat`/`extract`-based, same "no new sort, no new procedure" design as `enums.rs` | WIRED (public API), not part of the `Sort::Datatype` pipeline | `lib.rs:686,1429`; no caller in the datatype dispatch chain; exercised by `tests/records.rs`, `tests/api_namespaces.rs` |

**Which one actually runs**: not two alternate routes. `auto.rs:4558-4589`
runs a three-stage cascade inside one `features.has_datatype` block:
acyclicity structural check → elimination → native fallback on
elimination's `Unsupported`. `enums.rs`/`records.rs` are a separate,
independent public surface for constructing enum/record-shaped BV queries
directly — they do not participate in `Sort::Datatype` dispatch at all.

### Counting and optimization over the finite domain

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---:|---|---|---|
| `cardinality` | `cardinality.rs` | 126 | `at_least`/`at_most`/`exactly`/`between`/`at_most_one`/`exactly_one` — pure IR builders (`Σ ite(bᵢ,1,0)` as BV, then compare), each returns `Result<TermId, IrError>`. No search. | WIRED (public API, builder) | `lib.rs:283-294` (`constraints::cardinality`), `:1061` |
| `pb` | `pb.rs` | 113 | `pb_le`/`pb_ge`/`pb_eq`/`pb_lt`/`pb_gt` — weighted pseudo-Boolean, same pure-builder pattern (`Σ ite(bᵢ,wᵢ,0)`) | WIRED (public API, builder) | `lib.rs:294,1256`; doc comment names `max_satisfiable_weighted` as its optimization counterpart |
| `distinct` | `distinct.rs` | 31 | `distinct(arena, terms)` — conjunction of pairwise `!=`. Whole file is one builder function. | WIRED (public API, builder) | `lib.rs:283,1104` |
| `pbls` | `pbls.rs` | 1,456 | `solve_local_search` — genuine SLS solving procedure: WalkSAT-family stochastic local search over Bool/Int/BV(≤128), fixed-seed deterministic, greedy-flip with `NOISE_PCT=30` random-walk and restarts; one-sided (`Sat`-only, evaluator-verified; never emits `Unsat`) | WIRED (internal preprocessing probe + public API) | `preprocess.rs:145` (real caller, opt-in via `local_search_timeout`); `lib.rs:1257` re-export |
| `maxsat` | `maxsat.rs` | 180 | `max_satisfiable`/`max_satisfiable_weighted`(`_model`) — not core-guided or branch-and-bound; reduces to a single BV weighted-sum objective and delegates to `optimize::maximize_bv` (`maxsat.rs:19,55,124`); `_model` variants re-solve pinned at the found optimum via `auto::check_auto` | WIRED (public API) | `solver.rs:534` (`Solver::max_satisfiable`); `lib.rs:834,1228` |
| `optimize` | `optimize.rs` | 1,392 | OMT by iterated sound feasibility decisions: exponential-then-binary search over the objective bound, each probe a full `check_auto` call. LIA path built on `check_with_lia_simplex` (ADR-0020); BV path native. Lexicographic/box/Pareto multi-objective wrappers for both theories. No native OMT theory — soundness inherits entirely from the underlying decision procedure. | WIRED (public API, primary surface) | `solver.rs:353-533` — 11 direct `Solver<B>` methods; `lib.rs:842,1244`; also consumed internally by `maxsat.rs` |
| `set_cardinality` | `set_cardinality.rs` | 501 | Checked popcount/set-cardinality refutation recognizer over SMT-LIB finite-set-to-BV lowering; "intentionally narrow... callers must re-run this matcher" | WIRED (internal, beyond the re-export) | `evidence.rs:126,1807,2096,3065,4280`; `reconstruct.rs:1629,1768`; also `certificates::structural` at `lib.rs:626,1437` |

**Direct answer to the brief's question**: `optimize.rs`, `maxsat.rs`, and
`pbls.rs` are all reachable from the public API, but by three different
mechanisms. `optimize.rs` is the primary surface — 11 methods on the public
`Solver<B>` struct. `maxsat.rs` is reachable via `Solver::max_satisfiable` but
is a thin encoding layer over `optimize::maximize_bv`, not an independent
algorithm. `pbls.rs` is reachable through a different door entirely — not a
`Solver<B>` method, but an internal preprocessing fast-path plus a direct
free-function re-export — and it is the only one of the three that is a
genuine standalone search procedure rather than a reduction to another
routine. No external crate in `axeyum-bench`/`axeyum-py`/`axeyum-property`/
`axeyum-verify` calls into `optimize`/`maxsat` (`grep -rln` over their `src/`
returned empty for both) — contrast with `axeyum-fp` and `symexec`, which do
have external consumers.

### `axeyum-fp` and `axeyum-evm`

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---:|---|---|---|
| `axeyum-fp` | `crates/axeyum-fp/src/lib.rs` | 8,257 | IEEE 754 as bit-vector formula builders (ADR-0023): classification, sign ops, comparison, min/max exactly; constant-folded rounded arithmetic for constants; symbolic `add`/`sub`/`mul`/`div`/`sqrt`/`fma` bit-blasters for F16/F32/F64, validated (not proven) against native `f32`/`f64` and, for wide formats, `rustc_apfloat` (ADR-0028). ~60 `pub fn`, every one taking `&mut TermArena` and returning `TermId`/`Result<TermId,_>` — pure term construction, never a solver call. | WIRED | Two independent paths: (1) `crates/axeyum-smtlib/src/parse.rs:14,16246-19876` (37 call sites) — non-optional dependency of the SMT-LIB parser, lowers `fp.*` terms to BV **at parse time**; reached from `axeyum-solver`'s public front door via `crates/axeyum-solver/src/smtlib.rs:2171` (`axeyum_smtlib::parse_script_with_string_bound_within`, called from `solve_smtlib`/`solve_smtlib_with_model`). (2) `crates/axeyum-solver/src/lib.rs:912-913` — `pub use axeyum_fp as fp;` under `full`, a direct public re-export. Additionally wired into the evidence/trust layer: `evidence.rs:280,3992-4002` (`with_fpa2bv_step`, gates the `Fpa2Bv` trust step, task #69) and `trust.rs:107,126,156,178,204,223,280-320,337,353` (`TrustId::Fpa2Bv`, cites ADR-0023 and `crates/axeyum-fp/tests/fpa2bv_faithfulness.rs`) |
| `axeyum-evm` | `crates/axeyum-evm/` | 6,080 (src+tests+example) | An EVM bytecode symbolic bug-hunter: decodes runtime bytecode, symbolically executes it, decides branch feasibility with `axeyum-solver`'s BV/array path (`README.md`, `lib.rs` doc) | Downstream **consumer**, not solver code | `Cargo.toml:16-17` — depends on `axeyum-solver` (`features=["full"]`) and `axeyum-property`; `grep -rn "axeyum_evm\|axeyum-evm" crates/axeyum-solver/src/ crates/axeyum-solver/Cargo.toml` → empty, confirming the dependency is strictly one-directional. `src/lib.rs:43` and `src/symbolic.rs:51-52,235,320` import `axeyum_solver::{SymbolicExecutor, SymbolicMemory, SolverConfig, SolverError, EvidenceReport}` and drive DFS path exploration + array-sorted memory modeling directly |

`axeyum-fp` dependents beyond the SMT-LIB path: `axeyum-py/src/ir/floats.rs`
imports `axeyum_fp::{FloatFormat, RoundingMode}` and wraps ~50 of its builders
for Python bindings, independently of the SMT-LIB route.
`bv_defined_enum.rs:330` matches internal symbol names prefixed
`"axeyum_fp."` (constant-folding artifacts) — not a genuine crate import,
noted so it is not mistaken for one.

`axeyum-evm` does not use `axeyum_fp` (`grep -rln "axeyum_fp"` under
`crates/axeyum-evm/` is empty — EVM words are plain 256-bit BV, no float).
`axeyum-evm`'s `SymbolicMemory` builds `select`/`store` array terms
(`symexec.rs:105-113`'s doc comment) and routes unreduced array content to
`SymbolicExecutor`'s "one-shot full dispatcher" — i.e., it corroborates that
`symexec.rs`'s public API is exercised by a real external, differentially-
fuzzed consumer (`crates/axeyum-evm/tests/differential_fuzz.rs`), but does
not itself call `abv.rs`/`array_axiom.rs` directly — that composition happens
one layer down, inside whatever dispatcher `SymbolicExecutor::branch_with_memory`
calls, not confirmed further in this pass.

## Data flow

**BV satellite path** (concrete example, `lazy_bv`): SMT-LIB or programmatic
assertions → `Strategy::Auto`'s `lazy_bv::has_heavy_ops` structural scan
(`strategy.rs:111-121`) → if heavy nonlinear ops present,
`lazy_bv::check_lazy_bv_abstraction` abstracts them to fresh symbols → solves
the shrunk problem via the normal eager `axeyum-bv`/`axeyum-cnf` pipeline
(lane L1) → `lazy_bv::replay_holds` re-checks the abstraction against
`axeyum-ir`'s ground evaluator → on mismatch, refines and resolves.

**Array path** (`abv.rs`): assertions → `check_with_array_elimination`
(`abv.rs:39`) → `eliminate_arrays_counted` → `axeyum_rewrite::eliminate_arrays`
(read-over-write + Ackermann, ADR-0010) → pure QF_BV → bit-blast/CNF/SAT (lane
L1) → on `sat`, model projected back through the elimination map and
replay-checked. If the eager route declines (e.g. true array equality),
`check_qf_abv_lazy_row` (`abv.rs:672`) tries `axeyum_rewrite::abstract_arrays`
lazy-ROW CEGAR, escalating to `abv/lazy_ext.rs`'s extensionality CEGAR
(`abv.rs:713`) as a last resort before decline.

**Datatype path**: assertions with `features.has_datatype` →
`datatype_acyclicity::prove_datatype_unsat_structurally` (`auto.rs:4565`) →
`datatype_elim::check_with_datatype_elimination` (`auto.rs:4575`) →
`datatype_native::check_with_datatype_native` (`auto.rs:4585`) on elimination
`Unsupported`.

**FP path**: SMT-LIB text containing `fp.*`/`Float16`/etc. → `axeyum-solver`'s
`solve_smtlib` (`smtlib.rs`) → `axeyum_smtlib::parse_script_with_string_bound_within`
→ inside `axeyum-smtlib`'s `parse_term`, every FP literal/operator triggers an
`axeyum_fp::*` builder call, producing a `BitVec` IR term → the resulting
all-BV term tree is indistinguishable from a native BV query and flows
through `crate::solve`/`auto::solve` like any other BV problem → on `sat`,
the BV model *is* the FP model (bit-pattern reinterpretation, no separate
projection step) → the evidence/trust layer separately records whether the
`Fpa2Bv` reduction is "simple-op certified" (`FpUsage::fpa2bv_simple_op_certified`)
for the per-query trust step.

## Entry points and public API

- `crate::solver::Solver<B>` — the primary programmatic API. Relevant methods
  in this scope: `maximize_lia`/`maximize_bv`/`minimize_bv`/`minimize_lia`/
  `minimize_model`/`minimize_model_objectives`/`optimize_lexicographic{,_bv}`/
  `optimize_box{,_bv}`/`optimize_pareto{,_bv}`/`max_satisfiable`
  (`solver.rs:353-539`).
- `crate::smtlib::solve_smtlib`/`solve_smtlib_with_model` — the SMT-LIB text
  front door; this is where FP terms enter and get lowered before this
  scope's BV/array/datatype routes ever see them.
- Facade modules under `#[cfg(feature = "full")]`: `crate::theories::arrays`
  (`abv::{check_qf_abv_lazy, check_qf_abv_lazy_row, ..., check_with_array_elimination}`),
  `crate::theories::datatypes`, `crate::theories::combination::aufbv`,
  `crate::constraints::{cardinality, pseudo_boolean, distinct}`,
  `crate::certificates::arrays` (all seven `array_*.rs` recognizers plus
  `abv`/`array_axiom`/`array_finite` certificates), `crate::optimization`
  (`maxsat`, `objectives` = `optimize.rs`).
- `crate::fp` (= `axeyum_fp`, `lib.rs:912-913`) — direct access to the FP
  builder library for a caller that wants to construct FP-as-BV terms without
  going through SMT-LIB text.
- Crate-root aliases (hidden from root rustdoc but source-compatible) exist
  for nearly every function above at both the facade path and the historical
  root path — e.g. `pbls::{LocalSearchOutcome, PblsBackend, solve_local_search}`
  at `lib.rs:1257`.

## Tests and gates

All test files below are `axeyum-solver`'s `tests/` integration suite and, per
the crate's own convention, gated `#![cfg(feature = "full")]` — confirmed on a
sample: `tests/fp.rs:4`, `tests/maxsat.rs:2`, `tests/optimize.rs:2`,
`tests/datatype_elim.rs:2`, `tests/pbls.rs:7`, `tests/symbolic_execution.rs:11`,
`tests/aufbv.rs:11`, `tests/cardinality.rs:6`, `tests/pb.rs:2`,
`tests/distinct.rs:2` — every one compiles to zero tests and exits 0 without
`--features full` (the same trap CLAUDE.md's Commands section documents for
other suites).

Two suites additionally require `z3` (differential oracle fuzzing, zero tests
without it): `tests/abv_differential_fuzz.rs:56-57` and
`tests/fp_differential_fuzz.rs:54-55` are both `#![cfg(feature = "full")]` **and**
`#![cfg(feature = "z3")]`.

Relevant tests found in `crates/axeyum-solver/tests/` for this scope (partial,
by area): arrays — `abv_differential_fuzz.rs`, `abv_lazy_ext.rs`,
`abv_lazy_row.rs`, `array_elim_unsat_proofs.rs`, `array_scenarios.rs`,
`array_valued_uf_online.rs`, `arrays.rs`, `aufbv.rs`,
`aufbv_online_differential_fuzz.rs`, `int_array_sort.rs`,
`qfabv_elim_proof.rs`, `qfabv_proof.rs`, `warm_array_*.rs` (4 files); BV —
`bv_differential_fuzz.rs`, `lazy_bv_curated_measure.rs`, `lazy_bv_dispatch.rs`,
`math_resource_bv_routes.rs`, `symbolic_execution.rs`,
`symbolic_execution_memory.rs`; datatypes — `datatype_distinct_cert.rs`,
`datatype_elim.rs`, `datatype_injective_cert.rs`, `datatype_int_fields.rs`,
`datatype_native.rs`, `datatype_solve_path.rs`, `datatype_tester_cert.rs`,
`enums.rs`, `records.rs`; FP — `fp.rs`, `fp_differential_fuzz.rs`,
`fp_ground_division.rs`, `fp_preprocess.rs`, `fpa2bv_trust_step.rs`,
`qf_bvfp_budgeted_reduction_certificate.rs`; UF+BV —
`ufbv_online_differential_fuzz.rs`, `structural_array_projection_online.rs`;
counting/optimization — `cardinality.rs` (6 `#[test]`), `pb.rs`, `distinct.rs`,
`pbls.rs` (5 `#[test]`), `maxsat.rs` (5 `#[test]`), `optimize.rs` (25
`#[test]`), `optimize_bv_timeout.rs`, `optimize_robustness.rs`.

`crates/axeyum-fp/tests/` — `fpa2bv_faithfulness.rs`,
`fpa2bv_simple_faithfulness.rs`, `width_guard.rs`: the differential
faithfulness suites `trust.rs` cites as the assurance basis for the `Fpa2Bv`
trust step.

`crates/axeyum-evm/tests/` — `differential_fuzz.rs` and 14 other integration
suites, an external correctness check on `axeyum-solver`'s BV/array path from
outside the crate (concrete-execution vs. symbolic-execution agreement).

None of these suites were run in this pass (source-reading only, per the
method brief); "confirmed" above means the `#![cfg(...)]` line and `#[test]`
count were read from source, not that the suite was executed.

## Doc drift

- **ADR-0010** (`docs/research/09-decisions/adr-0010-arrays-via-eager-elimination.md`):
  "decide QF_ABV... by eagerly eliminating arrays to QF_BV before bit-blasting
  — not by a lazy array decision procedure (yet)." Stale: lazy CEGAR routes
  (`check_qf_abv_lazy`, `check_qf_abv_lazy_row`, `abv/lazy_ext.rs`) exist and
  are marked `Assurance::Validated` in `capabilities.rs:284-296`. The ADR's
  eager-elimination decision is still the correct baseline/fallback
  description; only the "not... yet" clause is out of date.
- **CLAUDE.md** (this repository's own instructions, Layout section):
  describes `axeyum-fp` as depending "only on `axeyum-ir`." Actual
  `crates/axeyum-fp/Cargo.toml` also depends on `axeyum-arith` (per
  ADR-1710, the shared exact-arithmetic crate). Minor, but the "only"
  qualifier is no longer accurate.
- **`docs/research/01-foundations/underspecified-operator-fuzz-coverage.md`**
  cites `eval.rs:533-534` for the `bvudiv`/`bvurem` degenerate-input
  convention. Current source has these at `crates/axeyum-ir/src/eval.rs:601-602`
  (the file has grown since that doc's citations were written). The
  convention itself (all-ones / dividend) is unchanged and matches
  `docs/research/01-foundations/bv-semantics-and-partial-operations.md`'s
  edge-case table exactly — only the line numbers moved.
- No drift found between `docs/research/09-decisions/adr-0023-floating-point-bv-lowering.md`
  and the current `axeyum-fp` implementation — the ADR's function list
  (`add`/`sub`/`mul`/`div`/`sqrt`/`fma`, `round_to_format`, the non-arithmetic
  core) matches what `axeyum-smtlib/src/parse.rs` actually calls.

## Gaps and open questions

- **Cross-crate totality-convention check not completed.** I confirmed the
  BV-satellite files in this scope share one evaluator-level source of truth
  for `bvudiv`/`bvurem`-by-zero (`axeyum-ir::eval.rs:601-602`,`1359-1360`),
  but did not read `axeyum-bv`'s CNF-level divider circuit (lane L1's
  territory) to confirm the bit-blasted gadget implements the identical
  convention structurally rather than merely agreeing on concrete evaluation.
  A structural mismatch there (evaluator says one thing, circuit computes
  another, and they only ever get compared via replay on `sat`) would be a
  latent soundness gap on `unsat` results — worth a targeted read by whichever
  lane owns `axeyum-bv`.
- **`symexec.rs`'s array-theory routing not traced to its end.** `axeyum-evm`
  calls `SymbolicMemory`/`SymbolicExecutor`, and the doc comment says
  unreduced array/UF terms "route to the one-shot full dispatcher," but I did
  not trace that dispatcher call to confirm it lands in `abv.rs`/`array_axiom.rs`
  specifically (as opposed to, e.g., `auto::solve`'s own array handling calling
  `abv.rs` at one more remove). The two are likely the same thing but this
  was not independently confirmed line-by-line.
- **Default eager/lazy BV selection for a bare `Solver::check()` call is not
  fully pinned down.** `Solver::check` (`solver.rs:161`) delegates to
  `self.backend.check(...)`, which depends on which `SolverBackend`
  implementation was constructed — `strategy.rs`'s `Strategy::Auto` gate and
  `auto.rs`'s `SolverConfig.lazy_bv` opt-in (default `false`) are two
  different mechanisms reachable from different call paths, and I did not
  determine which one the crate's own "default" backend construction (e.g.
  whatever `SatBvBackend::new()`'s typical caller wires up) actually reaches
  by default. This is adjacent to, but not squarely inside, this lane's BV
  scope.
- **`pbls.rs`'s exact algorithm parameters** (restart schedule, flip
  selection beyond "greedy with `NOISE_PCT=30` random walk") were read from
  doc comments and function names, not from a full line-by-line trace of the
  1,456-line file — sufficient to classify it as WalkSAT-family SLS but not
  to fully characterize its completeness/incompleteness guarantees beyond
  "one-sided, `Sat`-only, evaluator-verified."
- **`array_fifo.rs`'s direct `auto.rs` reference** was reported by the
  sub-search that produced this table as "also reached from `auto.rs`" without
  a specific line citation being carried forward into this synthesis; the
  `evidence.rs` citations for it are solid, the `auto.rs` one should be
  spot-checked before being cited elsewhere as a precise line number.
- Nothing in this scope came back `NO CALLER FOUND`. That is itself worth a
  second opinion: it is consistent with this being one of the codebase's
  oldest, most load-bearing subsystems (arrays and BV are the foundation
  layer per CLAUDE.md's north star), but a lane auditing 38 components with
  zero orphans should be treated as a claim to spot-check, not simply
  believed — re-run a sample of the `grep -rn "<module>::"` searches above
  independently before relying on the "no dead code" summary bullet for a
  downstream decision.
