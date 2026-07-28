# axeyum architecture review diary

## Setup
- 19 workspace members (axeyum-wasm deliberately excluded from `[workspace.members]`,
  built standalone). Task listed 20 incl. wasm.
- Root Cargo.toml: `resolver = "3"`, workspace lints: `missing_docs = warn`,
  `unsafe_code = deny`, clippy pedantic warn.

## Dependency graph (from each crate's `[dependencies]`)
Base layer (no internal axeyum deps): axeyum-ir (numeric crates only),
axeyum-aig (zero deps at all), axeyum-lean-kernel (zero deps), axeyum-egraph
(zero deps, generic decl:u32 e-graph, no term coupling - good decoupling).

Mid layer: axeyum-bv -> {aig, ir}; axeyum-cnf -> {aig} (+ batsat/rustsat);
axeyum-fp -> {ir}; axeyum-query -> {ir}; axeyum-rewrite -> {ir};
axeyum-strings -> {ir}; axeyum-scenarios -> {ir, query};
axeyum-smtlib -> {fp, ir, strings}.

Assembly layer: axeyum-solver -> mandatory {aig, bv, cnf, ir, rewrite},
optional (feature-gated) {egraph, fp, lean-kernel, smtlib, strings, z3}.

Top layer: axeyum-property -> {ir, property-macros, solver};
axeyum-verify -> {ir, solver, property, verify-macros};
axeyum-evm -> {ir, solver, property}; axeyum-wasm -> {solver};
axeyum-bench -> {cnf, ir, query, rewrite, scenarios, smtlib, solver}.

No cycles found in the `[dependencies]` graph. This is good, real layering.

Dev-dependency back-edge (not a cycle, but a layering wart):
axeyum-cnf/Cargo.toml `[dev-dependencies]`: axeyum-bv, axeyum-ir. cnf sits
below bv in the intended stack (aig -> {bv, cnf} -> solver) yet reaches up
into bv for its own test fixtures.

## Feature gating (qfbv vs full)
axeyum-solver/Cargo.toml: `default = ["full"]`, `qfbv = []` (adds no deps
itself - relies on the optional deps simply not being enabled),
`full = ["dep:axeyum-egraph","dep:axeyum-fp","dep:axeyum-lean-kernel",
"dep:axeyum-smtlib","dep:axeyum-strings"]`, `z3 = ["full","dep:z3"]`.

Verified empirically:
`cargo check -p axeyum-solver --no-default-features --features qfbv`
compiles cleanly, pulling only aig/ir/query/bv/rewrite/cnf/solver - egraph,
fp, lean-kernel, smtlib, strings, z3 excluded. So the qfbv profile is REAL
and minimal when explicitly requested.

BUT: both known external consumers do NOT request it.
- /nas4/data/workspace-infosec/glaurung/Cargo.toml:42-43:
  `axeyum-solver = { path = "...", optional = true }` /
  `axeyum-ir = { path = "...", optional = true }` - no
  `default-features = false, features = ["qfbv"]`. glaurung's own docs/
  intent say QF_BV only (per task framing), but `solver-axeyum` feature
  (Cargo.toml:99) just does `dep:axeyum-solver` -> pulls `default = full`.
  So glaurung silently compiles in egraph/fp/lean-kernel/smtlib/strings.
- crates/axeyum-wasm/Cargo.toml: `axeyum-solver = { path = "../axeyum-solver" }`,
  again no default-features=false. The browser playground therefore also
  ships the full ~208K-line/~155-module surface, not the minimal QF_BV path -
  directly contrary to what a wasm bundle-size-sensitive target wants.

So: the feature exists and works, but the ergonomics default to the
expensive choice, and every real consumer found in this review took the
default. That is a design footgun, not just a doc gap.

## Public API surface of axeyum-solver
lib.rs (596 lines) - non-`full` (qfbv) exports: Capabilities, CheckResult,
SolverBackend, SolverConfig, SolverError, UnknownKind, UnknownReason (backend
module), IncrementalSolver + friends (incremental module), BvLayerStats
(layers), Model (model), UnsatProof + export_* fns (proof), SatBvBackend.
That baseline is coherent and reasonably small (~25 items).

Under `full` (the default!): a `full_modules!()` macro declares ~150 `mod`
statements (lib.rs:33-184), and a parallel `full_exports!()` macro
re-exports from nearly all of them straight into the crate root - no
submodule namespacing anywhere (no `axeyum_solver::quant::`, no
`::proof::`, no `::array::`). Counted 136 `pub use` statements totalling
~567 individually-named exported items, all flat at crate root
(lib.rs:213-595).

Concretely this includes dozens of narrow, single-benchmark-pattern
"certificate" APIs living directly in the solver's public root namespace,
e.g.:
- array_binary_search::{BinarySearch16Certificate, binary_search16_refutation}
- array_fifo::{FifoBc04Certificate, fifo_bc04_refutation, fifo_ia04_sat_model}
- array_memcpy::{TwoByteMemcpyRefutationCertificate, two_byte_memcpy_refutation}
- array_sort2::{TwoElementBubbleSortCertificate, TwoElementSelectionSortCertificate, ...}
- array_xor_swap::{TwoByteXorSwapRoundtripCertificate, TwoCellXorSwapCertificate, ...}
- ~25 quant_*_cert/search modules (quant_bv_alternation_cert,
  quant_bv_paired_exists_cert, quant_negated_exists_cert,
  quant_vacuous_exists_counterexample_cert, quant_eq_partition_cert, ...)
  each with its own {BINDER,NODE}_CAP consts, its own Certificate struct
  {assertion/binding/residual proof}, its own check_* verifier - structurally
  near-identical shape, no shared trait (checked: no `trait Certificate` or
  similar unifying these).

Cross-checked against axeyum-scenarios (arithmetic/algebra/machine/memory
etc. scenario generators - a real, separate crate for exactly this kind of
"named benchmark pattern" content) and axeyum-bench: neither hosts these
array/quant certificate modules; they live only in axeyum-solver's own
public surface. This looks like scenario-catalog content that leaked into
the core solver crate rather than living in axeyum-scenarios/axeyum-bench,
inflating what "the solver's public API" means for any consumer (like
glaurung) that only wants SolverBackend/IncrementalSolver/Model/check_auto.

## Module organization inside axeyum-solver
161 `.rs` files, 155 of them directly under `src/` (flat), only 5
subdirectories (lex_reconstruct, reconstruct, regex_reconstruct,
word_alethe, word_reconstruct - all small, evidently split off from
reconstruct.rs). Largest files:
- reconstruct.rs: 18,517 lines
- abv.rs: 14,953 lines
- int_reconstruct.rs: 8,876 lines
- incremental.rs: 7,821 lines
- nra_real_root.rs: 7,113 lines
- qinst_egraph.rs: 7,113 lines (approx, see wc)
- auto.rs: 6,688 lines
Total src: 208,668 lines across the crate - this is by far the largest
crate in the workspace (next is axeyum-cnf at 23,083, axeyum-lean-kernel at
15,674 - solver is ~9x the next-largest crate).

Contrast: axeyum-ir (the base layer) is cleanly modularized - 14 small
private modules (arena/bits/error/eval/fmt/poly/poly_big/rational/
real_algebraic/sort/stats/term/value/wide) with curated pub re-exports at
lib.rs, only 2 of which are `pub mod`. This proves the flat-pile pattern in
axeyum-solver is not a workspace-wide norm; it is localized to the one
crate that most needs hierarchy.

## Trait design
`SolverBackend` (backend.rs:482) and `IncrementalSolver` (incremental.rs:744)
are both clean, object-safe traits: `&mut self`, no generics in method
signatures, owned return types, default method bodies where sensible
(`check_query`, `last_stats`). Good API design at the trait level.

SolverBackend has 7+ real implementors across the workspace (Z3Backend,
SatBvBackend, LazyBvBackend, PblsBackend, ArithDpllBackend, UfliaDpllBackend,
DeclaredSortEufBackend, plus 3 more in axeyum-bench for local benchmarking) -
a legitimately used extension point.

IncrementalSolver has exactly ONE production implementor
(IncrementalBvSolver, itself a 7,821-line file with ~100+ inherent methods
beyond the trait's 6). It IS exercised as `Box<dyn IncrementalSolver>` /
`&mut dyn IncrementalSolver` but only from crates/axeyum-solver/tests/
incremental_trait.rs. Not wrong, but worth flagging as a trait whose
abstraction is not yet paying for itself outside test code - most of
IncrementalBvSolver's real capability (warm arrays, replay-checked SAT
cache, deferred theories, ...) is exposed only as inherent methods on the
concrete type, not through the trait.

## Naming
`axeyum_solver::smtlib` (module, the SMT-LIB text front door,
solver/src/smtlib.rs) vs the `axeyum_smtlib` crate (the actual SMT-LIB
parser, a real dependency of axeyum-solver under `full`). The module
directly imports the crate (`use axeyum_smtlib::{...}` at smtlib.rs:21), so
within one file both `axeyum_smtlib::X` and `crate::smtlib::Y` appear side
by side - a persistent minor readability tax, easy to mis-grep.

## Cross-crate duplication
Small `eval_bv`-shaped adapter shims (wrap `axeyum_ir::eval::eval`, unwrap
to a Value/u128, assert BV-sortedness) are independently hand-written in at
least 5 places: axeyum-scenarios/src/arithmetic.rs:232,
axeyum-solver/src/quant_bv_model_sat_cert.rs:318,
axeyum-verify/src/reflect/mod.rs (x2), axeyum-verify/src/reflect/oracle.rs
(x2). Not core-semantics duplication (all delegate to the one canonical
`axeyum_ir::eval::eval` - good, that part is NOT duplicated), but the
boilerplate adapter itself is copy-pasted rather than factored into a
shared helper (e.g. in axeyum-ir itself, or a small shared test-support
crate). Low severity, easy fix.

No evidence of BV *semantic* duplication (wrapping_add/mul etc.) between
bv/aig/ir - the term-level `apply()` in axeyum-ir/src/eval.rs is the single
spec-level evaluator; bit-blasting in axeyum-bv/axeyum-aig is a distinct
circuit-construction concern, not a re-implementation of the same eval
logic. That is expected/correct separation for a bit-blasting solver, not
a smell.

## Misc
- `full_modules!()` / `full_exports!()` macros (lib.rs:33/214) exist purely
  to apply one `#[cfg(feature = "full")]` gate to ~150 mod/pub-use
  statements at once, rather than repeating the attribute 150 times. Modest
  legitimate technique given the scale, but the scale itself is the
  underlying problem (see module-org finding).
