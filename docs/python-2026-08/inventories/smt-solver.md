# Public Rust API inventory for `crates/axeyum-py` (`axeyum._native`)

Read-only survey, 2026-08-24, at `codex/autogenesis-knowledge-f1`. No repo file
was modified; no cargo was run. Line numbers are from the working tree.

Tier legend: **R** = read/pure (no search, cannot be wrong), **P** =
propose/untrusted search (a verdict the checker must confirm), **C** =
check/replay (the trusted small checker).

---

## 0. Findings that shape the whole binding

1. **`serde` is not a dependency of any crate the binding needs.** The only
   `serde*` lines in the workspace are `crates/axeyum-cas/Cargo.toml:29-30`
   (`serde` + `serde_json`, for the CAS lane), and `serde_json` as a **dev**
   dependency in `axeyum-smtlib`, `axeyum-bench`, `axeyum-lean-import`. So
   `axeyum-ir`, `axeyum-solver`, `axeyum-cnf`, `axeyum-bv`, `axeyum-aig`,
   `axeyum-query`, `axeyum-fp`, `axeyum-strings`, `axeyum-egraph` have **no
   derived serialization at all**.
2. **Exactly one `to_json` exists in the entire solver/IR/cnf/smtlib/query
   surface**: `RouteTrace::to_json` at
   `crates/axeyum-solver/src/route_trace.rs:317`. Every other public type's only
   serialization is `Debug` (and `Display` for `Sort`, `Value`, `ArraySortKey`,
   `SolverError`, `IrError`). **The binding must hand-roll `to_json` for
   `CheckResult`, `UnknownReason`, `Model`, `SmtLibOutcome`, `SmtLibModel`,
   `SmtLibResponse`, `SolveStats`, `UnsatProof`, `EvidenceReport`, `Value`,
   `Sort`, every `*Certificate`.** Precedent for the hand-rolled style already
   exists: `crates/axeyum-wasm/src/lib.rs:30 solve_smtlib_json` formats JSON with
   `format!` and two local `json_str`/`json_opt` helpers.
3. **The entire SMT-LIB text front door is `#[cfg(feature = "full")]` and
   `#[doc(hidden)]`** at the crate root (`crates/axeyum-solver/src/lib.rs:1332-1345`).
   `solve_smtlib` and friends are re-exported from `crate::smtlib`, which is a
   `full_modules!()` member. Only `solve_smtlib_session` / `SmtLibResponse` are
   *not* doc-hidden. Consequence: **`axeyum-py` must build `axeyum-solver` with
   `features = ["full"]`.** The default `qfbv` profile gives you `SatBvBackend`,
   `SolverConfig`, `CheckResult`, `Model`, the `proofs::*` DRAT exporters and the
   incremental solver — and *no* SMT-LIB parsing through the solver crate. (The
   `axeyum-wasm` crate is a working example of a `qfbv`-only binding: it depends
   on `axeyum-smtlib` directly and reimplements a `QF_BV`-only script walk.)
   `doc(hidden)` here means "not in root rustdoc", not "unstable" — these are the
   shipped entry points and are what `axeyum_cli` uses.
4. **No lifetimes, no `Rc`/`RefCell`, no raw pointers in the bindable surface.**
   `TermArena` is `Vec` + `HashMap` of owned data; `TermId`/`SymbolId`/`FuncId`/
   `SortId`/`DatatypeId`/`ConstructorId` are `#[derive(Copy)] pub struct X(u32)`
   with a private field and a `.index() -> usize` accessor (hard rule: "term
   handles are lifetime-free `Copy` IDs"). Everything is `Send + Sync` except the
   three exceptions in §6.
5. **`unknown` is a value, not an error** (hard rule). `CheckResult::Unknown`
   carries a structured `UnknownReason { kind, detail }`. The binding must **not**
   map `Unknown` to a Python exception — only `SolverError` becomes an exception.
6. **Determinism is a public API promise.** All iteration order in the public
   surface is over `Vec`s or `BTreeMap`s; the binding must not re-order in
   Python-side dict round-trips.

---

## 1. The SMT-LIB text front door — `crates/axeyum-solver/src/smtlib.rs`

All rows: feature **`full`**, crate `axeyum-solver`, all take `&SolverConfig`,
all return `Result<_, SolverError>`, no lifetimes, all inputs/outputs owned →
`Send + Sync`. Budgets come from `SolverConfig` (`timeout` is one deadline for
the *whole* front door, taken before the first attempt — the fallback ladder
shares it, it does not restart).

| path:line | signature (exact) | Python name | tier | notes |
|---|---|---|---|---|
| `smtlib.rs:1796` | `pub fn solve_smtlib(input: &str, config: &SolverConfig) -> Result<SmtLibOutcome, SolverError>` | `solve_smtlib` | P | THE front door. Zero-or-one `check-sat` only; multi-query scripts must use `solve_smtlib_incremental`/`_session`. `SolverError::Parse` for malformed/out-of-fragment text. |
| `smtlib.rs:3008` | `pub fn solve_smtlib_session(input: &str, config: &SolverConfig) -> Result<Vec<SmtLibResponse>, SolverError>` | `solve_smtlib_session` | P | ADR-0541. One response per output command, script order. The **only non-doc-hidden** front-door fn. Honors `set-option` (5 options); everything else answers `Unsupported{command,detail}` — never silently. An illegal-in-state command is `SmtLibResponse::Error`, not `Err`. |
| `smtlib.rs:2825` | `pub fn solve_smtlib_incremental(input: &str, config: &SolverConfig) -> Result<Vec<CheckResult>, SolverError>` | `solve_smtlib_incremental` | P | Verdict-only walk; delegates to the session with `SessionPolicy::VerdictsOnly`, so the two cannot disagree. `push`/`pop`/`check-sat-assuming`/`reset-assertions` honored; declarations are **global** (survive `pop`). |
| `smtlib.rs:2194` | `pub fn solve_smtlib_get_value(input: &str, config: &SolverConfig) -> Result<Option<Vec<axeyum_ir::Value>>, SolverError>` | `solve_smtlib_get_value` | C | `Ok(None)` when unsat/unknown or no `(get-value …)`. Values read from the **replay-checked** model via the ground evaluator. |
| `smtlib.rs:2335` | `pub fn solve_smtlib_get_assignment(input: &str, config: &SolverConfig) -> Result<Option<Vec<(String, bool)>>, SolverError>` | `solve_smtlib_get_assignment` | C | `:named` Boolean assertions → truth values under the model. |
| `smtlib.rs:2581` | `pub fn solve_smtlib_get_model(input: &str, config: &SolverConfig) -> Result<Option<SmtLibModel>, SolverError>` | `solve_smtlib_get_model` | C | Requires literal `(get-model)` in the text. |
| `smtlib.rs:2606` | `pub fn solve_smtlib_model(input: &str, config: &SolverConfig) -> Result<Option<SmtLibModel>, SolverError>` | `solve_smtlib_model` | C | **Prefer this for embedders** — same thing without requiring `(get-model)` in the script. |
| `smtlib.rs:2675` | `pub fn solve_smtlib_unsat_core(input: &str, config: &SolverConfig) -> Result<Option<Vec<String>>, SolverError>` | `solve_smtlib_unsat_core` | P/C | Deletion-**minimized** subset (every name is genuinely needed); `:named` labels, else `assertion #i`. `Ok(None)` on sat/unknown. Bounded-string `unsat` is gate-confirmed first. |
| `smtlib.rs:2739` | `pub fn solve_smtlib_get_proof(input: &str, config: &SolverConfig) -> Result<Option<String>, SolverError>` | `solve_smtlib_get_proof` | C | Textual **Alethe**. Self-validating emitters + a re-validation pass; three fragments also pass external Carcara, the `QF_LIA` one is internal-only (`lia_generic` is a hole for Carcara) so it is tried LAST. `Ok(None)` when no emitter covers the `unsat`. |
| `smtlib.rs:2380` | `pub fn solve_smtlib_get_assertions(input: &str, _config: &SolverConfig) -> Result<Option<Vec<Vec<String>>>, SolverError>` | `solve_smtlib_get_assertions` | R | Pure; config ignored. |
| `smtlib.rs:2451` | `pub fn solve_smtlib_get_info(input: &str, config: &SolverConfig) -> Result<Option<Vec<(String, String)>>, SolverError>` | `solve_smtlib_get_info` | R/P | Solves only when `:reason-unknown` is requested. Unknown keys → `unsupported`, not dropped. |
| `smtlib.rs:2524` | `pub fn solve_smtlib_get_option(input: &str, _config: &SolverConfig) -> Result<Option<Vec<(String, String)>>, SolverError>` | `solve_smtlib_get_option` | R | Pure. |
| `smtlib.rs:2091` | `pub fn optimize_smtlib(input: &str, config: &SolverConfig) -> Result<Vec<OptOutcome>, SolverError>` | `optimize_smtlib` | P | OMT, **box**/independent interpretation. `config` is currently ignored (`let _ = config;`) — budgets do NOT apply. Objective sort selects the engine (`Int`→simplex, `BitVec`→unsigned BV). |
| `smtlib.rs:2119` | `pub fn optimize_smtlib_lexicographic(input: &str, config: &SolverConfig) -> Result<Vec<OptOutcome>, SolverError>` | `optimize_smtlib_lexicographic` | P | Same, priority order; `config` also ignored. |
| `smtlib.rs:1612` | `pub fn confirm_bounded_string_verdict(script: &mut Script, assertions: &[TermId], config: &SolverConfig, result: CheckResult) -> Result<CheckResult, SolverError>` | *(skip v1)* | C | ADR-0052 `StringGate`. Needs a `&mut axeyum_smtlib::Script` — awkward for PyO3; only needed if the binding reimplements the front door. |
| `smtlib.rs:1643` | `pub fn upgrade_bounded_string_unknown(script: &mut Script, assertions: &[TermId], config: &SolverConfig) -> Result<CheckResult, SolverError>` | *(skip v1)* | C | Upgrade-only companion; never manufactures `sat`. |
| `smtlib.rs:765 / 861 / 1114 / 1264 / 1338 / 738` | `word_route_verdict`, `online_string_verdict`, `membership_verdict`, `lex_order_verdict`, `length_lia_verdict` — each `(script: &mut Script, config: &SolverConfig) -> Option<CheckResult>`; `decide_word_only_script` | *(skip v1)* | P | Internal string routes; `&mut Script` again. |
| `smtlib.rs:1155 / 1171` | `membership_unsat_lean_module(script: &Script, config) -> Option<String>`; `membership_unsat_certificate(...)` | *(later)* | C | Regex-emptiness Lean module. |

### Front-door result types (all need hand-rolled `to_json`)

| path:line | shape | Python name | notes |
|---|---|---|---|
| `smtlib.rs:1355` | `#[non_exhaustive] pub struct SmtLibOutcome { pub result: CheckResult, pub logic: Option<String>, pub expected_status: Option<String> }` | `SmtLibOutcome` | `Debug, Clone, PartialEq, Eq`. `expected_status` is the script's own `(set-info :status)` — **ground truth for cross-checking, never consulted when solving**. Expose it, and make clear in the Python docstring that comparing it is the caller's job. |
| `smtlib.rs:1373` | `#[non_exhaustive] pub struct SmtLibModel { pub constants: Vec<(String, Value)>, pub functions: Vec<(String, FuncValue)> }` | `SmtLibModel` | Declaration order, deterministic. Values are IR `Value`s, **not** SMT-LIB text. |
| `smtlib.rs:2861` | `pub enum SmtLibResponse { CheckSat(CheckResult), Model(String), Values(Vec<(String,String)>), UnsatCore(Vec<String>), Proof(String), Echo(String), Assertions(Vec<String>), Unsupported{command:String,detail:String}, Error{command:String,message:String}, Success }` | `SmtLibResponse` | Deliberately **not** `#[non_exhaustive]` (a wildcard `match` is how a variant gets silently dropped). Map to a Python tagged dict/union; do not collapse `Unsupported` and `Error` — they are different SMT-LIB responses. |
| `optimize.rs:76` | `pub enum OptOutcome { Optimal(i128), Unbounded, Infeasible, Unknown(UnknownReason) }` | `OptOutcome` | — |

---

## 2. Solver core — `backend.rs`, `error.rs`, `model.rs` (feature: **default `qfbv`**)

| path:line | signature | feature | Python name | tier | notes |
|---|---|---|---|---|---|
| `backend.rs:17` | `pub enum CheckResult { Sat(Model), Unsat, Unknown(UnknownReason) }` | qfbv | `CheckResult` | — | `Debug, Clone, PartialEq, Eq`. **Never map `Unknown` to an exception.** |
| `backend.rs:34` | `#[non_exhaustive] pub struct UnknownReason { pub kind: UnknownKind, pub detail: String }` | qfbv | `UnknownReason` | — | Structural so "budget exhausted" can never be misread as `unsat`. |
| `backend.rs:44` | `#[non_exhaustive] pub enum UnknownKind { Timeout, ResourceLimit, MemoryLimit, NodeBudget, EncodingBudget, Incomplete, Other }` | qfbv | `UnknownKind` | — | `Copy`. Expose as a Python `str` enum. |
| `error.rs:29` | `pub enum SolverError { NonBooleanAssertion(TermId), Unsupported(String), Backend(String), Parse(String) }` | qfbv | `AxeyumError` subclasses | — | `Display` + `core::error::Error`. Suggested Python hierarchy: `AxeyumError` ← `SortError`/`UnsupportedError`/`BackendError`/`ParseError`. `From<IrError>` folds IR errors into `Backend`. |
| `backend.rs:97` | `pub struct SolverConfig { pub timeout: Option<Duration>, pub resource_limit: Option<u64>, pub memory_limit_mb: Option<u64>, pub node_budget: Option<u64>, pub cnf_variable_budget: Option<u64>, pub cnf_clause_budget: Option<u64>, pub prove_unsat: bool, pub cnf_inprocessing: bool, pub cnf_vivify: bool, pub preprocess: bool, pub profile_bit_demand: bool, pub profile_cnf_construction: bool, pub bit_lowering_mode: BitLoweringMode, pub incremental_positive_and_flattening: bool, pub xor_cdcl_fallback: bool, pub lazy_bv: bool, pub native_cdcl: bool, pub lazy_bv_abstract_ite: bool, pub proof_progress: Option<ProofProgress>, pub check_progress: Option<CheckProgress> }` | qfbv | `SolverConfig` | — | **`Send` but `!Sync`**: the two progress fields hold `std::sync::mpsc::Sender<_>`. Fine for `#[pyclass]` (needs `Send`), NOT for `#[pyclass(frozen)]` + shared access. Simplest v1: expose the 18 plain fields as kwargs and **omit the two progress sinks**. 22 `with_*` builders at `backend.rs:391-586` plus `demand_bit_slicing()`/`range_demand_slicing()` getters at `:521`/`:527`. |
| `backend.rs:74` | `#[derive(Copy, Default)] pub enum BitLoweringMode { … }` | qfbv | `BitLoweringMode` | — | |
| `backend.rs:291` / `:322` | `pub struct ProofProgress { pub interval: usize, pub sink: mpsc::Sender<axeyum_cnf::ProofSearchProgress> }`, `pub struct CheckProgress { pub interval: usize, pub max_steps: Option<usize>, pub sink: mpsc::Sender<crate::proof::CheckingProgress> }` (`::new` at `:305`/`:343`) | qfbv | *(v2)* | — | **Hazard**: `mpsc::Sender` is the reason `SolverConfig` is `!Sync`. Binding these means owning a Rust thread + a channel drain; defer, or expose as a background-thread iterator. |
| `backend.rs:595` | `#[non_exhaustive] pub struct SolveStats { pub translate: Duration, pub solve: Duration, pub model_lift: Duration, pub terms_translated: u64, pub assertion_count: u64, pub backend: Vec<(String, f64)> }` | qfbv | `SolveStats` | R | Telemetry is returned data, not logs. Hand-rolled JSON. |
| `backend.rs:613` | `pub struct Capabilities { pub name: String, pub produces_models: bool, pub complete: bool }` | qfbv | `Capabilities` | R | |
| `backend.rs:629` | `pub trait SolverBackend { fn capabilities(&self) -> Capabilities; fn check(&mut self, arena: &TermArena, assertions: &[TermId], config: &SolverConfig) -> Result<CheckResult, SolverError>; fn check_query(&mut self, arena: &TermArena, query: &Query, config: &SolverConfig) -> Result<CheckResult, SolverError>; fn last_stats(&self) -> Option<&SolveStats> }` | qfbv | *(not a Python trait)* | P | Do **not** try to make this implementable from Python. Bind concrete backends. |
| `sat_bv_backend.rs` (re-export `lib.rs:870`) | `pub struct SatBvBackend` (`::new()`) | qfbv | `SatBvBackend` | P | The pure-Rust default. |
| `z3_backend.rs` (re-export `lib.rs:1421`) | `pub struct Z3Backend`, `pub const DETERMINISTIC_Z3_RANDOM_SEED` | **z3** | `Z3Backend` | P | Oracle only (ADR-0002). Feature `z3` pulls C++ libz3 — must be an **opt-in wheel variant**, never the default `axeyum._native`. |
| `model.rs:40` | `pub struct Model` with 34 public methods (`new`, `set/get`, `iter`, `set_function/function/functions`, `set/get real_div_zero`, uninterpreted cardinalities, five families of quantified-sat-certificate setters/getters, `len`, `is_empty`, `to_assignment`) | qfbv | `Model` | C | `Debug, Clone, Default, PartialEq, Eq`, fully owned → `Send + Sync`. Only `Debug` serialization. `Model::to_assignment() -> Assignment` (`model.rs:392`) is the bridge to the IR evaluator. |
| `solver.rs:56` | `pub struct Solver<B>` — 34 public methods incl. `new`, `with_config`, `assert`, `assert_all`, `push`, `pop`, `scope_depth`, `check(&mut self, arena: &TermArena)`, `unsat_core`, `check_assuming`, `interpolant`, 12 `optimize_*`, `prove_unsat_to_lean_module`, `into_backend` | qfbv (some methods `full`) | `Solver` | P | **Generic over `B`** — PyO3 cannot expose a generic. Monomorphize: expose `Solver<SatBvBackend>` as `axeyum.Solver`, and (z3 wheel only) `Solver<Z3Backend>`. |

### The three top-level solve entry points (feature **full**, `auto.rs`)

| path:line | signature | Python name | tier | notes |
|---|---|---|---|---|
| `auto.rs:491` | `pub fn solve(arena: &mut TermArena, assertions: &[TermId], config: &SolverConfig) -> Result<CheckResult, SolverError>` | `solve` | P | The multi-theory dispatcher the SMT-LIB front door calls. Takes `&mut TermArena` (it mints internal symbols) — the PyO3 `Arena` pyclass must hand out `&mut` for the call duration. |
| `auto.rs:1101` | `pub fn check_auto(arena: &mut TermArena, assertions: &[TermId], config: &SolverConfig) -> Result<CheckResult, SolverError>` | `check_auto` | P | Same dispatch, no recorder. |
| `auto.rs:1488` | `pub fn check_auto_explained(arena: &mut TermArena, assertions: &[TermId], config: &SolverConfig) -> Result<(CheckResult, RouteTrace), SolverError>` | `check_auto_explained` | P | **Verdict-invariant** with `check_auto` (recorder never participates in a branch; pinned by `tests/route_trace.rs`). `RouteTrace` is the ONE type with a real `to_json` (`route_trace.rs:317`) — bind it directly. |
| `auto.rs:792` | `pub fn unsat_core(arena: &mut TermArena, assertions: &[TermId], config: &SolverConfig) -> Result<Option<Vec<usize>>, SolverError>` | `unsat_core` | P/C | Assertion **indices**, deletion-minimized. |

`RouteTrace` companions (`route_trace.rs`, feature full, all `Debug/Clone/PartialEq/Eq`, all owned):
`Verdict:40`, `DeclineReason:53`, `RouteOutcome:109`, `RouteAttempt:132`, `RouteTrace:151`
(`attempts()`, `last()`, `is_empty()`, `to_json()`).
**Caution (documented gotcha):** `explain_corpus` is *not* an oracle and diverges
from `solve_smtlib` on 134 of 397 committed benchmarks. Whatever the binding
names this, do not let a Python user read a `check_auto_explained` verdict on a
flat term list as "what axeyum answers for this script".

---

## 3. Model replay — the **C** tier (feature **full**)

| path:line | signature | Python name | tier | notes |
|---|---|---|---|---|
| `quant_sat_cert.rs:408` | `pub fn check_model(arena: &TermArena, assertions: &[TermId], model: &Model) -> Result<bool, SolverError>` | `check_model` | **C** | The canonical `sat` replay. Hard rule: *every* `sat` must be checkable this way. Takes `&TermArena` (immutable) — trivial for PyO3. |
| `quant_sat_cert.rs:424` | `pub fn check_model_with_assignment(arena: &TermArena, assertions: &[TermId], model: &Model, assignment: &Assignment) -> Result<bool, SolverError>` | `check_model_with_assignment` | **C** | For consumers restoring eliminated ground symbols before replay. |
| `abv.rs:36` | `pub fn check_with_array_elimination<B: SolverBackend>(backend: &mut B, arena: &mut TermArena, assertions: &[TermId], config: &SolverConfig) -> Result<CheckResult, SolverError>` | `check_with_array_elimination` | P | ADR-0010, `QF_ABV` → `QF_BV`. **Generic** — monomorphize on `SatBvBackend`. Lifts the model back through the elimination before returning. |
| `aufbv.rs` (`lib.rs`) | `pub fn check_with_arrays_and_functions(...)` | `check_with_arrays_and_functions` | P | `QF_AUFBV`. |
| `evidence.rs:3428` | `pub fn produce_evidence(arena: &mut TermArena, assertions: &[TermId], config: &SolverConfig) -> Result<EvidenceReport, SolverError>` | `produce_evidence` | P+C | The **self-checking** unit: verdict + certificate + provenance + trust ledger in one. This is the right primary "give me a checkable answer" Python API. |
| `evidence.rs:1031` | `impl Evidence { pub fn check(&self, arena: &TermArena, assertions: &[TermId]) -> Result<bool, SolverError> }` and `check_outcome(...) -> Result<EvidenceCheck, _>` | `Evidence.check` / `.check_outcome` | **C** | **Bind `check_outcome`, not `check`.** `EvidenceCheck` (`evidence.rs:323`) is three-valued: `Verified` / `NothingToCheck(NoCheckReason)` / `Failed`. A Python `bool` collapses `NothingToCheck` into a pass — exactly the "checker that cannot fail" defect CLAUDE.md warns about. |
| `evidence.rs:4611` | `pub fn prove(arena: &mut TermArena, hypotheses: &[TermId], goal: TermId, config: &SolverConfig) -> Result<ProofOutcome, SolverError>` | `prove` | P+C | Negates the goal and runs `produce_evidence`. |
| `evidence.rs:233 / :366 / :285 / :323 / :818 / :136` | `EvidenceReport { evidence, provenance, trust_ids }`, `Evidence { Sat(Model), Unsat(Option<UnsatProof>), … }`, `NoCheckReason`, `EvidenceCheck`, `PortableArtifact { Drat, Alethe }`, `SEMANTICS_VERSION: &str` | same names | — | No serde; hand-roll. `LayerVersions`, `Provenance`, `EvidenceWithScript`, `produce_evidence_smtlib*`, `produce_*_evidence` variants and `produce_evidence_minimized*` are all in `proofs::evidence` (`lib.rs:264-333`). |
| `trust.rs:26/124/336/348` | `TrustId`, `ALL_TRUST_IDS: &[TrustId]`, `TrustStep`, `trust_ledger_markdown() -> String` | `trust_ledger()` | R | Not doc-hidden. Per-result trust ledger. |
| `capabilities.rs:26/82/125/144/2183` | `Assurance`, `CheckedBy`, `Capability`, `CAPABILITIES: &[Capability]`, `capability_matrix_markdown()` | `capabilities()` | R | `pub mod capabilities` under `full`. Good `axeyum.capabilities()`. |
| `support_matrix.rs:36..533` | `ParserStatus`, `IrStatus`, `SolverStatus`, `ProofStatus`, `SupportRow`, `SUPPORT_MATRIX: &[SupportRow]`, `support_matrix_markdown()` | `support_matrix()` | R | Static; pure. |

---

## 4. Term construction — `crates/axeyum-ir` (feature: **none**, always available)

This is where a Python user builds a query without SMT-LIB text. `axeyum-ir`
depends only on `num-bigint`/`num-rational`/`num-integer`/`num-traits` (pure
Rust, no features, no serde).

**`TermArena` (`arena.rs:25`) has 144 public methods.** All owned data (`Vec` +
`HashMap` of `String`/`Sort`/`TermNode`) → **`Send + Sync`, no lifetimes**. This
is the single most important pyclass: `#[pyclass] struct Arena(TermArena)` with
every builder taking/returning plain `u32`-backed handles.

Design consequence: **every builder is `&mut self`**, so a Python `Arena` must be
a `#[pyclass]` holding the arena (not `frozen`), and terms are `TermId` values
that are only valid against their own arena. Since `TermId` is `Copy(u32)` with a
private field, the binding should wrap it as `#[pyclass] struct Term { arena_id:
u64, id: TermId }` and **check `arena_id` on every use** — otherwise a term from
arena A passed to arena B indexes out of range (Rust-side panic, not a Python
exception). There is no arena identity in the Rust type; the binding must add it.

| group | representative signatures (`arena.rs`) | tier |
|---|---|---|
| construction / introspection | `new():93`, `len():98`, `is_empty():116`, `term_by_index(usize)->Option<TermId>:107`, `node(TermId)->&TermNode:125`, `sort_of(TermId)->Sort:134`, `rebuild_with_args(&mut self, TermId, &[TermId])->TermId:506` | R |
| symbols | `declare(&mut self, name:&str, sort:Sort)->Result<SymbolId,IrError>:285`, `declare_internal:342`, `find_symbol(&str)->Option<SymbolId>:143`, `symbol(SymbolId)->(&str,Sort):158`, `symbols()->impl Iterator<Item=(SymbolId,&str,Sort)>:168`, `var(&mut self, SymbolId)->TermId:377` | R |
| uninterpreted functions | `declare_fun:1637`, `declare_internal_fun:1678`, `apply(&mut self, FuncId, &[TermId])->Result<TermId,IrError>:1719`, `function(FuncId)->(&str,&[Sort],Sort):193`, `functions():203`, `find_function:179` | R |
| uninterpreted sorts | `declare_uninterpreted_sort(&mut self,&str)->SortId:220`, `find_uninterpreted_sort:238`, `uninterpreted_sort_name:247`, `uninterpreted_sort_ids:256` | R |
| constants | `bool_const(bool)->TermId:405`, `bv_const(u32,u128)->Result<TermId,IrError>:416`, `wide_bv_const(WideUint)->TermId:432`, `int_const(i128)->TermId:1742`, `real_const(Rational)->TermId:1918`, `real_ratio(i128,i128)->TermId:1927` | R |
| vars by name | `bv_var(&str,u32):387`, `bool_var(&str):397`, `int_var(&str):1752`, `real_var(&str):1937`, `array_var(&str,u32,u32):1340`, `array_var_with_sorts:1361` | R |
| Boolean | `not:734`, `and:744`, `or:755`, `xor:766`, `implies:932`, `eq:840`, `ite:855` (all `(&mut self, TermId, [TermId]) -> Result<TermId, IrError>`) | R |
| BV bitwise/arith | `bv_not:779`, `bv_and:790`, `bv_or:800`, `bv_xor:810`, `bv_nand:943`, `bv_nor:952`, `bv_xnor:961`, `bv_neg:970`, `bv_add:820`, `bv_sub:980`, `bv_mul:989`, `bv_udiv:998`, `bv_urem:1007`, `bv_sdiv:1016`, `bv_srem:1025`, `bv_smod:1034` | R |
| BV shifts/compare/overflow | `bv_shl:1043`, `bv_lshr:1052`, `bv_ashr:1061`, `bv_ult:830`, `bv_ule:1070`, `bv_ugt:1079`, `bv_uge:1088`, `bv_slt:1097`, `bv_sle:1106`, `bv_sgt:1115`, `bv_sge:1124`, `bv_comp:1133`, `bv_uaddo:1143`, `bv_saddo:1159`, `bv_usubo:1176`, `bv_ssubo:1187`, `bv_nego:1212`, `bv_umulo:1233`, `bv_smulo:1251` | R |
| BV structural | `extract(hi:u32,lo:u32,TermId):871`, `concat:887`, `bv_repeat(count:u32,_):903`, `zero_ext(by:u32,_):1268`, `sign_ext:1279`, `coerce_to(_,width:u32):1298`, `rotate_left:1314`, `rotate_right:1325` | R |
| arrays | `select:1386`, `store:1402`, `const_array(index:u32,TermId):1428`, `const_array_with_index_sort:1450` | R |
| Int | `int_neg:1792`, `int_add:1802`, `int_sub:1811`, `int_mul:1821`, `int_div:1831`, `int_mod:1841`, `int_abs:1850`, `int_pow2:1861`, `int_divisible(_,n:i128):1872`, `int_lt/le/gt/ge:1884/1893/1902/1911` | R |
| Real | `real_neg:1977`, `real_add:1987`, `real_sub:1996`, `real_mul:2006`, `real_div:2015`, `int_to_real:2024`, `real_to_int:2034`, `real_is_int:2044`, `real_lt/le/gt/ge:2054/2063/2072/2081` | R |
| conversions | `bv2nat:1480`, `int2bv(width:u32,_):1492`, `fp_from_bits(_,exp:u32,sig:u32):1508`, `rounding_mode_from_bits:1526` | R |
| sequences / strings | `seq_len:1544`, `seq_empty(ArraySortKey)->TermId:1556`, `seq_unit:1568`, `seq_concat:1582` | R |
| datatypes | `declare_datatype(&str)->DatatypeId:527`, `add_constructor:542`, `construct(ConstructorId,&[TermId]):644`, `dt_select:676`, `dt_test:715`, plus 8 accessors (`num_datatypes:561`, `datatype_ids:570`, `find_datatype:581`, `find_constructor:594`, `datatype_name:606`, `datatype_constructors:615`, `constructor_datatype:624`, `constructor_name:629`, `constructor_fields:634`) | R |
| quantifiers | `forall(&mut self, var: SymbolId, body: TermId)->Result<TermId,IrError>:2097`, `exists:2165`, `set_quantifier_patterns(&mut self, TermId, Vec<Vec<TermId>>):2120`, `quantifier_patterns(TermId)->Option<&[Vec<TermId>]>:2142`, `annotated_quantifiers():2149` | R |

**Degenerate-operator note (Hard Rule):** `bv_udiv`/`bv_urem` by zero, `int_div`/
`int_mod` by zero, `str.at` out of range are **total** with SMT-LIB semantics
(`bvudiv x 0` = all-ones). The Python docs must state this — a user who assumes a
Python `ZeroDivisionError` will misread a correct answer. Add a Python-side test
that builds `(div x 0)` explicitly, mirroring the fuzz-seed-class rule.

### IR value/sort types (`lib.rs:48-62`)

| path:line | item | Python name | notes |
|---|---|---|---|
| `sort.rs:128` | `#[derive(Copy)] pub enum Sort { Bool, BitVec(u32), Array{index:ArraySortKey, element:ArraySortKey}, Int, Real, RoundingMode, Datatype(DatatypeId), Uninterpreted(SortId), Float{exp:u32,sig:u32}, Seq(ArraySortKey) }` | `Sort` | `Display`, no serde. Helpers: `Sort::string():183` (`Seq(BitVec(18))`), `STRING_ELEM_WIDTH=18:179`, `bv_width:192`, `lowered_width:210`, `is_bool:226`, `float_format:231`, `array_widths:250`, `array_sorts:266`. `MAX_BV_WIDTH = 1<<16` (`sort.rs:117`). |
| `sort.rs:25` | `pub enum ArraySortKey` (`from_sort:54`, `to_sort:69`, `bv_width:83`, `Display:97`) | `ArraySortKey` | `Copy`. |
| `value.rs:14` | `pub enum Value { Bool(bool), Bv{width:u32,value:u128}, WideBv(WideUint), Array(ArrayValue), GenericArray(GenericArrayValue), Int(i128), Real(Rational), RealAlgebraic(RealAlgebraic), Datatype{datatype,constructor,fields:Vec<Value>}, Uninterpreted{sort:SortId,value:u128}, Seq(Vec<Value>) }` | `Value` | **The single hardest conversion.** `u128` exceeds Python `int` fast path but converts fine; `WideBv`/`Rational`/`RealAlgebraic` need dedicated Python reprs. Accessors: `from_scalar_code:653`, `scalar_code:692`, `sort:721`, `as_bool:749`, `as_bv:766`, `as_array:783`, `as_generic_array:801`, `as_int:818`, `as_real:839`, `as_real_algebraic:857`, `as_wide_bv:865`, `Display:954`. |
| `value.rs:75` / `:148` | `ArrayValue` (`constant:84`, `index_width:94`, `element_width:99`, `select:104`, `store:111`, `default_element:129`, `entries:134`), `GenericArrayValue` (`constant:161` — **panics** on sort mismatch, `index_sort:176`, `element_sort:181`, `default_value:186`, `select:195`, `store:213`, `entries:245`) | `ArrayValue`/`GenericArrayValue` | Normalized (entries equal to default removed) so equality is extensional and the representation deterministic. `GenericArrayValue::constant` **asserts** — wrap. |
| `value.rs:282` | `pub struct FuncValue` (`uses_value_storage_for:324`, `constant:336`, `constant_value:360`, `params:381`, `result:386`, `uses_value_storage:391`, `is_arith:396`, `apply:406`, `apply_value:426`, `define:465`, `define_in_place:496`, `define_value:522`, `default_result:571`, `default_value:581`, `entries:595`, `value_entries:604`) | `FuncValue` | Finite UF interpretation; appears in `SmtLibModel.functions`. |
| `term.rs:11/22/33/47/59` + `sort.rs:10` | `TermId`, `SymbolId`, `FuncId`, `DatatypeId`, `ConstructorId`, `SortId` — each `#[derive(Debug,Clone,Copy,PartialEq,Eq,Hash,PartialOrd,Ord)] pub struct X(pub(crate) u32)` with `index()->usize` | same | Private field ⇒ **the binding cannot reconstruct a handle from an integer**. That is a feature: it forces handles through the arena. |
| `term.rs:347` | `pub enum TermNode { BoolConst(bool), BvConst{width,value}, WideBvConst(WideUint), IntConst(i128), RealConst(Rational), Symbol(SymbolId), App{op:Op, args:Box<[TermId]>} }` | `TermNode` | For a Python term walker. |
| `term.rs:76` | `#[derive(Copy)] pub enum Op { … }` (82 variants) | `Op` | Expose as a Python str-enum. |
| `eval.rs:19` | `pub struct Assignment` (`new:42`, `set:47`, `get:52`, `set_function:58`, `function:63`, `functions:68`, `set_real_div_zero:75`, `real_div_zero:83`, `real_div_zeros:91`, `len:98`, `is_empty:103`) | `Assignment` | |
| `eval.rs:215` | `pub fn eval(arena: &TermArena, term: TermId, assignment: &Assignment) -> Result<Value, IrError>` | `eval` | **C**. The ground evaluator — the trusted small checker behind every `sat`. |
| `eval.rs:239` | `pub fn eval_with_memo(arena:&TermArena, term:TermId, assignment:&Assignment, memo:&mut HashMap<TermId,Value>) -> Result<Value, IrError>` | `eval_with_memo` | **C**. Iterative post-order, cannot stack-overflow. `&mut HashMap` — either hide the memo behind a pyclass or don't bind. |
| `eval.rs:122` | `pub fn well_founded_default(arena:&TermArena, sort:Sort)->Option<Value>` | `well_founded_default` | R |
| `fmt.rs:105` | `pub fn render(arena: &TermArena, term: TermId) -> String` | `render` / `Term.__str__` | R. The only term→text path in the IR. |
| `stats.rs:17/40/109` | `TermStats`, `TermStats::compute(arena, roots)`, `sharing_ratio()->f64` | `TermStats` | R |
| `bits.rs:12/30/80/94/116` | `BitOrder`, `value_to_lsb_bits`, `bv_value_to_lsb_bits`, `lsb_bits_to_bv_value`, `lsb_bits_to_value` | `bits.*` | R. LSB-first is the project-wide convention; state it in the Python docs. |
| `error.rs:11` | `pub enum IrError { SortMismatch{expected:&'static str, found:Sort}, SortsDiffer(Sort,Sort), InvalidWidth(u32), ValueOutOfRange{width,value}, ExtractOutOfRange{hi,lo,width}, ConcatTooWide(u32), BitCountMismatch{expected,actual}, … }` | `IrError` | Every builder returns this; map to a Python `TypeError`-flavored `SortError`. |
| `rational.rs` / `real_algebraic.rs` / `wide.rs` | `Rational`, `RealAlgebraic`, `Sign`, `WideUint` | same | `Rational` is `i128`-backed; `RealAlgebraic` is bigint poly + isolating interval (NRA witnesses only). |
| `poly` / `poly_big` | `pub mod poly`, `pub mod poly_big` | *(skip v1)* | CAS-facing. |

---

## 5. Incremental solver — `crates/axeyum-solver/src/incremental.rs` (feature **qfbv**)

| path:line | signature | Python name | tier | notes |
|---|---|---|---|---|
| `incremental.rs:795` | `#[derive(Debug)] pub struct IncrementalBvSolver` | `IncrementalSolver` | P | **Bound to a single `TermArena` over its lifetime** (term ids are arena-stable and the persistent lowering reuses them) — but the binding does *not* hold a borrow: every method takes `arena` as a parameter. So the Python object can own the solver and take an `Arena` argument, and must **assert it is the same arena** (same hazard as `TermId`, §4). |
| `:825 / :835 / :879` | `new()`, `with_config(SolverConfig)`, `with_config_and_profiling(SolverConfig)` | constructors | | |
| `:1187` | `pub fn assert(&mut self, arena: &TermArena, term: TermId) -> Result<(), SolverError>` | `assert_` | P | Also `assert_preprocessed:1204`, `assert_preprocessed_batch:1251`, `assert_configured:1290`, `assert_configured_batch:1321`, `assert_simplifying_memory:1160`. |
| `:1707 / :1727 / :902` | `push() -> Result<(), SolverError>`, `pop() -> bool`, `scope_depth() -> usize` | `push`/`pop`/`scope_depth` | P | `pop` returns `false` at the base frame instead of erroring. |
| `:1830` | `pub fn check(&mut self, arena: &TermArena) -> Result<CheckResult, SolverError>` | `check` | P | Plus `check_with_memory(&mut self, arena: &mut TermArena):1754`, `check_assuming_with_memory:1779`, `check_assuming_core_with_memory:1810`. |
| `:744` | `pub trait IncrementalSolver { assert; push; pop; scope_depth; check; check_assuming(&mut self, arena, assumptions: &[TermId]) }` | — | | Do not expose the trait; bind the concrete type. |
| `:67 / :107 / :164 / :188` | `IncrementalBvStats` (`delta_since:411`, `total_time:433`), `IncrementalModelLiftStats` (`delta_since:129`), `ReplayCheckedSatCachePolicy`, `ReplayCheckedSatCacheStats` — all `Copy, Default, PartialEq, Eq` | stats classes | R | Cheap; expose as read-only dicts. Also `stats():937`, `encoded_clause_count():912`, `encoded_variable_count():917`, `lowered_aig_node_count():927`, plus ~10 `retained_warm_*_count()` probes at `:1005-1070`. |
| `:471` | `pub enum AssumptionOutcome` | `AssumptionOutcome` | | |
| `:984 / :992 / :998` | `enable_replay_checked_sat_cache(...)`, `disable_replay_checked_sat_cache()`, `replay_checked_sat_cache_stats()` | | C | The warm path's replay cache — a **C**-tier control, expose it. |
| `:1077 / :1090 / :1102 / :1123` | `term_needs_deferred_theory(arena, term) -> bool` (assoc fn), `term_supported_by_warm_abstraction(arena, term) -> bool`, `has_deferred_theory_assertions()`, `simplify_memory_for_warm_assertion(arena: &mut TermArena, term) -> TermId` | | R | |
| `:962` | `profiled_last_cnf_snapshot(&self) -> Result<Option<CnfFormula>, CnfError>` | | R | Bridge into the CNF layer. |

`Send/Sync`: `IncrementalBvSolver` embeds `IncrementalCnf` → a batsat solver whose
callback structs hold `Cell<u64>`/`Cell<Option<_>>`
(`crates/axeyum-cnf/src/lib.rs:622-623, 725-726`, both **private**). `Cell` is
`Send` but `!Sync`, so expect **`Send`, `!Sync`** — fine for a plain
`#[pyclass]`, wrong for `#[pyclass(frozen)]`. Verify by compiling a
`fn assert_send<T: Send>()` probe rather than trusting this row.

---

## 6. Send/Sync and lifetime hazards — the complete list

Everything else in this inventory is owned data with no lifetime parameter and is
`Send + Sync`. The exceptions:

| item | hazard | mitigation |
|---|---|---|
| `SolverConfig` (`backend.rs:97`) | `!Sync` — `proof_progress`/`check_progress` hold `mpsc::Sender`. `Send` holds. | v1: omit the two progress fields from the Python config; the struct is still `Send`, which is all `#[pyclass]` needs. |
| `ProofProgress` / `CheckProgress` (`backend.rs:291`, `:322`) | `mpsc::Sender` channel endpoints. | Defer to v2; if bound, drain on a Rust thread and surface as a Python iterator. |
| `CheckBudget<'a>` (`proof.rs:376`) | **The only lifetime in the priority surface**: `pub progress: Option<&'a mut dyn FnMut(&CheckingProgress)>`. Also `!Send`. | Do **not** bind `CheckBudget` directly. Bind `export_qf_bv_unsat_proof_within` (deadline only) and, if progress is needed, add a Rust-side shim that constructs the budget internally. |
| `Solver<B>` (`solver.rs:56`), `check_with_array_elimination<B>` (`abv.rs:36`) | Generic over the backend — PyO3 cannot express it. | Monomorphize on `SatBvBackend` (and `Z3Backend` in the z3 wheel only). |
| `IncrementalBvSolver` | Likely `!Sync` via batsat's private `Cell` callbacks. | Plain `#[pyclass]`; verify with a compile-time `assert_send` probe. |
| `confirm_bounded_string_verdict` / the five string-route verdict fns | Take `&mut axeyum_smtlib::Script` | Skip in v1, or expose a `Script` pyclass in a later slice. |
| `eval_with_memo` (`eval.rs:239`) | `&mut HashMap<TermId, Value>` | Hide the memo inside an `Evaluator` pyclass, or bind only `eval`. |
| `TermId` / `SymbolId` / … | No arena identity in the type. Cross-arena use is a Rust panic, not an error. | The binding **must** carry an arena id on every handle and check it. |
| `GenericArrayValue::constant` (`value.rs:161`) | `assert!` on sort mismatch — panics. | Pre-validate in the binding, or catch via `catch_unwind` at the module boundary. |
| `RangeDemandPolicy`, `BitLoweringMemoRepresentation`, `IncrementalLoweringStats`, `RangeDemandDecision` (re-exported at `lib.rs:43-45` from `axeyum-bv`), `AigConstructionStats` (`lib.rs:42`), `IncrementalCnfStats` (`lib.rs:852`) | none | Plain stats/config enums; bind as-is. |

## 7. Feature matrix for `crates/axeyum-py/Cargo.toml`

| Python surface | required feature |
|---|---|
| `TermArena` + all builders, `eval`, `render`, `Value`/`Sort` | (none — `axeyum-ir` has no features) |
| `SatBvBackend`, `SolverConfig`, `CheckResult`, `Model`, `Solver<SatBvBackend>`, `IncrementalBvSolver`, `proofs::export_qf_bv_unsat_proof*`, `UnsatProof::recheck` | `axeyum-solver/qfbv` (default) |
| **`solve_smtlib` and every `solve_smtlib_*`, `solve_smtlib_session`, `SmtLibOutcome`, `SmtLibModel`, `SmtLibResponse`** | **`axeyum-solver/full`** |
| `solve`, `check_auto`, `check_auto_explained`, `RouteTrace`, `unsat_core`, `check_model`, `produce_evidence`, `Evidence`, `check_with_array_elimination`, `optimize_*`, interpolants, `capabilities`, `trust_ledger_markdown`, Alethe/Lean reconstruction, `axeyum_solver::fp` | `full` |
| `Z3Backend`, `DETERMINISTIC_Z3_RANDOM_SEED`, `Strategy::Oracle` | `z3` (implies `full`) — **C/C++ leaf dependency; separate opt-in wheel only.** ADR-0002 makes this bootstrap scaffolding, not the product. |
| `parse_script`/writer used directly | depend on `axeyum-smtlib` directly (no features) |

Recommended default: `axeyum-py` depends on `axeyum-solver` with
`default-features = false, features = ["full"]`, plus `axeyum-ir`,
`axeyum-smtlib`, `axeyum-cnf` directly. Keep `wasm32` buildability in mind
(ADR-0017): everything above except `z3` is pure Rust.

## 8. Portfolio / strategy (feature **full**, `strategy.rs`) — not doc-hidden

- `strategy.rs:40` `pub enum Strategy { EagerPureRust (default), LazyBvAbstraction, Auto, Oracle (feature z3) }` — `Copy`.
- `strategy.rs:99` `pub fn solve_with_strategy(arena: &mut TermArena, assertions: &[TermId], config: &SolverConfig, strategy: Strategy) -> Result<CheckResult, SolverError>` — tier P.
- `strategy.rs:143` `pub fn solve_with_portfolio(arena: &mut TermArena, assertions: &[TermId], config: &SolverConfig, strategies: &[Strategy]) -> Result<CheckResult, SolverError>` — tier P.
- `strategy.rs:182` `pub fn recommended_portfolio(arena: &TermArena, assertions: &[TermId]) -> Vec<Strategy>` — tier R, pure.

## 9. Proof / certificate export — `crates/axeyum-solver/src/proof.rs` (feature **qfbv**)

Re-exported at `lib.rs:864-869` (doc-hidden at the root; the canonical home is
`axeyum_solver::proofs`, `lib.rs:264`).

| path:line | signature | Python name | tier | notes |
|---|---|---|---|---|
| `proof.rs:38` | `pub struct UnsatProof { pub dimacs: String, pub drat: String, pub lrat: Option<String> }` | `UnsatProof` | C | `Debug, Clone, PartialEq, Eq`. **Three plain `String` fields — this is the one type that needs no JSON design**; expose `.dimacs`, `.drat`, `.lrat` as Python `str`/`Optional[str]` and let the user write files. |
| `proof.rs:66 / :102 / :147` | `pub fn recheck(&self) -> Result<bool, SolverError>`, `recheck_for_bool_terms(...)`, `recheck_lrat(&self) -> Result<Option<bool>, SolverError>` | `UnsatProof.recheck` etc. | **C** | The independent re-derivation. `recheck_lrat` returns `Ok(None)` when no LRAT is present — **do not let the Python wrapper collapse that to `True`.** |
| `proof.rs:165` | `pub enum UnsatProofOutcome { Proved(UnsatProof), Satisfiable, Inconclusive }` | `UnsatProofOutcome` | | `Inconclusive` = budget exhausted. A timeout is not a pass. |
| `proof.rs:183 / :199 / :218 / :280` | `export_qf_bv_unsat_proof(arena: &TermArena, assertions: &[TermId]) -> Result<UnsatProofOutcome, SolverError>`; `_within(..., deadline: Option<Instant>)`; `_within_with_check_budget(...)`; `_with_progress(...)` | `export_qf_bv_unsat_proof[_within]` | P+C | Bind the first two. The last two take `CheckBudget<'a>` — see §6. |
| `proof.rs:538 / :551 / :576 / :589 / :621 / :644 / :688` | `export_qf_abv_unsat_proof[_within]`, `export_qf_aufbv_unsat_proof[_within]`, `export_qf_uf_unsat_proof`, `export_qf_lia_unsat_proof`, `export_datatype_unsat_proof` | same names | P+C | Same shape. |
| `proof.rs:351` | `pub enum CheckingProgress { DratCheck(axeyum_cnf::DratCheckProgress), LratElaborate(axeyum_cnf::LratElaborateProgress) }` | *(v2)* | R | Exists because an unbounded checking pass once ran ~6 h after a 24 s search. |
| `proof.rs:376` | `pub struct CheckBudget<'a> { deadline, max_steps, progress_interval, progress: Option<&'a mut dyn FnMut(&CheckingProgress)> }` | **do not bind** | | §6. |

The **Alethe** side lives in `proofs::alethe` (`lib.rs:271-303`, feature `full`) —
`prove_qf_bv_unsat_alethe`, `prove_qf_uf_unsat_alethe`, `prove_lra_unsat_alethe`,
`prove_lia_unsat_alethe`, `prove_qf_abv_unsat_alethe`, `check_alethe_lra`, … all
returning textual proofs. `proofs::end_to_end` (`lib.rs:307`) has
`certify_qf_bv_unsat_end_to_end[_within]` and `certify_bitblast_by_miter[_within]`.
`proofs::faithfulness` (`lib.rs:335`) has `check_qf_bv_faithfulness`.
`proofs::lean` (`lib.rs:343`) is the Lean reconstruction surface — ~60 items,
`prove_unsat_to_lean_module`, `ReconstructCtx`, `LeanModuleContent`,
`refutation_axiom_footprint`, `MAX_LEAN_MODULE_BYTES`. Defer all of `proofs::lean`
past v1; it is a whole binding of its own.

## 10. Suggested `axeyum._native` module shape

```
axeyum._native
  ├─ ir           R : Arena, Term, Sort, Value, Op, TermNode, Assignment,
  │                   eval, render, TermStats, bits.*, IrError
  ├─ solve        P : SolverConfig, CheckResult, UnknownKind, SatBvBackend,
  │                   Solver, IncrementalSolver, Strategy, solve,
  │                   check_auto_explained, unsat_core, solve_with_portfolio
  ├─ smtlib       P : solve_smtlib, solve_smtlib_session, solve_smtlib_incremental,
  │                   solve_smtlib_model, solve_smtlib_unsat_core,
  │                   solve_smtlib_get_proof, optimize_smtlib, parse_script, write
  ├─ check        C : check_model, check_model_with_assignment, produce_evidence,
  │                   Evidence.check_outcome, UnsatProof.recheck / recheck_lrat,
  │                   export_qf_*_unsat_proof, check_drat, check_lrat
  └─ meta         R : capabilities(), support_matrix(), trust_ledger(), version()
```

Two rules to carry into the Python layer, both from CLAUDE.md:

- **A checker that cannot fail is worse than no checker.** `Evidence.check()`
  returns `bool` and collapses `NothingToCheck` into a pass — bind
  `check_outcome()` and make the three-valued `EvidenceCheck` the Python default.
  Likewise `UnsatProof::recheck_lrat` → `Optional[bool]`, never coerced.
- **`unknown` is a value.** `CheckResult.Unknown` must be a returnable Python
  object carrying `kind`/`detail`, never an exception.

---

## 11. `crates/axeyum-smtlib` — parser + writer (no features, no serde)

**The ownership answer PyO3 needs: `parse_script` does NOT take a caller-owned
`TermArena` — it creates one and gives it away.** `Script` owns it as a *public*
field (`parse.rs:104 pub arena: TermArena`). So the natural binding is one
`#[pyclass] Script` holding the whole `Script`, with `TermId`s valid only against
`script.arena`. `Script` is `Debug + Default` but **not `Clone`** (it owns the
arena). No lifetimes anywhere in the parser output.

| path:line | signature | Python name | tier | notes |
|---|---|---|---|---|
| `parse.rs:726` | `pub fn parse_script(input: &str) -> Result<Script, SmtError>` | `parse_script` | R | |
| `parse.rs:751` | `pub fn parse_script_within(input: &str, deadline: Option<std::time::Instant>) -> Result<Script, SmtError>` | `parse_script(…, timeout_ms=)` | R | `Instant` has no Python analogue — take `timeout_ms: Optional[float]` and build the `Instant` on the Rust side. Same for every `_within`/deadline API in this inventory. |
| `parse.rs:796 / :811` | `parse_script_with_string_bound(input, floor: u32)`, `…_within(input, floor, deadline)` | | R | |
| `parse.rs:503` | `pub fn solvable_flat_view(&self) -> Option<&[TermId]>` | `Script.flat_view` | R | **Bind this one.** Returns `None` for a word-first-fallback parse with empty `assertions`; solving the empty view is a **vacuous `sat`** — a shipped P0. |
| `parse.rs:536` | `pub fn checked_flat_view(&self) -> &[TermId]` | **do not bind** | | `debug_assert!`s instead of returning `None` — panics in debug, silently wrong in release. |
| `parse.rs:38` | `pub enum ScriptCommand` — 16 variants: `Assert(TermId)`, `Push(u32)`, `Pop(u32)`, `CheckSat`, `CheckSatAssuming(Vec<TermId>)`, `ResetAssertions`, `GetAssertions`, `SetLogic(String)`, `SetOption{key,value}`, `GetModel`, `GetValue(Vec<(String,TermId)>)`, `GetUnsatCore`, `GetProof`, `Echo(String)`, `UnansweredOutput(String)` | `ScriptCommand` | R | `Debug+Clone+PartialEq+Eq`. Hand-rolled tagged dict. |
| `write.rs:19` | `pub fn write_script(arena: &TermArena, assertions: &[TermId]) -> String` | `write_script` | R | **Sharing-preserving**: hoists fan-in>1 nodes to 0-ary `define-fun`s, so output is linear in the DAG, not the tree. Emits a complete `set-logic … check-sat` script; round-trip exercised by the crate doctest (`lib.rs:18-32`). **Panics if an assertion does not belong to `arena`** — validate in the binding. |
| `write.rs:304` | `pub fn sort_text(arena: &TermArena, sort: Sort) -> String` | | R | Its own doc warns some sorts render as non-re-parseable placeholders. |
| `lib.rs:77` | `pub enum SmtError { Syntax, Unsupported, Ir(IrError), DeadlineExceeded, ResourceLimit }` | `SmtError` | | `Display` + `core::error::Error`, `From<IrError>`. **`DeadlineExceeded`/`ResourceLimit` are `unknown`, not verdicts** — give them a distinct Python exception (or better, a non-exception outcome) so a user cannot read a budget miss as a parse failure. |
| `lib.rs:67`, `bounded_completeness.rs:64`, `sexpr.rs:134` | `string_literal_code_points(&str) -> Option<Vec<u32>>`, `is_bounded_complete(&str) -> bool`, `read_all(&str) -> Result<Vec<SExpr>, SmtError>` | | R | `SExpr::descendants(&self) -> Descendants<'_>` is a **borrowing** iterator — collect eagerly, do not expose as a Python iterator. |
| `parse.rs:23628 / :23649` | `decode_packed_string(width: u32, value: u128) -> Option<Vec<u8>>`, `packed_string_max_len(width: u32) -> Option<u32>` | | R | Needed to render bounded-string model values. |
| `parse.rs:1475 / :1556` | `SourceStringSatProblem::bounded_witness(&self, max_assignments, max_word_len, max_alphabet) -> Option<SourceStringWitness>`, `replays(&self, &SourceStringWitness) -> bool` | | C | |
| `parse.rs:398 / :440 / :471` | `FpUsage { uses_fp: bool, ops: BTreeSet<String> }`, `certified_faithful_op(&str)->bool`, `fpa2bv_simple_op_certified(&self)->bool` (hardcoded `false`, fail-closed) | | R | |
| `regex_membership.rs:127` | `MembershipProblem::build(arena: &mut TermArena, exprs: &[SExpr]) -> Option<MembershipProblem>` | | P | The only smtlib fn taking `&mut TermArena`. |

## 12. `crates/axeyum-query` — the query object (no features, no serde)

Fully owned, `Send + Sync`, **does not hold an arena**. Handles
`AssertionId:38` / `AssumptionId:49` / `ScopeId:60` (`Copy+Hash+Ord`, `.index()`),
`pub const ROOT_SCOPE: ScopeId = ScopeId(0)` (`lib.rs:70`). Value structs
`Assertion:74` / `Assumption:85` (`{term, scope, label: Option<String>}`) and
`Scope:96` (`{parent: Option<ScopeId>, label}`).

`Query` (`lib.rs:105`, `Debug+Clone+PartialEq+Eq`, private fields) — tier R:
`scopes()/assertions()/assumptions() -> &[…]` (`:118/:123/:128`),
`solver_terms() -> impl Iterator<Item=TermId> + '_` (`:137`, collect),
`solver_term_count():145`, `is_empty():150`,
`structural_cache_key(&self, arena) -> StructuralCacheKey` (`:159`),
`plan_full(&self, arena) -> QueryPlan` (`:164`),
`slice_for_targets(&self, arena, targets: &[TermId]) -> QueryPlan` (`:174`),
`slice_exact_targets(…):184`.

**The only lifetime hazard in this crate:** `QueryBuilder<'a>` (`lib.rs:213`)
holds `arena: &'a TermArena` for its whole life (`new(arena: &'a TermArena)`,
`:222`) and `build(self) -> Query` (`:323`) **consumes self** — awkward for
`#[pymethods]` (needs an `Option::take` dance). Recommendation: **do not expose
`QueryBuilder` as a pyclass.** Accumulate `(scope, term, label)` triples in
Python and run the whole builder inside one Rust call. Methods, for that shim:
`scope(&mut self, parent, label) -> Result<ScopeId, QueryError>:244`,
`assert(&mut self, term) -> Result<AssertionId, QueryError>:259`,
`assert_in(&mut self, scope, term, label):274`, `assume:293`, `assume_in:308`.
`QueryError:360` (`Display+Error`): `NonBooleanAssertion{term,sort}`,
`NonBooleanAssumption{…}`, `UnknownScope(ScopeId)` — type errors are `Err`, not
panics (builders `expect_bool` before pushing).

From `planning.rs` — the **slicing safety contract**, worth binding as a unit:
`QueryTermRole:17`, `StructuralCacheKey{digest,assertions,assumptions,dag_nodes,tree_nodes}:42`
with `hex() -> String:57` (**deterministic and independent of arena-local `TermId`
allocation and of labels — a safe Python cache key**), `PlannedTerm:64`,
`DropReason::{DisjointSupport,NotTarget}:73`, `DroppedTerm:82`, `QueryPlan:93`
(`planned_terms/dropped_terms`, `solver_terms`, `original_cache_key/solver_cache_key`,
`target_support() -> &[SymbolId]`, `is_sliced() -> bool`), and — tier **C** —
`QueryPlan::replay_original(&self, arena: &TermArena, assignment: &Assignment) -> Result<(), QueryReplayFailure>` (`:148`),
**mandatory before accepting a `sat` from a sliced plan.** `QueryReplayFailure:184`:
`Unsatisfied{role,term}` / `Evaluation{role,term,error:IrError}` / `NonBoolean{role,term,value:Value}`.

## 13. `crates/axeyum-cnf` — DIMACS, DRAT, proof-producing CDCL (no features)

Tier **C** is the point of this crate; it is the trusted small checker.

| path:line | signature | Python name | tier | notes |
|---|---|---|---|---|
| `lib.rs:290` | `CnfFormula::to_dimacs(&self) -> String` | `CnfFormula.to_dimacs` | R | Byte-stable contract. |
| `lib.rs:2926` | `pub fn parse_dimacs(input: &str) -> Result<CnfFormula, CnfError>` | `parse_dimacs` | R | |
| `lib.rs:270` | `CnfFormula::evaluate(&self, &[bool]) -> Result<bool, CnfError>` | | **C** | |
| `lib.rs:382` | `CnfAssignment::satisfies(&CnfFormula) -> Result<bool, CnfError>` | | **C** | |
| `drat.rs:83` | `pub fn check_drat(&CnfFormula, &[DratStep]) -> Result<bool, DratError>` | `check_drat` | **C** | The independent RUP+RAT checker (ADR-0011). |
| `drat.rs:379 / :743` | `write_drat(&[DratStep]) -> String`, `parse_drat(&str) -> Result<Vec<DratStep>, DratError>` | | R | |
| `drat.rs:224 / :198` | `DratCheckOutcome::{Verified(bool), ResourceOut, Interrupted}`, `DratCheckProgress` (Copy) | | | **`ResourceOut` is not a pass.** Do not let the Python wrapper turn it into `False` or `True`. |
| `drat.rs:288 / :356` | `check_drat_streaming_with_limits_and_progress(…, progress: Option<&mut dyn FnMut(&DratCheckProgress)>)`, `check_drat_with_limits_and_progress(…)` | *(shim)* | C | Closure + `&mut dyn` — wrap Rust-side; expose `deadline`/`max_steps` only. |
| `proof_sat.rs:216` | `pub fn solve_with_drat_proof(&CnfFormula) -> ProofSolveOutcome` | `solve_with_drat_proof` | P+C | ADR-0012 CDCL core. **Returns a plain enum, no `Result`, and never panics** — undecided is a verdict. |
| `proof_sat.rs:230 / :243` | `…_within(formula, deadline)`, `…_with_limits(formula, deadline, max_conflicts: usize)` | | P+C | |
| `proof_sat.rs:121 / :142 / :176` | `ProofSolveOutcome::{Sat(CnfAssignment), Unsat(Vec<DratStep>), ResourceOut, Interrupted}`, `StreamingProofOutcome`, `ProofSearchProgress` (Copy) | | | |
| `proof_sat.rs:29 / :38` | `DEFAULT_PROOF_SAT_CONFLICT_LIMIT: usize = 2_000_000`, `DEFAULT_PROGRESS_CONFLICT_INTERVAL: usize = 5_000` | | R | Expose as module constants so a Python user can reason about the default budget. |
| `lib.rs:590 / :605 / :671` | `solve_with_rustsat_batsat(&CnfFormula)`, `…_timeout(…, Option<Duration>)`, `…_limits(…, Option<Duration>, Option<u64>)` | | P | Non-proof-producing adapter; **lower assurance** than the DRAT route (ADR-0007). Label it as such in the Python docstring. |
| `lib.rs:548` | `rustsat_batsat_determinism() -> BatSatDeterminism` | | R | |
| `lib.rs:2874 / :2888 / :2908` | `tseitin_encode(&Aig, &[AigLit]) -> Result<CnfEncoding, CnfError>`, `_profiled`, `_profiled_with_origins` | | P | |
| `lib.rs:2838` | `CnfEncoding::aig_node_values_from_assignment(&Aig, &CnfAssignment) -> Result<Vec<bool>, CnfError>` | | **C** | The validating replay map — the "never drop lowering/lift maps" hard rule made concrete. Also `assignment_from_aig_inputs:2802`, `cnf_assignment_from_aig_inputs:2818`. |
| `lib.rs:773 / :1284` | `IncrementalSat` (11 methods), `IncrementalCnf` (13 methods) | | P | **`Send` but `!Sync`** — both embed `rustsat_batsat::Solver<DeadlineCallbacks>` whose private callbacks hold `Cell<u64>`/`Cell<Option<_>>` (`lib.rs:725-726`). Plain `#[pyclass]` is fine; `frozen`/shared access is not. |
| `compact.rs:132 / :59 / :96` | `compact(&CnfFormula) -> (CnfFormula, CompactMap)`, `original_of(usize)`, `expand(&[bool]) -> Vec<bool>` | | R | |

Value types (all `Copy`, all hand-rolled JSON): `CnfVar:132`, `CnfLit:159`
(`dimacs() -> i64`), `CnfVarBinding:2102`, `CnfRoot:2111`, `EncodedLit:2125`.
Owning: `CnfClause:201`, `CnfFormula:226`, `CnfAssignment:346`, `CnfEncoding:2768`,
`DratStep:41`, `VecProofSink:495`.
Not bindable directly: `TextProofSink<W: Write>:549`, `DratTextReader<R: BufRead>:799`,
`CacheDroppingWriter<F>:652` (**`#[cfg(unix)]`**), `colouring::TuplePredicate<F>`,
`DratSink` trait `:471`. The XOR / LRAT / Alethe / BVE / vivify / interpolant
re-exports (`lib.rs:65-115`) are a large additional surface — out of scope for v1.

## 14. `axeyum-bv` / `axeyum-aig` / `axeyum-fp` / `axeyum-strings` / `axeyum-egraph`

**None of these five define `[features]`.** All are pure owned data (`Send + Sync`)
except where noted, and none has serde or a `to_json`.

**`axeyum-bv`** (tier P for lowering, C for the replay maps):
`lower_terms(arena: &TermArena, roots: &[TermId]) -> Result<BitLowering, BitLowerError>` (`lib.rs:55`),
plus `_demanded:74`, `_profiled:91`, `_with_deadline:112`, `_demanded_with_deadline:130`,
`_range_demanded:240`, `_range_demanded_with_deadline:253`, `_with_deadline_profiled:284`.
**Bind the two preflight guards** — `first_unsupported_op(arena, roots) -> Option<(TermId, Op)>:298`
and `first_unsupported_sort(…) -> Option<(TermId, Sort)>:321` — because the lowerer
`unreachable!()`s on Int/Real/Array/datatype/uninterpreted/sequence sorts
(`:1480, :1679, :1912, :1984-1999, :2063-2078, :3085-3100, :3951-3966`), and that
path is **caller-reachable from Python**. `BitLowering:539` carries the maps the
soundness rule demands: `aig():552`, `roots():557`, `term_bits():562`,
`symbol_inputs():567`, `literal_for_term_bit(TermId,u32):585`,
`input_values(&Assignment):605`, `evaluate_root(usize,&Assignment) -> Result<Value,_>:636`,
`assignment_from_aig_values(&[bool]) -> Result<Assignment,_>:673`,
`root_value_from_aig_values:691`. `IncrementalLowering:899` (`new:911`,
`with_profiling:920`, `lower(&mut self, arena, root):967`, `lower_with_deadline:983`).
Value types: `LoweredTerm:344`, `TermBitBinding:370` (Copy), `SymbolBitInput:387`
(owning), `BitDemandStats:409`, `BitLoweringMemoStats:500`, `IncrementalLoweringStats:829`.
Errors: `BitLowerError:1037` incl. `DeadlineExceeded`.

**`axeyum-aig`** (zero deps): `Aig:270` with `input(&mut self, label: impl Into<String>) -> AigLit:333`
(the `impl Into<String>` needs a `&str` wrapper), `and/or/xor:345/:420/:425`, `mux:450`,
`eval(&self, root, inputs: &[bool]) -> Result<bool, AigError>:606`, `eval_many:617`,
and **`to_aiger_ascii(&self, outputs: &[AigLit]) -> String:628`** — deterministic
`aag`, cannot fail. `nodes() -> impl Iterator + '_:314` must be collected.
Handles `AigNodeId:28`, `AigInputId:39`, `AigLit:50` (private fields; `node():69`,
`is_inverted():74`, `negated():80`, `positive(node):88`), `AigNode:109`,
`AigConstructionStats:233`. One error variant: `AigError::InputCountMismatch:705`.

**`axeyum-fp`** (feature `full` when reached via `axeyum_solver::fp`; the crate
itself is unconditional): one file, **60 module-level `pub fn`s**, uniform shape
`fn(arena: &mut TermArena, fmt: FloatFormat, …, mode: RoundingMode) -> Result<TermId, IrError>`
— the `&mut` borrow lasts only the call. `FloatFormat{exp_bits,sig_bits}:46` (Copy)
with consts `F16/F32/F64/F128/BF16/TF32/FP8_E5M2/FP8_E4M3/FP4_E2M1:128-192`,
`width():195`, `is_ieee():203`; `RoundingMode:2578` (5 variants, Copy).
Representative: `is_nan(arena, fmt, x):409`, `eq(arena, fmt, x, y):525`,
`mul(arena, fmt, a, b, mode):861`, `to_fp(arena, src, dst, mode, x):1160`,
`to_ubv(arena, fmt, mode, x, width) -> Result<Option<TermId>, IrError>:3441`.
Groups: classification, comparison, arithmetic (+ `*_rne` no-mode wrappers at
`:2017-2216`), conversion, packing. Constant folders return
`Result<Option<TermId>, IrError>` where `None` means "argument not constant" —
**not** an error, and not a `False`.

**`axeyum-strings`** (feature `full` via the solver; crate itself unconditional):
`solve_word_equations(arena: &mut TermArena, equalities, disequalities, budget: &SearchBudget) -> SearchOutcome` (`arrange.rs:210`)
— `Sat(Assignment)` (replay-checked) or `Unknown{reason}`, **never claims unsat**;
`refute_word_equations(…) -> RefuteOutcome` (`refute.rs:93`) — `Unsat{premises: BTreeSet<usize>}`
or `Unknown`. That asymmetry is the P/C split made explicit and should survive
into Python. `SearchBudget{max_nodes: u64, #[cfg(not(wasm32))] deadline: Option<Instant>}`
— **the one struct in this survey whose shape changes under `cfg`**. Also
`normal_form.rs:59 normalize`, `:72 concat_components`, `infer.rs:209 infer`,
checkers `check_derivation.rs:{129 check_conflict, 193 check_equality, 240 check_congruence_equality, 460 check_fact, 483 check_cycle_constant_conflict}` (tier C),
`lex_order.rs:127 refute_lex`, and the regex surface (`Regex`, `Membership`,
`matcher.rs:40 matches(&Regex,&[u32])->bool`, `derivative.rs:{41 nullable, 147 derivative, 301 canon, 513 derivative_closure}`).
Premise sets are `BTreeSet<usize>` of **original** indices — deterministic, JSON as
sorted int lists. Do not bind `derivative_within<F: FnMut()->bool>:165` /
`canon_within:313` — the only closure-taking public fns in these five crates.

**`axeyum-egraph`** (zero deps, one file, everything `pub` at the crate root):
one long-lived mutable object → `#[pyclass] struct EGraph(EGraph)` with `&mut self`
methods; pure `Vec`s, so no `Send` issue. `EGraph:290`/`new():329`; `ENodeId:111`.
Mutation: `add(&mut self, decl: u32, args: &[ENodeId]) -> ENodeId:833`,
`merge(&mut self, a, b, reason: u32):889`, `find(&mut self, id):867` (path
compression — hence `&mut`), backtracking `push:896` / `pop:908` /
`scope_depth:902`, `attach_th_var:393`. Query (`&self`): `root:873`,
`equal:882`, `len:335`, `decl:348`, `args:354`, `parents:370`,
`class_has_declaration:381`, `th_vars:401`, `theory_var_classes:417`,
`application_decls_since:567`, `inverted_parent_declarations:608`.
E-matching: `Pattern::{Var(u32), App(u32, Vec<Pattern>)}:135`,
`Substitution = Vec<Option<ENodeId>>:155`, `AppMatch:124`,
`enumerate_apps:446`, `ematch(&self, &Pattern) -> Vec<Substitution>:474`,
`ematch_many:490`, `new_match_index() -> EMatchIndex:498`,
`ematch_many_indexed(&self, patterns, index: &mut EMatchIndex):509`,
`ematch_many_candidates_indexed(…):542` — **asserts `patterns.len() == candidates.len()`,
a reachable panic.** `EMatchIndex:165` is a revision-checked cache the caller keeps
alive between calls: a second, owned `#[pyclass]` (it does not borrow the graph).
Proofs (tier C): `explain(&self, a, b) -> Vec<u32>:1130`,
`explain_steps(&self, a, b) -> Vec<ProofStep>:1154` with
`ProofStep::{Input{a,b,reason}, Congruence{a,b,args}}:206`, and the free checker
`check_congruence(graph: &EGraph, premises: &[(ENodeId,ENodeId)], a, b) -> bool:1311`
(O(n²) fixpoint).

## 15. Panic surface a Python caller can reach (must be pre-screened or caught)

`axeyum-bv` `unreachable!()` on unsupported IR sorts (guard with
`first_unsupported_op`/`first_unsupported_sort`); `axeyum-smtlib::write_script`
on a foreign `TermId`; `Script::checked_flat_view` `debug_assert!`;
`GenericArrayValue::constant` `assert!`; `EGraph::ematch_many_candidates_indexed`
length assert; `axeyum-aig` / `axeyum-cnf` / `axeyum-query`
`u32::try_from(…).expect(…)` overflow guards (>4 G entries — not practically
reachable); `drat.rs:926` and `tseitin_encode_profiled_with_origins` internal
invariant `expect`s. Everything else returns `Result`. A `catch_unwind` at the
module boundary is a backstop, not a substitute for the two preflight guards.
