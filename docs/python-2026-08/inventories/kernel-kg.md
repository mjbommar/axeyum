# PyO3 binding inventory: `axeyum.kernel`, `axeyum.producers`, `axeyum.knowledge`

READ-ONLY survey, 2026-08-24. No repo file modified, no cargo run. All measurements
are from `python3`/`grep`/`sed` over committed sources and artifacts, plus one
foreground run of `scripts/fact-frontier.py --json` (exit 0, output written to the
session scratchpad, not the repo).

Tier legend: **R** = required for a minimum viable binding; **P** = phase 2, high
value; **C** = convenience / can be deferred.

---

## PART 1 — Kernel + import public API

### 1.1 Threading and ownership facts that govern the whole binding

`Kernel` (`crates/axeyum-lean-kernel/src/lib.rs:290`) derives
`#[derive(Debug, Default, Clone)]`. Every field is owned plain data —
`Vec<NameNode>`, `HashMap`, a private `SegmentedVec<ExprNode>` arena, an
`ExprInterner` of `Vec<HashMap<u64, ExprId>>`, a `BTreeMap<PreludeKey,
PreludePackage>`, an `Environment`. There is **no `Rc`, `RefCell`, raw pointer,
or interior mutability anywhere in the struct**, and the crate is
`#![forbid(unsafe_code)]` by workspace lint. Therefore `Kernel: Send + Sync +
Clone` by auto-derivation, and a PyO3 `#[pyclass]` wrapping `Kernel` needs no
`unsendable` marker. This is the single most important fact for the binding:
`Kernel` can be freely moved between Python threads and cloned to snapshot state.

The catch is the **handle-provenance rule** stated in CLAUDE.md's Hard Rules and
repeated on `Kernel`'s own doc comment: `NameId`, `LevelId`, `ExprId` are
lifetime-free `Copy` ids that are **only meaningful relative to the kernel that
interned them**. Rust's type system does not stop you mixing them; nothing does.
A Python binding makes that far easier to get wrong, so the wrapper types
(`PyNameId`, `PyExprId`, `PyLevelId`) must each carry a per-`Kernel` epoch/UUID
assigned at `Kernel.new()` and checked on every call that consumes a handle.
Without that, `kernel_a.render_lean(expr_from_kernel_b)` silently renders a
different term. Treat that as the binding's one non-negotiable invariant.

Mutation vs. read is cleanly split in the Rust API and should be mirrored: every
constructor (`name_str`, `level_succ`, `app`, `pi`, …) takes `&mut self` because
it interns; every query (`environment`, `axiom_footprint`, `render_lean`,
`declaration_dependency_closure`) takes `&self`. PyO3's `PyRefMut`/`PyRef` map
onto this directly, which means Python gets a real reader/writer discipline for
free rather than one bolted on.

`crates/axeyum-lean-kernel/Cargo.toml` has exactly one dependency:
`num-bigint = "0.4"`. No dev-dependencies. `crates/axeyum-lean-import/Cargo.toml`
depends on `axeyum-lean-kernel`, `serde_json = "1"`, `sha2 = "0.11"`, also with
no dev-dependencies. Both are `publish = false`. A `pyo3` binding crate would add
only `pyo3` itself, and the no-C/C++-dependency promise (ADR-0002) is preserved
because neither crate links anything native.

### 1.2 Kernel API table

| crate | path:line | signature | Send/Sync/Clone | Python name | tier | notes |
|---|---|---|---|---|---|---|
| lean-kernel | lib.rs:290 | `pub struct Kernel` (`derive(Debug, Default, Clone)`) | Send+Sync+Clone | `kernel.Kernel` | R | `#[pyclass]`, no `unsendable`. Clone = full snapshot. |
| lean-kernel | lib.rs:378 | `pub fn new() -> Self` | — | `Kernel()` | R | `Self::default()`. |
| lib.rs:592 | | `pub fn anon(&mut self) -> NameId` | — | `.anon()` | R | root of every dotted name. |
| lib.rs:597 | | `pub fn name_str(&mut self, parent: NameId, s: impl Into<String>) -> NameId` | — | `.name_str(parent, s)` | R | `impl Into<String>` becomes `String` at the FFI edge. |
| lib.rs:616 | | `pub fn name_num(&mut self, parent: NameId, n: u64) -> NameId` | — | `.name_num` | P | |
| lib.rs:623 | | `pub fn display_name(&self, id: NameId) -> NameDisplay<'_>` | borrows | `.display_name(id) -> str` | R | **borrowing type** (`NameDisplay<'k>`, lib.rs:631, `impl Display`). Must be eagerly `.to_string()`'d — a lifetime cannot cross into Python. |
| lean_pp.rs:1603 | | `pub fn lean_name(&self, id: NameId) -> String` | owned | `.lean_name(id)` | R | owned alternative to `display_name`; prefer for the binding. |
| lib.rs:671-696 | | `level_zero/level_succ/level_max/level_imax/level_param/level_offset(&mut self, …) -> LevelId` | — | `.level_*` | R | |
| lib.rs:705 | | `pub fn level_succs(&self, l: LevelId) -> (LevelId, usize)` | — | `.level_succs` | C | |
| lib.rs:735 | | `pub fn simplify(&mut self, l: LevelId) -> LevelId` | — | `.simplify_level` | C | rename in Python: bare `simplify` is misleading. |
| lib.rs:786/824 | | `substitute_level`, `substitute_expr_levels(&mut self, …, subst: &[(NameId, LevelId)])` | — | `.substitute_*` | P | slice-of-tuples → `Vec<(u32,u32)>`. |
| lib.rs:984-1002 | | `level_leq`, `level_is_equiv`, `level_is_zero`, `level_is_nonzero(&mut self, …) -> bool` | — | `.level_*` | P | note `&mut self` despite reading like predicates. |
| lib.rs:1064-1119 | | `bvar`, `fvar`, `sort`, `sort_zero`, `const_`, `proj`, `app`, `lam`, `pi`, `let_`, `lit` | — | `.bvar` … `.lit` | R | the whole expression constructor set. `const_` → Python `const_`; `let_` → `let_`. `lam`/`pi` take `BinderInfo` (expr.rs) — expose as a `#[pyclass]` enum. |
| lib.rs:1125/1134 | | `lam_body`, `pi_body(&self, e) -> Option<ExprId>` | — | `.lam_body`/`.pi_body` | P | `Option` → `None`. |
| lib.rs:1150-1169 | | `num_loose_bvars`, `has_loose_bvars`, `loose_bvar_range`, `has_fvars` | — | same | P | `Range<u32>` → `(u32,u32)` tuple. |
| lib.rs:1189/1250/1385/1526 | | `instantiate`, `abstract_fvars`, `close_scoped_fvars`, `lift_loose_bvars` | — | same | P | de Bruijn surgery; needed by any producer written in Python. |
| lib.rs:575/565/555 | | `expr_node`, `level_node`, `name_node(&self, id) -> &Node` | borrows | `.expr_node(id) -> PyExprNode` | P | returns `&ExprNode`; must be **copied into an owned Python enum**, never exposed by reference. This is how Python destructures a term. |
| lib.rs:581 | | `pub fn environment(&self) -> &Environment` | borrows | `.declarations()` iterator | R | see §1.3. |
| tc.rs:1505 | | `pub fn add_declaration(&mut self, decl: Declaration) -> Result<(), KernelError>` | — | `.add_declaration(decl)` | R | **the trusted gate.** Rejects `Declaration::Quotient` (use `add_quotient_package`) and duplicate names. |
| inductive.rs:239 | | `pub fn add_inductive(&mut self, name, uparams: &[NameId], num_params: usize, ty: ExprId, ctors: &[(NameId, ExprId)]) -> Result<(), KernelError>` | — | `.add_inductive` | P | |
| inductive.rs:273 | | `pub fn add_mutual_inductive(&mut self, uparams, num_params, families: &[InductiveFamilySpec]) -> Result<(), KernelError>` | — | `.add_mutual_inductive` | C | needs `InductiveFamilySpec` wrapper. |
| quotient.rs:60 | | `pub fn add_quotient_package(&mut self, declarations: &[Declaration]) -> Result<(), KernelError>` | — | `.add_quotient_package` | C | atomic 4-declaration package. |
| tc.rs:2949 | | `pub fn infer(&mut self, e: ExprId) -> Result<ExprId, KernelError>` | — | `.infer` | R | |
| tc.rs:1930/1937 | | `pub fn def_eq(&mut self, x, y) -> bool` / `def_eq_in(…, ctx: &mut LocalContext)` | — | `.def_eq` | R | used by `theorem_knowledge_audit`. |
| tc.rs:1168 | | `pub fn whnf(&mut self, e: ExprId) -> ExprId` | — | `.whnf` | P | |
| lean_pp.rs:1297 | | `pub fn axiom_footprint(&self, name: NameId) -> Vec<NameId>` | owned | `.axiom_footprint(name) -> list[str]` | R | sorted by rendered name → stable, committable. **An absent name yields an empty footprint**, identical to axiom-free: the binding must check `environment().contains(name)` first and raise, or it reproduces the "empty result from a tool never pointed at your subject" trap. |
| lean_pp.rs:1454 | | `pub fn declaration_dependency_closure(&self, name: NameId) -> Vec<NameId>` | owned | `.declaration_dependency_closure` | R | same absent-root caveat. |
| lean_pp.rs:1428 | | `pub fn theorem_dependencies(&self, name: NameId) -> Vec<NameId>` | owned | `.theorem_dependencies` | P | direct deps, self-reference dropped. |
| lean_pp.rs:1349 | | `pub fn declarations_reached(&self, roots: &[ExprId]) -> Vec<NameId>` | owned | `.declarations_reached` | P | |
| lean_pp.rs:378 | | `pub fn render_lean(&self, expr: ExprId) -> String` | owned | `.render_lean` | R | |
| lean_pp.rs:437 | | `pub fn render_lean_decl(&self, decl: &Declaration) -> String` | owned | `.render_lean_decl` | R | |
| lean_pp.rs:514/527/567/582 | | `render_lean_module`, `_compact`, `_with_inductives`, `_compact_with_inductives` | owned | `.render_lean_module*` | P | `_compact` hoists shared closed DAG nodes; semantically equivalent, much smaller. |
| lean_pp.rs:603 | | `write_lean_module_compact_with_inductives<W: Write>` | — | — | C | skip in Python; use the `render_*` twin. |
| lean_pp.rs:647 | | `pub fn render_lean_prelude_module(&self, module_name: &str, roots: &[NameId]) -> LeanPreludeModule` | owned | `.render_lean_prelude_module` | P | `LeanPreludeModule` (lean_pp.rs:196) has `name()`, `source()`, `file_name()`, `provided()`, `provided_len()`, `check_script(dir, query_file)`. |
| lean_pp.rs:689 | | `render_lean_module_compact_importing` | owned | same | C | |
| lean_pp.rs:392/418 | | `render_proofs_as_def(&self) -> bool` / `set_render_proofs_as_def(&mut self, bool)` | — | property | C | ADR-0518; off by default, changes nothing shipped. |
| lean_pp.rs:285-323 | | free fns `self_contained_module_banner()`, `shared_prelude_module_banner()`, `importing_module_banner(m)`, `split_module_banner(src) -> Option<(&str,&str)>` | owned/borrow | module-level fns | C | `split_module_banner` returns borrowed slices — copy at the edge. |
| lean_export.rs:332 | | `pub fn render_lean4export_ndjson(&self, metadata: &Lean4ExportMetadata) -> Result<String, ExportError>` | owned | `.render_lean4export_ndjson` | P | full environment as official NDJSON 3.1.0. |
| lean_export.rs:366 | | `render_lean4export_ndjson_roots(&self, metadata, roots: &[NameId]) -> Result<String, ExportError>` | owned | same | R | the round-trip primitive: export a closure, re-import it elsewhere. |
| lean_export.rs:393/413/466/522 | | `root_declaration_closure*` variants → `Result<Vec<NameId>, ExportError>` | owned | `.root_declaration_closure*` | P | four variants (plain, theorem-leaves, checked auto-param types, checked auto-param binders). |
| lean_export.rs:491/542 | | `render_lean4export_ndjson_roots_checked_auto_param_{types,binders}` | owned | same | P | |
| lean_export.rs:984/1004 | | `write_lean4export_ndjson[_roots]<W: Write>` | — | — | C | byte-identical to the render twins; skip. |
| lean_export.rs:57/70/84 | | `Lean4ExportMetadata` + `::axeyum(lean_version)`, `AutoParamTypeNormalizationReport` | owned | dataclasses | R | `Lean4ExportMetadata::axeyum(v)` is the constructor to expose. |
| lib.rs:494 | | `pub fn release_transient_tables_for_export(&mut self)` | — | `.release_transient_tables_for_export()` | C | one-way: sets `export_only`, after which the kernel cannot type-check. Document loudly or omit. |
| lean-kernel | prelude_cache.rs:97/108 | `pub fn stats() -> PreludeCacheStats`, `pub fn enabled() -> bool` | Copy struct | `kernel.prelude_cache.stats()` | P | `PreludeCacheStats { hits, misses, templates_built }`. |

### 1.3 `Declaration`, `Environment`, `KernelError`

`Declaration` (`env.rs:128`, `derive(Debug, Clone, PartialEq, Eq)`) is the
admission unit and has these variants: `Axiom{name,uparams,ty}`,
`Definition{name,uparams,ty,value,hint}`, `Theorem{name,uparams,ty,value}`,
`Opaque{name,uparams,ty,value}`, `Inductive{name,uparams,ty,num_params,
num_indices,is_recursive,ctor_names}`, `Constructor`, `Recursor`, `Quotient`.
Accessors at env.rs:290/305/320/337 are `name()`, `uparams()`, `ty()`,
`value() -> Option<ExprId>`. In Python this should be a `#[pyclass]` enum with
per-variant constructors (`Declaration.axiom(...)`, `.theorem(...)`) plus those
four accessors, mirroring the Rust shape rather than a dict.

The **trusted-surface distinction matters and is easy to get wrong**: `Axiom`
alone is not the trusted surface — `Opaque` has no proof body and `Quotient`
admits `Quot.sound`. CLAUDE.md records that a lane already got this wrong. Any
Python-side "is this axiom-free?" helper must consult `axiom_footprint` (which
is the kernel's `#print axioms` equivalent), never a variant test.

`Environment` (`env.rs`, re-exported from lib.rs:93) is minimal and maps
cleanly: `new()`, `get(name) -> Option<&Declaration>`, `contains(name) -> bool`,
`len()`, `is_empty()`, `iter() -> impl Iterator<Item = (&NameId, &Declaration)>`.
Because `environment()` returns `&Environment`, the Python side should expose
`Kernel.declarations()` returning an owned `list[(str, Declaration)]` or a
snapshot iterator, not a live borrow. Tier R.

`KernelError` (`tc.rs`, re-exported at lib.rs:118) is a large struct-variant
enum — 26+ variants counted, including `NotAPi`, `NotASort`, `TypeMismatch`,
`LooseBVar`, `UnboundFVar`, `UnsupportedConst`, `UnknownConst`,
`UniverseArityMismatch`, `UnsupportedLit`, `NatLiteralBootstrapMismatch`,
`StringLiteralBootstrapMismatch`, six `Projection*` variants,
`DeclarationExists`, `PreludePackageConflict`, `StringAlphabetSizeOverflow`,
five `Quotient*` variants, plus `DeclarationTypeNotASort` and
`DeclarationValueMismatch` referenced in `add_declaration`'s docs. Recommended
binding: one Python exception class `KernelError` carrying a `.variant: str`
and a `.fields: dict`, rather than 26 exception subclasses. Do **not** flatten
to a string — the variant is what a producer branches on. Tier R.

### 1.4 Preludes and the cache

Every prelude is a free function taking `&mut Kernel` and returning a package
struct: `build_logic_prelude` (prelude.rs:384 → `LogicPrelude`),
`build_nat_prelude` (nat_prelude.rs:886 → `NatPrelude`), `build_int_prelude`
(int_prelude.rs:873), `build_rat_prelude` (rat_prelude.rs:967),
`build_arith_prelude` (arith_prelude.rs:278 → `ArithPrelude`, the **axiomatized**
`AxReal` package), `build_creal_prelude` (creal.rs:1250 → `CRealPrelude`, the
**constructed** reals), `build_complex_prelude` (complex.rs:789),
`build_cpoint_prelude` (creal_point.rs:706), `build_string_prelude`
(string_prelude.rs:283 — takes a caller-held `LogicPrelude`). All return
`Result<_, KernelError>`.

There is **no function that returns a prelude `Kernel`**; every builder mutates
a caller-owned kernel and returns a handle bundle. So the natural Python API is
`k = Kernel(); nat = k.build_nat_prelude()` — with `nat` a `#[pyclass]` holding
the returned package's `NameId` fields.

`prelude_cache.rs` implements ADR-0464 process-wide reuse. Five `OnceLock<Option<Kernel>>`
statics (`LOGIC`, `NAT`, `INT`, `REAL`, `CREAL`) each hold a *template kernel*;
`try_restore` is `pub(crate)` and is called from inside the builders, so a
Python caller gets the cache automatically and cannot address it directly. The
`String` prelude deliberately has no template (it needs a caller-held
`LogicPrelude`, so it never starts pristine). The whole mechanism turns on
`Kernel: Clone`. The reuse precondition is that the target kernel is
*pristine* (identical to `Kernel::default()`); the `is_pristine` predicate is
private. `AXEYUM_PRELUDE_CACHE=0` disables it, read once per process.
`prelude_cache::stats()` is the only public surface and exists so a gate can
prove the cache actually ran — expose it, and expose `enabled()`. The cost
argument is worth surfacing in Python docs: a debug `build_creal_prelude` was
measured at **44 s** versus `AxReal` 5.6 ms and `Logic` 0.2 ms.

Two naming hazards to carry into the Python layer verbatim (both are CLAUDE.md
Gotchas): `AxReal` (30 declared axioms, the repository's only nonzero row,
prelude key **`axreal`** not `real`) versus `CReal` (constructed, 0 axioms) —
and a substring test for `"Real."` matches `"CReal."`. A Python helper that
classifies carriers must decide from the carrier *declaration*, not a substring.

### 1.5 The five kernel examples — what they actually call

| example | library functions used |
|---|---|
| `nat_theorem_inventory.rs` (124 ln) | `build_nat_prelude`, `Kernel::display_name`, `Kernel::render_lean`, iteration over `Declaration` |
| `theorem_axiom_footprint.rs` (103 ln) | `build_nat_prelude`, `build_int_prelude`, `build_arith_prelude`, `Kernel::axiom_footprint`, `display_name` |
| `theorem_dependency_inventory.rs` (124 ln) | `build_logic_prelude`, `build_nat_prelude`, `build_int_prelude`, `build_rat_prelude`, `build_string_prelude`, `theorem_dependencies`, `axiom_footprint`, `display_name` |
| `theorem_knowledge_audit.rs` (410 ln) | `build_nat_prelude`, `environment()`, `axiom_footprint`, `declaration_dependency_closure`, `render_lean`, `def_eq`, `anon`, `name_str`, `display_name` |
| `autogenesis_induction_plan_check.rs` (210 ln) | `build_nat_prelude`, `environment()`, `axiom_footprint`, `declaration_dependency_closure`, `render_lean`, `display_name`, plus `examples/autogenesis_support/mod.rs` (`parse_induction_plans`, `intern_dotted`, `search_induction`) |

Conclusion: **all five are thin CLI shells over the R-tier API above**. Once
`build_*_prelude`, `environment()`, `axiom_footprint`,
`declaration_dependency_closure`, `theorem_dependencies`, `render_lean` and
`display_name`/`lean_name` are bound, every one of them is reimplementable in
~40 lines of Python. That is the strongest argument for the binding: these
examples exist because there was no other way to read the kernel's inventory
(CLAUDE.md: "You cannot read the kernel's theorem inventory from source text" —
grepping `.theorem("…")` returns zero because declarations go through a helper
taking an interned `NameId`).

`examples/autogenesis_support/mod.rs` is a shared example module with three
public fns: `parse_induction_plans(...)`, `intern_dotted(kernel, rendered) ->
Result<NameId, String>` (name resolution by rendered dotted string), and
`search_induction(...)`. `intern_dotted` is the one worth promoting — a Python
caller will constantly want `k.name("Nat.add_comm")`.

### 1.6 `axeyum-lean-import`

| crate | path:line | signature | Send/Sync/Clone | Python name | tier | notes |
|---|---|---|---|---|---|---|
| lean-import | lib.rs:1884 | `pub fn import_ndjson<R: BufRead>(reader: R, limits: ImportLimits) -> Result<CompletedImport, ImportError>` | — | `import_ndjson(path_or_bytes, limits)` | P | generic over `BufRead` — bind a `path: &str` and a `bytes` overload. |
| lean-import | lib.rs:1995 | `pub fn import_statement_ndjson<R: BufRead>(reader: R, limits: ImportLimits, target: &str) -> Result<CompletedStatementImport, StatementImportError>` | — | `import_statement_ndjson(path, limits, target)` | **R** | the proof-isolation gate: rejects every axiom/theorem/opaque/quotient in the stream except names this import itself reconstructed (`report.substituted_theorems`). This is the front door for "hand an untrusted producer a goal". |
| lean-import | lib.rs:2108 | `pub fn census_ndjson<R: BufRead>(…) -> …CensusReport` | — | `census_ndjson` | C | |
| lean-import | lib.rs:2158 | `pub fn probe_first_decline<R, F, T>(…) -> ProbedDecline<T>` | — | — | C | higher-order over a closure; awkward across FFI, defer. |
| lean-import | lib.rs:133 | `pub struct ImportLimits { max_line_bytes: usize, max_records: usize }`, `derive(Debug, Clone, Copy, PartialEq, Eq)` | Copy | `ImportLimits(max_line_bytes=16MiB, max_records=2_000_000)` | R | defaults at lib.rs:140. Copy → trivial to bind. |
| lean-import | lib.rs:239 | `pub struct CompletedStatementImport` (`derive(Debug)`, **not Clone**) | Send+Sync | `CompletedStatementImport` | R | fields private; four accessors + `into_parts`. |
| lean-import | lib.rs:274 | `pub fn into_parts(self) -> (Kernel, ImportReport, NameId, ExprId)` | consuming | `.into_parts() -> (Kernel, ImportReport, name, expr)` | R | **consuming `self`** — PyO3 needs `take`-style handling (`Option<T>` inside the pyclass, or expose `.kernel()/.goal()/.target_name()/.report()` borrows instead and skip `into_parts`). |
| lean-import | lib.rs:246-272 | `kernel(&self) -> &Kernel`, `goal(&self) -> ExprId`, `target_name(&self) -> NameId`, `report(&self) -> &ImportReport` | borrows | same | R | the non-consuming path; prefer these for Python. |
| lean-import | lib.rs:225/374 | `CompletedImport` + `kernel()`, `report()`, `into_parts() -> (Kernel, ImportReport)` | — | same | P | |
| lean-import | lib.rs:151 | `pub struct ImportReport` (`Debug, Clone, PartialEq, Eq`) | Clone | `ImportReport` | R | carries `format_version`, `lean_version`, `lean_githash`, `exporter_version`, counts, `declaration_identities`, `axiom_identities`, `substituted_theorems`. |
| lean-import | lib.rs:283/396 | `StatementImportError`, `ImportError` (both `Debug` + `Display` + `Error`) | — | exception classes | R | |
| lean-import | lib.rs:120/128 | `FORMAT_VERSION = "3.1.0"`, `IDENTITY_VERSION = "axeyum-lean-declaration-identity-v1"` | consts | module constants | R | |
| lean-import | theorem_specialization.rs | `specialize_checked_theorem`, `verify_checked_theorem_specialization`, `CheckedTheoremSpecializationReceipt`, `CompletedTheoremSpecialization`, `SpecializationArgumentReceipt`, `CHECKED_THEOREM_SPECIALIZATION_VERSION`, `CheckedTheoremSpecializationError` | — | `producers.specialize_*` | P | issue/verify pair. |
| lean-import | theorem_composition.rs | `compose_checked_theorem_slice`, `…_with_target_leaves`, `verify_checked_theorem_composition`, `…_with_target_leaves`, `CheckedTheoremCompositionReceipt`, `CompletedTheoremComposition`, `AddedTheoremReceipt`, `AddedDefinitionReceipt`, `AddedSingletonInductiveReceipt`, `ReusedDeclarationReceipt`, `ReusedTypeCompatibility`, `checked_reused_declaration_compatibility`, two version consts | — | `producers.compose_*` | P | |
| lean-import | identity.rs | `canonical_declaration_sha256`, `canonical_expression_sha256`, `canonical_alpha_expression_sha256`, `canonical_kernel_type_shape_sha256`, `canonical_level_sha256`, `DeclarationIdentity`, `AxiomIdentity`, `DeclarationDependencyIdentity`, `DeclarationKind` | — | `kernel.identity.*` | **R** | these are the content-addressing primitives every artifact's `*_sha256` field comes from. Any Python that writes a receipt needs them. |
| lean-import | checked_theorem_receipt.rs, semantic_contract_receipt.rs, trace_contract_receipt.rs, trace_contract_theorem_receipt.rs, type_slice_receipt.rs, source_delta_trace.rs, contract_residualization.rs, type_slice.rs | ~40 further `issue_*`/`verify_*` + receipt types (see lib.rs:59-118) | — | `producers.*` | C | large, uniform issue/verify surface; bind on demand. |

**Receipt-shape warning for the binding.** CLAUDE.md's certificate gotcha applies
directly here: a certificate must carry every distinction its producer makes,
and mutation testing cannot find a guard that was never written. If the Python
layer ever *constructs* a receipt rather than passing one through, it inherits
that obligation. Safest initial policy: Python may `verify_*` freely, but
`issue_*` should stay Rust-side until the receipt shapes are frozen.

### 1.7 The producers — currently in `examples/`, not `src/`

Confirmed: **both live under `examples/`, neither is in any `src/`.**

- `crates/axeyum-lean-import/examples/bounded_induction_support/mod.rs` — 3,759
  lines. `pub const MAX_BINDERS: usize = 8` (line ~165);
  `pub struct Candidate { pub proof: ExprId, pub binders_used: usize, pub inductions_used: usize }`
  (line 269, `derive(Debug)`); `pub enum DeclineReason` (line 278,
  `derive(Debug, Clone, PartialEq, Eq)` + `impl Display`) with variants
  `BinderBudgetExceeded`, `NotEqualityGoal`, `TerminalNotDefEqNoRewrite`,
  `RequiredDeclarationUnavailable(String)`, `UnsupportedRecursorShape(String)`;
  and `pub fn propose_bounded_induction(kernel: &mut Kernel, goal: ExprId) ->
  Result<Candidate, DeclineReason>` (line 3494). Private consts
  `MAX_LE_ASCENT_STEPS = 16`, `FVAR_BASE = 9_000_000`.
- `crates/axeyum-lean-import/examples/modeq_family_support/mod.rs` — 605 lines.
  Same shape: `pub struct Candidate` (51), `pub enum DeclineReason` (58),
  `pub fn propose_modeq_family(kernel: &mut Kernel, goal: ExprId) ->
  Result<Candidate, DeclineReason>` (540), plus `pub struct CircularityAudit`
  (567) and `pub fn audit_circularity(kernel: &Kernel, candidate: NameId,
  target: NameId) -> CircularityAudit` (598).
- `crates/axeyum-lean-import/examples/modeq_family_operation.rs` — 111 lines, a
  driver: `import_statement_ndjson` → `into_parts` → `propose_modeq_family` →
  `sha256` of the rendered goal → mints
  `Axeyum.Autogenesis.ModEqFamily.M<sha16>` via `anon`/`name_str` → audits with
  `declaration_dependency_closure`. `examples/bounded_induction_operation.rs`
  (119 lines) is its twin.

**Promotion cost to `src/producers/`: essentially zero dependency work.**
`bounded_induction_support/mod.rs` imports only
`std::collections::BTreeSet` and `axeyum_lean_kernel::{BinderInfo, Declaration,
ExprId, ExprNode, Kernel, LevelId, LocalContext, LocalDecl, NameId}` —
every one already a dependency of `axeyum-lean-import`.
`modeq_family_support` imports the same minus `LocalContext`/`LocalDecl`. The
drivers add `sha2` (already a dependency) and `serde_json` is not used by the
support modules at all. Neither crate has dev-dependencies, so nothing
example-only is in play. Promotion is mechanical: move the two `mod.rs` files
under `src/producers/{bounded_induction,modeq_family}.rs`, add `pub mod
producers;` and re-exports, and replace the `#[path = "…/mod.rs"] mod` lines in
the drivers with `use axeyum_lean_import::producers::…`.

Two non-mechanical obligations come with it. First, **budget constants are part
of a settled fact's reproduction contract**: `MAX_BINDERS = 8` is pinned in every
`mathlib-bounded-induction-family-*` manifest, and
`check-autogenesis-bounded-induction-family.py` correctly refuses a mismatch
even when every `proof_sha256` is byte-identical. A comment in the file records
that raising it to 12 was reverted within the hour for exactly this reason. So
`MAX_BINDERS` must be exposed to Python as a read-only constant, never a
keyword argument with a default. Second, promotion moves ~4,400 lines from
example-compiled to library-compiled, which brings them under
`cargo test --workspace --lib` and `clippy -D warnings` on default features —
a benefit, but it changes the gate surface and should be its own commit.

For Python, the producer API is small and clean:
`producers.propose_bounded_induction(kernel, goal) -> Candidate` raising
`DeclineError(reason)`, with `DeclineReason` as a `#[pyclass]` enum so the
Python side branches on the *typed* reason (the whole point of the enum is that
a caller reports a precise reason rather than a free-form string). Tier R for
both producers.

---

## PART 2 — Knowledge-graph artifacts for `axeyum.knowledge`

### 2.1 `artifacts/facts/*.json` — the fact ledger

- **Path**: `artifacts/facts/*.json`, one file per proposition. **350 files.**
- **Schema**: `artifacts/ontology/fact.schema.json` (`title: "Fact"`).
- **Required**: `schema_version`, `id`, `title`, `statement`, `formal`,
  `epistemic_status`, `depends_on`, `evidence`, `provenance`.
- **Optional**: `external_status`, `proof_route`, `axiom_footprint`,
  `concept_refs`, `notes`, `supersedes`.
- **Measured field presence** (of 350): `schema_version`/`id`/`title`/
  `statement`/`formal`/`epistemic_status`/`depends_on`/`evidence`/`provenance`
  350 each; `notes` 346; `external_status` 342; `proof_route` 156;
  `axiom_footprint` 154; `concept_refs` 91.
- **`epistemic_status`** (what *we* established) enum: `axiom`, `proved`,
  `computed`, `empirical`, `conjectured`, `open`, `refuted`. Measured:
  `open` 191, `proved` 150, `refuted` 4, `conjectured` 3, `computed` 2.
- **`external_status`** (what mathematics knows) enum: `proved`, `refuted`,
  `conjectured`, `open`, `unknown`. Measured: `proved` 313, `unknown` 21,
  `open` 5, `refuted` 3, absent 8.
- **`proof_route`** enum: `kernel-lean`, `imported-kernel-lean`,
  `smt-term-level`, `smt-clausal`, `search-certificate`, `cas-certificate`,
  `none`.
- **`formal`**: `{language, statement, fragment, free_symbols}`, `language` ∈
  `smtlib2 | lean4 | lean4-surface | axeyum-ir | cas-term | certificate-spec`,
  `additionalProperties: false`.
- **`evidence[]`**: required `{id, kind, supports, check_status}`, optional
  `checkers[]`, `additionalProperties: true`. `kind` ∈ `kernel-term`,
  `witness-replay`, `unsat-certificate`, `cube-cover`, `cube-tree-cover`,
  `exhaustive-enumeration`, `published-value-replication`, `bound-citation`,
  `instance-pin`, `claim-ref`. `check_status` ∈ `checked | replay-only |
  not-checked`. The schema's own note records why `checkers[]` exists: the
  first 50 evidence rows all said `checked`, so the field had no discriminating
  power.
- **`provenance`**: required `date`; optional `established_by`, `source`,
  `prior_art[]`.
- **Canonical reader/validator**: `scripts/validate-facts.py`. Structural
  validation is deliberately local (no `jsonschema`), and the **semantic rules
  are the contract the Python layer must mirror**: `proved`/`computed`/
  `refuted` require evidence actually `checked`; `proved` requires an
  `axiom_footprint` (empty array = axiom-free, a *stronger* claim than absence);
  `open` requires an empty evidence array; `depends_on` must resolve; a
  `claim-ref` must point at an existing claim file; `external_status` of
  `proved`/`refuted` requires `provenance.prior_art`; a settled fact must name
  its `proof_route`, and `axiom_footprint: []` is rejected on routes that
  cannot deliver axiom-freedom (two incompatible footprint vocabularies once
  coexisted — 17 kernel `[]` vs 14 SMT `["axeyum-ir.bool-evaluator", …]`).
  It also *reports without failing* facts we established that the literature
  has not. Related gates: `check-fact-dag.py`, `check-fact-depends-derived.py`,
  `check-fact-derived-numbers.py`, `check-fact-evidence-replay.sh`,
  `check-settled-fact-statements.py` (against
  `artifacts/ontology/settled-fact-statement-pins.json`),
  `check-established-facts-bounded-truth.py`, `check-imported-fact-lean-axioms.sh`.
  Writers: `new-fact.py`, `close-fact.py`,
  `prepare-/apply-autogenesis-fact-transaction.py`.

### 2.2 `scripts/fact-frontier.py --json`

Ran foreground, exit 0. `kind: "axeyum-fact-frontier"`, `schema_version: 1`,
`authority: "artifacts/facts"`. Top-level keys: `authority`, `capabilities`,
`entries`, `frontier_sha256`, `kind`, `ledger`, `policy`, `schema_version`,
`selection`.

- `entries`: **196 rows**, each `{band, dependency_ready, epistemic_status,
  external_status, fact_id, fact_sha256, fragment, gate_mentions,
  missing_dependencies, registered_operation_ids, route_class,
  stale_reviewed_gate_mentions, unreviewed_gate_mentions, would_unlock}`.
- `selection`: `{admissible_fact_ids, outcome, rationale, ready_fact_ids,
  selected_fact_id}`. Current run: `outcome:
  "refused-no-admissible-candidate"`, `admissible_fact_ids: []`, with a
  per-fact `rationale[] = {fact_id, rejected_by[]}` naming
  `no-supported-route` / `no-registered-operation`. **This refusal is the
  designed behaviour, not a failure** — the Python accessor must surface
  `outcome` and never treat an empty `admissible_fact_ids` as an error.
- `capabilities`: `{decidable_fragments[19], demonstrated_by{fragment →
  fact_id}}`. Fragments: LIA, LRA, NRA, QF_ABV, QF_BV, QF_FP, QF_LIA, QF_LRA,
  QF_NIA, QF_NRA, QF_SLIA, QF_UF, QF_UFLIA, UF, finite-gf2-enumeration,
  gf2-extension-polynomial-identity, gf2-finite-field-order,
  gf2-polynomial-identity, hypergeometric-summation.
- `policy`: `{autonomous_dispatch_requires_registered_operation, band_order,
  fact_order, operation_registry_sha256, proof_route_fragments,
  registered_operations, settled_statuses, terminating_routes}`.
- `ledger`: `{fact_count, ledger_sha256}`.
- `frontier_sha256`: content hash of the whole frontier
  (this run: `874042bd…`). Expose it — it is what pins a dispatch decision.

### 2.3 `artifacts/autogenesis/operations.json`

`{schema_version: 1, kind: "axeyum-autogenesis-operation-registry"-family,
operations: […]}` — **26 operations**. Per-operation keys: `id`, `scope`,
`applicability`, `producer`, `checker`, `admission` (all 26), `executor` (25),
`reviewed_gate_mentions` (23). `applicability = {fact_ids[], formal_languages[],
fragments[]}`; `producer`/`checker` = `{operation, implementation, input_kind,
output_kind}`; `admission = {epistemic_status, proof_route, evidence_kind,
axiom_footprint_policy, axiom_footprint}`.

`scope`: `authoritative` 25, `counterfactual-fixture-only` 1.
**Generality, measured**: `fact_ids` length 1 for **24 of 26**; only
`authoritative-mathlib-bounded-induction-factorial-family-v1` (5) and
`authoritative-mathlib-modeq-family-v1` (4) name more than one. This is exactly
the "dispatch table, not a producer" defect CLAUDE.md documents — the Python
layer should expose `is_multi_target` / `n_targets` derived from
`applicability.fact_ids`, never from a label.

Validator: `scripts/validate-autogenesis-operations.py`. Its
`EXECUTION_DRIVERS` allowlist (lines 19-29) has **9 members**:
`axeyum-bench/smtcomp-evidence-v1`, `axeyum-lean-kernel/nat-zero-add-induction-v1`,
`axeyum-lean-kernel/nat-mul-one-episode-apply-v1`,
`axeyum-lean-import/statement-reflexivity-v1`,
`axeyum-lean-import/bounded-induction-multi-target-v1`,
`axeyum-lean-import/modeq-family-multi-target-v1`,
`axeyum-lean-import/checked-theorem-receipt-v1`,
`axeyum-lean-import/dependency-theorem-receipt-v1`,
`axeyum-lean-import/sealed-kernel-capsule-v1`. Each driver has its own required
`executor` key set (e.g. `nat-zero-add-induction-v1` needs `target_theorem`,
`denied_theorems`, `budget`). Also in that file: `ADMISSION_CONTRACTS` (two
allowed `(epistemic_status, proof_route, evidence_kind, footprint_policy)`
tuples) and `SEALED_CAPSULE_CONTRACTS` (per-fact `result_manifest`,
`capsule_path` under `/nas3/…`, `capsule_sha256`, `target_theorem`,
`receipt_sha256`). Executor: `scripts/execute-autogenesis-operation.py`.

### 2.4 `artifacts/autogenesis/knowledge-overlay-v1.json`

Schema: `artifacts/ontology/autogenesis-knowledge-overlay.schema.json`
(`$id: https://axeyum.dev/ontology/autogenesis-knowledge-overlay.schema.json`).
Required = the seven top-level keys exactly: `schema_version`, `kind`,
`sources`, `namespaces`, `relation_types`, `entities`, `links`.
`kind: "axeyum-autogenesis-knowledge-overlay"`, `schema_version: 1`.

- `sources`: **2** — `{id: "axeyum", kind: local-repository, revision_policy:
  live-worktree, path_hint: "."}` and `{id: "math-education", kind:
  external-repository, revision_policy: pinned, revision:
  "ce3e2a52e7c95075d69262b4d8f0ee8fe748f22c", path_hint: "../math-education",
  license_note: …}`.
- `namespaces`: **4** — `axeyum-knowledge` (overlay-entity; kinds capability,
  obstruction, episode, representation), `axeyum-fact` (local-required, path
  `artifacts/facts`, `id_pattern ^F:[a-z0-9]+(-[a-z0-9]+)*$`),
  `axeyum-operation` (local-required, `artifacts/autogenesis/operations.json`),
  `math-education` (external-pinned, path `graph`, `id_pattern` covering
  `C:<slug>[@remember|understand|apply|analyze|evaluate|create]` and `TQ:<slug>`).
- `relation_types`: **7** — `realizes-capability`, `established-by`,
  `formalizes`, `uses-technique`, `exemplifies`, `blocked-by`, `unlocks`, each
  with `source_kinds`/`target_kinds`/`semantics`.
- `entities`: **2** — `K:bounded-structural-induction` and
  `K:modeq-equivalence-combinators`, both `kind: capability`, with
  `attributes` carrying `max_binders: 8`, `max_inductions: 2`,
  `assurance_floor: "kernel-lean-empty-axiom-footprint"`.
- `links`: **24** — `{id, relation, source{namespace,kind,id}, target{…},
  assurance, status, reason, provenance{method, sources[]}}`. Relations:
  `formalizes` 10, `established-by` 7, `exemplifies` 3, `realizes-capability` 2,
  `uses-technique` 2. Assurance: `human-reviewed` 15, `independently-checked` 7,
  `registry-derived` 2. External endpoints additionally carry `source_revision`.

Validator: `scripts/validate-autogenesis-knowledge.py`. Beyond schema it checks
unique ids, typed endpoints, local resolution, pinned revisions, and
relation domain/range. `ENTITY_KINDS` (15), `ASSURANCE` (7:
formal-derived, independently-checked, registry-derived, mechanically-observed,
human-reviewed, heuristic, proposed), and a `METHODS` set are module constants
the Python layer should mirror. **Pin resolution**: `git_head()` runs
`git -C ../math-education rev-parse HEAD`; if the sibling is absent, external
resolution is *skipped* (the checkout is optional and CI does not vendor it);
if present but at a different commit, a **warning** is emitted and live
resolution is skipped; only at the exact pin does it resolve each endpoint via
`math_education_resolves()`, which maps `C:<slug>` → `graph/concepts/<slug>.md`
and `TQ:<slug>` → `graph/techniques/<slug>.md` (the `@level` suffix is stripped
first). Measured here: the sibling **is present and at `ce3e2a52…`**, so
resolution is live in this checkout. Coverage generator:
`scripts/gen-autogenesis-knowledge-coverage.py` → reads the overlay +
`operations.json`, writes `docs/plan/generated/autogenesis-knowledge-coverage.md`,
supports `--check`; it counts authoritative operations with
`len(applicability.fact_ids) > 1` — i.e. it gates generality, not coverage.

### 2.5 `artifacts/autogenesis/nursery-v1.json` — the blind evaluation population

`kind: "axeyum-autogenesis-nursery"`, `schema_version: 1`, `state:
"frozen-evaluation"`. Top-level keys: `schema_version`, `kind`, `state`,
`policy`, `amendments`, `entries`, `longitudinal_result`, `split_policy`,
`split_policy_sha256`, `source_catalog_sha256`, `notes`.

`entries`: **216 rows**, each `{fact_id, partition, provenance_class, family,
proof_shape, source_group, route_hypotheses[], mutation_of, answer_access}`.
Partition counts **as of today**: `development` 79, `train` 78, `held-out` 57,
`longitudinal` 2. **13 distinct families.** Note this is *post-amendment* — the
README's "214 Mathlib statements" plus 2 longitudinal rows.

`policy` fields: `admission_dependency_authority:
proof-derived-kernel-dependency`; `evaluation_fact_count {min 100, max 300}`;
`minimum_declared_dependency_depth: 2`; `minimum_held_out_components: 1`;
`minimum_provenance_classes: 2`; `minimum_route_hypothesis_families: 2`;
`minimum_statement_mutations: 1`; four leakage rules —
`family_leakage: no-family-may-cross-evaluation-partitions`,
`proof_shape_leakage`, `source_group_leakage`, `split_leakage:
no-declared-component-may-cross-evaluation-partitions`;
`required_evaluation_partitions: [train, development, held-out]`;
`split_component_authority: declared-dependency-weak-component`;
`split_freeze: before-target-outcomes`.

`amendments`: **1 row**, dated 2026-08-22 — family `natural-gcd` moved
`held-out → development`, `irreversible: true`, `breach: {fact_id:
F:ml430-nat-gcd-greatest-0a04214a, proof_shape: natural-gcd:conditional-proposition,
operation_id: authoritative-mathlib-nat-gcd-greatest-kernel-capsule-v1,
registered_commit: 6e112b4bc, registered_date: 2026-08-21, detected_date:
2026-08-22}`, `authority: docs/research/09-decisions/adr-0542-…md`. The reason
field states the rule directly: the family moves rather than splits because
`partition_unit` is whole-family-with-source-review-groups-indivisible.

**The held-out rule the Python layer must enforce**: the split key is
`<family>:<statement-shape>`, so touching one member spends the whole family —
one row cost 19 of 76 held-out propositions. Gate:
`scripts/check-autogenesis-holdout-isolation.py`, fail-closed, two directions:
(1) no held-out fact may be settled in the ledger (`SETTLED = {proved,
computed}`) by *any* route, and (2) **no artifact under
`artifacts/autogenesis/` may reference a held-out fact id**, except the two
`POPULATION_FILES = {nursery-v1.json, mathlib-nat-int-fact-catalog-v1.json}`.
It uses a generic recursive string walk deliberately, because operations already
carry fact ids at three JSON paths (`applicability.fact_ids[]`,
`executor.input_fact_id`, `executor.premise_fact_id`) and a field-specific guard
was bypassable the day it was written. An unreadable manifest or an empty
held-out population is an **error**, not a pass. Companion:
`check-autogenesis-nursery.py` (internal manifest integrity only — it does not
inspect what operations do to the population), plus
`create-autogenesis-mathlib-nursery-{split,review}.py` and
`create-autogenesis-nursery-dispatch-baseline.py`.

A trap to encode in the accessor: **"dependency-ready" and "train+development"
are both 138 and are different sets** — the ready set is 44 train, 44
development and 50 held-out. Any `knowledge.nursery` API must answer partition
questions by `partition`, never by a count.

### 2.6 `artifacts/claims/` — the claim ledger

Layout is `artifacts/claims/<family>/<id>/claim.json`, **not** flat.
**104 claim files** across 3 families: `offdiag-schur`, `rado`, `vdw`.
Schema `artifacts/ontology/claim.schema.json`; required `schema_version`, `id`,
`title`, `statement`, `epistemic_status`, `formal`, `concept_refs`,
`axeyum_refs`, `provenance`, `evidence`; optional `novelty`, `frontier`,
`supersedes`, `notes`. Measured presence: `novelty` 64, `frontier` 3, rest 104.
`epistemic_status`: `computed` 101, `open` 3. A claim's `formal` is a
**generator recipe** (`{language: "cnf-family", family, parameters, generator:
"crates/axeyum-search/src/offdiag.rs", semantics_note}`), which is the
documented distinction from a fact, whose `formal` is the proposition itself.
`concept_refs[]` entries carry `{graph: "math-education", ref: "C:…", relation,
resolved, notes}` — i.e. claims already point into the sibling graph.
Readers: `scripts/validate-claims.py` (also checks `axeyum_refs.fragments ⊆
artifacts/ontology/smt-fragments.json`; supports `--root`; prints
"no claims found under artifacts/claims/**/claim.json" rather than failing
silently), `scripts/gen-claims-dashboard.py` → `artifacts/claims/DASHBOARD.md`
(32 KB, note this generated file lives under `artifacts/`, **not**
`docs/plan/generated/`), `check-claim-certificates.py`,
`check-claim-negative-fixtures.py`, `check-stale-negative-claims.py`,
`recertify-claims.py`, `apply-recertified-claims.py`.

### 2.7 `artifacts/ontology/foundational-concepts.json`

`{schema_version: 1, generated_from: [4 sources], rows: [137]}`. Row keys:
`id`, `kind`, `title`, `domain`, `field_ids[]`, `curriculum_node`,
`curriculum_layer`, `curriculum_area`, `curriculum_status`, `curriculum_family`,
`resource_status`, `summary`, `prerequisites[]`, `unlocks[]`, `decidability`,
`axeyum_fragments[]`, `example_packs[]` (each `{id, status, path, notes}`),
`proof_routes[]`, `source_refs[]`, `open_gaps[]`, `graduation`.
**Generated**, not hand-written: `scripts/gen-foundational-concepts.py` reads
`docs/curriculum/curriculum.toml`, `docs/foundational-resources/MATH-FIELDS.md`
and the curriculum layer directories (`docs/curriculum/00-foundations` …
`03-destinations`) and writes the JSON. Validator:
`scripts/validate-foundational-concepts.py` against
`foundational-concepts.schema.json`, which additionally checks that every
`example_packs[].path` exists on disk when `status == "validated"`. Gate:
`just foundational-resources`. This is the `curriculum-node` layer of the
overlay's `ENTITY_KINDS` and the natural join target for facts' `concept_refs`.

### 2.8 The sibling `../math-education/graph/`

Present in this checkout, at `HEAD = ce3e2a52e7c95075d69262b4d8f0ee8fe748f22c`
— **exactly the overlay pin**, so live endpoint resolution is active here.
Layout: `graph/{concepts, techniques, events, misconceptions, ontology, people,
places, playables, themes, threads, tracks, vocab, works, figures}` plus
`README.md`, `AUTHORING.md`, `INVENTORY.md`, `QUALITY.md`.
Measured: **concepts 1,567 files**, **techniques 42 files**, and
**`encounters/` does not exist as a directory** — encounters are an inline
front-matter list *inside* each concept file, which the Python accessor must
model accordingly.

One file per node, Markdown with YAML front matter. Concept front matter:
`id` (`C:<slug>`), `type: Concept`, `title`, `pref_label`, `alt_labels[]`,
`short_definition`, `definition`, `epistemic_status`, `status`, `confidence`,
`strand` (`S:…`), `created`, `updated`, `related[]`, `bridges_to[]`
(`{concept, domain_area, reason}`), and `encounters[]` — each
`{level ∈ remember|understand|apply|analyze|evaluate|create, summary,
objectives[{statement, knowledge_dimension}], requires[{encounter:
"C:x@understand", strength}]}`. Technique front matter: `id` (`TQ:<slug>`),
`type: Technique`, `title`, `pref_label`, `short_definition`, `definition`,
`epistemic_status`, `status`, `confidence`, `created`, `updated`, `refrain`,
`related[]`, then prose body.

Ownership note from the overlay's `license_note`: the sibling is owned by the
project owner; **Axeyum copies or adapts selected metadata and never mutates
it**. A Python accessor must be strictly read-only over this path, and must
degrade cleanly when the checkout is absent or off-pin, mirroring the
validator's skip-with-warning rather than erroring.

### 2.9 `artifacts/autogenesis/` — plan / result / decline / capsule JSONs

**958 JSON files** parsed (plus `README.md`), every one carrying a `kind`.
**707 distinct `kind` values** — the vocabulary is per-episode, not enumerable
as a closed set, so a Python accessor must classify by *shape*, not by exact
kind. Aggregating on the terminal token of `kind` (after stripping a trailing
`-vN`):

| terminal token | count |
|---|---|
| `-plan` | 448 |
| `-result` | 408 |
| `-admission` | 13 |
| `-audit` | 12 |
| `-decline` | 11 |
| `-candidate` | 9 |
| `-adapter` | 9 |
| `-policy` | 8 |
| `-control` | 3 |
| `-census` | 3 |
| `-composition`, `-replay`, `-source`, `-reflexivity`, `-primary`, `-receipt`, `-qualification`, `-exact`, `-candidates` | 2 each |
| `-capsule`, `-addendum`, `-overlay`, `-family`, `-residualization`, `-delta`, and ~20 further singletons | 1 each |

Filename suffixes agree closely (`*-plan.json` 448, `*-result.json` 424,
`*-admission.json` 13, `*-decline.json` 11, `*-adapter.json` 9,
`*-policy.json` 8, `*-nursery.json` 2, `*-capsule.json` 1, `*-overlay.json` 1),
so a filename-suffix router is a sound first cut with the `kind` field as the
authoritative confirmation. The plan/result pairing is the dominant idiom: 448
plans, 408 results, each pair having its own dedicated
`scripts/check-autogenesis-<name>-{plan,result}.py` checker — roughly 60 such
scripts of the 716 in `scripts/`. `axeyum-theorem-goal-identity-audit` (12) and
`axeyum-autogenesis-mathlib-sealed-kernel-capsule-admission` (9) are the largest
non-plan/result families.

### 2.10 `docs/plan/generated/*.md` and their generators

**50 files** (26 `.md` with 24 `.json` twins). Mapping:

| generated file | generator |
|---|---|
| `autogenesis-baseline.md` / `.json` | `scripts/gen-autogenesis-baseline.py` (reads `artifacts/facts`, `docs/plan/generated/proof-gap-matrix.json`; `--capture` binds to a clean commit) |
| `autogenesis-knowledge-coverage.md` | `scripts/gen-autogenesis-knowledge-coverage.py` (overlay + operations) |
| `lean-axiom-ledger.md` | `scripts/gen-lean-axiom-ledger.py` (`EXPECTED_PRELUDES`; the SHA-256 binding of every prelude axiom type) |
| `lean-compatibility.md` | `scripts/gen-lean-compatibility.py` |
| `lean-complete-parity.md` / `.json` | `scripts/gen-lean-complete-parity.py` (+ `check-parity-docs.py`) |
| `lean-execution-acceptance.md` / `.json` | `scripts/lean_execution_acceptance.py` |
| `lean-execution-evidence.md` / `.json` | `scripts/gen-lean-execution-evidence.py` |
| `lean-execution-process.md` / `.json` | `scripts/lean_execution_process.py` |
| `lean-execution-store.md` / `.json` | `scripts/lean_execution_store.py` |
| `lean-official-construct-matrix.md` | `scripts/check-lean-official-construct-matrix.py` |
| `lean-u2-native-dependency.md` / `.json` | `scripts/gen-lean-u2-native-dependency.py` |
| `lean-u2-native-header-contract-m2.1.md` / `.json` | `scripts/lean_u2_native_dependency_m2_1.py` |
| `lean-u2-native-surface-classification.md` / `.json` | `scripts/gen-lean-u2-native-surface-classification.py` |
| `lean-u2-native-surface-content.md` / `.json` | `scripts/gen-lean-u2-native-surface-content.py` |
| `lean-u2-normalization-contracts.md` | `scripts/lean_u2_normalization_contracts.py` |
| `lean-u2-official-child-shards.md` / `.json` | `scripts/gen-lean-u2-official-child-shards.py` |
| `lean-u2-official-ci-profiles.md` / `.json` | `scripts/gen-lean-u2-official-ci-profiles.py` |
| `lean-u2-official-execution-tl0.6.3-m0.md` / `.json` | `scripts/lean_u2_official_execution.py` |
| `lean-u2-official-execution-tl0.6.3-m0-r3.md` / `.json` | `scripts/lean_u2_official_execution_r3.py` |
| `lean-u2-test-authority.md` / `.json` | `scripts/gen-lean-u2-test-authority.py` |
| `measurement-provenance-matrix.md` / `.json` | `scripts/gen-measurement-provenance.py` (from `docs/plan/measurement-provenance-v1.json`) |
| `production-provenance-ledger.md` | `scripts/gen-production-provenance-ledger.py` (facts + operations; derives generality from `applicability.fact_ids`, never a label) |
| `proof-gap-matrix.md` / `.json` | `scripts/gen-proof-gap-matrix.py` (from `bench-results/dominance`) |
| `proof-gap-shape-census.md` / `.json` | `scripts/gen-proof-gap-shape-census.py` |
| `smtcomp-repaired-p0-comparison.md` / `.json` | `scripts/generate-smtcomp-repaired-p0-comparison.py` |
| `smtcomp-resumable-run-contract.md` / `.json` | `scripts/gen-smtcomp-resume-contract.py` |
| `smtlib-api-conformance.md` | `scripts/gen-smtlib-api-conformance.py` |
| `smtlib-session-contract.md` | `scripts/gen-smtlib-session-contract.py` |
| `theorem-production-ledger.md` | `scripts/gen-theorem-production-ledger.py` — runs `cargo run --release -p axeyum-lean-kernel --example prelude_theorem_inventory -- --include-constructed`, with an `EXPECTED_PRELUDES` tuple so dropping a prelude reddens rather than narrows |

`scripts/flywheel-status.sh` reads three of these
(`theorem-production-ledger.md`, `production-provenance-ledger.md`,
`proof-gap-matrix.md`). Note `artifacts/claims/DASHBOARD.md` is generated too
but lives outside `docs/plan/generated/`.

---

## Recommended module split

- **`axeyum.kernel`** — `Kernel`, handle wrappers with epoch checking,
  `Declaration`, `Environment` snapshot, `BinderInfo`, `Lit`, `KernelError`,
  the `build_*_prelude` family, `axiom_footprint`,
  `declaration_dependency_closure`, `theorem_dependencies`, `render_lean*`,
  `render_lean4export_ndjson_roots`, `Lean4ExportMetadata`, `prelude_cache.stats()`,
  and the `identity.canonical_*_sha256` hashing primitives.
- **`axeyum.producers`** — `import_statement_ndjson` + `ImportLimits` +
  `CompletedStatementImport`, `propose_bounded_induction`,
  `propose_modeq_family`, `audit_circularity`, `Candidate`, `DeclineReason`,
  `MAX_BINDERS` as a read-only constant, and the `verify_*` half of the receipt
  surface (defer `issue_*`).
- **`axeyum.knowledge`** — typed read-only accessors over facts, the frontier,
  operations, the overlay, the nursery (partition-aware, held-out-safe),
  claims, `foundational-concepts.json`, the pinned math-education graph, and a
  shape-classified index of `artifacts/autogenesis/`. Every accessor should
  mirror its canonical validator's semantics rather than re-derive them, and
  every "nothing found" answer should be distinguishable from "not looked at",
  which is this repository's most-repeated failure mode.
