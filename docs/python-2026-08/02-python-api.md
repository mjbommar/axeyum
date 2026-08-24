# 02 — The Python API: a typed projection of the Rust engines and the knowledge artifacts

Status: plan, 2026-08-24. Depends on plan 01. Measured basis: three read-only
API inventories taken 2026-08-24 and reproduced under
[`inventories/`](inventories/) — [`smt-solver`](inventories/smt-solver.md),
[`cas`](inventories/cas.md), [`kernel-kg`](inventories/kernel-kg.md). Every
`path:line` below is from those; re-verify before binding, since the crates
move daily.

## Principles that decide every row below

1. **Submodule = trust tier.** `R` read/pure, `P` propose (untrusted search),
   `C` check/replay. A `C` function's result must be falsifiable: expose the
   report *counts*, never collapse a verdict to `bool` alone.
2. **`None` / `unknown` / `declined` are values.** Across the CAS, `Option::None`
   means *overflow or outside the fragment*, never error; across the solver,
   `unknown` is a first-class result; across the producers, `DeclineReason` is
   a typed enum. None of these becomes a Python exception. Exceptions are for
   malformed input, budget misuse, and kernel rejection.
3. **Handles are epoch-checked.** `ExprId`/`NameId`/`LevelId` and IR
   `TermId`/`SymbolId` are only meaningful relative to the arena that interned
   them. Rust does not stop you mixing them; Python makes it easier. Every
   handle wrapper carries the owning object's epoch and every consuming call
   checks it. This is the binding's one non-negotiable invariant.
4. **Nothing found ≠ not looked at.** `axiom_footprint` on an absent name
   returns `[]`, identical to axiom-free; `theorem_dependency_inventory` makes
   the opposite choice and errors. The Python layer follows the second: an
   accessor asked about a subject it cannot find raises `KeyError`.
5. **Mirror the canonical validator, do not re-derive.** Every
   `axeyum.knowledge` accessor implements the semantics of the script that
   already validates that artifact (`validate-facts.py`,
   `validate-autogenesis-operations.py`, `validate-autogenesis-knowledge.py`,
   `check-autogenesis-holdout-isolation.py`), and is tested against it: same
   inputs, same verdicts.
6. **Budgets are explicit and pinned constants are read-only.** `MAX_BINDERS =
   8` is part of every settled bounded-induction fact's reproduction contract
   (the family checker refuses a mismatch even when every proof hash agrees);
   it is a module constant, never a keyword default.
7. **Read-only over shared resources.** The fact ledger, operation registry,
   nursery and the sibling `../math-education` are never written by Python.
   Writes go through the existing scripts, from JSON the Python side produced.

## Module map

| module | tier | wraps | slice |
|---|---|---|---|
| `axeyum.smt` | R + C | `solve_smtlib`, `_get_value`, `_get_assignment`; `Outcome.replay()` | 01-S3, 02-A |
| `axeyum.solver` | R + C | `SolverConfig` limits, `IncrementalBvSolver` push/pop/assume, proof/certificate export, DIMACS + `check_drat` | 02-A |
| `axeyum.ir` | R | `Sort`, term construction over a Python-owned arena, `Value`, evaluator | 02-A |
| `axeyum.cas` | R | `Expr`, `MvPoly`, `Monomial`, `MultiPoly`, `Rational`, `normalize`, `simplify*`, `evalf`, `differentiate`, `integrate`, `factor`, `equal`/`ZeroTest` | 02-B |
| `axeyum.cas.certify` | P + C | geometry, telescoping, SOS, GF(2), Gröbner cofactors — `produce()` / `Certificate.check()` pairs | 02-B |
| `axeyum.kernel` | R + C | `Kernel`, `Declaration`, `KernelError`, `build_*_prelude`, footprints/closures, `render_lean*`, NDJSON export, identity hashes | 02-C |
| `axeyum.producers` | P | `import_statement_ndjson`, `propose_bounded_induction`, `propose_modeq_family`, `audit_circularity`, the `verify_*` receipts | 02-D |
| `axeyum.knowledge` | R | facts, frontier, operations, overlay, nursery, claims, foundational concepts, `math-education`, autogenesis artifact index | 02-E |
| `axeyum.evidence` | R | canonical JSON, `sha256`, receipt/certificate `to_json` | all |

## 02-A — `axeyum.smt`, `axeyum.solver`, `axeyum.ir`

Facts that shape it ([`inventories/smt-solver.md`](inventories/smt-solver.md)
§0, §6): the whole SMT-LIB text front door is `#[cfg(feature = "full")]` and
`#[doc(hidden)]` at the crate root — **`axeyum-py` builds `axeyum-solver` with
`features = ["full"]`** (pure Rust; `z3` stays a separate opt-in wheel, never
the default `_native`); **no serde anywhere** in solver/IR/cnf/smtlib/query and
exactly one `to_json` (`RouteTrace`), so every result type gets a hand-rolled,
deterministic serializer in `convert.rs`; `SolverConfig` is `Send` but `!Sync`
(two `mpsc::Sender` progress fields — omit them in v1); `Solver<B>` and
`check_with_array_elimination<B>` are generic — monomorphize on
`SatBvBackend`; `parse_script` creates and **owns** its `TermArena`
(`Script.arena` is a public field), so `Script` is one pyclass and its
`TermId`s are valid only against it; `TermId` carries no arena identity and a
cross-arena use is a Rust panic — the binding adds an arena epoch to every
handle.

`axeyum.smt` (tiers P + C):
- `solve(script, *, timeout_ms, resource_limit, memory_limit_mb, node_budget,
  cnf_variable_budget, cnf_clause_budget, prove_unsat, ...) -> Outcome`
  over `solve_smtlib` (01-S3); `Outcome.status`, `.logic`,
  `.expected_status` (ground truth for cross-checking, never consulted —
  say so in the docstring), `.unknown_reason: (kind, detail)`; `.model` via
  `solve_smtlib_model` (the embedder route that does not require a literal
  `(get-model)`); `.replay() -> bool` over `check_model`.
- `session(script) -> list[Response]` over `solve_smtlib_session` — one
  typed response per output command; `Unsupported` and `Error` stay distinct
  variants. `incremental(script) -> list[CheckResult]`.
- `get_value`, `get_assignment`, `unsat_core` (deletion-minimized `:named`
  labels), `get_proof` (textual Alethe; `None` when no emitter covers it),
  `optimize` / `optimize_lexicographic` (**`config` is currently ignored by
  the Rust side — budgets do not apply; documented**).
- `parse(script, timeout_ms=None) -> Script` with `.commands` (16-variant
  tagged union), `.flat_view()` (binds `solvable_flat_view`, **not**
  `checked_flat_view` — the former returns `None` on a word-first-fallback
  parse whose empty assertion list would otherwise solve as a vacuous `sat`,
  a shipped P0), `write_script(arena, assertions)` (sharing-preserving).
  `SmtError::DeadlineExceeded` / `ResourceLimit` become an `unknown`-shaped
  outcome, never a parse exception.

`axeyum.solver` (tiers P + C):
- `Config`: the 18 plain `SolverConfig` fields as kwargs with defaults quoted;
  `BitLoweringMode` enum.
- `CheckResult` as a tagged value: `Sat(Model)` | `Unsat` |
  `Unknown(kind: UnknownKind, detail)`; `UnknownKind` is a `str` enum
  (`Timeout`, `ResourceLimit`, `MemoryLimit`, `NodeBudget`, `EncodingBudget`,
  `Incomplete`, `Other`). **Never an exception.**
- `solve(arena, assertions, config)`, `check_auto_explained(...) ->
  (CheckResult, RouteTrace)` (verdict-invariant; `RouteTrace.to_json()` is
  the one native JSON — but see the `explain_corpus` gotcha: a flat-view
  verdict is not what the front door answers for a script), `unsat_core`
  (indices), `solve_with_strategy`, `solve_with_portfolio`,
  `recommended_portfolio`.
- `Incremental` over `IncrementalBvSolver`: `assert_`, `push`, `pop` (returns
  `False` at the base frame), `check`, `check_assuming`, the `stats()`
  family, `enable_replay_checked_sat_cache`; bound to one `Arena` and
  asserts it on every call.
- `produce_evidence(arena, assertions, config) -> EvidenceReport` — the
  primary "give me a checkable answer" API; **`Evidence.check_outcome()`
  is what is bound, three-valued `Verified | NothingToCheck(reason) |
  Failed`; the `bool`-returning `check()` is not exposed** because it
  collapses `NothingToCheck` into a pass. `prove(hyps, goal)`.
- `capabilities()`, `support_matrix()`, `trust_ledger()` as read-only data.
- Proofs (`axeyum.solver.proofs`): `UnsatProof{dimacs, drat, lrat}` (three
  strings — no JSON design needed); `recheck() -> bool`, `recheck_lrat() ->
  bool | None` (**`None` = no LRAT present, never coerced**);
  `export_qf_bv_unsat_proof[_within]` and the `abv`/`aufbv`/`uf`/`lia`/
  `datatype` twins returning `Proved | Satisfiable | Inconclusive`
  (`Inconclusive` = budget, not a pass); `CheckBudget<'a>` is **not** bound.
  `axeyum.cnf`: `parse_dimacs`, `CnfFormula.to_dimacs/evaluate`,
  `check_drat` (`DratCheckOutcome::ResourceOut` is neither `True` nor
  `False`), `solve_with_drat_proof[_within|_with_limits]`, the
  `DEFAULT_*` budget constants, `CnfEncoding.aig_node_values_from_assignment`.

`axeyum.ir` (tier R + C):
- `Arena` wrapping `TermArena` (144 methods, all `&mut self` builders):
  symbols/functions/sorts/datatypes, constants, the full Boolean/BV/Int/Real/
  array/sequence/quantifier constructor set by SMT-LIB name, `rebuild_with_args`,
  `render(term)`; `Term`/`Symbol`/`Func` handles carry the arena epoch.
- `Sort`, `ArraySortKey`, `Value` (the hardest conversion — `WideBv`,
  `Rational`, `RealAlgebraic`, `ArrayValue`, `GenericArrayValue`, `FuncValue`,
  `Datatype`, `Uninterpreted`, `Seq` each get a typed Python class; **no
  variant collapses to `repr`**), `Op` (82 variants, `str` enum), `TermNode`
  for walkers, `Assignment`, `eval(arena, term, assignment)` (the trusted
  evaluator), `well_founded_default`, `TermStats`, `bits.*` (LSB-first).
- `bv` preflight: `first_unsupported_op` / `first_unsupported_sort` are bound
  and **called by the binding before any lowering**, because the lowerer
  `unreachable!()`s on Int/Real/Array/datatype sorts and that path is
  reachable from Python. `Aig.to_aiger_ascii`. `fp.*` (60 builders,
  `FloatFormat` consts incl. the ML precisions). `query.Query`/`QueryPlan`
  with `replay_original` (mandatory before accepting a `sat` from a sliced
  plan) and `StructuralCacheKey.hex()` as a safe cache key; `QueryBuilder<'a>`
  is not a pyclass (accumulate triples, build in one Rust call).
- Degenerate operators are **total with SMT-LIB semantics**
  (`bvudiv x 0` = all-ones; int `div`/`mod` by zero; `str.at` out of range)
  — stated in every relevant docstring; a user expecting
  `ZeroDivisionError` would misread a correct answer.
- Tests: differential against `smtcomp_cli` over ≥ 20 corpus files spanning
  QF_BV, QF_LIA, QF_LRA, strings (nonzero comparison count asserted); every
  underspecified operator exercised through `ir` **with the degenerate
  argument** (the fuzz-seed-class hard rule applies to the binding's tests);
  a `Term` from arena A used in arena B raises `EpochError` rather than
  panicking; `Evidence.check_outcome()` returns `NothingToCheck` on a
  fixture where `check()` would have said `True`; `recheck_lrat()` returns
  `None` on a DRAT-only proof; `write_script` round-trips through `parse`
  with identical `flat_view` renders.

## 02-B — `axeyum.cas` and `axeyum.cas.certify`

Facts that shape it (inventory §0): **no text parser for `CasExpr`** — Python
builds expressions by constructors and operators; **no serde** on any
certificate except GF(2) — geometry/telescoping/SOS have hand-rolled
deterministic JSON (`*_json::to_json/from_json`), everything else is
`Debug`-only; every public type is plain owned data, so `Send + Sync` is free;
`Rational` is not re-exported from the crate (bind it from `axeyum-ir`) and
`CasExpr::rat(n, 0)` panics (wrap in `checked_new`, raise `ValueError`).

`axeyum.cas` (tier R):
- `Expr`: `int`, `rat`, `var`, `zero`, `one`, `pow`, the 27 unary builders
  (`ln … ceiling`), `imaginary_unit`, `__add__/__sub__/__mul__/__neg__/
  __truediv__/__pow__`, `differentiate`, `differentiate_n`, `substitute`,
  `eval(env: dict[str, Fraction]) -> Fraction | None`, `__str__` (not
  round-trippable; documented).
- `MvPoly`, `Monomial`, `MultiPoly`, `normalize`, `MvPoly.from_expr/to_expr`;
  `terms()` and `powers()` collected to owned lists at the boundary.
- `simplify`, `trigsimp`, `simplify_under_assumptions(expr, Assumptions)`,
  `simplify_radicals`, `evaluate_trig`, `expand`, `collect`, `cancel`,
  `apart`, `factor`, `evalf(expr, dict[str, float]) -> float | None`,
  `rationalize`, `nsimplify`, `limit`, `series`, `solve`, the
  `dsolve_*` family, sums/products, linear algebra (`Matrix` and friends) —
  bound mechanically as pure functions returning `Expr | None`.
- `equal(a, b) -> ZeroTest` and `ZeroTest` as a tier-C value: `Certified(equal,
  witness: MultiPoly)` | `Unknown`; `certainty()`. `integrate(expr, var) ->
  CertifiedIntegral | None` with `.certificate` a first-class `ZeroTest`.
- Skip: `RatFunc` (no public surface), unbudgeted `groebner::{reduce,
  groebner_basis, ideal_contains}` (prefer `groebner_cert`).

`axeyum.cas.certify` (tiers P and C), one submodule per route, each exporting
`produce(...) -> Outcome` and `Certificate.check(options) -> Verdict`:
- `groebner`: `reduce_with_cofactors(gens, target, Limits) -> CofactorOutcome`;
  `Limits.fast()` defaults quoted; `CofactorOutcome.check(gens, target) ->
  bool` implemented in Rust from `MvPoly` primitives (the crate has no
  standalone checker fn — the check is `Σ cofactor·gen + remainder == target`);
  `DeclineReason.is_ceiling()` distinguishes budget from overflow.
- `geometry`: the `Pt`/`det`/`collinear`/… DSL, `GeometryProblem`,
  `certify_any_route(problem, geometry_limits()) -> ProofOutcome`
  (three-way: `Certified | NotInSaturatedIdeal | Declined(GeometryDecline)`;
  `RefutedByOwnWitness` means the statement is false and must surface
  distinctly); `GeometryCertificate.check(CheckOptions) -> GeometryVerdict`
  with the five `GeometryReport` counts; `to_json/from_json`;
  `corpus()`/`frontier()` as fixtures.
- `telescoping`: `HyperTerm`/`LinearForm`/`factorial_factor`/
  `binomial_factors`, `zeilberger(term, shift, sum, Limits) ->
  TelescopingOutcome`, `TelescopingCertificate.check(CheckOptions) ->
  Verdict` with the four `CheckReport` counts, `check_closed_form*`,
  `CertificateDocument` JSON.
- `sos`: checker-first (no search producer in the crate): `SosArtifact`,
  `check(artifact) -> CheckReport`; **the wrapper asserts
  `not report.is_empty()`**, because the crate documents that an empty
  obligation list is indistinguishable from a checker that did nothing.
- `gf2`: `certify_irreducible(poly, Gf2Limits) -> Certificate | None`
  (`None` = reducible, decided) raising `Gf2Error` on budget/shape; **both**
  checkers exposed (`check_irreducible_certificate` and the independent dense
  one) and the convenience `check_both()` requires both; `HalfDegreeArtifact`
  canonical JSON (the one serde route); shard directory checks behind an
  explicit opt-in since they touch the filesystem.
- `sturm` / `interval`: pure fns; `interval.Interval.div` returning `None`
  when the divisor straddles zero is the soundness guard, documented as such.
  `sets.Interval` name-collides — expose as `cas.RealInterval`.
- Tests: for every route, the crate's own `tests/*_certificate_artifacts.rs`
  fixtures round-trip through Python `to_json/from_json` byte-identically; one
  tampered certificate per route is **rejected** (the checker must be shown
  to fail); `evalf` cross-checked against `fractions`/`math` on 50 random
  expressions; the CAS-tour example's outputs reproduced from Python.

## 02-C — `axeyum.kernel`

Facts (inventory §1.1–1.4): `Kernel` derives `Clone` and is `Send + Sync`
(no `unsendable`); constructors take `&mut self` (intern), queries `&self` —
`PyRefMut`/`PyRef` give Python a real reader/writer split; there is **no
function returning a prelude kernel**, only `build_*_prelude(&mut Kernel) ->
Package`, with the `OnceLock` template cache applied *inside* the builders
when the kernel is pristine; `Kernel::default()` is the pristine state.

- `Kernel()`; `Kernel.fork()` (clone — the snapshot primitive);
  `build_logic/nat/int/rat/arith/creal/complex/cpoint/string_prelude()`
  returning a package object of `NameId`s; `prelude_cache.stats()` and
  `enabled()` so a test can prove the cache ran.
- Names: `anon`, `name_str`, `name_num`, `lean_name(id) -> str` (owned;
  prefer over the borrowing `display_name`), `name("Nat.add_comm")` promoted
  from `examples/autogenesis_support::intern_dotted`.
- Levels and expressions: every constructor in `lib.rs:671–1119`; `lam`/`pi`
  take a `BinderInfo` enum; `expr_node(id)` returns an **owned** Python enum
  copy of `ExprNode` for destructuring; de Bruijn helpers
  (`instantiate`, `abstract_fvars`, `close_scoped_fvars`, `lift_loose_bvars`,
  `has_loose_bvars`, …) — needed by any producer written in Python.
- Checking: `infer`, `def_eq`, `whnf`, `add_declaration(Declaration)` raising
  `KernelError(variant: str, fields: dict)` — one class, 26+ variants carried
  as data, because a producer branches on the variant; `add_inductive`,
  `add_quotient_package`.
- `Declaration` as a class with per-variant constructors and the four
  accessors; `declarations()` returns an owned snapshot list; the trusted
  surface is **`Axiom | Opaque | Quotient`**, and `is_axiom_free(name)` is
  defined only via `axiom_footprint`, never a variant test.
- `axiom_footprint(name)`, `declaration_dependency_closure(name)`,
  `theorem_dependencies(name)`, `declarations_reached(roots)` — each raises
  `KeyError` when `name` is absent (principle 4).
- Rendering/export: `render_lean`, `render_lean_decl`, `render_lean_module*`,
  `render_lean_prelude_module`, `render_lean4export_ndjson_roots(metadata,
  roots)` with `Lean4ExportMetadata.axeyum(lean_version)`;
  `release_transient_tables_for_export()` documented as one-way or omitted.
- `kernel.identity`: `canonical_declaration_sha256`,
  `canonical_expression_sha256`, `canonical_alpha_expression_sha256`,
  `canonical_kernel_type_shape_sha256`, `canonical_level_sha256` — the
  content-addressing primitives every artifact's `*_sha256` comes from.
- Hazards carried verbatim: `axreal` (30 declared axioms, none reached) vs
  `creal` (0); never classify a carrier by substring.
- Tests: `Kernel().build_nat_prelude(); k.declarations()` count equals
  `nat_theorem_inventory`'s TSV row count (binary in
  `target/release/examples/`, no cargo lock); `axiom_footprint` empty for every
  nat/int/creal theorem and 30 for `axreal`, matching
  `theorem_axiom_footprint`; a handle from kernel A passed to kernel B raises
  `EpochError`; a duplicate `add_declaration` raises `KernelError` with
  `variant == "DeclarationExists"`; cache `stats().hits` increases on the
  second `build_nat_prelude()` in one process.

## 02-D — `axeyum.producers`

Prerequisite refactor (inventory §1.7): move
`examples/bounded_induction_support/mod.rs` (3,759 lines) and
`examples/modeq_family_support/mod.rs` (605) to
`axeyum-lean-import/src/producers/{bounded_induction,modeq_family}.rs`. Cost
is zero new dependencies (both import only `std` and `axeyum_lean_kernel`
items the crate already depends on); the drivers switch from `#[path]` to
`use`. Own commit: it moves ~4,400 lines under `--lib` tests and clippy.

- `ImportLimits(max_line_bytes, max_records)`;
  `import_statement_ndjson(path | bytes, limits, target) ->
  StatementImport` exposing `kernel()`, `goal()`, `target_name()`,
  `report()` (non-consuming accessors; skip `into_parts`).
- `propose_bounded_induction(kernel, goal) -> Candidate` raising
  `Declined(reason: DeclineReason)`; `Candidate{proof, binders_used,
  inductions_used}`; `MAX_BINDERS` read-only; same for
  `propose_modeq_family` plus `audit_circularity(kernel, candidate, target)`.
- Receipts: the `verify_*` half of `theorem_specialization`,
  `theorem_composition`, `checked_theorem_receipt`, … bound on demand;
  `issue_*` stays Rust-side until receipt shapes freeze (a certificate must
  carry every distinction its producer makes, and Python constructing one
  inherits that obligation).
- Tests: the seven frozen `natural-factorial` goals reproduce the documented
  reach exactly (accepts `descFactorial n 1 = n`, … ; declines `descFactorial
  n n = n!` with `TerminalNotDefEqNoRewrite`); every candidate's
  `axiom_footprint` empty; `proof_sha256` equals the committed
  `*-result-v1.json` value for each settled family fact.

## 02-E — `axeyum.knowledge`

Read-only, typed, validator-mirroring accessors over (inventory Part 2):

- `facts`: `Fact` dataclass from `fact.schema.json` (9 required keys; the
  two status axes `epistemic_status` / `external_status`); `facts.load()`,
  `facts.get(id)`, `facts.by_status()`, `facts.novel()` (established here,
  unknown to the literature — the validator prints these); semantic rules
  mirrored as `Fact.validate()` with the same verdicts as
  `validate-facts.py` (tested by running both over the ledger).
- `frontier`: wraps `fact-frontier.py --json` output — `entries` (196 rows),
  `selection` (`outcome`, `admissible_fact_ids`, `rationale`),
  `capabilities.decidable_fragments`, `frontier_sha256`; `--verify` exposed
  as `frontier.verify(sha)`. **`refused-no-admissible-candidate` is a value.**
- `operations`: 26 rows; `Operation.n_targets` and `is_multi_target` derived
  from `applicability.fact_ids` only; `EXECUTION_DRIVERS` (9) exposed as a
  frozen set.
- `overlay`: entities, links, relation types; `assurance` carried on every
  link; `query(relation, endpoint)`; external endpoints carry
  `source_revision`.
- `nursery`: `entries` (216: train 78, development 79, held-out 57,
  longitudinal 2; 13 families); `partition_of(fact_id)`, `family_of`,
  `held_out_ids()`, `is_safe_to_reference(fact_id)`; **every accessor answers
  by `partition`, never by count** (dependency-ready and train+development
  are both 138 and differ). Amendment ledger exposed read-only.
- `claims`: `artifacts/claims/<family>/<id>/claim.json` (104; `formal` is a
  generator recipe, not a proposition); `concept_refs` already point into
  `math-education`.
- `concepts`: `foundational-concepts.json` (137 rows, generated).
- `math_education`: `Concept`/`Technique` from YAML front matter (1,567 /
  42; encounters are inline per concept); `pin_ok()` compares `git rev-parse
  HEAD` in the sibling to the overlay pin and **degrades to
  `unavailable`**, never errors, mirroring the validator.
- `autogenesis`: an index of the 958 artifact JSONs classified by shape
  (`plan`/`result`/`decline`/`admission`/…), since `kind` has 707 distinct
  values; pairs plans with results.
- `generated`: the 26 `docs/plan/generated/*.md` with their generator
  scripts, for the agent's dashboards.
- Tests: for each accessor, the corresponding validator is run in a
  subprocess and its verdicts compared; `held_out_ids()` count equals the
  gate's; a fixture referencing a held-out id fails `is_safe_to_reference`.

## Slices and gates

Each slice: one PR-sized commit, `just py-check` green with the counts
printed, docs for the submodule in `docs/user-guide/python.md`, stubs
regenerated. Order: 02-A → 02-C → 02-E → 02-B → 02-D (the agent needs
solver, kernel and knowledge first; CAS certify routes and producers are
larger and can land in parallel lanes on disjoint files).

Exit criteria for the plan:

- Every row in the three inventories marked tier R is bound or has a
  recorded reason in the inventory for deferral.
- The five kernel example binaries and `fact-frontier.py --json` are each
  reproduced by ≤ 40 lines of Python with byte-equal output on the committed
  inputs (measured, in tests).
- All differential tests (solver vs `smtcomp_cli`, kernel vs inventories,
  knowledge vs validators, certificates vs fixtures) run with nonzero counts.
- `python -c "import axeyum; help(axeyum)"` lists every submodule with its
  tier in the first docstring line.
