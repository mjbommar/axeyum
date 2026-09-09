# cvc5 — technique inventory

**Subject.** `references/cvc5` at commit `1689f13331f7543801f82d9dcbcaac2f70a26781`
(2026-09-03, shallow clone, `scripts/fetch-references.sh`). Every `path:line`
below is relative to `references/cvc5/`.

**What this is.** A flat, checkable list of the decision procedures,
preprocessing passes, rewriting machinery, and search techniques cvc5 *ships*,
organised by layer and by SMT-LIB logic. It is one complete side of a
comparison; it deliberately contains **no comparison to axeyum** and **no
ranking by importance** — a sibling synthesis lane does the diff, and ranking
here would only encode this lane's guesses about our gaps.

**Why it exists.** Measured 2026-09-07: 91% of our remaining benchmark gap does
not respond to more time (at 2.5x budget we recover 12 of 135 missing files).
What is left is not slowness, it is procedures we do not have. Instrumentation
cannot find those — a trace shows where our budget went, never that a
competitor implements something we never wrote. So this is an inventory
question, and this document asks it flatly.

**Provenance key.** Every entry carries one:

| tag | means |
| --- | --- |
| `[C]` | read in the C++ source at the cited line |
| `[P]` | from a cvc5 paper / system description, **and** confirmed present in code |
| `[I]` | inference from surrounding code; not directly asserted anywhere |

**Status key.** `on by default` / `option --flag (default X)` / `expert-only`
(the option's `category = "expert"`, i.e. hidden from `--help`) / `undocumented`
/ `dead or unreachable` / `requires optional dep X`.

**Honesty rule applied throughout.** "Did not verify" is a complete answer and
appears as itself. Nothing here is inferred from a paper against the code: cvc5
ships several things its own papers describe, default-off — those entries are
the point of the exercise, not an embarrassment to be smoothed over.

---

## Contents

| § | subject | where it lives in cvc5 |
| --- | --- | --- |
| [0](#0-how-to-read-the-status-column--the-two-authorities) | how to read the status column; optional build deps | `src/options/*.toml`, `src/smt/set_defaults.cpp`, `CMakeLists.txt` |
| [1](#1-solver-core-theory-engine-and-combination) | solver core, theory engine, combination | `src/smt/`, `src/theory/` |
| [2](#2-rewriting) | the four rewriting mechanisms; the RARE DSL | `src/theory/rewriter.cpp`, `src/rewriter/`, `src/theory/*/rewrites*` |
| [3](#3-proofs-unsat-cores-and-other-evidence) | proofs, cores, model cores, output formats | `src/proof/`, `src/smt/proof_*` |
| [4](#4-parallelism-partitioning-and-external-cooperation) | partitioning, oracles, subsolvers, plugins | `src/theory/partition_generator.cpp` |
| [5](#5-preprocessing) | the 37 passes, their order, the per-logic overrides | `src/preprocessing/passes/`, `src/smt/process_assertions.cpp` |
| [6](#6-bit-vectors-and-floating-point) | BV solvers, abstraction CEGAR, circuits, rewriter, FP | `src/theory/bv/`, `src/theory/fp/` |
| [7](#7-the-propositional-layer-sat-back-ends-and-decision-heuristics) | CNF, CDCL(T) glue, SAT back ends, decision heuristics | `src/prop/`, `src/decision/` |
| [8](#8-arithmetic--linear-nonlinear-and-finite-fields) | simplex family, dio, approx/GLPK, nl-ext, CAC, ICP, finite fields | `src/theory/arith/`, `src/theory/ff/` |
| [9](#9-strings-sequences-sets-relations-bags-datatypes-arrays-uf-separation-logic) | strings/regex/sequences, sets+relations, bags, datatypes, arrays, UF, sep | `src/theory/{strings,sets,bags,datatypes,arrays,uf,sep}/` |
| [10](#10-quantifier-instantiation-and-model-finding) | **instantiation strategies, triggers, FMF, ieval, CEGQI** | `src/theory/quantifiers/` |
| [11](#11-synthesis-sygus-abduction-interpolation-and-rewrite-rule-synthesis) | SyGuS, abduction, interpolation, rewrite-rule mining | `src/theory/quantifiers/sygus/`, `src/smt/` |
| [12](#12-what-this-inventory-did-not-verify) | what was not verified | — |

**920 entries.** Counts that recur below and are worth having up front, all
measured on this commit:

| quantity | value | how measured |
| --- | --- | --- |
| declared options | **528** (332 `expert`, 135 `regular`, 58 `common`, 3 `undocumented`) | parse of `src/options/*.toml` |
| quantifier options alone | **179** (111 `expert`) | `src/options/quantifiers_options.toml` |
| RARE (DSL) rewrite rules | **439** across 13 files | `grep -cE '^\(define-(rule\|rule\*\|cond-rule) '` |
| `ProofRule` members (inference rules) | **172** | `include/cvc5/cvc5_proof_rule.h:89-2743` |
| `ProofRewriteRule` members | **534** | `include/cvc5/cvc5_proof_rule.h:2760-5087` |
| trust escapes in `ProofRule` | **2** (`TRUST`, `TRUST_THEORY_REWRITE`) | same |
| registered preprocessing passes | **37** | `src/preprocessing/passes/*.h` |
| named string rewrite ids | **202** | `src/theory/strings/rewrites.h:28-236` |
| `STRINGS_*` inference ids | **87** | `src/theory/inference_id.h:633-946` |

---

## 0. How to read the status column — the two authorities

A cvc5 technique's real default is the **conjunction of two files**, and reading
only one of them gets the answer wrong in both directions:

1. **`src/options/*.toml`** — the declared default and the visibility category.
   25 files, **528 options total**, of which **332 are `category = "expert"`**
   (hidden from `--help`), 3 `undocumented`, the rest `regular`/`common`.
   `src/options/quantifiers_options.toml` alone declares **179 options, 111 of
   them expert** — a third of cvc5's entire option surface is quantifier
   heuristics. `[C]`
2. **`src/smt/set_defaults.cpp`** (1930 lines) — runs *after* parsing, and
   rewrites those defaults per logic, per requested output (models / proofs /
   unsat cores / incremental), and per other option. `SET_AND_NOTIFY_IF_NOT_USER`
   means "override unless the user said otherwise". `[C]`

The consequence worth internalising: **an option whose toml default is `false`
may still be on for your logic, and an option whose toml default is `true` may
be force-disabled by the presence of a theory.** Both directions occur, and
several of the most interesting entries below are exactly that.

Option census per file (`long`, declared default, category) is reproduced inline
in each section rather than as one table, so an entry can be checked without
scrolling.

### Optional build dependencies — what is *not* in a default build

`CMakeLists.txt:129-137` `[C]`. A stock `./configure.sh && make` gets **none of
the `USE_*` options except LibPoly**, which `configure.sh:75` documents as
`[default=yes]`.

- **`USE_GLPK`** — `CMakeLists.txt:133`. Gates the approximate/branch-and-cut
  simplex path (`theory/arith/linear/approx_simplex.cpp`). Off unless
  `--glpk`. GPL, so also gated behind `--gpl`.
- **`USE_COCOA`** — `CMakeLists.txt:130`. Gates the finite-field Gröbner-basis
  solver (`theory/ff/`). Off by default.
- **`USE_POLY`** (LibPoly) — `CMakeLists.txt:136`, `configure.sh:75`
  `[default=yes]`. Gates the nonlinear CAD/coverings solver
  (`theory/arith/nl/coverings/`) and ICP.
- **`USE_CRYPTOMINISAT`** / **`USE_KISSAT`** — `CMakeLists.txt:131,134`.
  Alternative SAT back ends; off by default.
- **`USE_CLN`**, **`USE_MPFR`**, **`USE_EDITLINE`** — `CMakeLists.txt:129,135,132`.
- **`USE_NORMALIZ`** — `CMakeLists.txt:137`, help text *"Use Normaliz for
  liastar solver extension"*. **Present in the build system and reported by
  `--show-config` (`src/options/options_handler.cpp:380`), but `grep -rn
  'liastar\|Normaliz'` over `src/` finds no consumer at this commit and no
  `*_STAR` kind outside `SEP_STAR` (`theory/sep/kinds.toml:39`).** So: a wired,
  advertised, **unused** dependency — a LIA-with-star extension that is
  configured for but not present in this snapshot. `[C]`
- **`--best`** (`configure.sh:224-230`) turns on `cln`, `cryptominisat`,
  `editline`, `glpk`, `ipo`. So the configuration cvc5's own build script calls
  "known to give best performance" is **not** the configuration a default build
  or a distro package produces. `[C]`

---

## 1. Solver core, theory engine, and combination

- **`SolverEngine`** — `src/smt/solver_engine.cpp` — logics: all — status: on by
  default — the API-facing engine: assertion stack, push/pop, and the
  produce-* toggles that `set_defaults` reads. — `[C]`
- **`SmtDriver`** — `src/smt/smt_driver.cpp` — all — on by default — the
  check-sat loop: preprocess, hand to `SmtSolver`, and on `unknown` decide
  whether to re-run with a changed configuration. — `[C]`
- **`SmtDriverDeepRestarts`** — `src/smt/smt_driver_deep_restarts.cpp` — all —
  `--deep-restart=MODE` (default `NONE`, **expert**, `smt_options.toml:509`);
  `--deep-restart-factor=F` default `3.0` (`:533`) — restarts the *whole solve*
  from scratch after learning zero-level literals, re-preprocessing the input
  with those literals as substitutions. **Default off.** — `[C]`
- **`TheoryEngine`** — `src/theory/theory_engine.cpp` (2381 lines) — all — on by
  default — owns per-theory solvers, the propagation/lemma channel, the
  care-graph combination round, and model construction. — `[C]`
- **Theory combination via care graphs** — `src/theory/combination_care_graph.cpp` —
  any multi-theory logic — `--tc-mode=MODE` default `CARE_GRAPH`, **expert**
  (`theory_options.toml`, `tcMode`) — **`CARE_GRAPH` is the only mode the enum
  defines**: the option exists but has exactly one value, so it is a hook, not a
  choice. — `[C]`
- **Distributed equality engines** — `src/theory/ee_manager_distributed.cpp` —
  all — `--ee-mode=MODE` default `DISTRIBUTED`, `regular` (`theory_options.toml`,
  `eeMode`) — each theory keeps its own congruence closure; sharing goes through
  `SharedTermsDatabase` and the care graph. — `[C]`
- **Central equality engine** — `src/theory/ee_manager_central.cpp` — all —
  `--ee-mode=central`, **default off** — one congruence closure shared by all
  applicable theories, removing most care-graph traffic. Shipped, not default. — `[C]`
- **`SharedTermsDatabase` / `SharedSolver`** — `src/theory/shared_terms_database.cpp`,
  `shared_solver_distributed.cpp` — multi-theory — on by default — tracks terms
  shared across theories and the equalities they must agree on. — `[C]`
- **Care graph / `CarePairArgumentCallback`** — `src/theory/care_graph.h`,
  `care_pair_argument_callback.cpp` — multi-theory — on by default — the
  standard Nelson–Oppen split-on-shared-equality mechanism, driven by each
  theory's `computeCareGraph`. — `[C]` `[P]`
- **`ExtTheory` — context-dependent simplification** — `src/theory/ext_theory.cpp`
  (header cites Reynolds et al., *Designing Theory Solvers with Extensions*,
  FroCoS 2017) — strings, arith-nl, sets, bags — on by default where a theory
  registers extended functions — combines SAT-context equality reasoning with
  context-*in*dependent rewriting: substitute known equalities into an extended
  term, rewrite, and emit the resulting implication as a T-valid lemma. — `[C]` `[P]`
- **`RelevanceManager`** — `src/theory/relevance_manager.cpp` — all —
  `--relevance-filter` default `false`, **expert** (`theory_options.toml`,
  `relevanceFilter`); also driven on when difficulty or `--produce-difficulty`
  is requested — computes which asserted literals are actually relevant to the
  input formula under the current assignment. — `[C]`
- **`DifficultyManager`** — `src/theory/difficulty_manager.cpp` — all —
  `--produce-difficulty` default `false` (`smt_options.toml:218`),
  `--difficulty-mode=MODE` default `LEMMA_LITERAL_ALL`, **expert** (`:226`) —
  attributes solving effort back to input assertions; feeds
  `src/smt/difficulty_post_processor.cpp`. — `[C]`
- **`ConflictProcessor`** — `src/theory/conflict_processor.cpp` —
  `--conflict-process=MODE` default `NONE`, **expert** (`theory_options.toml`,
  `conflictProcessMode`; modes `none` / `min` / `min-ext`) — post-processes
  theory conflicts to minimise them, optionally using the extended rewriter.
  **Shipped, default off.** — `[C]`
- **`DecisionManager` / `DecisionStrategy`** — `src/theory/decision_manager.cpp`,
  `decision_strategy.cpp` — all — on by default — lets theory solvers register
  ordered decision strategies (used by UF cardinality, strings length, FMF,
  datatypes splitting) that the SAT solver consults before its own heuristic. — `[C]`
- **`TheoryModelBuilder`** — `src/theory/theory_model_builder.cpp` — all with
  `--produce-models` — on when models requested — builds a model by assigning
  representatives per type, normalising, and asking each theory to complete it;
  `--assign-function-values` default `true` (**expert**),
  `--condense-function-values` default `true` (`common`),
  `--default-function-value-mode=MODE` default `FIRST` (`common`) control the UF
  part. — `[C]`
- **`Evaluator`** — `src/theory/evaluator.cpp` — all — on by default — fast
  constant-leaf evaluation that bypasses the rewriter; used by model checking,
  SyGuS enumeration, and instantiation evaluation. — `[C]`
- **`TypeEnumerator`** — `src/theory/type_enumerator.h` + per-theory
  `type_enumerator.*` (arrays, bags, builtin, bv, datatypes, ff, fp, sets,
  strings, uf) — all — on by default — deterministic enumeration of the values
  of a type; the substrate for FMF, model completion, and SyGuS. — `[C]`
- **`SortInference`** — `src/theory/sort_inference.cpp` +
  `src/preprocessing/passes/sort_infer.cpp` — UF-heavy logics —
  `--sort-inference` default `false`, **expert** (`smt_options.toml:343`) —
  infers a finer monotone sort assignment than the input declares, shrinking
  the model-search space. **Default off.** — `[C]` `[P]`
- **`TheoryEngineModule` / plugin interface** — `src/theory/theory_engine_module.cpp`,
  `plugin_module.cpp` — all — `--plugin-notify-sat-clause-in-solve` default
  `true` (**expert**, `base_options.toml:369`), `--plugin-share-skolems` default
  `true` (`:377`) — a public extension point that lets an external component see
  SAT clauses and contribute lemmas. Only active if the API user registers a
  plugin. — `[C]`
- **`SubstitutionMinimize`** — `src/theory/subs_minimize.cpp` — all — used by
  the conflict processor and instantiation — finds a minimal sub-substitution
  that still entails a literal. — `[C]`
- **`safe-mode`** — `--safe-mode=MODE` default `UNRESTRICTED`, **expert**
  (`base_options.toml:351`) — restricts the solver to configurations with
  stronger correctness expectations. Default is the *unrestricted* one. — `[C]`
- **Resource limiting** — `--tlimit`, `--tlimit-per`, `--rlimit`, `--rlimit-per`
  all default `0` (= unlimited), plus `--rweight=VAL=N` (**expert**,
  `base_options.toml:338`) to reweight individual resource-spending events. — `[C]`

## 2. Rewriting

cvc5 has **four** distinct rewriting mechanisms, and they are not
interchangeable. Confusing them is the easiest mistake to make about this
codebase.

- **The `Rewriter` fixed-point loop** — `src/theory/rewriter.cpp:109`
  (`Rewriter::rewrite`) — all — on by default, unconditional — a
  pre-rewrite/rewrite-children/post-rewrite stack machine
  (`RewriteStackElement::{PRE_REWRITE, REWRITE_CHILDREN, POST_REWRITE,
  WAIT_FOR_FULL_REWRITE, FINALIZE}`, `rewriter.cpp:48-58`) dispatching to the
  owning theory by `theoryOf(node)` (`:34`, which routes `EQUAL` to the theory
  of the *domain type*). Every theory supplies a `TheoryRewriter` with
  `preRewrite`/`postRewrite`. — `[C]`
- **Per-theory C++ `TheoryRewriter`s** — `src/theory/*/theory_*_rewriter.cpp`
  (13 of them) — per theory — on by default — the hand-written normalisation:
  this is where the bulk of cvc5's simplification actually lives, not in the
  DSL. — `[C]`
- **RARE — the declarative rewrite-rule DSL** — `src/rewriter/mkrewrites.py`,
  `rw_parser.py`, `rule.py`, `node.py`; rules in `src/theory/*/rewrites*`;
  generated into `src/rewriter/rewrites_template.cpp` and
  `theory_rewrites_template.cpp` — all — on by default (compiled in) — an
  s-expression DSL with three forms: `define-rule` (unconditional),
  `define-cond-rule` (guarded), `define-rule*` ("deep"/fixed-point). Each rule
  becomes a `ProofRewriteRule` enum member, so a DSL rewrite is a *checkable
  proof step*, not just a code path. — `[C]` `[P]`

  **Measured rule census** (`grep -cE '^\(define-(rule|rule\*|cond-rule) '`):
  **439 rules total** across 13 files.

  | file | plain | deep (`define-rule*`) | conditional | total |
  | --- | --- | --- | --- | --- |
  | `theory/strings/rewrites` | 53 | 10 | 96 | **159** |
  | `theory/bv/rewrites-simplification` | 30 | 0 | 39 | **69** |
  | `theory/booleans/rewrites` | 34 | 4 | 3 | **41** |
  | `theory/bv/rewrites` | 14 | 1 | 23 | **38** |
  | `theory/arith/rewrites` | 27 | 0 | 10 | **37** |
  | `theory/bv/rewrites-elimination` | 11 | 0 | 15 | **26** |
  | `theory/sets/rewrites` | 11 | 0 | 8 | **19** |
  | `theory/uf/rewrites` | 7 | 0 | 6 | **13** |
  | `theory/strings/rewrites-regexp-membership` | 7 | 2 | 2 | **11** |
  | `theory/arith/rewrites-transcendentals` | 8 | 0 | 0 | **8** |
  | `theory/builtin/rewrites` | 8 | 0 | 0 | **8** |
  | `theory/sets/rewrites-card` | 3 | 0 | 1 | **4** |
  | `theory/arrays/rewrites` | 3 | 1 | 2 | **6** |

  Two things this table says. First, **strings is 36% of the DSL** — the DSL
  earns its keep where the rewrite set is large, irregular, and hard to trust by
  inspection. Second, **arrays has 6 rules and BV has 133**: the DSL is not a
  uniform replacement for the C++ rewriters, it is a targeted one.

- **`Rewriter::rewriteViaRule(ProofRewriteRule id, n)`** —
  `src/theory/rewriter.cpp:185` — all — on by default — applies *one named*
  rewrite rule to a term. This is the entry point that makes a rewrite
  addressable by name from proof reconstruction. — `[C]`
- **The extended rewriter** — `src/theory/quantifiers/extended_rewrite.cpp`,
  entry `Rewriter::extendedRewrite(node, aggr)` at `src/theory/rewriter.cpp:120` —
  all — **`--ext-rew-prep=MODE` default `OFF`, expert (`smt_options.toml:285`;
  modes `off`/`use`/`agg`)** — a much stronger, non-fixed-point normaliser
  (ITE pull-up, symmetry, equality inference, arithmetic normalisation) used
  internally by SyGuS, conjecture generation and conflict minimisation.
  **It is NOT on as a preprocessing pass by default**, in either the plain or
  the aggressive variant. — `[C]`
- **`Rewriter::rewriteEqualityExt`** — `src/theory/rewriter.cpp:157` — per
  theory — on by default where implemented — theory-specific equality
  normalisation beyond the ordinary rewriter (BV solves equalities, strings
  strips endpoints). — `[C]`
- **`rewriteWithProof`** — `src/theory/rewriter.cpp:126` — all with proofs —
  on when proofs requested — produces a `TrustNode` carrying a
  `TConvProofGenerator` for the rewrite chain. — `[C]`
- **`basic_rewrite_rcons.cpp`** — `src/rewriter/basic_rewrite_rcons.cpp` —
  all with proofs — on when proofs requested — reconstructs a *proof* for a
  rewrite the C++ rewriter performed, by searching for a DSL rule or a
  hand-registered `ProofRewriteRule` that explains it. This is the bridge from
  "the rewriter did something" to "here is a checkable step". — `[C]`
- **`RewriteDb` / `RewriteDbProofCons`** — `src/rewriter/rewrite_db.cpp`,
  `rewrite_db_proof_cons.cpp` — all with proofs — `--proof-rewrite-rcons-rec-limit=N`
  default `5`, `--proof-rewrite-rcons-step-limit=N` default `1000`
  (`proof_options.toml:123,139`, both `regular`) — matches a goal equality
  against the 439-rule DSL database with a bounded recursive search. The two
  limits are the reason a proof can legitimately fall back to a trust step. — `[C]`
- **`Evaluator`-based constant folding** — `src/theory/evaluator.cpp` — all — on
  by default — see §1. — `[C]`
- **ACI normalisation** — `ProofRule::ACI_NORM`, `ABSORB` — all — on by default
  where applicable — associative/commutative/idempotent flattening as a single
  proof step rather than a rewrite chain. — `[C]`
- **Polynomial normalisation as a proof rule** — `ProofRule::ARITH_POLY_NORM`,
  `ARITH_POLY_NORM_REL`, `BV_POLY_NORM`, `BV_POLY_NORM_EQ`, `FF_POLY_NORM`,
  `FF_POLY_NORM_EQ`; implementation `src/theory/arith/arith_poly_norm.cpp` —
  arith, BV, FF — on by default — normalises both sides of an equality to a
  canonical polynomial and discharges it in one step, *including over
  bit-vectors and finite fields*, not just arithmetic. — `[C]`
- **`foreign_theory_rewrite`** — `src/preprocessing/passes/foreign_theory_rewrite.cpp` —
  strings+arith — `--foreign-theory-rewrite` default `false`, **expert**
  (`smt_options.toml:359`) — uses one theory's entailment to simplify another's
  terms (e.g. `str.len ≥ 0` to discharge an arithmetic literal). **Default off.** — `[C]`
- **`learned_rewrite`** — `src/preprocessing/passes/learned_rewrite.cpp` — all —
  `--learned-rewrite` default `false`, `regular` (`smt_options.toml:44`) —
  rewrites the input using literals learned at decision level 0. **Default off.** — `[C]`

## 3. Proofs, unsat cores, and other evidence

cvc5's proof layer is two enums, and the split matters:

- **`ProofRule`** — `include/cvc5/cvc5_proof_rule.h:89-2743` — **172 members**
  (measured). The *inference* rules: `ASSUME`, `SCOPE`, `SUBS`, `REFL`, `TRANS`,
  `CONG`/`NARY_CONG`/`HO_CONG`/`PAIRWISE_CONG`, `RESOLUTION`/`CHAIN_RESOLUTION`/
  `CHAIN_M_RESOLUTION`/`FACTORING`/`REORDERING`, the 22 `CNF_*` Tseitin rules,
  `INSTANTIATE`, `SKOLEMIZE`, `ALPHA_EQUIV`, `ARITH_TRICHOTOMY`, `ARITH_SUM_UB`,
  `INT_TIGHT_LB`/`INT_TIGHT_UB`, the 17 `ARITH_TRANS_*` transcendental
  approximation rules, `ARRAYS_READ_OVER_WRITE*`/`ARRAYS_EXT`,
  `BV_BITBLAST_STEP`/`BV_EAGER_ATOM`, the 10 `FF_*` finite-field rules,
  `CONCAT_*`/`STRING_*`/`RE_UNFOLD_*` string rules, `DT_SPLIT`, `SETS_*`,
  `DSL_REWRITE`, `EVALUATE`, `DRAT_REFUTATION`, `SAT_REFUTATION`,
  `SAT_EXTERNAL_PROVE`, `LFSC_RULE`, `ALETHE_RULE`. `[C]`
- **`ProofRewriteRule`** — `include/cvc5/cvc5_proof_rule.h:2760-5087` —
  **534 members** (measured). One per *rewrite*. Since the DSL has 439 rules,
  roughly **95 of these are hand-registered C++ rewrites promoted to named,
  checkable steps** — the `MACRO_*` family (47 members: `MACRO_QUANT_MINISCOPE`,
  `MACRO_BV_BITBLAST`, `MACRO_STR_STRIP_ENDPOINTS`, `MACRO_ARITH_STRING_PRED_ENTAIL`,
  …) plus theory-specific ones. `[C]`
- **Trust holes** — exactly **two** rules in the whole `ProofRule` enum are
  trust escapes: `TRUST` and `TRUST_THEORY_REWRITE`. `--proof-allow-trust`
  **defaults to `true`** (`proof_options.toml:258`, **expert**) — so a default
  proof *may* contain unjustified steps, and `--proof-allow-trust=false` is the
  switch that forbids them. `src/proof/trust_id.h` enumerates what each trust
  step stands for. `[C]`

Entries:

- **Proof production** — `src/smt/proof_manager.cpp` — all — `--produce-proofs`
  default `false` (`smt_options.toml:120`, `common`); `--proof-mode=MODE`
  default `OFF`, **expert** (`:128`; modes `off` / `pp-only` / `sat-proof` /
  `full-proof` / `full-proof-strict`) — **proofs are off by default**; even
  `--produce-proofs` does not by itself select `full-proof-strict`, which is the
  only mode that disables techniques known to yield incomplete proofs. — `[C]`
- **Proof granularity** — `--proof-granularity=MODE` default **`MACRO`**
  (`proof_options.toml:99`, `common`; modes `macro` / `rewrite` /
  `theory-rewrite` / `dsl-rewrite` / `dsl-rewrite-strict`) — at the default,
  macros are *not* expanded, i.e. the coarsest proof. `dsl-rewrite-strict` is
  what forces DSL steps in preference to trusted ones. — `[C]`
- **Proof checking** — `--check-proofs` default `false` (`smt_options.toml:155`),
  `--proof-check=MODE` default `NONE` (`proof_options.toml:62`; modes `eager` /
  `eager-simple` / `lazy` / `none`), `--check-proofs-complete` default `false`
  (**expert**, `:83`), `--check-proof-steps` default `false` (**expert**, `:203`).
  **All four default off.** — `[C]`
- **`ProofNodeManager`, `ProofNodeUpdater`, `ProofNodeConverter`** —
  `src/proof/proof_node_manager.cpp`, `proof_node_updater.cpp`,
  `proof_node_converter.cpp` — with proofs — the proof DAG and its rewriting
  infrastructure. — `[C]`
- **Proof generators (7 kinds)** — `src/proof/`: `EagerProofGenerator`,
  `BufferedProofGenerator`, `LazyProof` / `LazyProofChain`,
  `LazyTreeProofGenerator`, `TConvProofGenerator` (`conv_proof_generator.cpp`),
  `TConvSeqProofGenerator`, `AssumptionProofGenerator`, `TrustProofGenerator`,
  `RewriteProofGenerator`, `ValidWitnessProofGenerator` — with proofs — the
  menu of ways a theory can attach a justification to a lemma, ranging from
  "I have the proof now" to "ask me later". — `[C]`
- **`ProofEqualityEngine`** — `src/theory/uf/proof_equality_engine.cpp` — all —
  with proofs — proof-producing congruence closure: the equality engine emits
  `REFL`/`SYMM`/`TRANS`/`CONG` chains for every derived equality. — `[C]`
- **`proof_ensure_closed.cpp`** — `src/proof/proof_ensure_closed.cpp` — with
  proofs and assertions — debug check that a proof has no free assumptions. — `[C]`
- **`ProofLetify`** — `src/proof/proof_letify.cpp` — with proofs — DAG sharing in
  printed proofs; `--proof-dag-global` default `true` (**expert**,
  `proof_options.toml:37`). — `[C]`
- **`SubtypeElimProofConverter`** — `src/proof/subtype_elim_proof_converter.cpp` —
  arith — `--proof-elim-subtypes` default `true` (**expert**, `:45`) — removes
  Int/Real subtyping from a proof so the output calculus does not need it. — `[C]`
- **Output format: CPC / Eunoia (ALF)** — `src/proof/eo/eo_printer.cpp`,
  `eo_node_converter.cpp`, `eo_print_channel.cpp`,
  `eo_dependent_type_converter.cpp`, `eo_list_node_converter.cpp` —
  **`--proof-format-mode=MODE` default `CPC`** (`proof_options.toml:5`,
  **expert**) — the *default* proof output is the Eunoia/Cooperating Proof
  Calculus format. — `[C]`
- **Output format: LFSC** — `src/proof/lfsc/` (printer, post-processor, node
  converter, list-side-condition converter, `lfsc_util`) —
  `--proof-format-mode=lfsc`; `--lfsc-expand-trust` default `false`
  (**expert**, `:211`), `--lfsc-flatten` default `false` (**expert**, `:219`). — `[C]`
- **Output format: Alethe** — `src/proof/alethe/` (printer, post-processor +
  a separate `alethe_post_processor_algorithm.cpp`, node converter, let
  binding, `alethe_proof_rule.*`) — `--proof-format-mode=alethe`;
  `--proof-alethe-define-skolems` default `false` (**expert**, `:163`),
  `--proof-alethe-res-pivots` default `false` (**expert**, `:171`),
  `--proof-alethe-testing` default `false` (**expert**, `:179`). — `[C]`
- **Output format: DOT** — `src/proof/dot/dot_printer.cpp` —
  `--proof-format-mode=dot`; `--proof-dot-dag` default `false` (**expert**,
  `:187`), `--print-dot-clusters` default `false` (**expert**, `:195`) —
  proof visualisation, not checking. — `[C]`
- **Proof logging (streaming)** — `src/smt/proof_logger.cpp` — `--proof-log`
  default `false`, **expert** (`proof_options.toml:266`) — emits proof steps as
  they are produced rather than at the end. **Default off.** — `[C]`
- **SAT-level proofs** — `src/prop/proof_cnf_stream.cpp`,
  `prop_proof_manager.cpp`, `proof_post_processor.cpp`,
  `src/proof/resolution_proofs_util.cpp` — `--prop-proof-mode=MODE` default
  `PROOF` (`proof_options.toml:243`, `regular`; alternative
  `sat-external-prove` emits a `SAT_EXTERNAL_PROVE` step to be discharged by an
  external checker); `--sat-proof-min-dimacs` default `true` (**expert**,
  `:235`); `--opt-res-reconstruction-size` default `true` (`:147`). — `[C]`
- **DRAT** — `ProofRule::DRAT_REFUTATION` — the enum admits a DRAT refutation as
  a single step, i.e. cvc5 can defer the propositional part to an external DRAT
  checker rather than reconstructing resolution. — `[C]`
- **`proof_post_processor_dsl.cpp`** — `src/smt/proof_post_processor_dsl.cpp` —
  with proofs — elaborates macro/trusted steps into DSL rewrite steps according
  to `--proof-granularity`. — `[C]`
- **Unsat cores** — `src/smt/unsat_core_manager.cpp` —
  `--produce-unsat-cores` default `false`; `--unsat-cores-mode=MODE` default
  `OFF`, **expert** (`smt_options.toml:168`; modes `off` / `sat-proof` /
  `assumptions`) — two distinct core routes: from the SAT proof, or from solving
  under assumptions. `--minimal-unsat-cores` default `false` (**expert**),
  `--check-unsat-cores` default `false`, `--print-cores-full` default `false`. — `[C]`
- **Timeout cores** — `src/smt/timeout_core_manager.cpp` —
  `--timeout-core-timeout=N` default `10000` ms, **expert**
  (`smt_options.toml:543`) — finds a *subset of assertions that is itself hard*,
  for diagnosing timeouts rather than proving unsat. Exposed via the API's
  `getTimeoutCore`. — `[C]`
- **Model cores** — `src/smt/model_core_builder.cpp` — `--model-cores=MODE`
  default `NONE` (`smt_options.toml:94`, `regular`) — the minimal part of a
  model that suffices to satisfy the input. **Default off.** — `[C]`
- **Model blocking** — `src/smt/model_blocker.cpp` — used by `block-model` /
  `block-model-values` — builds the blocking clause for enumerating distinct
  models. — `[C]`
- **Model checking** — `src/smt/check_models.cpp` — `--check-models` default
  `false` (`common`), `--debug-check-models` default `false`,
  `--check-model-subsolver` default **`true`** (`smt_options.toml:86`) — the
  subsolver-based check is the one that is on. — `[C]`
- **Learned literals** — `src/prop/zero_level_learner.cpp`,
  `src/prop/learned_db.cpp` — `--produce-learned-literals` default `false`
  (`smt_options.toml:112`, `regular`) — extracts literals fixed at decision
  level 0; consumed by `learned_rewrite` and by deep restarts. — `[C]`
- **`illegal_checker.cpp`** — `src/smt/illegal_checker.cpp` — guards API
  sequences that are illegal for the current configuration. — `[C]`
- **`witness_form.cpp`** — `src/smt/witness_form.cpp` — with proofs — converts
  skolems back to their defining witness terms so a proof can talk about them. — `[C]`

## 4. Parallelism, partitioning, and external cooperation

- **`PartitionGenerator`** — `src/theory/partition_generator.cpp` — all —
  `--compute-partitions=N` default `0` (= disabled; `n < 2` disables),
  **expert**, and **every one of `parallel_options.toml`'s 13 options is
  `category = "expert"`** — splits a problem into `N` cubes for external
  parallel solving. Strategies (`--partition-strategy=MODE`, default
  `DECISION_SCATTER`): `decision-scatter`, `heap-scatter`, `lemma-scatter`,
  and three mutually-exclusive-cube variants from decisions / order heap /
  lemmas. Timing knobs: `--partition-tlimit=60`, `--partition-start-time=30`,
  `--partition-time-interval=1.0`, `--checks-before-partition=1`,
  `--checks-between-partitions=1`, `--partition-when={tlimit,checks}`,
  `--partition-check={standard,full}`, `--partition-conflict-size=N` (default
  `0` → `log2(N)`), `--append-learned-literals-to-cubes` (default `false`),
  `--random-partitioning` (default `false`), `--write-partitions-to=output`.
  **cvc5 emits partitions; it does not itself run them in parallel** — the
  binary is single-threaded and this is a cube producer for an outer
  harness. — `[C]`
- **Oracle interface** — `src/theory/quantifiers/oracle_engine.cpp`,
  `oracle_checker.cpp` — quantified logics — `--oracles` default `false`,
  **expert** (`quantifiers_options.toml:696`) — lets a formula contain calls to
  an *external* black-box function that the solver invokes and treats as an
  oracle during instantiation. Shipped, default off. — `[C]` `[P]`
- **Subsolvers** — `src/theory/smt_engine_subsolver.cpp` — quantifiers, SyGuS,
  abduction, interpolation, model checking, MBQI — on by default in those uses —
  spawns a *fresh, independent* `SolverEngine` on a derived query. This is the
  mechanism behind almost every "check something else to decide this" technique
  in cvc5. — `[C]`
- **Plugin API** — `src/theory/plugin_module.cpp`, `include/cvc5/cvc5.h` — all —
  active only when registered — an external component receives lemmas and SAT
  clauses and may contribute its own. — `[C]`

## 5. Preprocessing

### 5.1 The framework

- **`PreprocessingPass` (base)** — `src/preprocessing/preprocessing_pass.h:225`,
  `.cpp:286` — all — on by default (infrastructure) — wraps `applyInternal()`
  with a per-pass `TimerStat` named `preprocessing::<name>`; returns
  `CONFLICT` / `NO_CONFLICT`. — `[C]`
- **`PreprocessingPass::addSubstitutions`** — `preprocessing_pass.cpp:297` — all —
  helper — pushes a `TrustSubstitutionMap` into the top-level substitutions and,
  for every skolem LHS, calls `AssertionPipeline::removeIteSkolem` so stale
  ITE-skolem entries are dropped. — `[C]`
- **`PreprocessingPassRegistry`** — `preprocessing_pass_registry.cpp:123` — all —
  on by default — thread-local singleton mapping **37 pass names** to
  constructor thunks. `ProcessAssertions::finishInit` instantiates *every*
  registered pass eagerly (`src/smt/process_assertions.cpp:75-80`), so
  **registration is not execution** — a pass can be constructed on every run and
  never called. — `[C]`
- **`PreprocessingPassContext`** — `preprocessing_pass_context.h:44` — all — on
  by default — the pass-visible facade over `Env`: theory engine, prop engine,
  circuit propagator, top-level `TrustSubstitutionMap`, `LearnedLiteralManager`,
  `spendResource`, and the user-context set of symbols occurring in
  assertions. — `[C]`
- **`LearnedLiteralManager`** — `preprocessing/learned_literal_manager.cpp:22` —
  all — on by default — user-context set of zero-level-entailed literals;
  `getLearnedLiterals()` re-applies current substitutions and rewrites before
  handing them out. **Its only producer is `non_clausal_simp.cpp:241`** — so
  `--learned-rewrite` and deep restarts are both silently inert whenever
  non-clausal simplification does not run. — `[C]`
- **`AssertionPipeline`** — `preprocessing/assertion_pipeline.h:192` — all — on
  by default — the mutable assertion vector with proof plumbing:
  `replace` / `replaceTrusted` / `pushBackTrusted` each require a
  `ProofGenerator*` or a non-`UNKNOWN_PREPROCESS` `TrustId`; carries the
  `IteSkolemMap` and the `d_conflict` / `d_isRefutationUnsound` /
  `d_isModelUnsound` / `d_isNegated` flags. — `[C]`
- **Substitution-as-assertion mode** — `assertion_pipeline.cpp:246,257` — all,
  incremental — on by default when incremental —
  `enableStoreSubstsInAsserts()` conjoins derived substitutions into a
  distinguished assertion index instead of applying them, because in incremental
  mode already-asserted formulas cannot be rewritten. — `[C]`
- **AND-elim / rewrite proof generators** — `assertion_pipeline.h:385-389` — all —
  with proofs — `d_andElimEpg` justifies flattening a top-level `AND` of inputs;
  `d_rewpg` justifies `ensureRewritten`. — `[C]`

### 5.2 The 37 registered passes

- **`ackermann`** — `preprocessing/passes/ackermann.cpp:310` — QF_UFBV / QF_ABV
  (BV + UF + uninterpreted sorts), non-incremental only (`AlwaysAssert` at
  `:313`) — `--ackermann` default `false`, **expert** (`smt_options.toml:5`);
  **force-enabled** under `--bitblast=eager` when non-incremental
  (`set_defaults.cpp:454`); **force-disabled** under `--produce-models` when
  ARRAYS or UF is present (`set_defaults.cpp:504`); when it survives with UF
  present, `set_defaults.cpp:509-517` **disables THEORY_UF in the LogicInfo
  entirely** — replaces each `f(X)` with a fresh variable `f_X`, adds congruence
  lemmas, and encodes uninterpreted-sort variables as bit-vectors of width
  `log2(k)+1`. **Correction to the common summary**: "force-disabled when UF is
  present" holds only in the *model-producing* case; otherwise ackermann runs and
  UF is removed from the logic instead. — `[C]` `[P]` (Hadarean thesis, cited in
  `ackermann.h:9`)
- **`apply-substs`** — `passes/apply_substs.cpp:33` — all — on by default,
  unconditional, **called 4 times** in the pipeline — applies the top-level
  `TrustSubstitutionMap` with rewriting, skipping `isSubstsIndex` entries;
  returns `CONFLICT` as soon as an assertion rewrites to false. — `[C]`
- **`bool-to-bv`** — `passes/bool_to_bv.cpp:39` — BV — `--bool-to-bv=MODE`
  default `OFF`, `regular` (`bv_options.toml:52`); force-`OFF` for non-BV logics
  when `ALL` (`set_defaults.cpp:802`) and under `--cegqi-bv` in quantified logics
  (`:693`); throws if combined with `--solve-bv-as-int` (`:478`) — lowers
  non-top-level Booleans to width-1 bit-vectors (`ALL` = everything below the
  top level, `ITE` = only `ITE`→`BITVECTOR_ITE`). — `[C]`
- **`bv-eager-atoms`** — `passes/bv_eager_atoms.cpp:66` — QF_BV — implied by
  `--bitblast=eager` (`bv_options.toml:21`, default `LAZY`) — wraps every
  non-constant assertion in a `BITVECTOR_EAGER_ATOM`. — `[C]`
- **`bv-gauss`** — `passes/bv_gauss.cpp:725` — QF_BV — `--bv-gauss-elim` default
  `false`, **expert** (`bv_options.toml:86`) — **runs first, before the dummy
  `true` push and before any `apply-substs`** (`process_assertions.cpp:115-118`),
  so its input is not yet guaranteed rewritten; detects linear equation systems
  over bit-vectors and solves them by Gaussian elimination mod 2ⁿ. — `[C]`
- **`bv-intro-pow2`** — `passes/bv_intro_pow2.cpp:35` — QF_BV —
  `--bv-intro-pow2` default `false`, **expert** (`bv_options.toml:78`) — applies
  the `IsPowerOfTwo` rewrite throughout; header targets QF_BV/pspace. — `[C]`
- **`bv-to-bool`** — `passes/bv_to_bool.cpp:44` — BV — `--bv-to-bool` default
  `false`, `regular` (`bv_options.toml:44`); **force-enabled whenever
  `--solve-bv-as-int != off`** (`set_defaults.cpp:610`) — lifts width-1 BV terms
  and atoms back to Booleans. — `[C]`
- **`bv-to-int`** — `passes/bv_to_int.cpp:48` — BV → (NL)IA —
  `--solve-bv-as-int=MODE` default `OFF`, `regular` (`smt_options.toml:376`);
  enabling it unlocks integers + nonlinear in the LogicInfo (`set_defaults.cpp:602`)
  and is listed in `usesInputConversion`, so it **blocks sygus, abduction and
  interpolation** (`:1080`) — int-blasts BV via `IntBlaster` (modes
  `sum`/`iand`/`bv`/`bitwise` for `bvand`), pushing range constraints as new
  assertions. — `[C]`
- **`distinct-elim`** — `passes/distinct_elim.cpp:40` — all —
  `--distinct-elim-threshold=N` default `0`, **expert** (`smt_options.toml:368`);
  the pipeline guard is `distinctElimThresholdWasSetByUser`
  (`process_assertions.cpp:229`), so **the pass never runs unless the user sets
  the flag — even to its own default value** — blasts `DISTINCT` with ≤N children
  into pairwise disequalities via `TheoryUfRewriter::blastDistinct` with a
  `DISTINCT_ELIM` proof step. — `[C]`
- **`ext-rew-pre`** — `passes/extended_rewriter_pass.cpp:37` — all —
  `--ext-rew-prep=MODE` default `OFF`, **expert** (`smt_options.toml:286`; modes
  `use`/`agg`) — rewrites every assertion with the extended (or aggressive
  extended) rewriter. **Default off.** — `[C]`
- **`ff-bitsum`** — `passes/ff_bitsum.cpp:42` — FF —
  `--ff-bitsum` default `false`, **expert** (`ff_options.toml:29`), **or** implied
  by `--ff-solver=split` (`process_assertions.cpp:362`) — collects bit
  constraints and rewrites `FINITE_FIELD_ADD` sums of bits into explicit
  `FINITE_FIELD_BITSUM` nodes. — `[C]`
- **`ff-disjunctive-bit`** — `passes/ff_disjunctive_bit.cpp:34` — FF —
  `--ff-elim-disjunctive-bit` default **`true`**, expert (`ff_options.toml:21`) —
  replaces `(or (= x 0) (= x 1))` with `(= (* x x) x)`. On by default when FF is
  in play. — `[C]`
- **`foreign-theory-rewrite`** — `passes/foreign_theory_rewrite.cpp:142` —
  cross-theory, mainly strings↔arith — `--foreign-theory-rewrite` default
  `false`, **expert** (`smt_options.toml:360`) — uses one theory's entailment to
  simplify another's terms. **Default off.** — `[C]`
- **`fun-def-fmf`** — `passes/fun_def_fmf.cpp:45` — quantified with
  `define-fun-rec` — `--fmf-fun` default `false`, **expert**
  (`quantifiers_options.toml:723`); implied by `--fmf-fun-rlv`
  (`set_defaults.cpp:1582`), and itself implies `--finite-model-find` (`:1587`);
  only reached inside `if (logicInfo().isQuantified())` — abstracts admissible
  recursive definitions to fresh sorts with injections. — `[C]` `[P]` (Reynolds
  et al., *Model Finding for Recursive Functions*, IJCAR 2016)
- **`global-negate`** — `passes/global_negate.cpp:93` — intended for pure linear
  arith or pure BV — `--global-negate` default `false`, **expert**
  (`quantifiers_options.toml:198`); force-disabled under incremental
  (`set_defaults.cpp:1291`) and unsat cores (`:1343`); incompatible with proofs
  (`:1107`), models (`:1200`), sygus (`:1375`); forces `--deep-restart=none`
  (`:1730`) — replaces F₁…Fₙ with `∀x⃗. ¬(F₁ ∧ … ∧ Fₙ)`.
  `SmtDriverSingleCall::checkSatNext` (`smt_driver.cpp:173-200`) then flips
  unsat→sat unconditionally, but flips **sat→unsat only** when
  `logic.isPure(ARITH) && isLinear()` or `isPure(BV)` — otherwise it must answer
  `unknown`. — `[C]`
- **`ho-elim`** — `passes/ho_elim.cpp:346` — higher-order — applied
  unconditionally whenever `logicInfo().isHigherOrder()`
  (`process_assertions.cpp:343`), **but `applyInternal` returns `NO_CONFLICT`
  immediately unless `--ho-elim` or `--ho-elim-store-ax` is set**
  (`ho_elim.cpp:351`). `--ho-elim` default `false`, expert
  (`quantifiers_options.toml:1845`). `--ho-elim-store-ax` has toml default
  `true` (`:1857`) **but `set_defaults.cpp:1568-1574` overwrites it with the
  value of `hoElim` — i.e. `false` — for every higher-order logic unless the user
  set it.** Net effect: **for higher-order inputs this pass is a registered
  no-op by default.** When enabled it lambda-lifts, converts `APPLY_UF` to
  `HO_APPLY`, encodes function sorts as uninterpreted sorts with an apply
  operator, and optionally adds the store/extensionality axiom. — `[C]`
- **`int-to-bv`** — `passes/int_to_bv.cpp:297` — pure QF_LIA / QF_NIA —
  `--solve-int-as-bv=N` default `0`, **expert** (`smt_options.toml:437`);
  non-incremental only (`:112`, and `set_defaults.cpp:1268`); enabling it
  **enables THEORY_BV and disables THEORY_ARITH in the LogicInfo**
  (`set_defaults.cpp:465`); blocks sygus/abduct/interpolate (`:1085`) — encodes
  integers as N-bit bit-vectors. — `[C]`
- **`ite-removal`** — `passes/ite_removal.cpp:37` — all — `--early-ite-removal`
  default `false`, **expert** (`smt_options.toml:320`); auto-enabled if
  `--ite-simp` is on (`set_defaults.cpp:709`) — calls `PropEngine::removeItes`,
  appends the skolem-definition lemmas, records the `IteSkolemMap`, rewrites.
  Always followed by an extra `apply-substs` because it can reintroduce
  already-solved skolems. — `[C]`
- **`ite-simp`** — `passes/ite_simp.cpp:245` — targeted at QF_LIA — `--ite-simp`
  default `false`, **expert** (`smt_options.toml:270`); **hard-incompatible with
  unsat cores: `incompatibleWithUnsatCores` returns a reason with no silent
  fallback, so `--produce-unsat-cores --ite-simp` throws**
  (`set_defaults.cpp:1346`); additionally gated on
  `d_simplifyAssertionsDepth <= 1 || --on-repeat-ite-simp` — runs `ITEUtilities`
  (compression, ITE-tree simplification, and `simplifyWithCare` when
  `--simp-with-care` is set — which `set_defaults.cpp:768` turns on for
  QF_AUFBV). — `[C]` `[P]` (Kim et al., SAT 2009)
- **`learned-rewrite`** — `passes/learned_rewrite.cpp:57` — arithmetic-bearing —
  `--learned-rewrite` default `false`, `regular` (`smt_options.toml:45`);
  **force-disabled under unsat cores** (`set_defaults.cpp:1323`, throwing if
  user-set) — feeds learned literals into `arith::BoundInference` and uses the
  bounds to rewrite assertions (e.g. eliminating div/mod guards). Returns
  immediately when there are no learned literals. — `[C]`
- **`miplib-trick`** — `passes/miplib_trick.cpp:186` — QF_LIA (MIPLIB shape) —
  `--miplib-trick` default `false`, **expert** (`arith_options.toml:140`);
  force-disabled under incremental (`set_defaults.cpp:1293`); enabling it
  **widens the logic to include integers** (`:1492`); additionally requires
  `simplificationMode != NONE`, THEORY_ARITH enabled, and
  `d_simplifyAssertionsDepth <= 1` — piggybacks on the `CircuitPropagator`
  back-edge map to find Boolean variables gating 0/1 arithmetic coefficients and
  replaces them with integer variables plus bounds. — `[C]`
- **`nl-ext-purify`** — `passes/nl_ext_purify.cpp:109` — NRA/NIA —
  `--nl-ext-purify` default `false`, **expert** (`arith_options.toml:450`) —
  replaces sums appearing under multiplications with fresh variables. — `[C]`
- **`non-clausal-simp`** — `passes/non_clausal_simp.cpp:58` — all except pure
  QF_SAT — `--simplification=MODE` default `BATCH`, `regular`
  (`smt_options.toml:13`); `set_defaults.cpp:659-682` sets it to `NONE` iff
  `logic.isPure(THEORY_BOOL) && !logic.isQuantified()`, `BATCH` otherwise —
  **and that entire block is skipped when `--produce-unsat-cores` is on** —
  asserts everything to the `CircuitPropagator`, propagates, returns `CONFLICT`
  on conflict; otherwise turns propagated units into top-level substitutions and
  constant propagations, notifies the `LearnedLiteralManager`, re-applies both
  substitution maps. `--simplification-bcp` (default `false`, **expert**;
  force-disabled under separation logic, `set_defaults.cpp:1418`) additionally
  substitutes non-equality literals to Boolean constants. — `[C]`
- **`normalize`** — `passes/normalize.cpp:905` — all — **only reachable via
  `-o normalize`** (`base_options.toml:281`), which also forces
  `--preprocess-only` (`set_defaults.cpp:1030`); on that path
  `ProcessAssertions::apply` applies substitutions *without* rewriting, beta
  reduces, normalizes, prints, and **returns early — no other pass runs**
  (`process_assertions.cpp:130-153`) — canonicalises a benchmark independently of
  symbol names and assertion order: structural encodings per assertion, bucketed
  into equivalence classes, classes sorted by encoding, variables renamed
  deterministically. — `[C]`
- **`pseudo-boolean-processor`** — `passes/pseudo_boolean_processor.cpp:41` —
  QF_LIA with 0/1 variables — `--pb-rewrites` default `false`, **expert**
  (`arith_options.toml:344`); force-disabled under unsat cores
  (`set_defaults.cpp:1333`) — learns pseudo-Boolean structure from `GEQ`/`ADD`
  polynomials and applies 0/1-variable replacements **only if `likelyToHelp()`**. — `[C]`
- **`quantifiers-preprocess`** — `passes/quantifiers_preprocess.cpp:34` — all
  quantified — on by default whenever `logicInfo().isQuantified()`, no flag guard
  (`process_assertions.cpp:247`) — delegates to
  `quantifiers::QuantifiersPreprocess::preprocess`: removes rewrite-rule syntax,
  applies pre-Skolemisation per `--pre-skolem-quant=MODE` (default `OFF`,
  `regular`; forced `ON` by `--cegqi-nested-qe` and by `--sygus-inference`). — `[C]`
- **`real-to-int`** — `passes/real_to_int.cpp:217` — pure real (NRA) —
  `--solve-real-as-int` default `false`, `regular` (`smt_options.toml:446`);
  blocks sygus/abduct/interpolate — converts real operations to integer
  operations. — `[C]`
- **`rewrite`** — `passes/rewrite.cpp:34` — all — on by default; run
  unconditionally at `process_assertions.cpp:235` and `:369`, conditionally at
  `:204` — top-level rewriter on every assertion with a
  `RewriteProofGenerator`. — `[C]`
- **`sep-skolem-emp`** — `passes/sep_skolem_emp.cpp:101` — SEP —
  `--sep-pre-skolem-emp` default `false`, **expert** (`sep_options.toml:13`);
  warns and no-ops if `!d_env.hasSepHeap()` — eliminates `sep.emp` by
  pre-Skolemising into location/data terms. — `[C]`
- **`sort-inference`** — `passes/sort_infer.cpp:33` — UF-bearing —
  `--sort-inference` default `false`, **expert** (`smt_options.toml:344`);
  force-disabled under incremental (`set_defaults.cpp:1290`); in
  `incompatibleWithModels` (`:1190`) — infers a monotone sort assignment and
  rewrites into it, recording `model_replace_f` correspondences. — `[C]`
- **`static-learning`** — `passes/static_learning.cpp:31` — all —
  **`--static-learning` default `true`, `regular` (`smt_options.toml:37`) — on by
  default** — flattens top-level ANDs and calls `TheoryEngine::ppStaticLearn` on
  each conjunct, appending the theory-supplied lemmas. Per-assertion cached, so
  idempotent in a context. — `[C]`
- **`static-rewrite`** — `passes/static_rewrite.cpp:39` — all — on by default,
  unconditional (`process_assertions.cpp:379`) — bottom-up
  `TheoryEngine::ppStaticRewrite` on subterms (notably equalities), with a
  fixpoint map. Deliberately separate from `theory-preprocess` because the
  latter's cache is reused for lemmas. — `[C]`
- **`strings-eager-pp`** — `passes/strings_eager_pp.cpp:28` — strings — runs iff
  `--strings-lazy-pp` is **false**, and that option's default is **`true`**
  (`strings_options.toml:21`, `regular`) — so **this pass is off by default**;
  turning it off also forces quantifiers into the logic
  (`set_defaults.cpp:532`) — eagerly reduces extended string functions to
  skolems + constraints. — `[C]`
- **`sygus-infer`** — `passes/sygus_inference.cpp:37` — quantified / UF with
  functions to solve for — `--sygus-inference=MODE` default `OFF`, **expert**
  (`quantifiers_options.toml:965`; modes `try`/`on`); force-disabled on internal
  subsolvers (`set_defaults.cpp:394`) and under incremental (`:1253`) — recasts
  the whole assertion set as a single SyGuS conjecture, solves it in a subsolver,
  substitutes the synthesised interpretations back. — `[C]`
- **`synth-rr`** — `passes/synth_rew_rules.cpp:44` — n/a —
  **DEAD as a preprocessing pass.** Registered at
  `preprocessing_pass_registry.cpp:137` and instantiated by
  `ProcessAssertions::finishInit`, but `applyPass("synth-rr", …)` appears
  **nowhere** in the tree and `applyInternal` is a one-line `return NO_CONFLICT`
  with a `CVC5_UNUSED` parameter. There is no `--sygus-rr-synth` option any more
  (only the eight `sygus-rr-synth-*` sub-options). The class survives **only**
  for its static `getGrammarsFrom`, called from `SolverEngine::findSynth` for
  `find-synth :rewrite_input` (`src/smt/solver_engine.cpp:1078`), tuned by
  `--sygus-rr-synth-input-nvars` (default `3`, expert). — `[C]`
- **`theory-preprocess`** — `passes/theory_preprocess.cpp:33` — all — on by
  default, unconditional (`process_assertions.cpp:381`) — `PropEngine::preprocess`
  (`Theory::ppRewrite` + term-formula removal) on every assertion, appending
  `SkolemLemma`s. The last structural pass; substitutions are deliberately *not*
  re-applied after it, because substitution ranges are not
  theory-preprocessed. — `[C]`
- **`unconstrained-simplifier`** — `passes/unconstrained_simplifier.cpp:833` —
  fully supported only on subsets of QF_ABV per the option help —
  `--unconstrained-simp` default `false`, **expert** (`smt_options.toml:328`),
  **but auto-enabled by `set_defaults.cpp:649-656`** under
  `!incrementalSolving && !logic.isQuantified() && !produceModels &&
  !produceAssignments && !checkModels && ARRAYS && BV && !ARITH` — i.e. **on by
  default for QF_ABV / QF_AUFBV without arithmetic and without model
  production**; the whole block is skipped when `--produce-unsat-cores` is set —
  replaces a subterm containing a variable that occurs exactly once by a fresh
  variable, collapsing the surrounding operator. Called twice
  (`process_assertions.cpp:205` and `:461`). — `[C]` `[P]` (Bruttomesso thesis)

### 5.3 The pass order in `src/smt/process_assertions.cpp`

`ProcessAssertions::apply` at `:90`. Returns false if simplification derived
`false`. The order is load-bearing and is *not* the registry order. `[C]`

| # | line | pass | guard |
| --- | --- | --- | --- |
| 0 | `:109` | early exit | `ap.size() == 0` |
| 1 | `:115` | `bv-gauss` | `options().bv.bvGaussElim` — **before** the dummy assertion and before any substitution |
| 2 | `:122` | push dummy `true` | unconditional — reserves the last slot for later additions |
| 3 | `:130` | `normalize` | `isOutputOn(NORMALIZE)` — **returns immediately; the rest of the pipeline is skipped** |
| 4 | `:159` | `apply-substs` | unconditional (non-incremental: expands `define-fun` only) |
| 5 | `:166` | `global-negate` | `quantifiers.globalNegate` |
| 6 | `:172` | `nl-ext-purify` | `arith.nlExtPurify` |
| 7 | `:177` | `real-to-int` | `smt.solveRealAsInt` |
| 8 | `:182` | `ackermann` | `smt.ackermann` |
| 9 | `:187` | `int-to-bv` | `smt.solveIntAsBV > 0` |
| 10 | `:196` | `ext-rew-pre` | `smt.extRewPrep != OFF` |
| 11 | `:202` | `rewrite` then `unconstrained-simplifier` | `smt.unconstrainedSimp` (one guard for both) |
| 12 | `:208` | `bv-intro-pow2` | `bv.bvIntroducePow2` |
| 13 | `:214` | `bv-to-bool` | `bv.bitvectorToBool` |
| 14 | `:218` | `bv-to-int` | `smt.solveBVAsInt != OFF` |
| 15 | `:222` | `foreign-theory-rewrite` | `smt.foreignTheoryRewrite` |
| 16 | `:229` | `distinct-elim` | `distinctElimThresholdWasSetByUser` (**not** the value) |
| 17 | `:235` | `rewrite` | unconditional — "assertions MUST be rewritten by this point" |
| 18 | `:238` | `bool-to-bv` | `bv.boolToBitvector != OFF` |
| 19 | `:242` | `sep-skolem-emp` | `sep.sepPreSkolemEmp` |
| 20 | `:247` | `quantifiers-preprocess`; then `fun-def-fmf`; then `apply-substs` | `logicInfo().isQuantified()`; `fmfFunWellDefined`; `preSkolemQuant != OFF` |
| 21 | `:266` | `strings-eager-pp` + `apply-substs` | `!strings.stringLazyPreproc` |
| 22 | `:273` | `sort-inference` | `smt.sortInference` |
| 23 | `:278` | `pseudo-boolean-processor` | `arith.pbRewrites` |
| 24 | `:284` | `sygus-infer` | `quantifiers.sygusInference != OFF` |
| 25 | `:294` | **`simplifyAssertions`** (see below) | unconditional |
| 26 | `:304` | `static-learning` | `smt.staticLearning` (default **true**) |
| 27 | `:310` | `learned-rewrite` | `smt.learnedRewrite` — must follow `non-clausal-simp`, its only literal producer |
| 28 | `:315` | `ite-removal` + `apply-substs` | `smt.earlyIteRemoval` |
| 29 | `:326` | `simplifyAssertions` again | `smt.repeatSimp` — raises `d_simplifyAssertionsDepth` to 2, which is what disables `miplib-trick` and (absent `--on-repeat-ite-simp`) `ite-simp` on the second pass |
| 30 | `:343` | `ho-elim` | `logicInfo().isHigherOrder()` (but see the pass entry — a no-op by default) |
| 31 | `:348` | *invariant boundary comment*: "no reordering of assertions or introducing new ones" — note that the FF passes, `rewrite`, `static-rewrite`, `theory-preprocess` and `bv-eager-atoms` all still run after this line, and `theory-preprocess` **does** append lemmas |
| 32 | `:358` | `ff-disjunctive-bit` | `ff.ffElimDisjunctiveBit` (default **true**) |
| 33 | `:362` | `ff-bitsum` | `ff.ffBitsum \|\| ff.ffSolver == SPLIT_GB` |
| 34 | `:369` | `rewrite` | unconditional |
| 35 | `:379` | `static-rewrite` | unconditional |
| 36 | `:381` | `theory-preprocess` | unconditional (includes ITE removal) |
| 37 | `:385` | `bv-eager-atoms` | `bv.bitblastMode == EAGER` |

- **`ProcessAssertions::simplifyAssertions`** — `process_assertions.cpp:405` —
  all — on by default — the inner sequence: (a) `:414` `non-clausal-simp` if
  `simplificationMode != NONE`; (b) `:425` `miplib-trick` if `arithMLTrick &&
  THEORY_ARITH && depth <= 1`; (c) `:445` `ite-simp` if `doITESimp && (depth <= 1
  || doITESimpOnRepeat)`; (d) `:459` `unconstrained-simplifier` if
  `unconstrainedSimp`; (e) `:464` `non-clausal-simp` **again** if `repeatSimp &&
  simplificationMode != NONE`. — `[C]`
- **`ProcessAssertions::applyPass`** — `:543` — all — on by default — dumps
  `assertions::pre-<name>` / `post-<name>` traces and **short-circuits every
  subsequent pass to `CONFLICT` once `ap.isInConflict()`**. — `[C]`
- **`dumpAssertionsToStream`** — `:504` — all — `-o pre-asserts` /
  `-o post-asserts`; `--output-print-defs` default `true`, **expert**
  (`smt_options.toml:552`) — prints the benchmark via `PrintBenchmark`, expanding
  `define-fun-rec` and re-emitting eliminated substitutions as `define-fun`. — `[C]`

### 5.4 `set_defaults.cpp` — the per-logic overrides, quoted

- **Three-phase structure** — `set_defaults.cpp:118` — `setDefaultsPre(opts)`
  (logic-independent) → `finalizeLogic(logic, opts)` (**may mutate the
  LogicInfo**) → `setDefaultsPost(logic, opts)`. Macros `SET_AND_NOTIFY`,
  `SET_AND_NOTIFY_IF_NOT_USER`, `OPTION_EXCEPTION_IF_NOT` at `:56-113`. — `[C]`
- **Safe mode** — `:130-176` — `--safe-options` / `SafeMode != UNRESTRICTED`
  turns off `sep`, `bags`, `ff`, `fp`, `ufHoExp`, `ufCardExp`, `datatypesExp`,
  `arithExp`, `relsExp`, `setsCardExp`; `SAFE` additionally sets `nlCov=false`,
  `ufSymmetryBreaker=false`, `cegqiBv=false`, `varEntEqElimQuant=false`, and
  forces `bvSolver=BITBLAST_INTERNAL`. — `[C]`
- **`unconstrainedSimp` by logic** — `:643-657` —
  `!incremental && !quantified && !produceModels && !produceAssignments &&
  !checkModels && ARRAYS && BV && !ARITH`; whole `else` block entered only when
  `!produceUnsatCores`. — `[C]`
- **`simplificationMode` by logic** — `:659-682` —
  `qf_sat = logic.isPure(THEORY_BOOL) && !logic.isQuantified()` → `NONE`,
  else `BATCH`; skipped entirely under unsat cores. — `[C]`
- **`repeatSimp` by logic** — `:777-785` — `!quantified && ARRAYS && UF && BV &&
  !safeUnsatCores(opts)` — i.e. QF_AUFBV. — `[C]`
- **`simplifyWithCareEnabled` by logic** — `:766-772` — QF_AUFBV. — `[C]`
- **`ufSymmetryBreaker` by logic** — `:752-763` —
  `logic.isPure(THEORY_UF) && !quantified && !incremental && !safeUnsatCores`. — `[C]`
- **`ackermann` auto-enable for eager bitblasting** — `:432-460` — under
  `--bitblast=eager`: downgrade to `LAZY` if models+ARRAYS/UF; else enable
  ackermann if non-incremental; else throw if quantified or not pure BV. — `[C]`
- **`bitvectorToBool` implied by `solveBVAsInt`** — `:602-611`. — `[C]`
- **`earlyIteRemoval` implied by `doITESimp`** — `:707-710`. — `[C]`
- **`hoElimStoreAx` silently flipped for HO** — `:1568-1574` — see the `ho-elim`
  entry; this is the mechanism that makes the pass inert. — `[C]`
- **`incompatibleWithProofs`** — `:1080-1180` — rejects fresh-binders,
  global-negate, deep restarts, lemma inprocessing; silently sets
  `bvAssertInput=false`, `bvSolver=BITBLAST_INTERNAL` (full proofs),
  `nlCovVarElim=false`; under `FULL_STRICT` also `ufSymmetryBreaker=false`,
  `cegqiMidpoint=true`, `cegqiUseInfInt/Real=false`,
  `dtSharedSelectors=false`. — `[C]`
- **`incompatibleWithModels`** — `:1183-1210` — rejects `unconstrained-simp` (if
  user-set), `sort-inference`, `minisat-simplification=all`, `global-negate`,
  `arrays-weak-equiv`. — `[C]`
- **`incompatibleWithIncremental`** — `:1212-1295` — hard-rejects separation
  logic, `ackermann`, eager bitblasting outside pure QF_BV, `solveIntAsBV`, deep
  restarts, `computePartitions > 1`, `proofLog`; silently disables
  `unconstrainedSimp`, `sygusInference`, `sygusInst`, `sortInference`,
  `globalNegate`, `cegqiNestedQE`, `arithMLTrick`. — `[C]`
- **`incompatibleWithUnsatCores`** — `:1297-1355` — states the rule outright: a
  pass is incompatible if "(A) its reasoning is not local … AND (B) it does not
  track proofs". Silently disables `deepRestartMode`, `learnedRewrite`,
  `pbRewrites`, `globalNegate`; **hard-rejects `--ite-simp`**. — `[C]`
- **`safeUnsatCores`** — `:1357-1362` — `unsatCoresMode == ASSUMPTIONS`, which is
  the default mode when `--produce-unsat-cores` is set *without* proofs
  (`:212-219`) — so it is true in the common case, and that is what disables
  `repeatSimp` and `ufSymmetryBreaker`. — `[C]`
- **`usesInputConversion` / `incompatibleWithSygus`** — `:1076-1093`,
  `:1364-1382` — `solveBVAsInt`, `solveIntAsBV`, `solveRealAsInt` are the three
  "input conversion" passes; any of them blocks sygus and therefore blocks
  `--produce-abducts` / `--produce-interpolants`. — `[C]`
- **`incompatibleWithSeparationLogic`** — `:1412-1421` — sets
  `simplificationBoolConstProp = false` because spatial predicates are
  position-dependent. — `[C]`
- **Internal-subsolver overrides** — `:390-403` — `sygusInference = OFF`,
  `deepRestartMode = NONE`. — `[C]`
- **Strings widening** — `:530-545` — `stringExp` on for any THEORY_STRINGS logic
  unless user-set; `stringExp || !stringLazyPreproc || regExpElim == AGG`
  **forces quantifiers into the logic**. — `[C]`
- **`sygusInst` auto-enable** — `:413-429` — `!isSygus && quantified &&
  (isPure(FP) || (isPure(ARITH) && !isLinear() && areIntegersUsed())) &&
  !incremental` — i.e. **SyGuS-based instantiation is a default strategy for
  quantified pure-FP and quantified NIA.** — `[C]`
- **`satSolver` under incremental** — `:408-413` — `MINISAT` rather than CaDiCaL,
  "due to performance". — `[C]`

### 5.5 The SMT driver layer

- **`SmtDriver::checkSat`** — `src/smt/smt_driver.cpp:40` — all — on by default —
  sets assumptions, runs `IllegalChecker::checkAssertions`, short-circuits on an
  already-exhausted resource manager, then loops
  `getNextAssertionsInternal` → `checkSatNext` while the result is
  `UNKNOWN(REQUIRES_CHECK_AGAIN)`, calling `d_smt.finishInit()` (a **fresh theory
  and prop engine**) between rounds. — `[C]`
- **`SmtDriver` push/pop callbacks** — `smt_driver.cpp:128-149` — incremental —
  `notifyPushPre` eagerly preprocesses and asserts pending formulas *before* the
  user push, so assertions are only ever preprocessed in one context. — `[C]`
- **`SmtDriverSingleCall`** — `smt_driver.cpp:151-215` — all — **the default
  driver** — preprocess → bail with `REQUIRES_FULL_CHECK` if `--preprocess-only`
  → assert → check; post-processes the global-negate inversion. — `[C]`
- **`SmtDriverDeepRestarts`** — `src/smt/smt_driver_deep_restarts.cpp:32` — all,
  non-incremental — `--deep-restart=MODE` default `NONE`, **expert**
  (`smt_options.toml:510`); force-`NONE` on internal subsolvers, under unsat
  cores, and under `--global-negate`; hard-rejected with proofs, incremental and
  sygus — on `UNKNOWN`, pulls `getLearnedZeroLevelLiteralsForRestart()`, and if
  non-empty rebuilds the whole pipeline from the *preprocessed* assertions plus
  the carried `IteSkolemMap` plus the learned literals as new assertions. Asserts
  (in assertion builds) that no literal is ever relearned. — `[C]`
- **`TimeoutCoreManager`** — `src/smt/timeout_core_manager.cpp:45` — all — API
  `getTimeoutCore`; `--timeout-core-timeout=N` default `10000` ms, **expert** —
  a model-guided minimal-covering loop: maintain a candidate set C; if C is
  unsat or times out, return it; if C is sat with model m, record m and grow C
  with one input assertion m falsifies, dropping assertions whose owned models
  are covered by another. The header (`timeout_core_manager.h:40-63`) bounds the
  worst case at N check-sats with **at most one timeout call**. — `[C]`
- **`UnsatCoreManager::getUnsatCore`** — `unsat_core_manager.cpp:39,81` —
  `--unsat-cores-mode` auto-set to `ASSUMPTIONS` at `set_defaults.cpp:212`, to
  `SAT_PROOF` when proofs are on at `:277` — extracts the free assumptions of the
  refutation proof and maps them back to inputs. — `[C]`
- **`UnsatCoreManager::reduceUnsatCore`** — `:224`, invoked at `:114` —
  `--minimal-unsat-cores` default `false`, **expert** — iteratively re-checks the
  core with one assertion dropped. — `[C]`
- **`getUnsatCoreLemmas`** — `:50` — `--dump-unsat-cores-lemmas` (implies full
  proofs, `set_defaults.cpp:238`) — the theory lemmas used in the refutation. — `[C]`
- **`getRelevantQuantTermVectors`** — `:138` — quantified —
  `get-instantiations` / `--dump-instantiations` — walks the proof for
  `INSTANTIATE` steps and reports, per quantified formula, **the term vectors
  actually used in the refutation** (as opposed to all those generated). — `[C]`
- **`partitionUnsatCore` / `convertPreprocessedToInput`** — `:283`, `:302` —
  splits a core into input vs. non-input and maps preprocessed assertions back to
  original inputs via the preprocess proof. — `[C]`
- **`ModelBlocker::getModelBlocker`** — `src/smt/model_blocker.cpp:32` —
  `block-model` / `block-model-values` — `VALUES` (`:219`) emits the disjunction
  of disequalities; `LITERALS` (`:46`) instead computes a **minimal implicant** of
  the assertions under the model (keeping only the literals needed to make each
  assertion true) and negates it. — `[C]`
- **`ModelCoreBuilder::setModelCore`** — `model_core_builder.cpp:23` —
  `--model-cores=MODE` default `NONE`, `regular` — `NON_IMPLIED` uses
  `SubstitutionMinimize::findWithImplied`, `SIMPLE` uses `find`. — `[C]`
- **`AbductionSolver`** — `src/smt/abduction_solver.cpp:37,109` —
  `--produce-abducts` default `false`, `regular`; sets `isSygus`, pulling in
  `setDefaultsSygus`, which forces `sygusFilterSolMode=STRONG` and basic SyGuS
  algorithms — builds "find A s.t. axioms ∧ A is sat and axioms ∧ A ⊨ goal" as a
  SyGuS conjecture and solves it in a subsolver; `getAbductNext` (`:97`)
  streams. `--check-abducts` (`:170`) re-verifies both conditions
  independently. — `[C]`
- **`InterpolationSolver`** — `src/smt/interpolation_solver.cpp:38,130` —
  `--produce-interpolants` default `false`, `regular`;
  `--interpolants-mode=MODE` default `DEFAULT`, `regular` (modes
  `assumptions`/`conjecture`/`shared`/`all`, restricting the allowed vocabulary)
  — delegates to `quantifiers::SygusInterpol`. `--check-interpolants` (`:148`)
  re-verifies both implications in fresh subsolvers. — `[C]`
- **`QuantElimSolver`** — `src/smt/quant_elim_solver.cpp:40` — quantified
  LIA/LRA/BV (whatever CEGQI supports) — `get-qe` / `get-qe-partial` — negates
  the query, solves, and **reconstructs the quantifier-free answer from the
  instantiation terms recorded in the unsat proof**. — `[C]`
- **`FindSynthSolver`** — `src/smt/find_synth_solver.cpp:30,46` —
  `find-synth` / `find-synth-next` — initialises possibly several SyGuS
  enumerators and interleaves them until one produces a term matching the target
  (`:rewrite`, `:rewrite_unsound`, `:query`, `:rewrite_input`). — `[C]`
- **`ExpandDefs::expandDefinitions`** — `src/smt/expand_definitions.cpp:35` —
  all — on by default for `get-value` — a deliberately lightweight alternative to
  `PropEngine::preprocess` for user-supplied terms. The header states it is
  **not proof-producing** and must only be used for model values. — `[C]`
- **`RemoveTermFormulas`** — `src/smt/term_formula_removal.cpp:61,89,127,264` —
  all — on by default via `theory-preprocess` and `ite-removal` — term-context-aware
  purification of term-level formulas into skolems plus defining lemmas; caching
  is keyed on the `TermContext`, so the same term is handled differently inside
  and outside a term position. Non-Boolean `ITE` → skolem `k` with
  `(ite c (= k t1) (= k t2))` justified by `ITE_EQ` + `MACRO_SR_PRED_INTRO` +
  `MACRO_SR_PRED_TRANSFORM`. `AlwaysAssert(node.getKind() != Kind::WITNESS)` —
  witness terms must never appear in asserted formulas. — `[C]`
- **`WitnessFormGenerator`** — `src/smt/witness_form.cpp:34,50,74` — with proofs
  — proves `t = witness-form(t)` via a `TConvProofGenerator`;
  `requiresWitnessFormTransform` / `Intro` return a `WitnessReq`
  (`WITNESS_AND_REWRITE` / `WITNESS` / `REWRITE` / `NONE`). — `[C]`
- **`ProofLoggerCpc`** — `src/smt/proof_logger.cpp:21` — `--proof-log` default
  `false`, **expert**; rejected under incremental; mutually exclusive with
  `--dump-proofs` — streams an on-the-fly Eunoia/CPC proof:
  `logCnfPreprocessInputs` at preprocessing end, `logTheoryLemma` per lemma,
  `logSatRefutation` at the end. — `[C]`
- **`ProofPostprocessCallback::expandMacros`** —
  `src/smt/proof_post_processor.cpp:177` — with proofs and
  `--proof-granularity != macro` — expands each macro rule into primitives:
  `MACRO_SR_EQ_INTRO` (`:206`) → `SUBS` + `MACRO_REWRITE` + `REFL`/`TRANS`;
  `MACRO_SR_PRED_INTRO` (`:290`) → `TRUE_ELIM`; `MACRO_SR_PRED_ELIM` (`:354`) →
  `EQ_RESOLVE`; `CHAIN_M_RESOLUTION` (`:478`) → `CHAIN_RESOLUTION`
  (+`FACTORING`/`REORDERING`); `SUBS` (`:651`) → per-variable `TRANS` chains;
  `MACRO_REWRITE` (`:852`) → `EVALUATE` / `TRUST_THEORY_REWRITE` / `TRANS` /
  `REFL`; `MACRO_ARITH_SCALE_SUM_UB` (`:958`); `MACRO_STRING_INFERENCE` (`:966`);
  `MACRO_BV_BITBLAST` (`:983`). — `[C]`
- **Proof rule-elimination policy** — `src/smt/proof_manager.cpp:120-159` —
  `--proof-granularity` (default `MACRO`, but **auto-raised to `DSL_REWRITE`
  whenever proofs are genuinely requested**, `set_defaults.cpp:265-272`, and to
  `THEORY_REWRITE` for Alethe, `:288`) — at `!= MACRO`: eliminate the four
  `MACRO_SR_*` rules, `MACRO_ARITH_SCALE_SUM_UB`, `MACRO_STRING_INFERENCE`,
  `MACRO_BV_BITBLAST`, `TRUST`, and `CHAIN_M_RESOLUTION` (the last skipped for
  Alethe unless `--proof-chain-m-res`, which is `proof_options.toml:131`,
  default **`true`**, `regular`; always done for LFSC). At `!= REWRITE`
  additionally `SUBS` and `MACRO_REWRITE`; at `!= THEORY_REWRITE` additionally
  `setEliminateAllTrustedRules()`. — `[C]`
- **`ProofPostprocessDsl::reconstruct`** — `src/smt/proof_post_processor_dsl.cpp:36`
  — with proofs at `dsl-rewrite` granularity (the effective default once proofs
  are on) — replays trusted rewrite steps as sequences of RARE rules via
  `RewriteDbProofCons`. — `[C]`
- **`DifficultyPostprocessCallback`** — `src/smt/difficulty_post_processor.cpp:25,42,64`,
  driven by `PfManager::translateDifficultyMap` (`proof_manager.cpp:376`) —
  `--produce-difficulty` default `false`, `regular` — walks the preprocessing
  proof of each preprocessed assertion and attributes its difficulty to the
  *source* free assumptions rather than to definitional ones. — `[C]`
- **`IllegalChecker`** — `src/smt/illegal_checker.cpp:38,152,198` — all — on by
  default; the forbidden set depends on `--arrays-exp`, `--arith-exp`,
  `--datatypes-exp`, `--uf-card-exp`, `--sets-card-exp`, `--rels-exp`, `--fp`,
  `--sep`, `--bags`, `--ff` — rejects assertions containing kinds/types the
  current configuration does not admit: `STORE_ALL` without `--arrays-exp`; the
  whole transcendental / `POW` / `IAND` / `POW2` / `INTS_LOG2` family without
  `--arith-exp`; `MATCH` and `NULLABLE_TYPE` without `--datatypes-exp`;
  `CARDINALITY_CONSTRAINT` without `--uf-card-exp`; `SET_CARD` and the ten
  `RELATION_*` kinds without `--sets-card-exp` / `--rels-exp`. `HO_APPLY` is
  deliberately **not** guarded because it has proof support. — `[C]`

## 6. Bit-vectors and floating-point

### 6.1 The BV theory and its two solvers

- **`TheoryBV` (dispatcher)** — `src/theory/bv/theory_bv.cpp:47` — any logic with BV — on by default; picks the sub-solver from `--bv-solver` (`bv_options.toml:94`, default `BITBLAST`) — constructs `BVSolverBitblast` or `BVSolverBitblastInternal` and forwards every callback. — [C]
- **`BVSolverBitblast` (private SAT instance, lazy)** — `src/theory/bv/bv_solver_bitblast.cpp:105` — all BV — **default** (`--bv-solver=bitblast`), but the option carries `no_support = ["proofs"]` (`bv_options.toml:99`) — bit-blasts BV facts into a *private* `CnfStream` + SAT solver and solves under assumptions, returning unsat-assumption conflicts. — [C]
- **`BVSolverBitblastInternal` (into the main CDCL(T) solver)** — `src/theory/bv/bv_solver_bitblast_internal.cpp:87` — all BV — `--bv-solver=bitblast-internal`; **silently forced on whenever full proofs are required** (`set_defaults.cpp:1141`) and by safe-options (`:181`) — emits `atom <=> bitblast(atom)` as ordinary theory *lemmas* into the main SAT solver, so `BV_BITBLAST_STEP` proofs exist. — [C]
- **The difference, stated plainly** — `bv_solver_bitblast.cpp:368` vs `bv_solver_bitblast_internal.cpp:78` — the default solver owns a separate SAT solver (CaDiCaL / Kissat / CryptoMiniSat via `--bv-sat-solver`) and communicates only conflicts; the internal one reuses the main solver through lemmas, is proof-producing, and supports proof/incremental workflows. **So cvc5's fast BV path and its proof-producing BV path are different solvers.** — [C]
- **`BBRegistrar`** — `bv_solver_bitblast.cpp:74` — QF_BV (and QF_UFBV after ackermannization) — only under `--bitblast=eager` — bit-blasts any BV atom the private CnfStream meets inside a `BITVECTOR_EAGER_ATOM`. — [C]
- **`NotifyResetAssertions`** — `bv_solver_bitblast.cpp:32` — BV incremental — only with `--bv-assert-input` (default `false`, **expert**, `bv_options.toml:110`; force-disabled under proofs, `set_defaults.cpp:1815`) — rebuilds the private SAT solver and CnfStream on a pop to level 0. — [C]
- **Bit-level propagation** — `bv_solver_bitblast.cpp:147` — all BV — `--bv-propagate` default `true`, **expert** (`bv_options.toml:36`) **but set to false for the default `BITBLAST` solver** at `set_defaults.cpp:788` — runs the SAT backend in `setPropagateOnly()` at non-full effort. **So the documented default is not the effective default.** — [C]
- **BV equality engine / eager evaluation** — `theory_bv.cpp:81` — all BV — `--bv-eq-engine` default `true`, **expert**; `--bv-eager-eval` default `false`, `regular` (`bv_options.toml:126,134`) — adds CONCAT/MULT/ADD/EXTRACT as congruence kinds. — [C]
- **`TheoryBV::getValue`** — `theory_bv.cpp:347` — all BV — on by default — bottom-up evaluation of a term from bit-level SAT assignments, cached per SAT context. — [C]
- **`ppStaticLearn` power-of-two case split** — `theory_bv.cpp:301` — QF_BV — on by default, though the source notes it is "only useful in combination with `--bv-intro-pow2`" — for `(bvadd (bvshl 1 x) (bvshl 1 y)) = (bvshl 1 z)` emits `b=0 ∨ c=0 ∨ b=c`. — [C]
- **`ppRewrite` overflow elimination** — `theory_bv.cpp:202` — BV with the SMT-LIB 2.7 overflow predicates — on by default, **skipped when `--solve-bv-as-int != off`** — applies `UltAddOne` and `eliminateOverflows`. — [C]
- **`ppStaticRewrite`: SolveEq / BitwiseEq / extend-eq-const** — `theory_bv.cpp:228` — all BV — `SolveEq` on by default; `BitwiseEq` behind `--bitwise-eq` (default `false`, **expert**); `SignExtendEqConst`/`ZeroExtendEqConst` behind `--bv-rw-extend-eq` (default `false`, **expert**, help text: "useful on BV/2017-Preiner-scholl-smt08"). — [C]
- **`BvPpAssert` — extract-over-variable substitution** — `src/theory/bv/bv_pp_assert.cpp:33` — all BV — on by default (from `theory_bv.cpp:184`) — turns `x[h:l] = c` into `x -> sk1 :: c :: sk2` with purification skolems and a `TrustId::BV_PP_ASSERT` step. — [C]
- **`BVProofRuleChecker`** — `src/theory/bv/proof_checker.cpp:26` — BV with proofs — checks `MACRO_BV_BITBLAST` (trusted, depth 2), `BV_BITBLAST_STEP`, `BV_POLY_NORM`, `BV_POLY_NORM_EQ` (odd-multiplier cancellation), `BV_EAGER_ATOM`. — [C]
- **`MacroRewriteElaborator` (BV)** — `src/theory/bv/macro_rewrite_elaborator.cpp:30` — BV with proofs — expands the six `MACRO_BV_*` rewrite rules into `ACI_NORM` / `CONG` / `TRANS` chains. — [C]
- **`IntBlaster`** — `src/theory/bv/int_blaster.cpp:311` — QF_BV → QF_NIA — `--solve-bv-as-int=MODE` default `OFF`, `regular`, `no_support=["proofs"]` — maps each BV term to an integer term mod 2ᵏ; `bvand` becomes a granularity-sized block sum, shifts become ITE-exponentiation, signed comparisons go through `uts`. `--bvand-integer-granularity=N` default `1`, max 8, **expert**; `--bv-to-int-use-pow2` default `false`, **expert** (uses the internal `pow2` operator instead of an ITE chain). — [C]

### 6.2 BV arithmetic abstraction (CEGAR) — present, default-off

- **`AbstractionModule`** — `src/theory/bv/abstract/abstraction_module.cpp:28`, built at `src/CMakeLists.txt:660` — QF_BV etc. — **reachable but default-off**: `--bv-abstraction` default `false`, **expert** (`bv_options.toml:142`), instantiated at `bv_solver_bitblast.cpp:126` **only under `--bv-solver=bitblast`** (the internal solver never constructs it) — replaces binary `bvmul` / `bvudiv` / `bvurem` of width ≥ threshold with fresh opaque constants before bit-blasting, then refines by lemmas. **This is a full CEGAR loop over multiplier and divider circuits, shipped off by default and unavailable in the proof-producing configuration.** — [C] [P] (Niemetz/Preiner/Zohar, *Scalable Bit-Blasting with Abstractions*, CAV 2024, cited in `abstraction_module.h:14`)
- **Abstraction threshold** — `abstraction_module.cpp:31,51` — `--bv-abstraction-size=N` default `33`, min 3, **expert**. — [C]
- **Theory-leaf guard** — `abstraction_module.cpp:100` — QF_ABV / QF_AUFBV — refuses to descend below non-BV/non-Bool theory terms, so shared terms are not duplicated (soundness under theory combination). — [C]
- **Tier-1/2 refinement** — `abstraction_module.cpp:170` — adds the *first* violated symbolic/value lemma per abstracted term per round; ported from Bitwuzla. — [C] [P]
- **Multiplication lemma schemes (19)** — `abstraction_lemmas.h:50` — `MUL1_POW2`, `MUL2_NEG_POW2`, `MUL3_IC`, `MUL4_ODD`, `MUL5`…`MUL19` — power-of-two shifts, inverse conditions, parity, and 15 opaque bit-level invariants on `t = x*s`. — [C]
- **Unsigned-division lemma schemes (37)** — `abstraction_lemmas.h:74` — `UDIV1_POW2`, `UDIV37` (s=1), `UDIV2`…`UDIV36` — self-division, div-by-zero = all ones, `t ≤ x`, plus 30 bit-level invariants. — [C]
- **Unsigned-remainder lemma schemes (15)** — `abstraction_lemmas.h:112` — `UREM1_POW2`, `UREM2`…`UREM15` — `t < s`, `s=0 ⇒ t=x`, `x<s ⇒ t=x`, … — [C]
- **Tier-3 value instantiation** — `abstraction_module.cpp:212` — budget = bit-width / `--bv-abstraction-value-limiter` (default `8`, **expert**) — adds `(x=v_x ∧ s=v_s) ⇒ t = op(v_x,v_s)` a bounded number of times. — [C]
- **Tier-4 bit-blasting fallback** — `abstraction_module.cpp:222` — once the tier-3 budget is spent, asserts `t = op(x,s)`, forcing the real circuit. — [C]
- **The CEGAR loop itself** — `bv_solver_bitblast.cpp:450` — **only at `EFFORT_FULL`** — re-solves the private SAT instance after asserting refinement lemmas through `BITVECTOR_EAGER_ATOM`, never through `d_im.lemma()`. — [C]

### 6.3 The bit-blasting circuits

- **Atom strategy table** — `src/theory/bv/bitblast/bitblaster.h:102` — all BV — on by default — per-`Kind` atom blasters; anything unregistered maps to `UndefinedAtomBBStrategy` (an `Unreachable`). — [C]
- **`DefaultEqBB`** — `bitblast_strategies_template.h:48` — AND of bitwise IFFs. — [C]
- **`DefaultUltBB` / `DefaultUleBB`** — `:92, :107`, helper `bitblast_utils.h:283` — a **ripple comparator**: `res_i = (a_i↔b_i ∧ res_{i-1}) ∨ (¬a_i ∧ b_i)`, seeded with equality for `≤`. — [C]
- **`AdderUltBB` (subtraction-based `<`)** — `:70` — **dead/unreachable**: defined but never installed in `initAtomBBStrategies`; its only reference is its own definition. Would encode `a<b` as `¬carry_out(a + ¬b + 1)`. — [C]
- **`DefaultSltBB` / `DefaultSleBB`** — `:137, :151`, helper `bitblast_utils.h:307` — unsigned compare of the low n−1 bits plus a sign-bit case split. — [C]
- **`DefaultUgtBB` / `UgeBB` / `SgtBB` / `SgeBB`** — `:122, :129, :165, :173` — swap operands and delegate. — [C]
- **`DefaultVarBB` (leaf)** — `:200` — the default strategy for *every* unregistered term kind — introduces `BITVECTOR_BIT` literals; also how abstraction constants and foreign-theory leaves are handled. — [C]
- **Boolean gates** — `DefaultConstBB` `:215`, `NotBB` `:245`, `ConcatBB` `:257`, `AndBB` `:283`, `OrBB` `:305`, `XorBB` `:327`, `XnorBB` `:349`, `NandBB` `:368`, `NorBB` `:377` — bit-parallel. — [C]
- **`DefaultCompBB`** — `:386` — `bvcomp` = 1-bit AND of bitwise equalities. — [C]
- **`DefaultAddBB` — ripple-carry adder** — `:454`, helper `bitblast_utils.h:243` — n-ary add folded as a chain of ripple-carry adders (`sum = a⊕b⊕c`, `c' = ab ∨ (a⊕b)c`). **No carry-lookahead, no carry-save, no Wallace tree.** — [C]
- **`DefaultSubBB` / `DefaultNegBB`** — `:478, :497` — `a-b = adder(a, ¬b, 1)`; `-a = adder(¬a, 0, 1)`. — [C]
- **`DefaultMultBB` — shift-and-add multiplier** — `:408`, helper `shiftAddMultiplier` at `bitblast_utils.h:262` — partial products `b_k ∧ a_j` accumulated with an inline ripple carry. The commented-out no-overflow specialisation at `:415-434` is **dead code**. — [C]
- **`uDivModRec` — recursive restoring divider** — `:519` — recurses on `a>>1` for `rec_width` steps, doubling quotient and remainder, conditionally subtracting `b` via a ripple adder with `¬b+1`: an O(n) chain of n-bit adders, O(n²) gates. — [C]
- **`UdivUremBB` — division-by-zero patch** — `:591` — ITE-muxes `b=0 ⇒ quot = 1…1, rem = a`, matching SMT-LIB totality. — [C]
- **`DefaultUdivBB` / `DefaultUremBB`** — `:626, :638` — project quotient/remainder out of `UdivUremBB`. — [C]
- **`DefaultSdivBB` / `SremBB` / `SmodBB`** — `:650, :659, :668` — **dead**: bodies are `Unimplemented()` *and* the term table maps `BITVECTOR_SDIV/SREM/SMOD` to `UndefinedTermBBStrategy` (`bitblaster.h:167-172`). Signed division is always removed by the rewriter's `SdivEliminate` / `SremEliminate` / `SmodEliminate`. — [C]
- **`DefaultShlBB` — barrel shifter** — `:678` — ⌈log₂ n⌉ mux stages shifting by 2ˢ, plus a `b < n` guard zeroing the result on over-shift. — [C]
- **`DefaultLshrBB` / `DefaultAshrBB`** — `:738, :798` — same barrel structure; `ashr` fills with the sign bit and saturates on over-shift. — [C]
- **`DefaultUltbvBB` / `DefaultSltbvBB`** — `:860, :874` — the 1-bit-result forms of the comparators, for the internal `BITVECTOR_ULTBV` / `SLTBV` kinds produced by `IneqElimConversion`. — [C]
- **`DefaultIteBB`** — `:888` — per-bit `(¬c ∨ t_i) ∧ (c ∨ e_i)`. — [C]
- **`DefaultExtractBB` / `DefaultSignExtendBB`** — `:909, :958` — slicing; sign-extend replicates the top bit. — [C]
- **`DefaultRepeatBB` / `ZeroExtendBB` / `RotateRightBB` / `RotateLeftBB`** — `:935, :946, :988, :999` — registered but `Unimplemented()`: **reachable only as an error path**, since the rewriter always eliminates these kinds. — [C]
- **`NodeBitblaster`** — `src/theory/bv/bitblast/node_bitblaster.cpp:27` — used by `BVSolverBitblast` — blasts to plain Boolean `Node`s, rewriting the atom before and after, caching atoms and term bit-vectors. — [C]
- **`BBProof` / `BitblastProofGenerator`** — `bitblast/proof_bitblaster.cpp:1`, `bitblast_proof_generator.cpp:1` — used by `BVSolverBitblastInternal` — records a `TConvProofGenerator` chain so each `atom <=> bb(atom)` lemma carries a `BV_BITBLAST_STEP` / `MACRO_BV_BITBLAST` proof. — [C]

### 6.4 The BV rewriter

- **Dispatch table** — `src/theory/bv/theory_bv_rewriter.cpp:851` (`initializeRewrites`), entry points `:70` / `:84` — per-`Kind` `RewriteResponse` built from `LinearRewriteStrategy<...>` chains; pre-rewrite applies only the flattening subset, post-rewrite the full set. — [C]
- **`theory_bv_rewrite_rules_core.h` — 10 rules** — `:29-354` — on by default — `ConcatFlatten, ConcatExtractMerge, ConcatConstantMerge, ExtractWhole, ExtractConstant, ExtractConcat, ExtractExtract, FailEq, SimplifyEq, ReflexivityEq`. — [C]
- **`..._normalization.h` — 17 rules** — `:39-1334` — on by default except `BitwiseEq` — `ExtractNot, ExtractSignExtend, FlattenAssocCommut, AddCombineLikeTerms, MultSimplify, MultDistribConst, MultDistrib, SolveEq, BitwiseEq, NegMult, NegSub, NegAdd, AndSimplify, FlattenAssocCommutNoDuplicates, OrSimplify, XorSimplify, BitwiseSlicing`. — [C]
- **`SolveEq` (linear equality solving over BV)** — `..._normalization.h:531` — on by default in `ppStaticRewrite` — moves terms to one side and isolates a variable when the coefficient permits. — [C]
- **`BitwiseSlicing`** — `..._normalization.h:1334` — on by default at *post*-rewrite only (`theory_bv_rewriter.cpp:424`) — slices `bvand`/`bvor`/`bvxor` with a constant argument into concatenations of constant and variable slices; exposed as `BV_BITWISE_SLICING`. — [C]
- **Multiplication normalisation** — `MultSimplify` `:114`, `MultDistribConst` `:367`, `MultDistrib` `:441`, `FlattenAssocCommut` `:488` — flatten and sort, fold constants, distribute constants over sums (distribution at post-rewrite only). — [C]
- **`..._simplification.h` — 46 rules** — `:34-1893` — on by default — BV-ITE (9), shift-by-constant (3), bitwise (5), unsigned/signed inequality (11: `UltZero, UltOne, UltOnes, UltSelf, UleZero, UleSelf, ZeroUle, UleMax, SltSelf, UgtUrem, UltAddOne`), div/rem (6: `UdivPow2, UdivZero, UdivOne, UremPow2, UremOne, UremSelf`), mult (4: `MultPow2, ExtractMultLeadingBit, MultSlice, MultSltMult`), extension (5: `MergeSignExtend, ZeroExtendEqConst, SignExtendEqConst, ZeroExtendUltConst, SignExtendUltConst`), misc (`NegIdemp, ShiftZero, IneqElimConversion`). — [C]
- **`SignExtendUltConst` / `ZeroExtendUltConst`** — `:1578, :1496` — on by default in `RewriteUlt` — solves `(sign_extend x) < c` by reducing the constant to the original width. — [C]
- **`IneqElimConversion`** — `:1675` — converts BV inequality atoms into the 1-bit `BITVECTOR_ULTBV` / `SLTBV` term form. — [C]
- **`MultSltMult`** — `:1893`, also a proof rule `MACRO_BV_MULT_SLT_MULT` — cancels a common odd multiplier on both sides of a signed inequality. — [C]
- **`..._operator_elimination.h` — 28 rules** — `:29-777` — on by default — `SizeEliminate, UgtEliminate, UgeEliminate, SgtEliminate, SgeEliminate, SleEliminate, UleEliminate, SubEliminate, RepeatEliminate, RotateLeftEliminate, RotateRightEliminate, NandEliminate, NorEliminate, XnorEliminate, SdivEliminate, SremEliminate, SmodEliminate, ZeroExtendEliminate, RedorEliminate, RedandEliminate, NegoEliminate, UaddoEliminate, SaddoEliminate, UmuloEliminate, SmuloEliminate, UsuboEliminate, SsuboEliminate, SdivoEliminate`. **This file is why the bit-blaster's `Unimplemented()` strategies are unreachable.** — [C]
- **Overflow-predicate elimination** — `theory_bv_rewriter.cpp:155` (`eliminateOverflows`), `:505` (`RewriteOverflow`) — on by default, **deliberately skipped under `--solve-bv-as-int`** — expands each overflow predicate into a widened arithmetic comparison. — [C]
- **`..._constant_evaluation.h` — 28 rules** — `:29-566` — on by default — the `Eval*` family for every operator; note a **commented-out duplicate `EvalComp` at `:118`** (the live one is at `:527`). — [C]
- **`rewriteViaRule` (proof-rewrite entry)** — `theory_bv_rewriter.cpp:97` — maps `MACRO_BV_EQ_SOLVE` (via `arith::PolyNorm`), `MACRO_BV_EXTRACT_CONCAT`, `MACRO_BV_{OR,AND,XOR}_SIMPLIFY`, `MACRO_BV_AND_OR_XOR_CONCAT_PULLUP`, `MACRO_BV_MULT_SLT_MULT`, `MACRO_BV_CONCAT_{EXTRACT,CONSTANT}_MERGE`, `BV_UMULO_ELIM`, `BV_SMULO_ELIM`, `BV_BITWISE_SLICING`, `BV_REPEAT_ELIM` onto the C++ rules. — [C]

### 6.5 Floating-point

- **SymFPU is not optional** — `CMakeLists.txt:652` — `find_package(SymFPU REQUIRED)`; commit `40bdec00…` is auto-downloaded (`cmake/FindSymFPU.cmake:32`). `--use-mpfr` only swaps the *literal constant-folding* backend, not the word-blaster. — [C]
- **`TheoryFp`** — `src/theory/fp/theory_fp.cpp:31` — all FP logics — enabled unless `--no-fp` (`fp_options.toml:5`, default `true`, **expert**); with `--no-fp`, `preRegisterTerm` throws `SafeLogicException` (`:766`) and `getTheoryRewriter()` returns `nullptr` (`:62`). — [C]
- **Experimental FP formats** — `theory_fp_rewriter.cpp:1605`, `theory_fp.cpp:773` — FP with formats other than Float32/Float64 — `--fp-exp` default `false`, **expert** — without it, `checkForExperimentalFloatingPointType` **rejects any sort other than (8,24) and (11,53)** at pre-rewrite and pre-registration. — [C]
- **`FpWordBlaster`** — `src/theory/fp/fp_word_blaster.cpp:836` — all FP — on by default — instantiates SymFPU's algorithms over cvc5 `Node`s (`traits::rm/prop/sbv/ubv`, `:115-190`), producing pure BV/Boolean circuits. — [C]
- **Word-blasted FP operators** — `fp_word_blaster.cpp:958-1119` — `FLOATINGPOINT_ABS, NEG, SQRT, RTI, REM, MAX_TOTAL, MIN_TOTAL, ADD, MULT, DIV, FMA, TO_FP_FROM_FP, FP (from 3 BVs), TO_FP_FROM_IEEE_BV, TO_FP_FROM_SBV, TO_FP_FROM_UBV`. — [C]
- **Word-blasted FP predicates** — `:1135-1235` — `EQUAL` (`symfpu::smtlibEqual`), `LEQ`, `LT`, `IS_NORMAL, IS_SUBNORMAL, IS_ZERO, IS_INF, IS_NAN, IS_NEG, IS_POS`. — [C]
- **Word-blasted FP→BV conversions** — `:1240+` — `TO_UBV_TOTAL` / `TO_SBV_TOTAL` with an explicit "undefined value" third argument. — [C]
- **`buildComponents` — the part that is *not* word-blasted** — `:814` — FP theory *leaves* and `FLOATINGPOINT_TO_FP_FROM_REAL` are represented by six uninterpreted component kinds
  (`COMPONENT_NAN/INF/ZERO/SIGN/EXPONENT/SIGNIFICAND`) plus a `valid()` well-formedness assertion. — [C]
- **FP↔Real axiomatisation (abstraction + refinement)** — `theory_fp.cpp:590` (`registerTerm`), `:152` (`refineAbstraction`), loop at `:818` — QF_FPLRA / FPLRA and any FP+arith — on by default when such terms occur — **`fp.to_real` and `(_ to_fp) rm r` are axiomatised, not word-blasted**: purified into a skolem constrained by registration lemmas (NaN/Inf/zero cases, sign preservation) and refined lazily with `fp.leq`/`fp.geq`-anchored "cell" lemmas against model values. — [C]
- **Classification aliasing lemmas** — `theory_fp.cpp:614` — `isNaN`/`isZero`/`isInf` are additionally equated to explicit equalities with NaN / ±0 / ±∞ constants for the equality engine. — [C]
- **Lazy word-blasting** — `theory_fp.cpp:753, :857` — `--fp-lazy-wb` default `false`, **expert** — moves word-blasting from `registerTerm` to `preNotifyFact`, so only asserted facts are blasted. **Default off.** — [C]
- **`FpExpandDefs` (partial-operator totalisation)** — `src/theory/fp/fp_expand_defs.cpp:74` — all FP — on by default — `fp.min`/`fp.max` → `*_TOTAL` with an `APPLY_UF` tie-breaker skolem; `fp.to_ubv`/`to_sbv` → `*_TOTAL` with an undefined-case skolem; `fp.to_real` → `TO_REAL_TOTAL`. — [C]
- **`TheoryFpRewriter`** — `theory_fp_rewriter.cpp:1207,1601,1646` — all FP — on by default — roughly 60 rewrites including `convertSubtractionToAddition, removeDoubleNegation, compactAbs, breakChain, ieeeEqToEq, geqToleq, gtTolt, reorderFPEquality, reorderBinaryOperation, reorderFMA, removeSignOperations, compactRemainder, compactMinMax, leqId, ltId, toFPSignedBV, fpLiteral, roundingModeBitBlast`, plus constant folders for every operator, predicate and conversion. — [C]
- **FP has no proof checker** — `theory_fp.cpp:69` — `TheoryFp::getProofChecker()` returns `nullptr`. **FP reasoning is proof-opaque in cvc5.** — [C]

## 7. The propositional layer, SAT back ends, and decision heuristics

- **`PropEngine`** — `src/prop/prop_engine.cpp:63` — all — on by default — owns `SkolemDefManager`, `TheoryProxy`, the SAT solver, the `CnfStream`, and (only with `--produce-proofs`, `:96`) `PropPfManager`. — [C]
- **`CnfStream` — Tseitin encoding** — `src/prop/cnf_stream.cpp:496` (`toCNF`), `:318-495` (`handleXor/Or/And/Implies/Iff/Ite`) — all — on by default — one definition literal per Boolean connective, standard clause sets. — [C]
- **CNF optimisation: top-level clause flattening** — `cnf_stream.cpp:569-760` (`convertAndAssertAnd/Or/Xor/Iff/Implies/Ite`), polarity push at `:785` — all — on by default — asserted formulas are traversed with a polarity flag: a top-level AND becomes separate assertions, a top-level OR becomes one clause directly, negation is pushed into the recursion. **No auxiliary variable is created for the assertion spine.** — [C]
- **CNF optimisation: shared definition-literal cache** — `cnf_stream.cpp:159` — all — on by default — `d_nodeToLiteralMap` caches literals structurally (DAG-aware), so a shared subformula gets exactly one definition. — [C]
- **`FormulaLitPolicy`** — `cnf_stream.cpp:166-215` — all — `INTERNAL` / `TRACK` / `TRACK_AND_NOTIFY` / `TRACK_AND_NOTIFY_VAR` — controls whether *formula* literals (not just theory atoms) are back-mapped and notified; the BV private stream uses `INTERNAL` (`bv_solver_bitblast.cpp:381`). — [C]
- **`ensureLiteral`** — `cnf_stream.cpp:118` — forces a literal for a node without asserting it; used for assumption-based unsat cores and the BV bit-blaster. — [C]
- **`dumpDimacs`** — `cnf_stream.cpp:815` — expert debug path. — [C]
- **`TheoryProxy` (CDCL(T) hub)** — `src/prop/theory_proxy.cpp:40` — all — on by default — bridges SAT assignments to `TheoryEngine::check`, `theoryPropagate` (`:275`), `explainPropagation` (`:288`), `notifySatClause` (`:327`), `getNextDecisionRequest` (`:380`). — [C]
- **`ZeroLevelLearner` construction condition** — `theory_proxy.cpp:60` — **constructed only if** `--deep-restart != none`, `-o learned-lits`, `--produce-learned-literals`, `--compute-partitions > 0`, or `--lemma-inprocess != none`. Otherwise `d_zll == nullptr` and **no level-0 tracking happens at all**. — [C]
- **`ZeroLevelLearner`** — `src/prop/zero_level_learner.cpp:27`, `notifyAsserted` `:180` — records every literal asserted at SAT level 0 and classifies it. — [C]
- **Learned-literal classification** — `zero_level_learner.cpp:234` — `PREPROCESS_SOLVED`, `PREPROCESS`, `INPUT`, `SOLVABLE` (via `TheoryEngine::solve`, `:424`), `CONSTANT_PROP`, `INTERNAL`. — [C]
- **Deep-restart threshold** — `zero_level_learner.cpp:167` — `--deep-restart-factor=F` default `3.0`, **expert** — restart when non-learning assertions exceed `#input atoms × F`; the `--deep-restart` mode selects which learned types count (`INPUT`, `INPUT_AND_SOLVABLE`, `INPUT_AND_PROP`, `ALL`). — [C]
- **`LearnedDb`** — `src/prop/learned_db.cpp:20` — six context-dependent node sets, one per `LearnedLitType`, backing `get-learned-literals`. — [C]
- **`LemmaInprocess`** — `src/prop/lemma_inprocess.cpp:49` — all — `--lemma-inprocess=MODE` default `NONE`, **expert** (`theory_options.toml:107`; modes `full`/`light`); **incompatible with proofs** (`set_defaults.cpp:1160`) — rewrites each outgoing lemma's literals under the zero-level substitution map, replacing a literal when its substituted form is constant or already has a SAT literal. **This is inprocessing at the lemma boundary, and it is off by default.** — [C]
- **Lemma-inprocess policy** — `lemma_inprocess.cpp:83`, `zero_level_learner.cpp:265` — `--lemma-inprocess-subs=MODE` default `SIMPLE`, **expert** (only leaf RHS); `--lemma-inprocess-infer-eq-lit` default `false`, **expert**. — [C]
- **`TheoryPreregistrar`** — `src/prop/theory_preregistrar.cpp:75` — all — `--preregister-mode=MODE` default **`EAGER`**, `regular` (`prop_options.toml:98`) — `eager` preregisters at SAT-literal creation and re-registers on backtrack (`:91`); `lazy` preregisters only when the literal is asserted (`:120`). — [C]
- **Backtrack re-registration cache** — `theory_preregistrar.cpp:91`, notify at `:30` — newest-to-oldest re-registration of literals whose registration level exceeded the new SAT level. — [C]
- **`SkolemDefManager`** — `src/prop/skolem_def_manager.cpp:26,52` — all (mainly quantifiers, strings, ITE removal) — on by default, but *activation tracking* only if the decision engine or preregistrar asks (`theory_proxy.cpp:87,98`) — maps skolems to their defining lemmas and reports which definitions become active. — [C]
- **`ProofCnfStream`** — `src/prop/proof_cnf_stream.cpp:33` — with proofs — mirrors `CnfStream` while emitting the 22 `CNF_*` proof steps for every clause. — [C]
- **`PropPfManager`** — `src/prop/prop_proof_manager.cpp:36`, `getProof` `:230` — with proofs — connects the SAT refutation to the CNF proof, normalises and registers clauses, extracts unsat-core lemmas (`:133`) and clauses (`:182`), drives proof logging. — [C]
- **Prop-level `ProofPostprocessCallback`** — `src/prop/proof_post_processor.cpp:13` — with proofs — expands `ASSUME` leaves of the SAT proof into their CNF-stream proofs, with a "blocked" set to stop traversal. — [C]
- **`SatSolverFactory`** — `src/prop/sat_solver_factory.cpp:23` (CDCL(T)) and `:38` (BV) — two factories: `--sat-solver` → {MINISAT, CADICAL}; `--bv-sat-solver` → {CADICAL, KISSAT, CRYPTOMINISAT}. — [C]
- **Default CDCL(T) SAT backend = CaDiCaL** — `prop_options.toml:5`, `common` — **but switched to MiniSat whenever `--incremental` is on and the user did not set it** (`set_defaults.cpp:408`, reason "incremental", "due to performance"). — [C]
- **Default BV SAT backend = CaDiCaL** — `bv_options.toml:5`, `regular` — Kissat and CryptoMiniSat require build flags. — [C]
- **`CadicalSolver`** — `src/prop/cadical/cadical.cpp:93,288` — all — **CaDiCaL is a required dependency** (`CMakeLists.txt:577`) — sets `quiet=1`; when an external propagator is connected it disables `walk`, `lucky`, `ilb`, `ilbassumptions`. — [C]
- **`CadicalPropagator` (IPASIR-UP CDCL(T) integration)** — `src/prop/cadical/cdclt_propagator.cpp:25` — all with `--sat-solver=cadical` — on by default — implements `notify_assignment` (`:25`), `notify_fixed_assignment` (`:90`), `notify_new_decision_level` (`:120`), `notify_backtrack` (`:130`), `cb_check_found_model` (`:206`), `cb_decide` (`:311`, external decision requests), `cb_propagate` (`:362`), `cb_add_reason_clause_lit` (`:386`, lazy explanations), `cb_has_external_clause` / `cb_add_external_clause_lit` (`:427`/`:439`), user push/pop with activation literals (`:589`/`:597`/`:604`), and phase hints (`:691`). — [C]
- **CaDiCaL `ProofTracer` (LRUP)** — `src/prop/cadical/proof_tracer.cpp:1`, doc at `proof_tracer.h:26` — with proofs — connected only if `env.isSatProofProducing()` (`cadical.cpp:307`) — tracks original vs derived clauses and antecedents, reconstructs the unsat core from final clause ids. — [C]
- **`CadicalSolver::attachProofManager`** — `cadical.cpp:315` — **a stub, "not implemented yet"** — the MiniSat-style `PropPfManager` attachment is a no-op for CaDiCaL. — [C]
- **`ResourceLimitTerminator`** — `cadical.cpp:126` — spends `Resource::BvSatStep` and terminates CaDiCaL when the budget runs out. — [C]
- **Clause-learner plugin hook** — `cadical.cpp:301` — only with registered API plugins — forwards CaDiCaL-learned clauses to the theory proxy. — [C]
- **`MinisatSatSolver` (bundled MiniSat 2.2 fork)** — `src/prop/minisat/minisat.cpp:1`, `README.minisat` — `--sat-solver=minisat`; **the default for incremental solving** — CDCL(T) core with theory-aware propagation (`CHECK_WITH_THEORY` / `CHECK_WITHOUT_THEORY` / `CHECK_FINAL`, `minisat/core/Solver.cc:1161`). — [C]
- **MiniSat decision heuristic** — `minisat/core/Solver.cc:718-810` — first asks `d_proxy->getNextDecisionRequest` (theory / justification heuristic), then falls back to the VSIDS activity order heap; random decisions with probability `random_var_freq` (`:778`). — [C]
- **MiniSat variable activity decay** — `Solver.cc:101`, wired from `--sat-var-decay` default `0.95`, **expert** (`prop_options.toml:37`) at `minisat.cpp:164`. — [C]
- **MiniSat clause activity decay** — `Solver.cc:102`, `--sat-clause-decay` default `0.999`, **expert** (`prop_options.toml:46`). — [C]
- **MiniSat random decisions** — `minisat.cpp:156,158` — `--random-freq=P` default **`0.0`**, **expert**; `--sat-random-seed=N` default `0` — **with defaults, MiniSat makes no random decisions at all.** — [C]
- **MiniSat restarts — Luby by default** — `Solver.cc:1755`, `luby_restart` defaults true (`:108`); `--restart-int-base=N` default `25`, `--restart-int-inc=F` default `3.0` — budget = `luby(inc, k) * first`; geometric `pow(inc,k)` if Luby is disabled. — [C]
- **MiniSat clause deletion (`reduceDB`)** — `Solver.cc:1369`, comparator `:1363` — sorts removable learnts by activity, keeps binaries and locked (reason) clauses, deletes the lower half plus anything under `cla_inc / |learnts|`; the limit grows via `learntsize_factor=1`, `learntsize_inc=1.5` (`:165-172`). — [C]
- **MiniSat phase saving** — `Solver.cc:693` (save on backtrack), `:800` / `:1959` (reuse on decision) — `opt_phase_saving = 2` (full) by default (`:106`); `rnd_pol` hard-coded false (`:156`); the `0x2` bit marks a user-preferred phase (`preferPhase`, `prop_engine.cpp:380`). — [C]
- **MiniSat conflict-clause minimisation** — `Solver.cc:950` (deep, `litRedundant` `:1027`) and `:978` (basic) — `opt_ccmin_mode = 2` (deep) by default (`:105`) — recursive self-subsuming resolution. — [C]
- **MiniSat garbage collection** — `Solver.cc:111` — compacts the clause allocator at 20% waste. — [C]
- **`SimpSolver` (variable/clause elimination)** — `src/prop/minisat/simp/SimpSolver.cc:67` — `--minisat-simplification=MODE` default **`ALL`**, **expert** (`prop_options.toml:72`; `clause-elim` disables variable elimination at `:695`) — bounded variable elimination (`grow=0`, `cl-lim=20`), subsumption (`sub-lim=1000`), self-subsumption. — [C]
- **`SimpSolver` asymmetric branching** — `SimpSolver.cc:39`, used at `:685` — **default false, and no cvc5 option exposes it** — shrinks clauses by asymmetric branching. — [C]
- **`SimpSolver` redundancy check (`rcheck`)** — `SimpSolver.cc:40`, guarded at `:61` — default false, and force-disabled under `--produce-unsat-cores`. — [C]
- **MiniSat DIMACS dump** — `SimpSolver.cc:121` — `--minisat-dump-dimacs` default `false`, **expert** — dumps clauses instead of solving. — [C]
- **`SatProofManager` (MiniSat resolution proofs)** — `src/prop/minisat/sat_proof_manager.cpp:1`, doc `sat_proof_manager.h:31` — with `--sat-solver=minisat --produce-proofs` — records every resolution and stitches them into a refutation only when the empty clause appears. — [C]
- **`OptimizedClausesManager`** — `src/prop/minisat/opt_clauses_manager.cpp:1` — MiniSat proofs only — re-inserts proofs of clauses that outlive the context level in which their proof was generated. — [C]
- **`CryptoMinisatSolver`** — `src/prop/cryptominisat.cpp:72` — BV only — **requires `-DUSE_CRYPTOMINISAT`** (`CMakeLists.txt:589-594`); without it `sat_solver_factory.cpp:96` is `Unreachable()` — non-incremental BV back end. — [C]
- **CryptoMiniSat XOR clauses — dead** — `src/prop/cryptominisat.cpp:109` — `addXorClause` has **no caller anywhere in `src`**; cvc5 never uses CryptoMiniSat's Gaussian/XOR reasoning. — [C]
- **CryptoMiniSat resource-bounded solve — unimplemented** — `cryptominisat.cpp:182` — `Unreachable()` ("not sure how to set different limits"); only a wall-clock `set_max_time` path exists (`:105`). — [C]
- **`KissatSolver`** — `src/prop/kissat.cpp:64` — BV only — **requires `-DUSE_KISSAT`**; otherwise `sat_solver_factory.cpp:74` is `Unreachable()`. — [C]
- **Kissat limitations** — `kissat.cpp:118,125,132` — `setTimeLimit` and incremental solving are `Unimplemented()`; `getUnsatAssumptions` is `Unreachable()`. **Kissat is usable only for one-shot, non-incremental bit-blasting without assumption-based conflicts.** — [C]

### 7.1 Decision heuristics

- **`DecisionEngine` / `DecisionEngineEmpty`** — `src/decision/decision_engine.cpp:18,31` — installed when `--decision=internal` (`theory_proxy.cpp:88`) — returns `undefSatLiteral`, leaving VSIDS to the SAT solver. — [C]
- **`--decision=MODE`** — `decision_options.toml:5` — default `INTERNAL`, `common`, **but overridden per logic** when the user did not set it (`set_defaults.cpp:1818-1888`): `JUSTIFICATION` for ALL/supersets, quantified logics, strings, QF_AUFBV/QF_ABV/QF_UFBV, and QF_BV *unless* `--bv-solver=bitblast-internal`; `STOPONLY` for QF_AUFLIA and QF_LRA; `INTERNAL` for SyGuS. — [C]
- **`JustificationStrategy`** — `src/decision/justification_strategy.cpp:60` — as above — walks a stack of assertions for an unjustified literal to decide on; when all assertions are justified it sets `stopSearch` (`:214`). — [C] [P] (ATGP-inspired)
- **`STOPONLY` mode** — `justification_strategy.cpp:40,183` — QF_AUFLIA and QF_LRA by default — uses justification only to detect that the formula is already satisfied, never to pick decisions. — [C]
- **Justification skolem ordering** — `justification_strategy.cpp:42` — `--jh-skolem=MODE` default `FIRST`, **expert**. — [C]
- **Justification skolem relevance** — `justification_strategy.cpp:43`, consumed at `theory_proxy.cpp:85` — `--jh-skolem-rlv=MODE` default `ASSERT`, **expert**. — [C]
- **Activity-based relevance ordering** — `justification_strategy.cpp:31,39` — `--jh-rlv-order` default `false`, **expert**. — [C]
- **`AssertionList` / `JustifyStack` / `JustifyInfo` / `JustifyCache` / `JustifyStats`** — `src/decision/{assertion_list,justify_stack,justify_info,justify_cache,justify_stats}.cpp` — the context-dependent assertion list with activity monitoring, the DFS stack over Boolean structure, per-node justification state, and a `CDInsertHashMap` cache of justification values read from the SAT solver. — [C]

## 8. Arithmetic — linear, nonlinear, and finite fields

### 8.0 Four findings to read before the list

1. **cvc5 generates no Gomory or MIR cuts of its own.** `GmiInfo` / `MirInfo`
   (`src/theory/arith/linear/approx_simplex.cpp:1366`, `:1329`) are populated by
   *reading GLPK's cut pool* — `glp_ios_cut_get_aux_rows`,
   `glp_ios_cut_get_mir_cset`, dispatched on `GLP_RF_GMI` / `GLP_RF_MIR` at
   `:1635` / `:1641` — after switching GLPK's own generator on with
   `parm.gmi_cuts = GLP_ON` at `:1840`. cvc5 then *reconstructs and replays* the
   cut exactly in rationals (`attemptGmi` `:2232`, `applyCMIRRule` `:270`). The
   whole block is inside `#ifdef CVC5_USE_GLPK` (`:30`…`:3617`). cvc5's own cuts
   are only: branch splits, round-robin branches, cut-all-bounded, and Diophantine
   cuts. `[C]`
2. **GLPK is doubly gated off.** `option(USE_GLPK …)` has no default value, so it
   is OFF (`CMakeLists.txt:133`) and `configure.sh:147` leaves `glpk=default`, so
   `-DUSE_GLPK` is never passed. Without it `ApproximateSimplex::enabled()`
   returns `false` (`approx_simplex.cpp:3636-3642`) and
   `mkApproximateSimplexSolver` raises
   `Unimplemented() << "Approximate simplex solver requires GLPK"` (`:3629`).
   And `--use-approx` itself ships `default = "false"`
   (`arith_options.toml:224`). `[C]`
3. **`--use-soi` ships `default = "false"`** (`arith_options.toml:200`, block
   `:195-201`, `category = "expert"`), as does `--use-fcsimplex` (`:192`).
   **But** SOI is still reachable in a default build: `d_otherSDP` defaults to
   `d_soiSimplex` (`theory_arith_private.cpp:3478`), so SOI *is* the second-pass
   simplex regardless of the flag. `[C]`
4. **LibPoly is on by default only via `configure.sh`** (`configure.sh:150`
   `poly=ON`); the CMake `option(USE_POLY …)` itself defaults OFF
   (`CMakeLists.txt:136`), and safe mode disables it (`CMakeLists.txt:610-614`).
   **CoCoA defaults OFF** (`configure.sh:151`, `CMakeLists.txt:130`) — a hard
   error for finite fields, and a silent warn-and-fall-back for
   `--nl-cov-lift=lazard`. `[C]`

### 8.1 `src/theory/arith/` top level

- **`TheoryArith`** — `src/theory/arith/theory_arith.cpp:238` — all `Int`/`Real` logics — on by default — dispatches `postCheck` to the linear solver, then at last call to `NonlinearExtension` if the logic is non-linear (`:88-94`). — [C]
- **Nonlinear-extension gating** — `theory_arith.cpp:90-94` — non-linear logics only — on by default — linear logics never construct `nl::NonlinearExtension`. — [C]
- **Transcendental logic exception** — `theory_arith.cpp:106-140` — NRA/NIA with `sin`/`exp`/`iand`/`pow2` — throws unless `--arith-exp` (default `true`, `arith_options.toml:422`) **and** `--nl-ext=full`. — [C]
- **CoCoA global manager init** — `theory_arith.cpp:54-57` — requires CoCoA. — [C]
- **`ArithRewriter`** — `arith_rewriter.cpp:284` / `:299` — all arith — on by default — canonicalises sums/products/atoms into the `rewriter::Sum` ordered normal form. — [C]
- **Atom rewriting / relation evaluation** — `arith_rewriter.cpp:314` (`preRewriteAtom`), `:357` (`postRewriteAtom`) — all arith — on by default — evaluates constant relations, eliminates `<`, `>`, `<=` in favour of `>=`, normalises to `(>= p c)`. — [C]
- **Extended equality rewrite** — `arith_rewriter.cpp:474` — LIA/LRA/NIA/NRA — used when `--arith-rewrite-equalities` is off — non-term-preserving equality normalisation, preprocess only. — [C]
- **Int div/mod total rewriting** — `arith_rewriter.cpp:990, :1015` — LIA/NIA — on by default — folds div/mod by constants, sign-normalises negative divisors. — [C]
- **IAND / PIAND rewriting** — `arith_rewriter.cpp:1162, :1213`, reached via `postRewriteExpert` `:596` — NIA with `iand` (from `--solve-bv-as-int`) — `--arith-exp` (default `true`). — [C]
- **Transcendental rewriting** — `arith_rewriter.cpp:1344` — NRA + transcendentals — expert path via `--arith-exp` — folds `sin 0`, `cos→sin`, `tan→sin/cos`. — [C]
- **`expandPowConst`** — `arith_rewriter.cpp:1698`, reached at `:604` — NRA/NIA — `--arith-exp` — unrolls `x^k` for constant `k`. — [C]
- **`rewriteIneqToBv`** — `arith_rewriter.cpp:1589, :1603` — mixed Int/BV (`bv2nat`/`int2bv`) — **did not verify a dedicated flag**; invoked from the rewriter — turns integer inequalities over `bv2nat` back into BV comparisons. — [C]
- **Proof-rewrite registry** — `arith_rewriter.cpp:124-131`, dispatch `:137` — `ARITH_POW_ELIM`, `MACRO_ARITH_INT_EQ_CONFLICT`, `MACRO_ARITH_INT_GEQ_TIGHTEN`, `MACRO_ARITH_STRING_PRED_ENTAIL`. — [C]
- **RARE arith rules** — `src/theory/arith/rewrites` (37) and `rewrites-transcendentals` (8) — on by default — `arith-div-total-zero-*`, `arith-int-div-total-*`, `arith-elim-gt/lt/leq`, `arith-leq-norm`; `arith-sine-zero`, `arith-sine-pi2`, `arith-cosine-elim`, `arith-tangent-elim`, `arith-{sec,csc,cot}-elim`, `arith-pi-not-int`. — [C]
- **`rewriter::Sum` ordered monomial IR** — `src/theory/arith/rewriter/addition.h:30` — a `std::map<monomial, multiplicity>` making the leading term cheap to find. — [C]
- **`LeafNodeComparator` / `TermComparator`** — `rewriter/ordering.h:23` — total order on leaves (rationals < RANs < reals < ints < vars < rest) fixing the canonical form. — [C]
- **`buildIntegerInequality` (GCD/LCM tightening)** — `rewriter/rewrite_atom.h:52` — LIA/NIA/IDL — on by default — normalises coefficients to integers via GCD/LCM, then tightens the constant to a weak integer inequality. — [C]
- **`tryEvaluateRelation` / `…Reflexive`** — `rewriter/rewrite_atom.h:26, :35` — constant and real-algebraic evaluation of relations. — [C]
- **`PolyNorm`** — `src/theory/arith/arith_poly_norm.cpp:345` (`mkPolyNorm`), `:468` (`isArithPolyNorm`) — all arith **and BV** (`toNode` handles bit-vectors at `:244`) — on by default — decides "equal after ring normalisation", backing `ARITH_POLY_NORM`. — [C]
- **`isArithPolyNormRel`** — `arith_poly_norm.cpp:497`, premises `:615` — decides `(~ a b) ≡ (~ c d)` up to positive scaling, backing `ARITH_POLY_NORM_REL`. — [C]
- **`modCoeffs`** — `arith_poly_norm.cpp:89` — reduces coefficients modulo a constant; used for FF and BV poly norm. — [C]
- **`OperatorElim`** — `src/theory/arith/operator_elim.cpp:83` — LIA/LRA/NIA/NRA — on by default — eliminates `TO_INTEGER`, `IS_INTEGER`, `INTS_LOG2`, `DIVISION`, `INTS_DIVISION(_TOTAL)`, `INTS_MODULUS(_TOTAL)`, `ABS`, `SQRT`, and all six arc-trig functions into skolems plus defining lemmas. — [C]
- **Arc-function elimination via witness** — `operator_elim.cpp:~338` — NRA + transcendentals — `--arith-exp` (default `true`); `:67` throws `SafeLogicException` when off — replaces `arcsin(x)` by a witness `w` with `sin(w) = x` plus range bounds. — [C]
- **`getAxiomFor` / `getArithSkolemApp`** — `operator_elim.cpp:463, :486` — the div-by-zero / mod-by-zero uninterpreted skolem functions. — [C]
- **Branch-and-bound: rounding split** — `src/theory/arith/branch_and_bound.cpp:47` — LIA/NIA/IDL — `--arith-brab` default **`true`** (`arith_options.toml:512`) — emits `(or (= x n) (<= x n-1) (>= x n+1))` with a phase preference on `(= x n)`, trying the nearest integer first. — [C]
- **Branch-and-bound: plain split** — `branch_and_bound.cpp:124-140` — the fallback when `--arith-brab=false` — the classic `(or (<= x floor) (> x floor))`, proof rule `SPLIT`. — [C]
- **B&B proof reconstruction** — `branch_and_bound.cpp:81-116` — builds the `NOT_AND` / `CONTRA` / `ARITH_TRICHOTOMY` skeleton. — [C]
- **`BoundInference`** — `src/theory/arith/bound_inference.cpp:57`, `replaceByOrigins` `:130` — LRA/LIA/NRA/NIA — parses assertions into per-variable `Bounds` with origins. — [C]
- **`EqualitySolver`** — `src/theory/arith/equality_solver.cpp:56` — `--arith-eq-solver` default **`false`** (`arith_options.toml:612`); **forced true when `--ee-mode=central`** (`set_defaults.cpp:879`), itself non-default. — [C]
- **`ArithIteUtils` — variable reduction in ITEs** — `src/theory/arith/arith_ite_utils.cpp:52` — LIA/LRA with ITEs — **reachable only from `ITESimp`** (`preprocessing/passes/ite_simp.cpp:168`), which is gated on `--ite-simp` (default `false`). **So the whole file is unreachable in a default run.** — [C]
- **`ArithIteUtils` — GCD reduction / substitution learning** — `arith_ite_utils.cpp:205, :262, :291, :362, :470` — same default-off gate. — [C]
- **`PreprocessRewriteEq`** — `src/theory/arith/pp_rewrite_eq.cpp:30` — pure linear QF arith — `--arith-rewrite-equalities` toml default **`false`** (`arith_options.toml:136`) **but flipped to true** for `logic.isPure(ARITH) && isLinear() && !isQuantified()` (`set_defaults.cpp:805-811`) — splits `(= x y)` into `(and (<= x y) (>= x y))`. — [C]
- **`ppNormalizeEq` fallback** — `pp_rewrite_eq.cpp:69` — the non-split case: `rewriteEqualityExt` plus a trusted rewrite. — [C]
- **`ArithMSum`** — `src/theory/arith/arith_msum.cpp:64, :80, :176, :319` — all arith; heavily used by quantifier instantiation, `real-to-int`, `nl_model` — decomposes a literal into `{monomial → coeff}` and solves for a chosen variable. — [C]
- **`ArithSubs`** — `src/theory/arith/arith_subs.cpp:29, :120` — substitutes only through arithmetic subterms, treating foreign-theory terms as atoms; mixes Int/Real safely. — [C]
- **`ArithProofRCons`** — `src/theory/arith/arith_proof_rcons.cpp:163`, `solveEquality` `:53` — LIA (dio lemmas) — with proofs — reconstructs a proof of `ARITH_DIO_LEMMA` by inferring entailed equalities; falls back to a trust step. — [C]
- **`ArithProofRuleChecker`** — `src/theory/arith/proof_checker.cpp:44-53` — checks `MACRO_ARITH_SCALE_SUM_UB`, `ARITH_SUM_UB`, `ARITH_TRICHOTOMY`, `INT_TIGHT_UB`, `INT_TIGHT_LB`, `ARITH_REDUCTION`, `ARITH_MULT_POS`, `ARITH_MULT_NEG`, `ARITH_POLY_NORM`, `ARITH_POLY_NORM_REL`. — [C]
- **`ArithPreprocess`** — `src/theory/arith/arith_preprocess.cpp:36` — context-dependently records which atoms already had their partial operators eliminated; emits `ARITH_PP_ELIM_OPERATORS(_LEMMA)`. — [C]
- **`isExpressionZero`** — `src/theory/arith/arith_evaluator.cpp:23` — NRA (coverings/ICP model checks) — evaluates under a substitution, handling real-algebraic values. — [C]
- **Entailed-conflict check** — `src/theory/arith/inference_manager.cpp:114` — `--nl-ext-ent-conf` default `false`, **expert** (`arith_options.toml:438`). — [C]

### 8.2 `src/theory/arith/linear/`

- **`TheoryArithPrivate`** — `linear/theory_arith_private.cpp:3727` (`postCheck`) — QF_LRA/LIA/IDL/RDL and the linear core of everything else — on by default — the simplex-for-DPLL(T) main loop. — [C] [P] (Dutertre–de Moura)
- **`AssertLower` / `AssertUpper` / `AssertEquality` / `AssertDisequality`** — `:501, :668, :837, :948` — bound assertion with conflict detection against the opposing bound. — [C]
- **`splitDisequalities`** — `:4251` — at full effort, for `x ≠ c` whose model value is `c`, emits the `<`/`>` split. — [C]
- **`roundRobinBranch` / `nextIntegerViolation`** — `:4235, :2003` — cycles over integer variables with fractional model values, emitting `ARITH_BB_LEMMA`, retrying until one is accepted (`:4070-4123`). — [C]
- **`cutAllBounded`** — `:4212` — LIA — `--cut-all-bounded` default `false`, **expert** — periodically branches on *all* integer variables with both bounds. — [C]
- **`dioCutting`** — `:1676`, resource guard `:478` — LIA/IDL — `--dio-solver` default **`true`** (`arith_options.toml:126`) **but forced false for QF non-linear logics** (`set_defaults.cpp:853-857`); budgets `--dio-turns` (10) and `--rr-turns` (3) — derives a cutting plane from the Diophantine solver, emitted as `ARITH_DIO_CUT`. — [C] [P] (Griggio, JSAT 2012)
- **`callDioSolver`** — `:1764`, conflict handling `:4020-4045` — feeds tight integer equalities to `DioSolver`; the conflict is proof-reconstructed via `ArithProofRCons`. — [C]
- **Dio decomposition lemmas / restart** — `:4126-4143` — once `--maxCutsInContext` (65535) is hit, flushes `ARITH_DIO_DECOMPOSITION` lemmas, else signals a solver restart. — [C]
- **`propagateCandidates` (old row propagation)** — `:5053`, `propagateCandidateBound` `:4938` — reached only when `--new-prop=false`; `--new-prop` default **`true`** — bound inference from tableau rows, capped by `--prop-row-length` (16). — [C]
- **`propagateCandidatesNew` / `attemptSingleton` / `attemptFull`** — `:5107, :5183, :5218` — on by default — rows shorter than `--arith-prop-clauses` (8) are propagated as clauses rather than implications. — [C]
- **Unate propagation driver** — `:3940-3990` — `--arith-prop` default `both` (bounds inference + unate), **expert**. — [C]
- **Unate lemma generation (pre-search)** — `--unate-lemmas` default `all`, **expert** (`arith_options.toml:9`) — emits `(= p c) ⇒ (<= p d)` and `(<= p c) ⇒ (<= p d)` families before SAT search begins. — [C]
- **`entailmentCheck` / `decomposeLiteral` / `entailmentCheckRowSum`** — `:5526, :5850, :5976` — used by strings and quantifiers — decides entailment by bound lookup, row sum, or bounded simplex. — [C]
- **`deltaValueForTotalOrder`** — `:4610` with `delta_rational.cpp` — picks a concrete δ making the strict-inequality symbolic model concrete. — [C]
- **`revertArithModels`** — `:3751` — `--revert-arith-models-on-unsat` default `false`, **expert**. — [C]
- **`SimplexDecisionProcedure` base** — `linear/simplex.cpp:64, :97, :148` — shared machinery: `standardProcessSignals`, `checkBasicForConflict`, Farkas conflict emission, infeasibility-function bookkeeping (`:170-235`). — [C]
- **`DualSimplexDecisionProcedure`** — `linear/dual_simplex.cpp:56` (`dualFindModel`), `:149` — **the default simplex** (`selectSimplex`, `theory_arith_private.cpp:3442-3460`) — heuristic pivot rounds then Bland's rule. — [C]
- **`FCSimplexDecisionProcedure`** — `linear/fc_simplex.cpp:64, :782` — `--use-fcsimplex` default **`false`**, **expert** — **"FC" is *focusing and converging*, not Fruehwirth–Chvátal** (the option help cites an FMCAD 2013 submission): maintains a focus set, shrinks it (`focusDownToJust` `:263`, `focusDownToLastHalf` `:679`), falls back to Bland after 10/100 degenerate pivots (`fc_simplex.h:141-142`). — [C] [P]
- **FC degenerate-pivot penalties** — `fc_simplex.cpp:359` — `--fc-penalties` default `false`, **expert**, and reachable only under `--use-fcsimplex`. — [C]
- **`SumOfInfeasibilitiesSPD`** — `linear/soi_simplex.cpp:67, :1006, :970` — `--use-soi` default **`false`**, **expert** — minimises Σ|bound violation| instead of fixing one violated variable at a time. — [C] [P] (FMCAD 2013)
- **SOI greedy conflict subsets** — `soi_simplex.cpp:662, :836, :920` — extracts multiple minimal conflicting subsets from the infeasibility function. — [C]
- **SOI QuickExplain minimisation** — `soi_simplex.cpp:482, :602` — `--soi-qe` default `false`, **expert**, and only under `--use-soi`. — [C]
- **SOI as the second-pass solver** — `theory_arith_private.cpp:3468-3479` — **on by default**: `d_otherSDP` defaults to `d_soiSimplex` even when `--use-soi` is false (`:3478`). — [C]
- **`AttemptSolutionSDP`** — `linear/attempt_solution_simplex.cpp:54` — reachable only from `importSolution` (`theory_arith_private.cpp:3486`), i.e. only under `--use-approx` + GLPK — installs an externally supplied assignment into the tableau with minimal pivoting. — [C]
- **`ApproxGLPK`** — `linear/approx_simplex.cpp:30`–`:3617` — **requires GLPK (off by default) and `--use-approx` (default false)** — floating-point relaxation plus branch-and-cut whose search tree is logged and replayed exactly. — [C]
- **GLPK GMI cut extraction** — `approx_simplex.cpp:1477, :2232, :266` — reads GLPK's Gomory mixed-integer cuts and rebuilds them exactly in rationals. — [C]
- **GLPK MIR / c-MIR cut extraction** — `approx_simplex.cpp:1443, :269, :270, :271-274` — reconstructs mixed-integer-rounding cuts including complemented ranges, slack substitution, and virtual bounds. — [C]
- **`heuristicOptCoeffs`** — used at `theory_arith_private.cpp:3597` — guesses LP objective coefficients before the relaxation. — [C]
- **Gaussian-elimination construction for approx** — statistic `z::approx::gaussianElimConstruct` (`approx_simplex.cpp:3648-3652`). — [C]
- **`ApproximateSimplex::enabled()` glue** — `approx_simplex.cpp:3625-3643` — **dead without GLPK**. — [C]
- **`solveInteger`** — `theory_arith_private.cpp:3286`, guard `:3254` — requires GLPK + `--use-approx`; depth cap `--approx-branch-depth` (200). — [C]
- **`attemptSolveInteger` at standard effort** — `:2219, :2269` — `--se-solve-int` default `false`, **expert**, on top of `--use-approx`. — [C]
- **`replayLog` / `replayLogRec`** — `:2287, :2754` — re-derives every branch and cut in exact arithmetic, escalating conflicts; tuned by `--replay-early-close-depth` (1), `--replay-num-err-penalty` (4194304), `--replay-reject-cut` (25500). — [C]
- **`replayLemmas`** — `:3184, :3041` — `--lemmas-on-replay-failure` default `false`, **expert**; cut size capped by `--replay-lemma-reject-cut` (25500) — emits the approximate cuts as external lemmas when exact replay fails. — [C]
- **`turnOffApproxFor`** — `:3248` — disables approx for N attempts after a numeric failure. — [C]
- **`tryBranchCut` / `branchToNode` / `cutToLiteral`** — `:2565, :3139, :3166` — turns a logged `BranchCutInfo` back into an arithmetic literal. — [C]
- **`TreeLog` / `NodeLog` / `CutInfo`** — `linear/cut_log.cpp:237, :643, :346`; klasses at `cut_log.h:60-66` (`MirCutKlass`, `GmiCutKlass`, `BranchCutKlass`, `RowsDeletedKlass`) — records the external solver's branch-and-cut tree for replay, including row deletions. **Populated only by the GLPK path.** — [C]
- **`DioSolver`** — `linear/dio_solver.cpp:460, :534, :551` — LIA/IDL — `--dio-solver` default `true`, forced off for QF non-linear — solves integer equalities by repeated substitution. — [C] [P] (Griggio, JSAT 2012)
- **`solveIndex` / `decomposeIndex`** — `dio_solver.cpp:706, :304` — eliminates a unit-coefficient variable, else introduces a fresh variable via extended GCD (`Integer::extendedGcd`, `:415`) — Omega-style. — [C] [P]
- **`impliedGcdOfOne` / `columnGcdIsOne`** — `dio_solver.cpp:369, :316` — detects unsatisfiable congruences from column GCDs. — [C]
- **`anyCoefficientExceedsMaximum`** — `dio_solver.cpp:220` — aborts substitution when coefficients blow up. — [C]
- **Dio decomposition-lemma export** — `dio_solver.cpp:950` — `--dio-decomps` default `false`, **expert**. — [C]
- **`proveIndex` / proof variables** — `dio_solver.cpp:178, :77` — reconstructs the input-constraint explanation for a derived equation. — [C]
- **`Constraint` / `ConstraintDatabase`** — `linear/constraint.cpp:2466` (transitive unates), `:1509` (`unateFarkasSigns`) — canonical `(var, DeltaRational, type)` literals with negation links, sorted-by-value iterators, context-dependent internal proofs. — [C]
- **`unatePropLowerBound` / `…UpperBound` / `handleUnateProp`** — `constraint.cpp:2592, :2645, :2567` — propagates `x ≥ c ⊨ x ≥ d` for `d < c`, and disequality consequences. — [C]
- **`ArithCongruenceManager`** — `linear/congruence_manager.cpp:326, :186, :221, :252` — arith combined with UF/arrays/datatypes — bridges the tableau to the equality engine by watching `x−y` slack variables and asserting `x=y` when pinned to zero. — [C]
- **Congruence-manager poly-norm explanations** — `congruence_manager.cpp:432-438, :561-565` — uses `PolyNorm::isArithPolyNormRel` to justify literal↔literal equivalences. — [C]
- **`LinearEqualityModule`** — `linear/linear_equality.cpp` (class doc `linear_equality.h:9-24`) — maintains the tableau/partial-model invariant, row-bound computation, update-preference functions. — [C]
- **Sparse `Matrix<T>` / `RowVector` / `ColumnVector`** — `linear/matrix.h:7-30`, `matrix.cpp:20` — doubly-linked sparse matrix with a row-change callback interface. — [C]
- **`Tableau`** — `linear/tableau.cpp:25, :79, :178` — rational matrix in solved form; basic-variable row add/remove at `:112`/`:169`. — [C]
- **`TableauSizes`** — `linear/tableau_sizes.h:21` — row/column length oracle for the pivot heuristics. — [C]
- **`NormalForm`** — `linear/normal_form.cpp:315, :330, :347` — the canonical polynomial representation assertions are parsed into. — [C]
- **`ArithVariables` / partial model** — `linear/partial_model.cpp:515, :537` — context-dependent per-variable assignment plus bounds. — [C]
- **`BoundCounts`** — `linear/bound_counts.h:20`, `partial_model.cpp:282` — per-row counts of at-bound non-basics, for cheap propagatable/conflicting-row detection. — [C]
- **`ErrorSet` + pivot-rule heap** — `linear/error_set.cpp:203, :233` — `--error-selection-rule` default `min`, **expert** (modes `varord`/`max`/`sum`) — binary heap of bound-violating variables ordered by the selected metric. — [C]
- **`ErrorSet` focus manipulation** — `error_set.cpp:397, :363, :516` — `blur`, `dropFromFocus`, `focusDownToJust`; heavily used by the (default-off) focusing simplexes. — [C]
- **`UpdateInfo`** — `linear/simplex_update.cpp:93-181` — records candidate updates and their `WitnessImprovement` class. — [C]
- **Simplex pivot budgets** — `--heuristic-pivots` (0; **logic-tuned to −1 for difference logic, 0 for pure real, 5 otherwise**, `set_defaults.cpp:812-827`), `--pivot-threshold` (2; **16 for difference logic**, `:829-839`), `--standard-effort-variable-order-pivots` (−1; **200 for pure arith**, `:841-849`), `--simplex-check-period` (200) — all **expert**. — [C]
- **`--restrict-pivots`** — `theory_arith_private.cpp:3563` — default **`true`**, **expert** — pivot cap below full effort. — [C]
- **`--collect-pivot-stats`** — `:3831, :3853, :3884` — default `false`, diagnostics only. — [C]
- **`ArithStaticLearner`: ITE min/max** — `linear/arith_static_learner.cpp:145` — `--arith-static-learning` default **`true`** *and* `--static-learning` default `true` — learns `(ite c a b) ≥ min(a,b)` / `≤ max(a,b)`. — [C]
- **`ArithStaticLearner`: ITE constant bounds** — `arith_static_learner.cpp:209, :321`. — [C]
- **`ArithStaticLearner` proof generation** — `arith_static_learner.cpp:358, :425, :551`. — [C]
- **`InferBounds` / `ArithEntailmentCheckParameters`** — `linear/infer_bounds.h:47, :69`, used at `theory_arith_private.cpp:5528-5583` — selects `mkLookup` / `mkRowSum` / `mkSimplex(rounds)` for `entailmentCheck`. **The class is only constructed inside `entailmentCheck`, so the `mkSimplex` variant is reachable only through that path.** — [C]
- **`FarkasConflictBuilder`** — `linear/callbacks.cpp:70, :100, :141` — assembles Farkas-coefficient conflicts (`MACRO_ARITH_SCALE_SUM_UB`). — [C]
- **Callback plumbing** — `callbacks.cpp:47, :29, :60, :42` — `TempVarMalloc`, `SetupLiteralCallBack`, `BasicVarModelUpdateCallBack`, `DeltaComputeCallback`. — [C]
- **`LinearSolver` facade** — `linear/linear_solver.cpp:30`. — [C]
- **`ArithVar` / `ArithVarNodeMap`** — `linear/arithvar.cpp:27`, `arithvar_node_map.h` — dense index ↔ `Node`. — [C]

### 8.3 `src/theory/arith/nl/`

- **`NonlinearExtension`** — `nl/nonlinear_extension.cpp:427` (`modelBasedRefinement`), `:270` — NRA/NIA — on by default for non-linear logics — build candidate model → check assertions → run the inference strategy → emit lemmas. — [C] [P] (Cimatti et al., incremental linearisation)
- **Strategy / `InferStep` schedule** — `nl/strategy.cpp:108` — builds the ordered sequence: ICP → NL_INIT → TRANS_INIT → SPLIT_ZERO → TRANS_INITIAL → IAND/PIAND/POW2 init+initial → MONOMIAL_SIGN → MAGNITUDE0 → FLATTEN_MON → TRANS_MONOTONIC → MAGNITUDE1/2 → MONOMIAL_INFER_BOUNDS → IAND/PIAND/POW2 full → COVERINGS → (last resort) FACTORING / RES_BOUNDS / TANGENT_PLANES / TRANS_TANGENT_PLANES. — [C]
- **Coverings preempts the heuristics** — `strategy.cpp:150-154` — **the single biggest behavioural fork in the nl solver**: the non-terminating heuristic block (factoring, tangent planes, transcendental tangent planes) is *skipped entirely* when `--nl-cov` is on and `--nl-cov-force` is off. — [C]
- **`Interleaving` / `StepGenerator`** — `strategy.cpp:81, :88` — round-robins between step sequences; currently a single branch is registered. — [C]
- **`NlModel`** — `nl/nl_model.cpp:68, :169` — separates the linear solver's abstract value from the true nonlinear value of a term. — [C]
- **`solveEqualitySimple`** — `nl_model.cpp:381` — solves simple (including quadratic, via a square-root witness) equalities to repair the candidate model. — [C]
- **`simpleCheckModelLit` / `…Msum`** — `nl_model.cpp:560, :767` — interval-arithmetic-style check of a literal under the bound-annotated candidate model. — [C]
- **`addSubstitution` / `addBound` / `getModelValueRepair`** — `nl_model.cpp:272, :341, :1038`. — [C]
- **`--nl-ext-inc-prec`** — `nonlinear_extension.cpp:538` — default **`true`**, **expert** — increments Taylor degree when the previous round used an approximation. — [C]
- **`--nl-ext-rewrite`** — `nonlinear_extension.cpp:285` — default **`true`** — rewrites assertions using the extended-theory substitution before checking. — [C]
- **`--nl-rlv`** — `nonlinear_extension.cpp:143, :147` — default `none`, **expert** (modes `interleave`/`always`); incompatible with proofs and unsat cores (`set_defaults.cpp:1391-1397`). — [C]
- **`--nl-rlv-assert-bounds`** — `nonlinear_extension.cpp:171` — toml default **`false`** but **flipped to true for all quantifier-free logics** (`set_defaults.cpp:864-870`) — drops assertions entailed by another via `BoundInference`. — [C]
- **`--nl-ext-initial-sign-lemmas`** — `nonlinear_extension.cpp:92` — default `false`, **expert**, and additionally forced false for quantified logics (`set_defaults.cpp:1034-1042`). — [C]
- **`NlExtTheoryCallback`** — `nl/ext_theory_callback.h:21` — supplies the extended-theory framework with substitution/reduction over the arith equality engine. — [C]
- **`MonomialCheck`: initial refinement** — `nl/ext/monomial_check.cpp:124` — `--nl-ext ∈ {full, light}` (default `full`) — axioms like `x*x ≥ 0`, `|x*y| ≥ |x|` under unit bounds. — [C]
- **`MonomialCheck`: sign lemmas** — `monomial_check.cpp:156` — infers monomial sign from factor signs. — [C]
- **`MonomialCheck`: magnitude classes 0/1/2** — `monomial_check.cpp:193, :168, :182` — class 0 with `nl-ext ∈ {full, light}`; classes 1 and 2 **require `nl-ext=full`** (`strategy.cpp:145-146`). — [C]
- **`ArithNlCompareProofGen` (`ARITH_MULT_ABS_COMPARISON`)** — `nl/ext/arith_nl_compare_proof_gen.cpp`, checker `nl/ext/proof_checker.cpp:35`. — [C]
- **`MonomialBoundsCheck::checkBounds`** — `nl/ext/monomial_bounds_check.cpp:84` — **requires `--nl-ext=full`** — multiplies asserted bounds into monomial bounds. — [C]
- **`checkResBounds` (resolution-style bounds)** — `monomial_bounds_check.cpp:446` — `--nl-ext-rbound` default `false`, **expert**, and in the last-resort block. — [C]
- **`FactoringCheck`** — `nl/ext/factoring_check.cpp:40` — `--nl-ext-factor` default **`true`** **but only reached in the last-resort block**, i.e. when `nl-ext=full` and (`!nl-cov` or `--nl-cov-force`). — [C]
- **`TangentPlaneCheck`** — `nl/ext/tangent_plane_check.cpp:37` — `--nl-ext-tplanes` default **`true`**; non-terminating, so also in the last-resort block unless interleaved — tangent/secant linearisations of `x*y` at the model point. — [C] [P]
- **Tangent-plane interleaving** — `strategy.cpp:131-135` — `--nl-ext-tplanes-interleave` toml default **`false`** but **forced true for pure-integer logics** (`set_defaults.cpp:859-863`). — [C]
- **`ARITH_MULT_TANGENT` proof rule** — `nl/ext/proof_checker.cpp:34, :135`. — [C]
- **`SplitZeroCheck`** — `nl/ext/split_zero_check.cpp:33` — `--nl-ext-split-zero` default `false`, **expert**; also requires `nl-ext=full`. — [C]
- **`FlattenMonomialCheck`** — `nl/ext/flatten_monomial_check.cpp:123` — `--nl-ext-flatten-mon` default **`true`** — associativity-based equality propagation between differently parenthesised products. — [C]
- **`MonomialDb` / `NodeMultiset`** — `nl/ext/monomial.h:24` — exponent-multiset representation with containment/GCD queries. — [C]
- **`ExtState`** — `nl/ext/ext_state.h:16` — shared model, monomial db, and `CDProof` set for all `ext/` checks. — [C]
- **`ARITH_MULT_SIGN` proof rule** — `nl/ext/proof_checker.cpp:33, :48`. — [C]
- **`ICPSolver`** — `nl/icp/icp_solver.cpp:358` — NRA — `--nl-icp` default **`false`**, **expert**, **and requires LibPoly**; without LibPoly the `#else` at `:400-412` raises `Unimplemented() << "ICPSolver requires cvc5 to be configured with LibPoly"` — contracts variable intervals from polynomial constraints to a fixpoint. — [C]
- **ICP contraction candidates** — `nl/icp/candidate.h:24` — `lhs ~rel~ rhsmult*rhs` contraction rules derived from assertions. — [C]
- **ICP contraction-origin tracking** — `nl/icp/contraction_origins.h:20` — recursive DAG mapping each contracted interval back to input literals. — [C]
- **ICP interval intersection** — `nl/icp/intersection.h:25`, `icp/interval.h:22`. — [C]
- **`CoveringsSolver` (CAC / CDCAC)** — `nl/coverings_solver.cpp:107, :144` — NRA (real-only, quantifier-free by default) — `--nl-cov` default **`true`** (`arith_options.toml:520`) **but `set_defaults.cpp:1007-1015` turns it off for "logic without reals, or involving integers or quantifiers"**; the option also carries `no_support = ["proofs"]`. **Requires LibPoly**: without it `set_defaults.cpp:1018-1021` forces `nlCov=false` (or throws if requested) and every method warns "Tried to use CoveringsSolver but libpoly is not available. Compile with --poly." — [C] [P] (arXiv:2003.05633)
- **CDCAC core (`getUnsatCover`)** — `nl/coverings/cdcac.cpp:670`, recursion `:555` — cylindrical algebraic coverings: build unsat intervals per variable, recurse, characterise, generalise. — [C] [P] (Ábrahám–Davenport–England–Kremer)
- **`getUnsatIntervals`** — `cdcac.cpp:131` — isolates real roots to derive infeasible intervals. — [C]
- **`constructCharacterization` / `intervalFromCharacterization`** — `cdcac.cpp:358, :444` — the projection/generalisation step producing a cell that excludes the whole covering. — [C]
- **Projection operators (McCallum / Lazard / Lazard-mod)** — `cdcac.cpp:340-346`, `nl/coverings/projections.cpp` — `--nl-cov-proj` default `mccallum`, **expert**. — [C]
- **Lifting scheme** — `cdcac.cpp:151, :790, :804` — `--nl-cov-lift` default `regular`, **expert**. — [C]
- **`LazardEvaluation`** — `nl/coverings/lazard_evaluation.cpp:24` — **requires CoCoA on top of LibPoly**. Without CoCoA the `#else` at `:850-906` **silently degrades**: `reducePolynomial` becomes the identity and root isolation falls back to plain LibPoly with `WarningOnce() << "nl-cov::LazardEvaluation is disabled because CoCoA is not available."` — [C]
- **CoCoA↔LibPoly converter** — `nl/coverings/cocoa_converter.cpp:17`. — [C]
- **`--nl-cov-var-elim`** — `coverings_solver.cpp:58` — default **`true`** **but forced false when producing proofs** (`set_defaults.cpp:1143-1146`). — [C]
- **`--nl-cov-linear-model`** — `cdcac.cpp:107, :195-205` — default `none` (modes `initial`/`persistent`) — seeds the CAC sample point from the LRA relaxation's model. — [C]
- **`--nl-cov-prune`** — `cdcac.cpp:754` — default `false`, **expert**. — [C]
- **CDCAC integrality handling** — `cdcac.cpp:702, :713` — reachable only if `--nl-cov-force` (default `false`) turns coverings on for integer logics. — [C]
- **Coverings variable ordering** — `nl/coverings/variable_ordering.h:26` — CAC-tailored orderings (Brown-style heuristics plus a by-id dummy). — [C]
- **Coverings proof generator** — `nl/coverings/proof_generator.cpp:113`, `cdcac.cpp:684, :692`, checker `nl/coverings/proof_checker.cpp` — **present, but `--nl-cov` is annotated `no_support = ["proofs"]`**; inference ids `ARITH_NL_COVERING_CONFLICT` / `…_EXCLUDED_INTERVAL`. — [C]
- **`poly_conversion`** — `nl/poly_conversion.h:18` — **the entire file is inside `#ifdef CVC5_POLY_IMP`**. — [C]
- **`PolyConverter::ran_to_node`** — used at `operator_elim.cpp:449` — turns a real-algebraic root into a `REAL_ALGEBRAIC_NUMBER` node during `SQRT` elimination. — [C]
- **`EqualitySubstitution`** — `nl/equality_substitution.cpp:51, :173` — on by default when `--nl-cov-var-elim` is true (so, off under proofs) — general Gaussian-style variable elimination over arith leaves with origin tracking. — [C]
- **`TranscendentalSolver`** — `nl/transcendental/transcendental_solver.cpp:52` — requires `--nl-ext=full`; `set_defaults.cpp:1024-1028` **forces `nl-ext=full` whenever the logic uses transcendentals**. — [C] [P] (Cimatti–Griggio–Irfan–Roveri–Sebastiani)
- **Transcendental initial refinement / monotonicity** — `transcendental_solver.cpp:191, :197`; `exponential_solver.cpp:63, :148`; `sine_solver.cpp:211, :328` — sign/positivity/zero axioms, then monotonicity lemmas between model-ordered arguments. — [C]
- **Transcendental tangent/secant planes** — `transcendental_solver.cpp:203, :257`; `exponential_solver.cpp:85, :88`; `sine_solver.cpp:97, :104` — `--nl-ext-tf-tplanes` default **`true`**, but non-terminating so in the last-resort block. — [C]
- **`TaylorGenerator`** — `nl/transcendental/taylor_generator.h:61, :77, :101` — degree from `--nl-ext-tf-taylor-deg` (default **4**, **expert**), incremented by `--nl-ext-inc-prec` — upper/lower polynomial approximations of `exp`/`sin` with remainder bounds. — [C]
- **Sine phase shift / argument purification** — `sine_solver.cpp:63, :58` — introduces `y ∈ [-π, π]` with `sin(x) = sin(y)` and `x = y + 2πk`, backed by `ARITH_TRANS_SINE_SHIFT`. — [C]
- **Exponential purification** — `exponential_solver.cpp:52`. — [C]
- **Transcendental proof checker (17 rules)** — `nl/transcendental/proof_checker.cpp:56-72`. — [C]
- **`TranscendentalState`** — `nl/transcendental/transcendental_state.cpp` — shared secant-point cache, model bounds, `CDProof` set. — [C]
- **`IAndSolver`** — `nl/iand_solver.cpp:69, :113` — NIA with `iand` — **unconditionally in the strategy** (`strategy.cpp:119-120, :151`) — refines `iand` by value, sum, or bitwise per `--iand-mode` (default `value`, **expert**). — [C]
- **`IAndUtils`** — `nl/iand_utils.h:19`, used at `iand_solver.cpp:262, :278` — table width from `--bvand-integer-granularity` (default 1, max 8). — [C]
- **`PIAndSolver`** — `nl/piand_solver.cpp:69, :168, :351` — the bit-width-parametric variant, also unconditional. — [C]
- **`Pow2Solver`** — `nl/pow2_solver.cpp:77, :136` — NIA with `int.pow2` — unconditional in the strategy — monotonicity plus value-based refinement of `2^x`. — [C]
- **Pow2 proof checker** — `nl/pow2_proof_checker.cpp`. — [C]
- **`NlLemma` / `NlLemmaSideEffect`** — `nl/nl_lemma_utils.h:22` — carries a lemma plus deferred side effects (e.g. secant-point registration). — [C]
- **`NlStats`** — `nl/stats.cpp` — per-inference-step counters. — [C]

### 8.4 `src/theory/ff/` — finite fields

- **`TheoryFiniteFields`** — `src/theory/ff/theory_ff.cpp:94, :170` — QF_FF — `--ff` default `true`, **expert**, forced false under safe options (`set_defaults.cpp:141`); **requires CoCoA** — one `SubTheory` per field size; without CoCoA every fact path calls `noCoCoA()`, which throws `LogicException("cvc5 can't solve field problems since it was not configured with --cocoa")` (`theory_ff.cpp:43-48`). — [C]
- **`SubTheory` (the decision procedure)** — `ff/sub_theory.cpp:53` — collects facts, dispatches to `gb` or `split` per `--ff-solver`, maps the result to SAT/UNSAT/UNKNOWN, handles `FfTimeoutException`. — [C] [P] (OKTB23, doi:10.1007/978-3-031-37703-7_8)
- **`gb` (single Gröbner basis)** — `ff/gb.cpp:30` — `--ff-solver=gb` is the **default** (`ff_options.toml:41`) — one GB over the whole system, then model construction or core extraction. — [C]
- **`--ff-field-polys`** — `gb.cpp:53` — default `false`, **expert**; **the help text literally says "don't do this"** — adds field polynomials `x^p − x` to the ideal. — [C]
- **`--ff-trace-gb`** — `gb.cpp:66, :73, :81` — default **`true`**, **expert** — installs CoCoA callback hooks so the `Tracer` can build UNSAT cores. — [C]
- **`Tracer`** — `ff/core.cpp:55, :100, :141, :159-173` — records S-polynomial and reduction steps to derive a minimal conflict core. — [C] [P] (OKTB23 Fig. 4)
- **`findZero` (multivariate model construction)** — `ff/multi_roots.cpp:228`, helpers `:110, :123, :165` — extends a partial assignment to a common zero of the ideal, backtracking on inconsistency. — [C] [P] (OKTB23 Fig. 5/6)
- **Assignment enumerators** — `multi_roots.cpp:49, :93` — `ListEnumerator`, `RoundRobinEnumerator`. — [C]
- **`distinctRootsPoly` / `roots`** — `ff/uni_roots.cpp:73, :117`, `powerMod` `:55` — computes `gcd(f, X^p − X)`-style distinct-root polynomials, then splits to get all roots in GF(p). — [C]
- **`split` / `splitGb` / `splitFindZero` / `applyRule` / `admit`** — `ff/split_gb.cpp:131, :251, :245`, `split_gb.h:86, :121` — `--ff-solver=split` (**not** the default) — partitions the system and maintains multiple GBs, propagating between them. — [C] [P] (Ozdemir et al., *Split Gröbner Bases for SMT over Finite Fields*)
- **`BitProp::getBitEqualities`** — `split_gb.cpp:548`, `split_gb.h:156` — split-GB only — propagates 0/1 bit facts between the split bases (circuit / ZK-style problems). — [C]
- **`Gb::zeroDimensional` / `isWholeRing` / `contains`** — `split_gb.cpp:405, :397, :393`. — [C]
- **`CocoaEncoder`** — `ff/cocoa_encoder.cpp:235, :304, :115, :42` — two-pass scan then encode; disequalities `a ≠ b` become `(a−b)·z − 1` with a fresh inverse witness. — [C]
- **Bitsum encoding** — `cocoa_encoder.cpp:173` — `--ff-bitsum` default `false`, **expert**; the `ff-bitsum` pass runs when `--ff-bitsum` **or** `--ff-solver=split`. — [C]
- **`cocoa_util`** — `ff/cocoa_util.cpp:13-149` — conversions between cvc5 `Integer` / `FiniteFieldValue` and CoCoA types. — [C]
- **`parse`** — `ff/parse.h:35` — **no CoCoA guard** — pattern-matches `x=0`, disjunctive bit constraints, and bitsums out of assertions. — [C]
- **`FieldObj` / `FfResult`** — `ff/util.h:26-32` — `std::variant<FfUnknown, FfModel, FfCore>` is the uniform return type of every FF subprocedure. — [C]
- **`FfTimeoutException`** — `ff/util.cpp:16`, caught at `sub_theory.cpp:103` — turns a resource-limit abort inside CoCoA into `UNKNOWN(TIMEOUT)`. — [C]
- **`TheoryFfRewriter`** — `ff/theory_ff_rewriter.cpp` — **no CoCoA needed** — normalises `ff.add`/`ff.mul`/`ff.neg` and folds constants in GF(p). — [C]
- **FF type rules / type enumerator** — `ff/theory_ff_type_rules.cpp`, `type_enumerator.h` — no CoCoA needed. — [C]

### 8.5 Defaults in this area that are easy to misread

- `--nl-ext` is `common` with default `full`, but `set_defaults.cpp:996-1006` **downgrades it to `light` for QF_UFNRA and for quantified real-only logics when `--nl-cov` survives**, and `:1024-1028` upgrades it back to `full` whenever transcendentals are used. `[C]`
- `--nl-cov` reads `default = "true"`, but for anything with integers, quantifiers, or no reals, `set_defaults.cpp:1011-1015` silently sets it false. **"CAC is on by default" is true only for QF real non-linear logics in a LibPoly build.** `[C]`
- `--dio-solver` reads `default = "true"` but is silently disabled for every quantifier-free non-linear logic (`set_defaults.cpp:853-857`). `[C]`
- `--arith-rewrite-equalities` reads `default = "false"` but is silently set true for pure linear quantifier-free arithmetic (`set_defaults.cpp:805-811`). `[C]`
- `--nl-rlv-assert-bounds` reads `default = "false"` but is silently set true for all quantifier-free logics (`set_defaults.cpp:864-870`). `[C]`
- `--nl-ext-tplanes-interleave` reads `default = "false"` but is forced true for pure integer logics (`set_defaults.cpp:859-862`). `[C]`
- Every simplex tuning knob has a **logic-dependent** effective default different from the toml value (`set_defaults.cpp:812-849`), including a special difference-logic path (`heuristicPivots = -1`, `pivotThreshold = 16`). `[C]`

## 9. Strings, sequences, sets, relations, bags, datatypes, arrays, UF, separation logic

Logic-string facts used below, from `src/theory/logic_info.cpp`: `S`→strings
(`:598`), `DT`→datatypes (`:590`), `FS`→sets (`:695`), `SEP_`→sep (`:342` emit /
`:800` via `ALL`), `A`/`AX`→arrays, `UF`→uf. **`FB` (bags) is emitted at `:411`
but never parsed** — the bags theory is reachable only via `ALL` / `QF_ALL`. `[C]`

### 9.1 Strings and sequences — the round structure

- **Strings strategy / round schedule** — `src/theory/strings/strategy.cpp:113` — QF_S, QF_SLIA, SLIA, QF_SNIA, ALL — on by default — builds the fixed ordered list of `InferStep`s (with a `BREAK` after each) run at `EFFORT_FULL` and optionally `EFFORT_LAST_CALL`; three steps are conditionally omitted by option. — [C]
- **CHECK_INIT** — `strings/base_solver.cpp:67` — on by default (`strategy.cpp:124`) — builds the term index over string-like eqcs, detects congruent concat terms, infers `I_NORM`/`I_NORM_S`/`I_CONST_MERGE`/`I_CONST_CONFLICT` from identical concat prefixes. — [C]
- **CHECK_CONST_EQC** — `base_solver.cpp:444`, worker `:476` — on by default — computes a constant representative per eqc by folding concatenations of constants; conflicts when two distinct constants meet. — [C]
- **`processConstantLike`** — `base_solver.cpp:343` — strings + sequences — handles `seq.unit`/`str.unit` as constant-like: `UNIT_SPLIT`, `UNIT_INJ`, `UNIT_INJ_OOB`, `UNIT_CONST_CONFLICT`. — [I]
- **CHECK_CYCLES (occurs check on the concat graph)** — `strings/core_solver.cpp:120`, worker `:454` — on by default — detects `x = … ++ x ++ …`; `I_CYCLE`, `I_CYCLE_E`, `I_CYCLE_CONFLICT`. Must run before flat forms. — [C]
- **CHECK_FLAT_FORMS** — `core_solver.cpp:142`, `checkFlatForm` `:230` — `--strings-ff` default **`true`**, **expert** (`strings_options.toml:133`) — cheap non-normal-form unification over one-level concat forms, in both directions: `F_CONST`, `F_UNIFY`, `F_ENDPOINT_EMP`, `F_ENDPOINT_EQ`, `F_NCTN`. `--no-strings-ff` removes the whole step from the strategy. — [I]
- **CHECK_NORMAL_FORMS_EQ_PROP** — `core_solver.cpp:573` — cheap propagation before the full normalisation fixed point. — [C]
- **CHECK_NORMAL_FORMS_EQ (word-equation normal forms)** — `core_solver.cpp:2834`; `normalizeEquivalenceClass:634`, `getNormalForms:918`, `processNEqc:1146`, `processSimpleNEq:1297` — on by default — the Liang et al. CAV 2014 core: build a normal form per eqc by recursive concat expansion, then pairwise-unify, emitting `N_UNIFY`, `N_CONST`, `N_EQ_CONF`, `N_ENDPOINT_EMP/EQ`, `INFER_EMP`, `SSPLIT_CST`, `SSPLIT_VAR`, `SSPLIT_CST_PROP`, `SSPLIT_VAR_PROP`, `LEN_SPLIT`, `LEN_SPLIT_EMP`. — [P] [I]
- **Inference selection (`pickInferInfo`)** — `core_solver.cpp:2788` — prefers facts and conflicts over splits, and shorter explanations. — [C]
- **Length-entailment guard on splitting** — `core_solver.cpp:1707` — `--strings-check-entail-len` default **`true`** — uses `ArithEntail` to skip an unnecessary `LEN_SPLIT`. — [C]
- **Loop detection and breaking** — `core_solver.cpp:1807` (`detectLoop`), `:1848` (`processLoop`) — `--strings-process-loop-mode` default `FULL` — handles `x·y = y·x` loops via the `FLOOP` skolem decomposition; `none` sets `IncompleteId::STRINGS_LOOP_SKIP`. `--strings-fmf` forces `SIMPLE` (`set_defaults.cpp:935`). — [P] [C]
- **CHECK_NORMAL_FORMS_DEQ** — `core_solver.cpp:2628`; `processDeq:2065`, `processReverseDeq:2373`, `processSimpleDeq:2392` — splits disequal pairs into `DEQ_LENS_EQ`, `DEQ_LENGTH_SP`, `DEQ_NORM_EMP`, `DEQ_STRINGS_EQ`, and the `DEQ_DISL_*` first-character/length splits. — [I]
- **Disequality extensionality** — `core_solver.cpp:2545`, gate `:2691` — `--strings-deq-ext` default **`false`** — **default off for strings**, always used for sequences: replaces a disequality by an explicit witness index (`DEQ_EXTENSIONALITY`) instead of length/character splitting. — [I]
- **CHECK_LENGTH_EQC** — `core_solver.cpp:2719` — `--strings-len-norm` default **`true`**, **expert** — asserts `LEN_NORM`: an eqc's length equals the sum of its normal-form components' lengths. — [I]
- **CHECK_REGISTER_TERMS_NF** — `core_solver.cpp:2771`, dispatch at `theory_strings.cpp:1303` — **dead/unreachable**: the `InferStep` has an enum value, a printer case, and a dispatch case, but `Strategy::initializeStrategy` (`strategy.cpp:113-170`) never calls `addStrategyStep(CHECK_REGISTER_TERMS_NF)`. — [C]
- **CHECK_CODES (`str.to_code` injectivity)** — `strings/code_point_solver.cpp:45` — QF_SLIA and up — on by default — asserts `CODE_INJ` (`code(x)=-1 ∨ code(x)≠code(y) ∨ x=y`) for relevant disequal pairs; `CODE_PROXY` links constants to proxies. — [I]
- **CHECK_CARDINALITY (alphabet pigeonhole)** — `base_solver.cpp:661`, `checkCardinalityType:807`, `getCardinalityReq:676` — on by default — for a length-equal collection of eqcs, if their count exceeds |Σ|^len it either splits pairs (`CARD_SP`) or asserts a length lower bound (`CARDINALITY`); |Σ| from `--strings-alpha-card` (default `196608`, **expert**). — [I]
- **Sequence finite-element cardinality gap** — `base_solver.cpp:729, :807` — sets `IncompleteId::SEQ_FINITE_DYNAMIC_CARDINALITY` (model-unsound) when a sequence's element type is finite only because FMF is on. — [C]

### 9.2 Strings — extended functions

- **CHECK_EXTF_EVAL** — `strings/extf_solver.cpp:305` — on by default; efforts 0/1 (`strategy.cpp:126, :141`) and effort 3 at LAST_CALL (`:163`) — substitutes current representatives into extended-function arguments, rewrites, and emits `EXTF`/`EXTF_N`/`EXTF_D`/`EXTF_D_N` or marks the term reduced. — [I]
- **Symbolic-definition minimisation** — `extf_solver.cpp:391-400` — `--strings-infer-sym` default **`true`**, **expert** — replaces constants by proxy variables so the same unit lemma is reused across contexts. — [C]
- **`checkExtfInference`** — `extf_solver.cpp:547` — from a determined `str.contains` value, derives component-wise contains facts (`CTN_POS`, `CTN_NEG_EQUAL`), transitivity (`CTN_TRANS`), decomposition (`CTN_DECOMPOSE`), and `EXTF_EQ_REW`/`EXTF_REW_SAME`. — [I]
- **`getCurrentSubstitutionFor`** — `extf_solver.cpp:759` — effort-dependent substitution source: representative (effort 0/1), normal form, or **model value at effort 3** — the model-based-reduction path. — [C]
- **CHECK_EXTF_REDUCTION_EAGER / CHECK_EXTF_REDUCTION** — `extf_solver.cpp:253, :259`, `shouldDoReduction:80`, `doReduction:140` — the eager step is on by default (`strategy.cpp:137`); the full reduction is gated by `--strings-exp` (`strategy.cpp:155`) — replaces an extended function by its quantifier-free / bounded-quantified definition when entailment fails. — [I]
- **`--strings-exp`** — `strings_options.toml:9`, `default = "false"`, `regular` — **but forced `true` by `set_defaults.cpp:520-526` whenever the logic includes strings.** This is the single most important toml/set_defaults divergence in strings. Enabling it also enables quantifiers in the logic (`set_defaults.cpp:532-548`). — [C]
- **Model-based reduction block at LAST_CALL** — `strategy.cpp:160-170` — `--strings-mbr` default **`true`** — adds a whole second strategy block at `EFFORT_LAST_CALL` so extended functions already correct in the candidate model are never reduced. — [C]
- **Extended-function reduction table** — `strings/theory_strings_preprocess.cpp:44` — on by default — one reduction per kind: `str.substr` (`:57`), `str.update` (`:117`), `str.indexof` (`:181`), `str.indexof_re` (`:256`), `str.from_int` (`:344`), `str.to_int` (`:430`), `seq.nth` (`:521`), `str.replace` (`:566`), `str.replace_all` (`:627`), `str.replace_re` (`:702`), `str.replace_re_all` (`:768`), `str.to_lower/upper` (`:883`), `str.rev` (`:932`), `str.contains` (`:965`), `str.<=` (`:991`). — [C]
- **Lazy vs eager preprocessing** — `theory_strings_preprocess.cpp:1053, :1148` — `--strings-lazy-pp` default **`true`** — when false, all extended functions are eliminated at preprocess time by the `strings-eager-pp` pass, and quantifiers are forced on. — [C]

### 9.3 Strings — regular expressions

- **CHECK_MEMBERSHIP / unfolding** — `strings/regexp_solver.cpp:83`, `checkUnfold:184`, `doUnfold:275` — on by default — unfolds asserted memberships one step via `RegExpOpr::simplify`, producing `RE_UNFOLD_POS` / `RE_UNFOLD_NEG`. — [I]
- **Positive/negative unfolding reductions** — `strings/regexp_operation.cpp:1047, :1227, :1113, :1155` — positive membership in `re.++` becomes a skolem concatenation; negative membership becomes a bounded quantified formula, specialised to a quantifier-free split when a prefix has fixed length (`getRegExpConcatFixed:1093`). — [P] [C]
- **Effort split for pos/neg unfolding** — `regexp_solver.cpp:167` — tied to `--strings-mbr` (default true) — positive memberships unfold at FULL effort, negative ones only at LAST_CALL. — [C]
- **Eager positive concat unfolding** — `regexp_solver.cpp:134` — `--strings-re-posc-eager` default **`false`**, **expert** — the step is always scheduled (`strategy.cpp:138`) but the body returns immediately when the flag is off. — [C]
- **Regular-expression inclusion** — `regexp_solver.cpp:107, :316`; engine `strings/regexp_entail.cpp:891, :1065` — `--strings-regexp-inclusion` default **`true`** — syntactic language-inclusion over `re.++`/`re.*`/`re.union`/`re.range`/constants; a subsumed membership is marked inactive (`RE_INTER_INCLUDE`), or a positive/negative pair yields a conflict. — [C]
- **Regular-expression intersection (product automaton)** — `regexp_solver.cpp:433`; `regexp_operation.cpp:1730, :1470, :1649` — `--re-inter-mode` default **`NONE`**, **expert** — **default off.** When enabled (`all` / `constant` / `one-constant`), intersects multiple memberships on one eqc into a single regexp via a derivative-based product construction, emitting `RE_INTER_INFER` or `RE_INTER_CONF`. — [C]
- **Brzozowski/Antimirov derivatives** — `regexp_operation.cpp:274` (`derivativeS`), `:631` (`derivativeSingle`), `:123` (`delta`, nullability), `:900` (`firstChars`) — on by default via `checkPDerivative` — `delta` decides whether ε ∈ L(r) (0/1/2 = yes/no/unknown); `derivativeS` computes the derivative w.r.t. a leading constant character. **This is the derivative machinery; unfolding above is a separate mechanism.** — [P] [C]
- **`checkPDerivative` / `deriveRegExp`** — `regexp_solver.cpp:544, :616` — when the LHS is empty, uses `delta` for `RE_DELTA` / `RE_DELTA_CONF`; otherwise strips a known constant prefix and asserts the derivative membership (`RE_DERIVE`). — [I]
- **Derivative-based conflict detection** — `regexp_solver.cpp:626` — `--strings-re-derive-conf` default **`false`**, **expert** — strengthens `deriveRegExp` to report a conflict when the derivative is empty. — [C]
- **NFA compilation evaluator** — `strings/regexp_eval.cpp:241, :284`, NFA state class `:24` — on by default (used by the rewriter and `checkEvaluations`) — Thompson construction with a linear scan; handles only `re.*`, `re.++`, `re.union`, `re.allchar`, constant `re.range`/`str.to_re`. **No intersection, no complement, not cached, not determinised.** — [C]
- **`checkEvaluations`** — `regexp_solver.cpp:722` — discharges memberships whose LHS became a constant. — [C]
- **Constant-membership testing (recursive)** — `regexp_entail.cpp:483, :501` — the general fallback matcher, including `re.inter`/`re.comp`, where `RegExpEval` cannot apply. — [C]
- **`simpleRegexpConsume`** — `regexp_entail.cpp:35` — peels matching constant / `re.allchar` / fixed-length prefixes and suffixes off both sides until stuck; the engine behind the `RE_SIMPLE_CONSUME` rewrite. — [C]
- **Regexp length bounds** — `regexp_entail.cpp:760, :811`, cached at `:1131, :1145` — exact or constant lower/upper length bounds for a regexp, used for quantifier-free negative unfolding and length propagation. — [C]
- **Eager length entailment from memberships** — `strings/eager_solver.cpp:174` — `--strings-eager-len-re` default **`false`** — when set, membership facts immediately install arithmetic length bounds in the eqc info. — [C]
- **Regular-expression elimination (preprocessing)** — `strings/regexp_elim.cpp:41, :74, :519`, invoked at `theory_strings.cpp:1183` — `--re-elim` default **`OFF`** — rewrites `str.in_re` into `str.len` / `str.substr` / `str.contains` / `str.indexof` constraints; `agg` additionally introduces quantifiers (and so forces quantifiers on). Produces trusted rewrites via an `EagerProofGenerator` (`:55`). — [C]
- **Regexp type enumerator** — `strings/regexp_enumerator.cpp`, `.h:34` — enumerates only singleton languages `(str.to_re s)`, driven by the string enumerator. — [C]
- **First-class regular expressions** — `src/smt/env.cpp:267`, `--re-first-class` default `false`, **expert** — allows `RegLan` as a first-class sort (variables and quantification over regexps). **Default off.** — [C]

### 9.4 Strings — sequences as arrays

- **CHECK_SEQUENCES_ARRAY_CONCAT** — `strings/array_solver.cpp:53, :110, :150` — sequences (ALL) — `--seq-array` default **`NONE`**, **expert** — distributes `seq.nth`/`seq.update` over `seq.++`: `ARRAY_NTH_CONCAT`, `ARRAY_UPDATE_CONCAT`, `ARRAY_UPDATE_CONCAT_INVERSE`, `ARRAY_UPDATE_UNIT`, `ARRAY_NTH_UNIT`, `ARRAY_UPDATE_BOUND`. **Default off.** — [I]
- **CHECK_SEQUENCES_ARRAY (lazy array core solver)** — `array_solver.cpp:69` → `strings/array_core_solver.cpp:216`; `checkNth:59`, `checkUpdate:108` — `--seq-array=lazy|eager` — a read-over-write procedure for sequences: reduces length-1 `seq.extract` to `seq.nth` (`ARRAY_NTH_EXTRACT`), and `nth(update(x,i,a),j)` to an ITE (`ARRAY_NTH_UPDATE`, `ARRAY_NTH_TERM_FROM_UPDATE`, `ARRAY_NTH_UPDATE_WITH_UNIT`, `ARRAY_EQ_SPLIT`, `ARRAY_NTH_REV`). **Default off.** — [P] [I]
- **CHECK_SEQUENCES_ARRAY_EAGER** — `array_solver.cpp:82`, scheduled at `strategy.cpp:129` — `--seq-array=eager` only — same, but before cycle detection and over *all* nth/update terms. — [C]
- **Connected-sequence computation** — `array_core_solver.cpp:281, :324` — partitions sequence eqcs into classes linked by updates so the model builder can construct a consistent `seq.++` skeleton with per-index write values. — [C]

### 9.5 Strings — eager solver, registry, model, proofs

- **Eager solver (EE notification layer)** — `strings/eager_solver.cpp:35, :80, :119, :157` — `--strings-eager-solver` default **`true`** — maintains per-eqc prefix/suffix constants and arithmetic length bounds; detects `PREFIX_CONFLICT`, `PREFIX_CONFLICT_MIN` (`:211, :219`) and `ARITH_BOUND_CONFLICT` (`:225, :270`) **at merge time** rather than in the strategy. — [C]
- **Eqc info** — `strings/eqc_info.h:53-95` — context-dependent per-eqc fields: length term, code term, cardinality-lemma counter, normalised length, first/second arithmetic bound, prefix/suffix constants. — [C]
- **Eager congruence evaluation** — `strings/theory_strings.cpp:142-165` — `--strings-eager-eval` default **`true`** — registers ~20 string kinds as congruence kinds *with evaluation*, so the equality engine constant-folds them on merge; `str.unit` and `seq.nth` are deliberately excluded (partial / underspecified). — [C]
- **Eager term registration** — `strings/term_registry.cpp:258` — `--strings-eager-reg` default **`true`**, **expert** — registers length/lemma constraints at preregistration rather than lazily. — [C]
- **String finite model finding** — `strings/strings_fmf.cpp:33, :85` — `--strings-fmf` default **`false`** — adds the decision strategy `Σ len(x_i) ≤ k` over input variables, enumerating k upward; also forces `--strings-process-loop-mode=simple`. **Default off.** — [C]
- **Model construction (default)** — `strings/model_cons_default.cpp:29, :47, :96`, installed at `theory_strings.cpp:963` — groups string reps into equal-length collections with concrete lengths, then assigns distinct constants; the `ModelCons` interface (`model_cons.h:31`) lets the array solver substitute a write-skeleton constructor. — [C]
- **Model length cap** — `theory_strings.cpp:344-353` — `--strings-model-max-len` default `65536`, **expert** — aborts model construction (unknown) rather than materialising a longer string. — [C]
- **Facts vs lemmas** — `strings/inference_manager.cpp:171` — `--strings-infer-as-lemmas` default **`false`**, **expert**. — [C]
- **Recursive explanation of lemmas** — `inference_manager.cpp:391` — `--strings-rexplain-lemmas` default **`true`**, **expert** — minimises lemma antecedents down to input literals. — [C]
- **Skolem cache with normalisation** — `strings/skolem_cache.cpp:36, :49, :143, :286, :295, :303` — canonicalises the (a,b,id) key of every string skolem (e.g. rewriting suffix skolems into prefix skolems) so semantically identical skolems are shared. — [C]
- **`Word` constant API** — `strings/word.cpp:24-500` — uniform operations over string *and* sequence constants: `getLength`, `getNth`, `strncmp`/`rstrncmp`, `find`/`rfind`, `update`, `replace`, `substr`, `overlap`/`roverlap`/`hasBidirectionalOverlap` (`:376-459`), `splitConstant` (`:475`), `reverse` (`:500`). **The overlap functions are what make constant-aware entailment rewriting possible.** — [C]
- **Strings proof reconstruction** — `strings/infer_proof_cons.cpp:66, :148, :1322, :1444, :1497` — lazy: `getProofFor` first emits `MACRO_STRING_INFERENCE` with packed args (`packArgs:96`), then elaborates into concrete `CONCAT_*` / `STRING_*` rules on demand. — [C]
- **Macro rewrite elaborator (strings)** — `strings/macro_rewrite_elaborator.cpp:45` — elaborates each string macro rewrite into fine-grained steps: `MACRO_ARITH_STRING_PRED_ENTAIL` (`:79`, five stages: normalise relation → unfold `str.len` → compare to zero → safe approximation → entailment), `RE_INTER_UNION_INCLUSION` (`:278`), `RE_INTER_UNION_CONST_ELIM` (`:379`), `SUBSTR_STRIP_SYM_LENGTH` (`:474`), `STR_EQ_LEN_UNIFY[_PREFIX]` (`:543, :747`), `OVERLAP` (`:828`), `STR_COMPONENT_CTN` (`:1011`), `STR_CONST_NCTN_CONCAT` (`:1060`), `STR_IN_RE_INCLUSION` (`:1145`). — [C] [P] (Noetzli et al., CAV 2019)

### 9.6 Strings — entailment-based rewriting

- **Sequences rewriter** — `strings/sequences_rewriter.cpp:2338` (`postRewrite`), `:2470` (`preRewrite`) — dispatches to ~40 kind-specific rewriters, all of which may consult `ArithEntail` / `StringsEntail`. — [C]
- **Proof-rewrite dispatcher** — `sequences_rewriter.cpp:99` (`rewriteViaRule`) — applies one named `ProofRewriteRule` in isolation so the checker can replay it. — [C]
- **Extended equality rewriting** — `sequences_rewriter.cpp:282, :297, :592` — solves string equalities non-locally: length-based conjunctive splitting (`STR_EQ_CONJ_LEN_ENTAIL`), non-containment refutation (`EQ_NCTN`), prefix/suffix mismatch (`EQ_NFIX`), replace-based equalities (`STR_EQ_REPL_*`). — [C]
- **Length-unification rewrites** — `sequences_rewriter.cpp:1235, :1260` — if `len(x₁..xₖ)` is entailed equal to `len(y₁..yₘ)` for a prefix of both sides, splits the equality in two. — [C]
- **Symbolic-length stripping** — `strings/strings_entail.cpp:113, :1030`; rewriter side `sequences_rewriter.cpp:1550` — removes leading components whose combined length is entailed ≤/≥ a symbolic length; behind `SS_STRIP_START_PT`, `SS_STRIP_END_PT`, `IDOF_STRIP_SYM_LEN`. — [C]
- **Component containment** — `strings_entail.cpp:225, :236, :247, :387` — decides whether one concat's component list is contained in another, allowing partial-constant matching at the endpoints; drives `CTN_COMPONENT`, `CTN_STRIP_ENDPT`. — [C]
- **Constant-endpoint stripping** — `strings_entail.cpp:516` — uses `Word::overlap`/`roverlap` to remove constant prefixes/suffixes that provably cannot participate. — [C]
- **Multiset (Parikh-image) subset check** — `strings_entail.cpp:751, :871` — refutes `str.contains(a,b)` by showing some character occurs more often in `b` than can possibly occur in `a`; the `CTN_MSET_NSS` rewrite. **A commutative over-approximation of the word — distinctive.** — [C]
- **Homogeneous-string check** — `strings_entail.cpp:830` — a string built from a single repeated character, enabling length-only containment reasoning. — [C]
- **Constant-containment feasibility** — `strings_entail.cpp:35, :83` — greedy left-to-right match of a concat's constant components inside a constant. — [C]
- **`inferEqsFromContains`** — `strings_entail.cpp:944` — from `contains(x,y)` and `len(x) = len(y)`, infers `x = y`. — [C]
- **Cheap definite checks** — `strings_entail.cpp:699, :725, :736, :898` — `checkContains`, `checkNonEmpty`, `checkLengthOne`, `getStringOrEmpty`. — [C]
- **Arithmetic entailment for string lengths** — `strings/arith_entail.cpp:251, :261, :1147` — decides `a ≥ b` (or `>`) over terms containing `str.len` by monomial-sum normalisation plus string facts (`len(x) ≥ 0`, `len(c) = |c|`). — [C]
- **Approximation search** — `arith_entail.cpp:283, :305, :609` — recursion gated by `--strings-rec-arith-approx` default **`false`**, **expert** — replaces `len(str.substr …)`, `len(str.replace …)`, `str.indexof`, `str.to_int` by sound over/under-approximations, expanding `ADD` on demand to avoid blowup, until the goal is trivially entailed. **The recursive variant is default off.** — [P] (Noetzli et al., CAV 2019) [C]
- **Constant bounds** — `arith_entail.cpp:1008, :1094`, caches `:971, :985`. — [C]
- **Entailment with assumptions** — `arith_entail.cpp:803, :877, :939, :1175` — case-splits on an assumed equality/inequality (e.g. `len(x) = 0`); `inferZerosInSumGeq` deduces that all terms in a nonneg sum must be zero. — [C]
- **Predicate rewriting via entailment** — `arith_entail.cpp:41, :47, :107, :134` — turns an arithmetic predicate over string lengths into `true`/`false` when entailed. **This is exactly what the `foreign-theory-rewrite` pass calls.** — [C]
- **Contains / indexof / replace / substr rewrites** — `sequences_rewriter.cpp:2824, :3123, :3347, :3387, :3798, :3888, :3918, :2525, :2736, :2475, :3981, :4018` — the bulk of the named rewrites; every one consults the entailment utilities above. — [C]
- **Length-preserving canonicalisation** — `sequences_rewriter.cpp:4096, :4106` — rewrites a term to a canonical string of the same symbolic length so length-only equalities discharge syntactically. — [C]
- **Regexp rewrites** — `sequences_rewriter.cpp:757, :925, :1087, :1205, :2123`, plus `:991, :1060, :1717, :2081`. — [C]
- **Strings-only rewriter** — `strings/strings_rewriter.cpp:36, :96, :132, :154, :214, :225, :275, :298, :321, :334` — the kinds that exist only for `String`, not `Seq`. — [C]
- **Named rewrite catalogue** — `strings/rewrites.h:28-236` — **202 named rewrite IDs**: `RE_*` 44, `STR_*` 25, `CTN_*` 24, `SS_*` 22, `IDOF_*` 15, `RPL_*` 10, `UPD_*` 8, `REPL_*` 8, `SUF_PREFIX_*` 7, `REPLACE_RE*` 5, `LEN_*` 5, `INDEXOF_RE_*` 5, `EQ_*` 5, `SEQ_*` 4, `SPLIT_EQ*` 3, `STOI_*` 2, `REPLALL_*` 2, plus 8 singletons. — [C]
- **Strings inference-ID catalogue** — `src/theory/inference_id.h:633-946` — **87 `STRINGS_*` IDs**: base/normalisation/cycle 7, unit/seq-unit 5, cardinality 2, flat-form 5, normal-form core 17, disequality 9, code points 2, sequences-as-array 12, regexp 9, extended functions 11, eager/registration/misc 8. — [I]

### 9.7 Sets

- **Full-effort check loop** — `src/theory/sets/theory_sets_private.cpp:254, :1368` — *FS* logics, ALL — on by default — iterates to fixed point: register terms → downward closure → upward closure → filter/map up/down → group → disequalities → comprehension reduction → cardinality → relations. — [C]
- **Downward closure** — `theory_sets_private.cpp:490` — propagates memberships downward into operands (`SETS_DOWN_CLOSURE`). — [I]
- **Upward closure** — `:552` — propagates memberships from operands up into `∪`/`∩`/`\`/`univset` terms (`SETS_UP_CLOSURE`, `SETS_UP_CLOSURE_2`, `SETS_UP_UNIV`). — [I]
- **Proxy variables** — `:296`, IDs `SETS_PROXY`, `SETS_PROXY_SINGLETON` — `--sets-proxy-lemmas` default **`false`**, **expert**, controls the *eager* variant; singleton proxies are unconditional. — [C]
- **Disequality handling** — `:1275` — introduces a witness element skolem per asserted set disequality (`SETS_DEQ`). — [I]
- **Comprehension reduction** — `:1326` — ALL (`set.comprehension` is a cvc5 extension) — reduces to a quantified membership axiom. — [I]
- **Higher-order set operators** — `:750, :784, :813, :863, :908, :917, :1038-1251`, kind test `:1653` — ALL — on by default — membership propagation for `set.map`, `set.filter`, `rel.group`: `SETS_MAP_UP`, `SETS_MAP_DOWN_POSITIVE`, `SETS_FILTER_UP/DOWN`, `SETS_RELS_GROUP_*` (7 rules). **Combining these with cardinality sets `IncompleteId::SETS_HO_CARD`** (`:358`). — [I]
- **Set reduction (fold/aggregate/project)** — `sets/set_reduction.cpp:33, :90, :114`; callers `theory_sets.cpp:169, :177, :182`, `theory_sets_rewriter.cpp:1109` — eliminates `set.fold` / `rel.aggregate` / `rel.project` at `ppRewrite` into quantified/UF definitions. — [C]
- **Set cardinality: Venn-region graph** — `sets/cardinality_extension.cpp:199, :234, :260, :313, :335, :678, :697, :983` — *FS*, ALL, when `set.card` occurs — `--sets-card-exp` default **`true`**, **expert** — nodes are eqc representatives, edges connect a set to its Venn regions; maintains *normal forms* (sets of non-empty Venn regions) in the style of the string solver, emitting `SETS_CARD_SPLIT_EMPTY`, `SETS_CARD_SPLIT_EQ`, `SETS_CARD_CYCLE`, `SETS_CARD_EQUAL`, `SETS_CARD_GRAPH_*` (5), `SETS_CARD_MINIMAL`, `SETS_CARD_NEGATIVE_MEMBER`, `SETS_CARD_POSITIVE`. — [P] (Bansal et al., IJCAR 2016; Liang et al., CAV 2014) [I]
- **Extended cardinality (universe / complement)** — `cardinality_extension.cpp:74, :86, :1136` — `--sets-exp` default **`false`**, **expert**, enables `set.complement` / `set.universe`. **Default off.** Emits `SETS_CARD_UNIV_SUPERSET`, `SETS_CARD_UNIV_TYPE`. — [I]
- **Cardinality incompleteness sources** — `theory_sets_private.cpp:316, :358, :365` — `SETS_RELS_CARD` (cardinality on a relation term — explicitly "hard"/unsupported), `SETS_HO_CARD` (cardinality + map/filter/fold), `SETS_FMF_BOUND_CARD` (cardinality + `--fmf-bound`). — [C]
- **Model construction from the cardinality graph** — `cardinality_extension.cpp:1036, :1041` — assigns model elements only to graph leaves, deriving all other sets by union of their Venn regions. — [C]
- **Sets care graph / model** — `theory_sets_private.cpp:1434, :1502, :1518, :1630`. — [C]
- **`set.choose` / `set.is_singleton` expansion** — `theory_sets_private.cpp:1716, :1749`. — [C]
- **Sets normal form** — `sets/normal_form.h:26, :58` — the canonical constant set value is a right-nested `(set.union (set.singleton c1) …)` with sorted, distinct elements. — [C]
- **Sets rewriter** — `sets/theory_sets_rewriter.cpp:141, :798, :119, :48`, plus `:829, :839, :884, :918, :953, :990, :1028, :1065, :1089, :1104`. — [C]
- **Sets skolem cache** — `sets/skolem_cache.h:48-57` — `SK_PURIFY`, `SK_DISEQUAL`, `SK_TCLOSURE_DOWN1/2`, `SK_JOIN`. — [C]
- **Sets proof reconstruction** — `sets/infer_proof_cons.cpp`, `sets/proof_checker.cpp`. — [C]

### 9.8 Relations

- **Relations solver main loop** — `sets/theory_sets_rels.cpp:57, :75, :239` — ALL (relation kinds are a cvc5 extension) — `--rels-exp` default **`true`**, **expert**; enabled lazily at `theory_sets_private.cpp:217`. — [C]
- **Transpose** — `theory_sets_rels.cpp:1211, :1232` — `(a,b) ∈ R ⟺ (b,a) ∈ R⁻¹`; `SETS_RELS_TRANSPOSE_EQ`, `…_REV`. — [I]
- **Product** — `:997` — `SETS_RELS_PRODUCT_SPLIT`, `…_PRODUCE_COMPOSE`. — [I]
- **Join** — `:1061, :1402` — `SETS_RELS_JOIN_SPLIT_1/2`, `…_JOIN_COMPOSE`. — [I]
- **Table join** — `:1142, :1515` — `SETS_RELS_TABLE_JOIN_UP/DOWN`. — [I]
- **Join image** — `:330, :455` — `SETS_RELS_JOIN_IMAGE_UP/DOWN`. — [I]
- **Identity relation** — `:529, :571` — `SETS_RELS_IDENTITY_UP/DOWN`. — [I]
- **Transitive closure** — `:635, :755, :786, :824, :868, :907, :1263`; ground evaluation `sets/rels_utils.cpp:30, :48` — **handled by an explicit reachability graph, not a fixpoint saturation.** Up-rules: `(a,b) ∈ R ⟹ (a,b) ∈ R⁺` and `(a,b),(b,c) ∈ R⁺ ⟹ (a,c) ∈ R⁺` (`SETS_RELS_TCLOSURE_UP`). Down-rule: `(a,b) ∈ R⁺` yields skolems `SK_TCLOSURE_DOWN1/2` with a one-step-or-split disjunction (`SETS_RELS_TCLOSURE_DOWN`, `:715-726`). A per-relation graph (`d_rRep_tcGraph`/`d_tcr_tcGraph`) prunes already-derivable memberships. **Completeness: no explicit claim in the source, and no `setModelUnsound` for tclosure itself — but `set.card` applied to any relation kind, `R⁺` included, sets `IncompleteId::SETS_RELS_CARD` (`theory_sets_private.cpp:316`), so tclosure with cardinality is explicitly model-incomplete.** — [C] [I]
- **Tuple trie index** — `:1763, :1796, :1826, :1853` — prefix trie over tuple element representatives, for join/product composition lookups. — [C]
- **Tuple variable reduction** — `:1701, :1719, :1735` — `SETS_RELS_TUPLE_REDUCTION`. — [I]
- **Relation aggregate / group evaluation** — `rels_utils.cpp:81, :150, :74`. — [C]
- **Relations inference-ID catalogue** — `inference_id.h:603-625` — **23 `SETS_RELS_*` IDs** (identity 2, join 3, join-image 2, table-join 2, product 2, tclosure 2, transpose 2, tuple reduction 1, group 7), plus **21 `SETS_*` core IDs** (`:556-577`) and **13 `SETS_CARD_*`** (`:580-601`). — [I]

### 9.9 Bags

- **Bags reachability** — `src/theory/bags/theory_bags.cpp:54, :437` — **`ALL` / `QF_ALL` only** — `--bags` default `true`, **expert** — `LogicInfo` emits the string `FB` (`logic_info.cpp:411`) but **never parses it**, so no SMT-LIB logic name enables `THEORY_BAGS` on its own. — [C]
- **Bags strategy** — `bags/strategy.cpp:83-86` — a four-step fixed schedule with breaks: `CHECK_INIT`, `CHECK_BAG_MAKE`, `CHECK_BASIC_OPERATIONS`, `CHECK_QUANTIFIED_OPERATIONS`. **Much simpler than the strings strategy; no effort-dependent block.** — [C]
- **`bag.make` handling** — `bags/bag_solver.cpp:192, :225, :237` — `BAGS_BAG_MAKE`, `BAGS_BAG_MAKE_SPLIT`, `BAGS_NON_NEGATIVE_COUNT`. — [I]
- **Basic bag operations** — `bag_solver.cpp:47, :122, :138, :148, :159, :170, :181, :243, :254, :271` — count-based (multiplicity) axioms per element: `BAGS_EMPTY`, `BAGS_UNION_DISJOINT`, `BAGS_UNION_MAX`, `BAGS_INTERSECTION_MIN`, `BAGS_DIFFERENCE_SUBTRACT`, `BAGS_DIFFERENCE_REMOVE`, `BAGS_SETOF`, `BAGS_DISEQUALITY`. — [I]
- **Quantified / higher-order bag operations** — `bag_solver.cpp:92, :280, :333, :355, :379, :403` — `BAGS_MAP_DOWN`, `BAGS_MAP_DOWN_INJECTIVE`, `BAGS_MAP_UP1/UP2`, `BAGS_FILTER_UP/DOWN`. — [I]
- **Inference generator** — `bags/inference_generator.cpp:69-955` — 30+ builders, one per axiom. — [I]
- **Bag reduction (card/fold/aggregate/project)** — `bags/bag_reduction.cpp:34, :94, :170, :194`; callers `theory_bags.cpp:106, :117, :127, :133` — `bag.card` and `bag.fold` are reduced at `ppRewrite` into quantified/UF definitions. — [C]
- **Bags constant evaluation** — `bags/bags_utils.cpp:59, :120, :153, :265-1004` — canonical constant bag is a sorted disjoint union of `bag.make` terms; all operators evaluated on the element→multiplicity map. — [C]
- **Bags inference-ID catalogue** — `inference_id.h:226-248` — **23 `BAGS_*` IDs**. — [I]

### 9.10 Datatypes

- **Check loop (labelling + splitting)** — `src/theory/datatypes/theory_datatypes.cpp:216, :1814` — *DT*, ALL, plus internally for tuples/records/nullables/sygus — on by default — cycle check → split until fixed point; splits an eqc with no known constructor over all constructors (`DATATYPES_SPLIT`). — [C]
- **Constructor labelling / tester propagation** — `theory_datatypes.cpp:629, :634, :648, :672, :685, :741` — per-eqc constructor label and negative-tester set; `DATATYPES_LABEL_EXH`, `DATATYPES_TESTER_CONFLICT`, `DATATYPES_TESTER_MERGE_CONFLICT`. — [I]
- **Constructor merge / unification / clash** — `:491, :950` — same constructor ⟹ argument-wise `DATATYPES_UNIF`; different ⟹ `DATATYPES_CLASH_CONFLICT`. — [I]
- **Selector collapse and instantiation** — `:908, :995, :1350, :1367` — `DATATYPES_COLLAPSE_SEL` and `DATATYPES_INST`. — [I]
- **Shared selectors** — `:1157, :1359`; `datatypes_rewriter.cpp:1074` — `--dt-share-sel` default **`false`**, **expert**, but **forced true for SyGuS** (`set_defaults.cpp:900`) — shares one selector symbol across constructors with same-typed arguments. — [C]
- **Occurs check / cycle detection** — `:1446, :1735`, gate `:1462` — `--dt-cyclic` default **`true`**, **expert** — detects `x = C(… x …)` for inductive datatypes ⟹ `DATATYPES_CYCLE`. **`--no-dt-cyclic` silently drops the acyclicity axiom.** — [I]
- **Codatatype bisimulation** — `:1556, :1242`, gate `:1500` — `--cdt-bisimilar` default **`true`**, **expert** — partition refinement over codatatype eqcs; bisimilar classes are forced equal (`DATATYPES_BISIMILAR`). — [P] [I]
- **Recursive-singleton reasoning** — `:1278, :1847-1900` — for datatypes with exactly one value modulo the cardinality of uninterpreted argument sorts: `DATATYPES_REC_SINGLETON_EQ` (quantified, under card-1 assumptions) and `DATATYPES_REC_SINGLETON_FORCE_DEQ` (non-quantified: assert the sorts have cardinality > 1). — [I]
- **Cardinality-driven split suppression** — `:1929-1957` — does **not** split an eqc whose possible constructors admit infinitely many values *and* which has no selectors applied; uses `Env::isFiniteCardinalityClass`, so the answer depends on whether FMF is on. — [C]
- **Binary splitting** — `:1888` — `--dt-binary-split` default **`false`**, **expert** — replaces the n-way split with `is-C(x) ∨ ¬is-C(x)` plus a phase preference. — [C]
- **Blast splits** — `:1996` — `--dt-blast-splits` default **`false`**, **expert** — continues splitting all eqcs in one round. — [C]
- **Inferences as lemmas** — `datatypes/inference_manager.cpp:53-55`, `inference.h:54` — `--dt-infer-as-lemmas` default **`false`**, **expert**. — [C]
- **Polite-combination optimisation** — `theory_datatypes.cpp:1411` — `--dt-polite-optimize` default **`true`**, **expert**. — [C]
- **Nested recursion** — `:340, :353` — `--dt-nested-rec` default **`false`**, **expert** — allows datatypes recursing through other parametric types (sets/arrays); otherwise such types raise a logic exception. — [C]
- **`--datatypes-exp`** — `:365, :384`; `datatypes_options.toml:173` default **`true`**, **expert** — gates experimental datatype features (raises `SafeLogicException` when off). — [C]
- **Care graph / model** — `:1060, :1114, :2088, :2168`. — [C]
- **Datatypes rewriter** — `datatypes/datatypes_rewriter.cpp:268, :538, :577, :598, :651, :691, :714, :447, :1094, :1127, :1169, :1196, :63` — includes `match` expansion, updater expansion, and SyGuS-to-builtin evaluation folding. — [C]
- **Codatatype constant normalisation (μ-terms / de Bruijn)** — `datatypes_rewriter.cpp:749, :884, :912, :1003, :1038` — canonicalises cyclic codatatype constants by quotienting the reference graph and re-indexing back-references as de Bruijn indices. — [C]
- **Tuple utilities** — `datatypes/tuple_utils.cpp:27-199` — reused by sets, bags, relations. — [C]
- **Project operator payload** — `datatypes/project_op.cpp:41, :53, :58`. — [C]
- **SyGuS extension (datatype-level symmetry breaking)** — `datatypes/sygus_extension.cpp:63, :242, :171, :1047, :1593` — SyGuS inputs — on by default for SyGuS — emits `DATATYPES_SYGUS_SYM_BREAK`, `_CDEP_SYM_BREAK`, `_ENUM_SYM_BREAK`, `_SIMPLE_SYM_BREAK`, `_FAIR_SIZE`, `_FAIR_SIZE_CONFLICT`, `_VAR_AGNOSTIC`, `_SIZE_CORRECTION`, `_VALUE_CORRECTION`, `_MT_BOUND`, `_MT_POS`. — [I]
- **SyGuS fairness / size decision strategy** — `sygus_extension.cpp:1358, :1474, :1488, :1838-1899` — `--sygus-fair` default `DT_SIZE`, `--sygus-fair-max` default `true`, `--sygus-abort-size` default `-1` — enumerates candidate solution sizes in increasing order with a fairness measure term. — [C]
- **SyGuS symmetry-breaking sub-options** — `datatypes_options.toml:109, :117, :125`; relevancy `sygus_extension.cpp:436`, traversal predicates `:501, :518`, lemma caching `:1256, :1298, :1305` — `--sygus-sym-break-pbe`, `--sygus-sym-break-lazy`, `--sygus-sym-break-rlv`, all default **`true`**. — [C]
- **Simple SyGuS symmetry breaking** — `datatypes/sygus_simple_sym.cpp:153, :421, :476, :568, :576`; predicate builder `sygus_extension.cpp:594` — `--sygus-simple-sym-break` default `AGG` — syntactic, per-constructor redundancy elimination (`x+0`, `x∧x`, associativity/commutativity orderings) applied without search. — [C]
- **SyGuS rewriter mode** — `datatypes_options.toml:91` — `--sygus-rewriter` default `EXTENDED` (`none`/`basic`/`extended`). — [C]
- **Datatypes proof reconstruction** — `datatypes/infer_proof_cons.cpp:36, :51, :509, :526`. — [C]
- **Datatypes inference-ID catalogue** — `inference_id.h:274-336` — **26 `DATATYPES_*` IDs**: core 15, SyGuS 11. — [I]

### 9.11 Arrays

- **Lazy Row-lemma architecture** — `src/theory/arrays/theory_arrays.cpp:1899, :1971, :2043, :2198, :1322` — QF_A*, A* — on by default — Row lemmas are queued during merges and discharged only at full effort. — [P] (de Moura & Bjørner, FMCAD 2009) [C]
- **RIntro1** — `theory_arrays.cpp:837-842`, flag `arrays/array_info.h:59` — asserts `select(store(a,i,v), i) = v` (`ARRAYS_READ_OVER_WRITE_1`). — [I]
- **RIntro2 (Row)** — `:2018-2020, :2176, :2324` — `i ≠ j ⟹ select(store(a,i,v), j) = select(a,j)` (`ARRAYS_READ_OVER_WRITE`), with the contrapositive `ARRAYS_READ_OVER_WRITE_CONTRA` (`:2034`). — [I]
- **Extensionality** — `:1506, :1514`; skolem `arrays/skolem_cache.cpp:27` (`SkolemId::ARRAY_DEQ_DIFF`) — from `a ≠ b`, introduces a deterministic difference index `k` and asserts `select(a,k) ≠ select(b,k)` (`ARRAYS_EXT`). — [I]
- **Row-lemma tautology filtering** — `:2109, :2126, :2150, :2162, :2257, :2274, :2298, :2310` — `ARRAYS_EQ_TAUTOLOGY`: discards a queued Row lemma whose antecedent or consequent already holds. — [I]
- **Constant arrays** — `:1856`, `array_info.h:61` — `--arrays-exp` default **`false`**, **expert**, checked at `:321` — enables constant arrays and `eqrange`; also forces quantifiers on (`set_defaults.cpp:551`) and `--fmf-bound` on (`:1514`). **Default off.** — [C]
- **Linear-array optimisation** — `:1665, :1811, :1879, :1948`; `array_info.h:58`, `setNonLinear:1600` — `--arrays-optimize-linear` default **`true`**, **expert** — skips Row lemmas for arrays occurring linearly in the store chain. **Automatically disabled whenever models are produced** (`set_defaults.cpp:932`). — [P] [C]
- **Weak equivalence** — `:449, :463, :509, :553, :567, :609, :656`, main loop `:1326-1425` — `--arrays-weak-equiv` default **`false`**, **expert**, **and listed under `incompatibleWithModels`** (`set_defaults.cpp:1205`) — implements Christ/Hoenicke SMT 2014: a weak-equivalence graph with primary/secondary edges (`array_info.h:62-65`), generating lemmas only when two reads land in the same bucket with equal weak-equiv rep index. Note the lemma at `:1417` is emitted with `InferenceId::NONE` (an acknowledged TODO). **Default off and model-incompatible.** — [P] [C]
- **Eager index splitting** — `:2078` — `--arrays-eager-index` default **`true`**, `regular`, **but forced false for non-quantified A+UF+arith logics (QF_AUFLIA)** (`set_defaults.cpp:767-776`). — [C]
- **Eager lemma generation** — `:1324, :2092` — `--arrays-eager-lemmas` default **`false`**, **expert**. — [C]
- **Care-graph sharing reduction** — `:2200, :929, :1030` — `--arrays-reduce-sharing` default **`false`**, **expert** — uses model values to prune the care graph. — [C]
- **Propagation effort** — `:1498, :1996, :2070, :2232, :426` — `--arrays-prop` default `2` (full), **expert**. — [C]
- **Preprocessing: solve-write and `ppAssert`** — `:177, :316, :384, :167` — solves `store(a,i,v) = b` for `a` when possible. — [C]
- **`may-equal` equality engine** — `:1367, :1646, :1794, :1829` — a second, coarser union-find over array terms connected by `store`, used to bucket reads and trigger Row lemma generation only within a may-equal class. — [C]
- **Array info map** — `arrays/array_info.cpp`, `.h:56-70` — per-array context-dependent record; `RowLemmaType` is a 4-tuple `(a,b,i,j)` with a custom hash (`array_info.h:31`). — [C]
- **Arrays decision strategy** — `:2187, :2343-2353` — requests decisions on queued Row-lemma index equalities. — [C]
- **Arrays rewriter** — `arrays/theory_arrays_rewriter.cpp:529, :738, :45, :125, :248, :270, :488, :855, :76` — store-chain sorting and dedup, constant-array normalisation using the most-frequent stored value as the default, and `eqrange` expansion to a bounded quantifier. — [C]
- **Arrays inference-ID catalogue** — `inference_id.h:215-222` — **6 `ARRAYS_*` IDs**; the weak-equivalence path emits `InferenceId::NONE`. — [I]

### 9.12 UF

- **Congruence closure engine** — `src/theory/uf/equality_engine.cpp:350, :551, :685, :972, :1010, :2190` — all logics with equality — on by default — backtrackable union-find with a **proof forest** of equality edges (`addGraphEdge:1165`), a use-list/trigger-term mechanism, and function-kind registration (`addFunctionKind:308`) that can additionally *evaluate* congruent applications (`subtermEvaluates:332`, `evaluateTerm:2138`, `processEvaluationQueue:2161`). — [P] [C]
- **Explanation generation** — `equality_engine.cpp:1290, :1472, :1491, :1552, :1209, :2462` — shortest-path walk in the proof forest producing an antecedent set, optionally populating an `EqProof` tree annotated with `MergeReasonType`. — [C]
- **`EqProof` → `ProofNode` conversion** — `uf/eq_proof.cpp:797, :854, :104, :540, :619, :691, :78` — **reachable**, called from `uf/proof_equality_engine.cpp:500` — described in-source as a *"best-effort solution until the EqualityEngine is updated to produce ProofNodes directly"*: reorders coarse-grained steps, uncurries HO applications, normalises away predicate equalities `(= t true/false)`. — [C]
- **Proof equality engine** — `uf/proof_equality_engine.cpp:48, :81, :128, :152, :169, :193, :203, :212, :252, :287, :321` — the proof-producing wrapper every theory uses to assert facts, conflicts, and lemmas into the shared equality engine. — [C]
- **`TheoryUF` core** — `uf/theory_uf.cpp:143, :173, :299, :387, :582, :535, :499` — registers `APPLY_UF` as a congruence kind (HO flag at `:112`), builds the care graph. — [C]
- **UF cardinality / sort model (region-based)** — `uf/cardinality_extension.cpp:574, :618, :631, :660, :725, :795, :984, :1163, :1239, :1266, :1319`; regions at `:33-556` — UFC and FMF — `--uf-ss` default `FULL` (`uf_options.toml:26`), **instantiated only when `--finite-model-find` is on** (`theory_uf.cpp:108-113`); `--uf-card-exp` default `true`, **expert**, must be on for cardinality-constraint logics or a `SafeLogicException` is thrown (`:94-102`) — splits eqcs of an uninterpreted sort into *regions*, merges regions when disequality density is high, and a fully-disequal set inside one region is a clique ⟹ `UF_CARD_CLIQUE`. Also `UF_CARD_SPLIT`, `UF_CARD_EQUIV`, `UF_CARD_COMBINED`, `UF_CARD_ENFORCE_NEGATIVE`, `UF_CARD_MONOTONE_COMBINED`, `UF_CARD_SIMPLE_CONFLICT`. — [P] [I]
- **Cardinality decision strategy** — `cardinality_extension.cpp:556-569, :1410` — enumerates `|S| ≤ k` for increasing k; `--uf-ss=no-minimal` shrinks without minimality, `--uf-ss=none` disables the subsolver. — [C]
- **Cardinality fairness across sorts** — `cardinality_extension.cpp:1426+, :1467, :1518, :1532` — `--uf-ss-fair` default **`true`** — interleaves cardinality bounds across multiple uninterpreted sorts. — [C]
- **Cardinality abort bound** — `uf_options.toml:18` — `--uf-ss-abort-card` default `-1` (no limit). — [C]
- **Higher-order: app completion** — `uf/ho_extension.cpp:490, :515, :211` — HO logics — on by default when HO; requires `--uf-ho-exp` (default `true`, **expert**) or a `SafeLogicException` — equates a curried `HO_APPLY` chain with its uncurried `APPLY_UF` form (`UF_HO_APP_ENCODE`, `UF_HO_APP_CONV_SKOLEM`, `UF_HO_CG_SPLIT`); run to fixed point before any other HO schema (`check:824`). — [I]
- **Higher-order: extensionality** — `ho_extension.cpp:143, :193, :305` — `--uf-ho-ext` default **`true`**, **expert** — from `f ≠ g`, introduces argument skolems with `f(k) ≠ g(k)` (`UF_HO_EXTENSIONALITY`); the model-driven variant emits `UF_HO_MODEL_EXTENSIONALITY` / `UF_HO_MODEL_APP_ENCODE`. **Disabling it sets `IncompleteId::UF_HO_EXT_DISABLED`.** — [I]
- **Lambda lifting** — `uf/lambda_lift.cpp:67, :103, :157, :215, :230, :273, :293, :318` — `--uf-lazy-ll` default **`true`** — replaces a lambda by a fresh skolem plus a defining axiom, asserted only when needed. — [C]
- **Lazy lambda handling** — `ho_extension.cpp:602` — the last HO schema (`check:842-848`) — `UF_HO_LAMBDA_APP_REDUCE`, `UF_HO_LAMBDA_LAZY_LIFT`, `UF_HO_LAMBDA_UNIV_EQ`; deliberately run *after* extensionality because it may introduce quantifiers. — [I]
- **Lambda quantifier elimination** — `uf_options.toml:68` — `--uf-lambda-qe` default **`false`**, **expert** — applies QE eagerly when two lambdas are equated. — [C]
- **Function constants ↔ array constants** — `uf/function_const.cpp:35, :74, :88, :102, :154, :171, :436` — represents a function model value internally as an array constant and converts back to a `LAMBDA` for printing and evaluation. — [C]
- **BV↔arith conversions subsolver** — `uf/conversions_solver.cpp:45, :57`, instantiated at `theory_uf.cpp:335-340` — logics mixing BV and arith (`bv2nat`/`int2bv`) — on by default, lazy and model-based — reduces `BITVECTOR_UBV_TO_INT` / `INT_TO_BITVECTOR` only when the term's model value disagrees with its UF representative (`UF_ARITH_BV_CONV_REDUCTION`). — [C]
- **Eager BV↔arith conversion** — `uf_options.toml:76` — `--eager-arith-bv-conv` default **`false`**, `regular`. — [C]
- **Model-based BV↔arith refinement** — `conversions_solver.cpp:77-87`; `uf_options.toml:84` — `--model-based-arith-bv-conv` default **`false`**, **expert** — asserts a point-wise refinement `arg = v ⟹ n = eval(v)` instead of the full reduction. — [C]
- **UF symmetry breaker** — `uf/symmetry_breaker.cpp:200, :252, :258, :485, :566, :709, :715, :863, :955`; template matcher `:54-193`; call sites `theory_uf.cpp:446-449` (`presolve`) and `:473-475` (`ppStaticLearn`) — QF_UF — `--symmetry-breaker` default **`true`**, `regular`, `no_support = ["proofs"]`, **but narrowed by `set_defaults.cpp:732-744` to non-incremental, pure-QF_UF, non-safe-unsat-core runs** — **reachable, but very narrowly**: any incremental run, any non-pure-UF logic, any quantified logic, or unsat cores / `FULL_STRICT` proofs disables it. Detects permutation invariance of the assertion set and emits `UF_BREAK_SYMMETRY` clauses during `presolve` (noted in-source as a non-standard, unsound-lemma mechanism). — [P] (Déharbe et al., CADE 2011) [C]
- **Lazy distinct handling** — `uf/distinct_extension.cpp:130, :157, :222, :282, :151`; wired at `theory_uf.cpp:57, :164, :205, :701` — all UF logics — **on by default, no option gate** — instead of expanding `distinct(x₁..xₙ)` into O(n²) disequalities, tracks per-eqc lists of the distinct constraints they occur in; a merge bringing two members of the same `distinct` together is a conflict (`UF_DISTINCT_DEQ`). Negated distincts are reduced lazily at LAST_CALL against the model (`UF_DISTINCT_DEQ_MODEL`). — [C]
- **Diamonds preprocessing** — `uf/diamonds_proof_generator.cpp:25, :167`; call site `theory_uf.cpp:471` — all UF logics — **on by default, no option gate** — recognises the "diamond" pattern `(x=a ∨ x=b) ∧ (y=c ∨ y=d) ∧ …` chained by equalities and learns the transitive consequence; produces its own proofs. — [C]
- **UF rewriter** — `uf/theory_uf_rewriter.cpp:73, :106, :207, :295` — beta-reduces applications of lambdas and function constants, uncurries `HO_APPLY`. — [C]
- **UF inference-ID catalogue** — `inference_id.h:951-1027` — **17 `UF_*` IDs**: symmetry 1, distinct 3, cardinality 7, higher-order 8 (sic — the file lists 9 HO ids across two groups), conversions 2. — [I]

### 9.13 Separation logic

- **`TheorySep` main check** — `src/theory/sep/theory_sep.cpp:524, :290, :321, :883` — `SEP_*` logics, ALL — `--sep` default `true`, **expert** — labelled-heap reduction plus a counterexample-guided refinement loop over negated spatial assertions. — [P] (Reynolds et al.) [C]
- **Labelling reduction (`reduceFact`)** — `theory_sep.cpp:342` — every spatial atom is rewritten to a `SEP_LABEL`-ed form over a set-of-locations label; unlabelled top-level atoms get the base label via `SEP_LABEL_INTRO` (`:375`); `sep.star` / `sep.wand` children get fresh labels via `SEP_LABEL_DEF`. — [I]
- **Disjoint-heap constraints** — `:1374, :1327, :1355, :1418, :1449` — encodes separation as set disjointness plus union over label sets, **using the theory of sets**. — [C]
- **`sep.wand` nil constraint** — `:404-411` — `sep.nil` is forced not to occur in the antecedent heap of a magic wand (`SEP_NIL_NOT_IN_HEAP`). — [I]
- **Points-to propagation** — `:1952, :1918, :896, :901` — when two locations merge, matching `pto` facts force their data equal (`SEP_PTO_PROP`) or conflict (`SEP_PTO_NEG_PROP`). — [I]
- **Counterexample-guided refinement for negated star/wand** — `:1515, :1467, :1791, :1813`, refinement lemma `:795` — for each active negated spatial atom, instantiates it against the *current label model* and, if the instantiation is not already falsified, adds a `SEP_REFINEMENT` lemma. — [P] [I]
- **Minimal refinement** — `:668, :1528` — `--sep-min-refine` default **`false`**, **expert** — restricts refinement lemmas to the innermost assertions. — [C]
- **Incompleteness and the supported fragment** — `:876` (`setModelUnsound(IncompleteId::SEP)`), warning `:800` ("should never happen for complete fragments"), `:963-990` — **the procedure is complete only for the quantifier-free, bounded fragment.** When a refinement lemma repeats (the loop makes no progress) or the reference-location bound cannot be established (typically from a quantified `pto`), the theory declares the result model-unsound. **`TheorySep::getProofChecker()` returns `nullptr` (`:103`) — separation logic produces no proofs.** — [C]
- **Heap bounds / reference bound** — `:1183, :1221, :948, :925, :1146, :79` — collects all location terms syntactically occurring in the input to bound the base label set (`SEP_REF_BOUND`, `SEP_DISTINCT_REF`, `SEP_SYM_BREAK`); assertions must be processed at preprocess time so quantified assertions are seen (`:923`). — [I]
- **`sep.emp` reduction** — `SEP_EMP` (`inference_id.h:534`) — `emp` labelled by L reduces to `L = ∅`. — [I]
- **Finite-data witness** — `:820-825` — `SEP_WITNESS_FINITE_DATA`: for a finite data type, forces a witness location so the heap model is well-defined. — [I]
- **Model post-processing / label model** — `:159, :1813, :2105, :1765` — builds the concrete heap (a set of location↦data pairs) from the label model for `get-model`. — [C]
- **Sep rewriter** — `sep/theory_sep_rewriter.cpp` — flattens nested `sep.star`, handles `emp` units and trivially false spatial formulas. — [C]
- **Sep inference-ID catalogue** — `inference_id.h:525-550` — **13 `SEP_*` IDs**. — [I]

### 9.14 Cross-cutting defaults for this group

- **strings ⟹ `--strings-exp`** — `set_defaults.cpp:520-526` — overrides the toml default `false`. The most consequential default flip in this group. — [C]
- **strings / eager-pp / `re-elim=agg` ⟹ quantifiers enabled** — `set_defaults.cpp:532-548` — so that extf reductions and `--re-elim=agg` can introduce bounded quantifiers, handled by the bounded-integers module via `InternalQuantAttribute`. E-matching stays on; `--fmf-bound` is deliberately *not* enabled. — [C]
- **`--arrays-exp` ⟹ quantifiers + `--fmf-bound`** — `set_defaults.cpp:551-556, :1512-1516`. — [C]
- **Uninterpreted-sort owner: arrays vs UF** — `set_defaults.cpp:746-758` — `THEORY_ARRAYS` owns uninterpreted sorts for non-HO, non-FMF, non-quantified-with-UF array logics; otherwise `THEORY_UF`. — [C]
- **MiniSat variable elimination disabled for these theories** — `set_defaults.cpp:905-925` — sets, bags, arrays, strings, datatypes (plus quantifiers, models, nonlinear) force `ALL` → `CLAUSE_ELIM`, because these solvers introduce new literals into the search. — [C]
- **`--arrays-optimize-linear` disabled with models** — `set_defaults.cpp:930-935` — any of `--produce-models` / `--produce-assignments` / `--check-models`. — [C]
- **Cardinality constraints ⟹ `--finite-model-find`** — `set_defaults.cpp:1519-1524` — required for the UF `SortModel` machinery to be instantiated at all. — [C]
- **SyGuS ⟹ `--dt-share-sel`** — `set_defaults.cpp:898-903`. — [C]
- **`--safe-options` ⟹ `--no-uf-ho-exp`** — `set_defaults.cpp:144` — disables the higher-order solver, so HO inputs throw a `SafeLogicException`. — [C]

## 10. Quantifier instantiation and model finding

### 10.0 The spine: module list, priority, and effort

`QuantifiersModules::initialize` is a flat sequence of
`if (option) { new Module; modules.push_back(...) }`. **The push order is the
intra-effort priority order**, because `QuantifiersEngine::checkInternal`
iterates modules in vector order inside each effort level and **breaks at the
first module that queues a lemma.** `[C]`

Construction order — `src/theory/quantifiers/quantifiers_modules.cpp:51-131`:

> `QuantConflictFind` → `InstStrategySubConflict` → `ConjectureGenerator` →
> `InstantiationEngine` (E-matching) → `InstStrategyCegqi` → `SynthEngine`
> (sygus) → `BoundedIntegers` → `ModelEngine` → `QuantDSplit` →
> *(AlphaEquivalence — allocated but NOT pushed as a module)* →
> `InstStrategyEnum` → `InstStrategyPool` → `SygusInst` → `InstStrategyMbqi` →
> `OracleEngine`

Effort levels (`quant_module.h:43-56`):
`QEFFORT_CONFLICT < QEFFORT_STANDARD < QEFFORT_MODEL < QEFFORT_LAST_CALL`. The
outer loop is `quantifiers_engine.cpp:455-458`; the model is built by
`d_te->buildModel()` exactly at the level returned by the max `needsModel`
(`:462-476`). `[C]`

| effort | modules |
| --- | --- |
| CONFLICT | `QuantConflictFind` (`quant_conflict_find.cpp:2634`), `InstStrategySubConflict` (`inst_strategy_sub_conflict.cpp:67`), `QuantDSplit` (`quant_split.cpp:233`) |
| STANDARD | `InstantiationEngine` (`ematching/instantiation_engine.cpp:153`), `InstStrategyCegqi` (`cegqi/inst_strategy_cegqi.cpp:294`), `BoundedIntegers` (`fmf/bounded_integers.cpp:420`), `SygusInst` (`sygus_inst.cpp:265`), `ConjectureGenerator` (`conjecture_generator.cpp:463`), `ModelEngine` under `--mbqi-interleave` (`fmf/model_engine.cpp:77`), `InstStrategyEnum` under `--enum-inst-interleave` (`inst_strategy_enumerative.cpp:76`) |
| MODEL | `ModelEngine` (`fmf/model_engine.cpp:81`), `InstStrategyMbqi` (`inst_strategy_mbqi.cpp:119`), `OracleEngine` (`oracle_engine.cpp:122`), `SynthEngine` (`sygus/synth_engine.cpp:67`) |
| LAST_CALL | `InstStrategyEnum` with `--enum-inst` (`inst_strategy_enumerative.cpp:82`) |
| **all four** | `InstStrategyPool` — its `check` ignores `quant_e` entirely (`inst_strategy_pool.cpp:149-151`), so it fires at CONFLICT too. **A notable asymmetry.** |

Ownership arbitration is a priority integer: `QuantifiersRegistry::setOwner`
refuses to override an owner with `priority <= existing`
(`quantifiers_registry.cpp:77-98`); `hasOwnership(q,m)` is true if `m` owns `q`
**or nobody does**, so unowned quantifiers are processed by every module. `[C]`

### 10.1 Top level

- **`QuantifiersModules::initialize`** — `quantifiers/quantifiers_modules.cpp:41` — all quantified — on by default — gates every quantifier module on exactly one option and fixes their check order. — [C]
- **`QuantifiersEngine::checkInternal`** — `quantifiers_engine.cpp:270-600` — runs modules in four escalating efforts, stops at the first lemma, and at MODEL effort decides sat/unknown by polling `checkComplete` / `checkCompleteFor`. — [C]
- **`shouldRecheck` (term-db saturation retry)** — `quantifiers_engine.cpp:220-262` — all quantified except sygus — `--term-db-mode=relevant-all-delay` (default, `regular`) — before answering unknown, marks *all* eqc terms as "current" in the term DB and re-runs one more round. — [C]
- **`QuantifiersState::getInstWhenNeedsCheck`** — `quantifiers_state.cpp:62` — `--inst-when=MODE` default `full-last-call`, `regular` (toml:505); `--inst-when-phase=N` default `2`, **expert** — decides at which SAT-solver effort instantiation modules may run. — [C]
- **`QuantifiersRegistry`** — `quantifiers_registry.cpp:32` — maps each `forall` to fresh `INST_CONSTANT`s, the inst-constant body, and its owning module. — [C]
- **`Instantiate::addInstantiation` — the single gate** — `instantiate.cpp:92`, internal `:103` — **every strategy funnels through here**; rejects on entailment, duplication, or inst level, else emits `q ⇒ q[t/x]`. — [C]
- **Entailed-instance filter** — `instantiate.cpp:208-223` — `--inst-no-entail` default **`true`**, `regular` (toml:862) — drops an instance whose body is already entailed by current ground equalities; **turned off by `set_defaults` for pure ARITH / pure BV with cegqi** (`set_defaults.cpp:1650`). — [C]
- **Instantiation-level cutoff** — `instantiate.cpp:227-238` — `--inst-max-level=N` default `-1` (off), **expert** — refuses terms whose derivation depth from the input exceeds N; **setting it force-disables cegqi** (`set_defaults.cpp:1527`). — [C]
- **Instantiation round cap** — `quantifiers_options.toml:568` — `--inst-max-rounds=N` default `-1`, `regular`. — [C]
- **Local instantiation** — `instantiate.cpp:188-193`, `isLocalInstId` `:401` — `--inst-local` default **`false`**, `regular` — records certain inference-ids' instances in SAT context rather than user context, so they can be re-derived after backtracking. — [C]
- **`addInstantiationExpFail` (failure masks)** — `instantiate.cpp:434-527` — reverts one variable at a time to compute a minimal sub-tuple responsible for a redundant instance; feeds `IndexTrie`. — [C]
- **`InstMatchTrie` / `CDInstMatchTrie`** — `inst_match_trie.cpp:21, :29` — trie over term vectors used by `recordInstantiationInternal` to reject duplicate instantiations modulo equality. — [C]
- **`InstMatch`** — `inst_match.cpp:23`, `setEvaluatorMode` `:32` — holds the partial substitution during E-matching and forwards each binding to the instantiation evaluator. — [C]
- **`IndexTrie`** — `index_trie.cpp:20`, doc `index_trie.h:28-58` — stores partially-blank index tuples that produced useless instances, so the tuple enumerator never repeats a matching super-tuple. — [C]
- **`TermDb`** — `term_database.cpp:110` — indexes ground terms per operator for candidate generation; `--term-db-mode` default `relevant-all-delay`, `regular`. — [C]
- **Quantifier-body term registration** — `term_registry.cpp:86` — `--register-quant-body-terms` default **`false`**, **expert** — when off, ground subterms occurring only inside quantifier bodies are not added to the term DB. — [C]
- **`HoTermDb`** — `ho_term_database.cpp:28`, merge `:96` — HO logics — `--ho-merge-term-db` default `true`, **expert** — adds `HO_APPLY` / partial-application congruence and merges operator indices modulo equality. — [C] [P] (Barbosa et al., CADE 2019)
- **`EqualityQuery::getInternalRepresentative`** — `equality_query.cpp:29, :78, :196, :201` — `--quant-rep-mode` default `first`, **expert** (`ee`, `depth`) — chooses the canonical eqc representative used by FMF and enumerative instantiation. — [C]
- **`EntailmentCheck`** — `entailment_check.cpp:379, :385` — decides ground/partial entailment by walking term-arg tries. — [C] [P] (Reynolds et al., TACAS 2018 §4.1)
- **`Skolemize::process`** — `skolemize.cpp:47`, constants `:102` — replaces `¬∀x. F` by `¬F[k/x]` with cached skolem constants; proof-producing. — [C]
- **Skolemize induction** — `skolemize.cpp:169, :181, :345`, `isInductionTerm` `:383` — quantified DT / Int — `--dt-stc-ind` and `--int-wf-ind` (both default **`false`**, **expert**), auto-enabled by `--quant-ind` (default `false`, **expert**; `set_defaults.cpp:1685-1706`) — emits a skolemised body strengthened with the induction hypothesis over subterms or smaller integers. **All default off.** — [C]
- **`preSkolemizeQuantifiers`** — `quantifiers_preprocess.cpp:125, :237` — `--pre-skolem-quant` default **`OFF`**, `regular`; nested variant `--pre-skolem-quant-nested` default `true`, **expert** — skolemises existentials at preprocess time using free-variable-indexed skolem functions. Forced ON by `--cegqi-nested-qe` (`set_defaults.cpp:1676-1683`); nested is disabled when the logic lacks UF (`:1715-1721`). — [C]
- **`QuantifiersRewriter` pipeline** — `quantifiers_rewriter.cpp:598`, dispatch `:637`, gating `doOperation` `:2512` — applies COMPUTE_* steps in fixed order: ELIM_SHADOW, ELIM_SYMBOLS, MINISCOPING, AGGRESSIVE_MINISCOPING, PROCESS_TERMS, PRENEX, VAR_ELIMINATION, DT_VAR_EXPAND, COND_SPLIT, EXT_REWRITE. — [C]
- **Miniscoping** — `quantifiers_rewriter.cpp:2611`, gate `:2525-2559` — `--miniscope-quant` default `conj-and-fv`, `regular` — pushes `forall` through conjunctions and splits off variable-free conjuncts; `agg` also distributes over disjunctions. Skipped for quantifiers with user patterns unless `--miniscope-quant-user` (default `false`). — [C]
- **Prenexing** — `quantifiers_rewriter.cpp:2649`, gate `:2568-2583` — `--prenex-quant` default `simple`, **expert** — pulls nested same-polarity quantifiers up. Disabled for pools and user patterns unless `--prenex-quant-user` (default `false`). **Forced to `none` by `--fmf-bound` and by `--global-negate`** (`set_defaults.cpp:1560-1563, 1663-1670`). — [C]
- **Variable elimination** — `quantifiers_rewriter.cpp:2664`, gate `:2584` — `--var-elim-quant` default **`true`**, `regular` — eliminates `x` when the body contains `x ≠ t` / `x = t` at the right polarity. Companions `--var-ent-eq-elim-quant` (default `true`, **no proof support**) and `--var-ineq-elim-quant` (default `true`). — [C]
- **Leibniz equality elimination** — `quantifiers_rewriter.cpp:1756, :1796` — `--leibniz-elim` default **`false`**, **expert** — eliminates variables occurring only under a Leibniz-style equality encoding. — [C]
- **Datatype variable expansion** — `quantifiers_rewriter.cpp:2668`, gate `:2588` — `--dt-var-exp-quant` default `true`, **expert** — expands a datatype-typed bound variable into constructor form when the body forces a single constructor. — [C]
- **Conditional variable splitting** — `quantifiers_rewriter.cpp:2645`, gate `:2561` — `--cond-var-split-quant` default `on`, **expert**; extra `--ite-dtt-split-quant` (default `false`, **expert**, auto-on with `--dt-stc-ind`). — [C]
- **ITE lifting in bodies** — `quantifiers_options.toml:108` — `--ite-lift-quant` default `simple`, `regular`; `--dt-stc-ind` raises it to `all`. — [C]
- **Tautology elimination** — `quantifiers_options.toml:181` — `--elim-taut-quant` default `true`, `regular`. — [C]
- **Extended rewriting of bodies** — `quantifiers_rewriter.cpp:2637`, gate `:2553` — `--ext-rewrite-quant` default **`false`**, `regular`, **no proof support**. — [C]
- **`ExtendedRewriter`** — `extended_rewrite.cpp:45` — a library utility used by sygus, MBQI query construction (`inst_strategy_mbqi.cpp:287`) and solution filtering — aggressive normaliser: redundant-child elimination, commutative-child sorting, BCP, equality-chain normalisation, NNF, ITE pulling and subsumption. — [C]
- **`QuantifiersMacros`** — `quantifiers_macros.cpp:36`, `solveEq` `:254`, `isBoundVarApplyUf` `:158` — quantified UF — `--macros-quant` default **`false`**, `regular`, **no proof support**; `--macros-quant-mode` default `ground-uf` — detects `∀x. f(x) = t[x]` axioms and eliminates `f` by substitution. **Not even constructed unless the flag is on** (`theory_quantifiers.cpp:55-58`), and **unconditionally disabled for higher-order logic** (`set_defaults.cpp:1570-1573`). — [C]
- **`AlphaEquivalence`** — `alpha_equivalence.cpp:176`, trie `:36, :41, :82` — `--quant-alpha-equiv` default **`true`**, `regular` — canonises each quantifier body and asserts `q1 = q2` for alpha-equivalent quantifiers via a typed multiset trie. **Not a `QuantifiersModule`** — invoked from `quantifiers_engine.cpp:644-655` during reduction, so it never participates in the effort ladder. — [C]
- **`QuantConflictFind` (conflict-based instantiation)** — `quant_conflict_find.cpp:2630`, per-quantifier `checkQuantifiedFormula`, match gens `:36` — all quantified, especially UF/DT — `--cbqi` default **`true`**, **`common`** (toml:807); mode `--cbqi-mode` default `prop-eq`, `regular` — searches for a variable assignment making the quantifier body **false** under current ground literals, producing a conflicting (or propagating) instance.
  - *Produces an instance when*: a complete match of the body's negation is found via `MatchGen` (types ground / pred / eq / formula / var / bool_var / tconstraint / tsym, `quant_conflict_find.h:38-49`), checked by `entailmentTest`.
  - *Gives up when*: no match at `EFFORT_CONFLICT` and, in `prop-eq` mode, none at `EFFORT_PROP_EQ` (`:2622-2625`); it also drops quantifiers marked irrelevant this round (`d_irr_quant`). Stops after the first conflict unless `--cbqi-all-conflict` (default `false`, `regular`). — [C] [P]
- **QCF theory-constraint matching** — `quant_conflict_find.cpp:84, :255, :1434, :820` — quantified arithmetic — `--cbqi-tconstraint` default **`false`**, **expert**; **setting it force-enables `--cbqi`** (`set_defaults.cpp:1672-1675`) — allows match generators of type `typ_tconstraint` (theory literals) to participate. — [C]
- **QCF variable-order experiment** — `quant_conflict_find.cpp:1555` — `--cbqi-vo-exp` default `false`, **expert**. — [C]
- **QCF relevant-domain skip** — `quant_conflict_find.cpp:125` — `--cbqi-skip-rd` default `false`, **expert**. — [C]
- **`InstStrategySubConflict`** — `inst_strategy_sub_conflict.cpp:65` — all quantified, no proofs — `--sub-cbqi` default **`false`**, `regular`, `no_support = ["proofs"]`; timeout `--sub-cbqi-timeout=N` default 0 — ships all current theory assertions to a **subsolver**; if UNSAT, emits a core-negation lemma **plus the instantiations the subsolver's proof used**.
  - *Produces instances when*: the subsolver returns UNSAT and `getRelevantQuantTermVectors` yields instantiations for currently-asserted `forall`s.
  - *Gives up when*: the subsolver is sat/unknown, there are no asserted quantifiers, or the returned quantifier is not literally among the asserted ones (`:126-134`). **Default off.** — [C]
- **`ConjectureGenerator`** — `conjecture_generator.cpp:462`, irrelevance fixed point doc `conjecture_generator.h:24-52` — quantified UF/DT (TPTP-style) — `--conjecture-gen` default **`false`**, **expert**; `--conjecture-gen-per-round=N` (1), `--conjecture-gen-gt-enum=N` (50), `--conjecture-gen-max-depth=N` (3) — enumerates ground terms per eqc, builds a theorem index, and proposes universally quantified conjectures as lemmas. **Default off.** — [C]
- **`InstStrategyEnum` (enumerative instantiation)** — `inst_strategy_enumerative.cpp:67`, per-quantifier `process` `:159` — all quantified — **`--enum-inst` default `false`, `common`** (toml:602); alias `--full-saturate-quant` (default `false`, `common`, mapped at `set_defaults.cpp:1510-1513`) — enumerates tuples of ground terms in a staged lexicographic order and instantiates.
  - *Produces an instance when*: the first non-redundant term tuple passes `addInstantiationExpFail`.
  - *Gives up when*: the enumerator's stages are exhausted, or after `--enum-inst-limit=N` rounds (default `-1`, **expert**).
  - Two effort tiers: relevant-domain terms first (`--enum-inst-rd`, default `true`, **expert**), then arbitrary ground terms, and only at full effort.
  **Default off — and nothing in `setDefaultsQuantifiers` turns it on for any logic.** — [C] [P] (Reynolds et al., *Revisiting Enumerative Instantiation*)
- **Enumerative-inst interleaving** — `inst_strategy_enumerative.cpp:74-78` — `--enum-inst-interleave` default **`false`**, `regular` — runs enum-inst at QEFFORT_STANDARD *only when another module already queued a lemma*, instead of at last call. — [C]
- **Enumerative-inst stratification** — `inst_strategy_enumerative.cpp:129-147` — `--enum-inst-stratify` default `false`, **expert** — stops after any lemma at effort level r instead of proceeding to arbitrary ground terms. — [C]
- **`TermTupleEnumerator`** — `term_tuple_enumerator.cpp:80, :213, :249` — on by default whenever enum-inst or pool-inst runs — treats a tuple as a mixed-radix number and enumerates stage by stage, where a stage fixes either the **max** digit or (with `--enum-inst-sum`, default `false`, `regular`) the **sum** of digits. Duplicates modulo equality are skipped; failure masks are recorded into `IndexTrie`. — [C]
- **`RelevantDomain`** — `relevant_domain.cpp:131, :225` — **constructed only when `--enum-inst` or `--enum-inst-interleave` is set** (`quantifiers_modules.cpp:106-110`) — computes per-argument relevant term sets by union-find over equated argument domains. — [C] [P] (Ge & de Moura, CAV 2009)
- **`InstStrategyPool` (user pool instantiation)** — `inst_strategy_pool.cpp:149`, `process` `:195` — inputs with `INST_POOL` annotations (a cvc5 extension) — `--pool-inst` default **`true`**, **expert**; `--user-pool` default `trust`, **expert** — instantiates over the Cartesian product (product semantics) or a tuple set (tuple semantics) of user-declared pools.
  - *Produces an instance for*: every tuple drawn from the pool enumerator.
  - *Gives up when*: the pool product is exhausted or a conflict occurs.
  In `trust` mode it **takes ownership (priority 1)** of any quantifier carrying a pool, excluding E-matching. Runs at **all** efforts. A no-op unless the input has pool annotations (`:150-153`). — [C]
- **`TermPools`** — `term_pools.cpp:39, :53, :81` — tracks the current value of each declared pool, including pools defined by `add-to-pool` side effects of instantiation. — [C]
- **`SygusInst` (syntax-guided instantiation)** — `sygus_inst.cpp:262`, CE lemma `:589`, registration `:358, :470` — quantified logics with usable grammars — `--sygus-inst` default **`false`**, `regular` — for each variable builds a sygus datatype grammar from ground terms and asserts `ce_lit ⇒ ¬P[eval(dt_x)]`; **the DT solver's model value for `dt_x` becomes the instantiation term**.
  - *Produces an instance when*: the datatypes solver assigns a sygus value to every `dt_x` of an active quantifier.
  - *Gives up when*: the CE literal is assigned false and is not a decision (the quantifier is deactivated, `:225-241`).
  Knobs `--sygus-inst-scope` (`in`), `--sygus-inst-term-sel` (`min`), `--sygus-inst-mode` (`priority-inst`), all **expert**. Disabled when `--mbqi` is set (`set_defaults.cpp:1546`); incompatible with proof logging (`:529-534`); fatal if combined with SyGuS input (`:414-420`). **But note: `set_defaults.cpp:413-429` auto-enables `--sygus-inst` for quantified pure FP and quantified nonlinear integer arithmetic.** — [C] [P] (Reynolds et al., CAV 2019b)
- **`InstStrategyMbqi` (subsolver model-based quantifier instantiation)** — `inst_strategy_mbqi.cpp:116`, `process` `:155`, query build `:427` — quantified UF plus arith/BV/DT/FP — `--mbqi` default **`false`**, `regular` (toml:206) — skolemises `q`, converts the current model of uninterpreted sorts into a concrete query, and asks a **subsolver** whether `¬body` is satisfiable.
  - *Produces an instance when*: the subsolver returns SAT — its model values for the skolems become the instantiation.
  - *Gives up / declares `q` satisfied when*: the subsolver returns UNSAT (`d_quantChecked.insert(q)`, `:306-311`); abandons `q` entirely if the query could not be constructed (unconvertible terms).
  Timeout `--mbqi-check-timeout=N` default **500 ms**, `regular`; nested-quantifier guard `--mbqi-nested-check` default `true`, **expert**. **Enabling it turns off cegqi and sygus-inst** (`set_defaults.cpp:1541-1547`). **Default off.** — [C] [P] (Ge & de Moura, CAV 2009)
- **`MbqiEnum` (sygus-enumeration repair of MBQI instances)** — `mbqi_enum.cpp:92`, used at `inst_strategy_mbqi.cpp:335` — `--mbqi-enum` default **`false`**, `regular`; **setting it force-enables `--mbqi`** (`set_defaults.cpp:1537-1540`) — when the raw model value is not a usable term, enumerates candidates from a per-variable sygus grammar until one yields a successful instantiation. Grammar content: `--mbqi-enum-ext-vars-grammar` (`true`), `--mbqi-enum-free-syms-grammar` (`true`), `--mbqi-enum-global-syms-grammar` (`true`), `--mbqi-enum-choice-grammar` (`false`), `--mbqi-enum-choice-grammar-all` (`false`) — all **expert**. — [C]
- **`QuantDSplit` (dynamic datatype splitting)** — `quant_split.cpp:230`, `split` `:268`, ownership `:128` — quantified datatypes — `--quant-dsplit` default `default`, `regular` — splits one datatype-typed bound variable per round into a disjunction over constructors. `default` = split finite datatypes only when FMF is on; `agg` = split aggressively; **forced to `none` when the logic has no datatypes** (`set_defaults.cpp:1723-1730`), and set to `default` under `--finite-model-find` (`:1592-1598`). Runs at QEFFORT_CONFLICT because it is a reduction; proof-producing via `QuantDSplitProofGenerator` (`:40-110`). — [C]
- **`OracleEngine` (SMT modulo oracles)** — `oracle_engine.cpp:120` — inputs with oracle-interface quantifiers — `--oracles` default **`false`**, **expert** — invokes external oracle binaries on model values of oracle-function applications and adds `QUANTIFIERS_ORACLE_INTERFACE` lemmas until every application is consistent with the model.
  - *Produces a lemma when*: an application's oracle output disagrees with the model.
  - *Declares completeness when*: every oracle function application is consistent. **Default off.** — [C] [P] (Polgreen et al., VMCAI 2022)
- **`OracleChecker`** — `oracle_checker.cpp:25, :30, :42` — caches oracle invocations and checks `f(t)^M == oracle(t^M)`. — [C]
- **`FirstOrderModel`** — `first_order_model.cpp:44, :108, :274, :297` — maintains the ordered list of asserted quantifiers; **QCF calls `markRelevant` so conflict-prone quantifiers are checked first next round** (`quant_conflict_find.cpp:2850, :2866`). — [C]
- **`QuantifiersBoundInference`** — `quant_bound_inference.cpp:24, :32` — `--fmf-type-completion-thresh=N` default **1000**, `regular` — decides whether a sort's domain is small enough to enumerate completely, and classifies each variable's bound as `BOUND_INT_RANGE` / `BOUND_SET_MEMBER` / `BOUND_FIXED_SET` / `BOUND_NONE` (`quant_bound_inference.h:32-47`). — [C]
- **`QRepBoundExt`** — `quant_rep_bound_ext.cpp:25, :34, :54` — supplies the `RepSetIterator` with per-variable finite bounds from `BoundedIntegers` and the model's rep set. — [C]
- **`QuantRelevance` (SInE-style symbol relevance)** — `quant_relevance.cpp:23, :25` — large UF axiom sets — `--relevant-triggers` default **`false`**, `regular` — ranks symbols by how many quantifiers contain them and prefers triggers over rarer symbols (`inst_strategy_e_matching.cpp:278, :673`). **The whole utility is not even allocated when off** (`instantiation_engine.cpp:44-47`). — [C] [P] (Hoder et al., CADE 2011)
- **`QuantAttributes`** — `quantifiers_attributes.cpp`, doc `quantifiers_attributes.h:23-90` — classifies quantifiers as standard / quant-elim / sygus / oracle-interface / bounded / internal, which gates every module's `shouldProcess`. — [C]
- **`FunDefEvaluator`** — `fun_def_evaluator.cpp:26, :28` — evaluates ground applications of recursively defined functions by unfolding. — [C]
- **`MasterNotifyClass`** — `master_eq_notify.cpp:21, :25, :29` — forwards master-EE new-class/merge notifications for term-DB maintenance. — [C]
- **Global negation** — `src/smt/process_assertions.cpp:166`, gating `set_defaults.cpp:1107, :1200, :1336, :1375, :1441` — `--global-negate` default **`false`**, **expert** — negates the whole input and flips sat/unsat, turning a `forall` problem into an `exists` one. — [C]

### 10.2 `ematching/` — every file

- **`InstantiationEngine` (E-matching round driver)** — `ematching/instantiation_engine.cpp:147`, `doInstantiationRound` `:78` — `--e-matching` default **`true`**, `regular` (toml:288); **auto-disabled under `--finite-model-find`** (`set_defaults.cpp:1600-1603`) — runs an internal effort ladder `e = 0..2` (0..10 at LAST_CALL), calling each `InstStrategy::process(q, effort, e)` per active quantifier, and **stops escalating as soon as any lemma was queued at the current level** (`:122-126`). — [C]
- **`InstStrategyUserPatterns`** — `ematching/inst_strategy_e_matching_user.cpp:59` — inputs with `:pattern` — `--user-pat` default `trust`, `regular` (toml:470) — instantiates using user-supplied `INST_PATTERN`s.
  - *Produces an instance when*: a user trigger E-matches.
  - *Gives up / hands over when*: mode is `resort` (runs only at internal effort 2, `:67`) or `interleave`.
  In `strict` mode `InstantiationEngine::checkOwnership` **takes ownership (priority 1)** of any patterned quantifier (`instantiation_engine.cpp:184-193`); in `ignore` mode the strategy is not even constructed (`:51-57`). — [C]
- **`InstStrategyAutoGenTriggers`** — `ematching/inst_strategy_e_matching.cpp:122` — on by default with `--e-matching` — generates triggers, then processes single triggers (r=0) before multi-triggers (r=1).
  - *Produces an instance when*: any enabled trigger's match generator yields a non-redundant match.
  - *Gives up when*: it declines to auto-generate at all if the quantifier has user patterns and the mode is `trust`/`strict` (`:126-132`); it defers to internal effort `peffort` (2 with user patterns, else 1, `:133-140`); it prints `(no-trigger q)` if no trigger could be built (`:164-171`).
  Trigger regeneration is periodic (`d_regenerate_frequency`, `:143-158`), controlled by `--increment-triggers` (default `true`, **expert**). — [C]
- **Trigger selection strategy** — `ematching/pattern_term_selector.cpp:263` — `--trigger-sel` default **`min`**, `regular` (toml:428) — MIN keeps minimal-size single triggers (discarding a parent subsumed by a child with the same free-variable set), MAX keeps maximal ones; MIN_SINGLE_MAX / MIN_SINGLE_ALL differ only in which partial terms are eligible for multi-triggers (the long comment at toml:392-426). Ties break on `TriggerTermInfo::d_weight`. — [C]
- **Usable-trigger predicate** — `pattern_term_selector.cpp:174, :60, :249` — a term is a usable trigger iff every path from it to a bound variable goes only through atomic-trigger kinds; polarity is folded into an equality (`¬P(x)` → `P(x) = false`). — [C]
- **Relational trigger recognition** — `pattern_term_selector.cpp:101, :128` — quantified arithmetic — `--relational-triggers` default **`false`**, **expert** — without it only `f(x) ~ c` forms are accepted; with it, `x = c`, `x = y`, `f(x) ~ y` become triggers too. — [C]
- **`RelationalMatchGenerator`** — `ematching/relational_match_generator.cpp:25, :64`, doc `.h:17-36` — quantified LIA/LRA — reachable via `--relational-triggers` **and** via `getInstMatchGenerator` (`inst_match_generator.cpp:744-750`) — for `x ~ t` with `t` ground, tries only the canonical witnesses from `{t, t+1, t-1}`. **Produces at most 1 instance** with a required polarity, **at most 2** otherwise, then gives up immediately. — [C]
- **Trigger purification / term inversion** — `pattern_term_selector.cpp:642, :688`; generator `ematching/var_match_generator.cpp:24, :43` — `--purify-triggers` default **`false`**, **expert**; auto-enabled by `--int-wf-ind` — turns an invertible term like `x+1` into a trigger by matching the whole term and solving back for `x` (`VarMatchGeneratorTermSubs`). — [C]
- **Partial triggers** — `inst_strategy_e_matching.cpp:444, :571` — `--partial-triggers` default **`false`**, **expert** — allows triggers that do not cover all bound variables (uncovered ones later get model values). — [C]
- **Trigger active selection** — `inst_strategy_e_matching.cpp:173-205` — `--trigger-active-sel` default `all`, **expert** — instead of running every generated trigger, enables only the one with min/max "active score" (`trigger.cpp:191`). — [C]
- **Multi-trigger construction** — `inst_strategy_e_matching.cpp:298-343` — `--multi-trigger-when-single` default **`false`**, `regular` — **by default multi-triggers are built only when no single trigger exists**; with the flag they are always additionally built. **Exactly one multi-trigger is added per call** (`:340-342`), reshuffled randomly on regeneration. — [C]
- **Multi-trigger priority** — `inst_strategy_e_matching.cpp:239-243` — `--multi-trigger-priority` default **`false`**, `regular` — when set, if single triggers produced any instance, multi-triggers are skipped this round. — [C]
- **`InstMatchGeneratorMultiLinear` (the default multi-trigger)** — `ematching/inst_match_generator_multi_linear.cpp:25, :113, :125`, built at `inst_match_generator.cpp:639` — `--multi-trigger-linear` default **`true`**, `regular` — chains the multi-trigger terms into a linked list and forbids reusing the same ground term against the same trigger position twice, keeping the instance count **linear** in ground terms. *Gives up when* the head generator's candidate stream for the first term is exhausted. — [C]
- **`InstMatchGeneratorMulti` (cached product multi-trigger)** — `ematching/inst_match_generator_multi.cpp:26, :132` — `--multi-trigger-cache` default **`false`**, `regular` — the older implementation taking the **product** of per-term match sets via inst-match tries; **no polynomial guarantee** (`inst_match_generator_multi.h:21-27`). **Dead in default configurations.** — [C]
- **`InstMatchGenerator` (non-simple single trigger)** — `ematching/inst_match_generator.cpp:40`, init `:100-290`, `getMatch` `:288` — on by default — builds a linked list of sub-generators for nested applications; the `d_active_add` flag enforces **at most one instantiation per (pattern, ground-term) pair per round** (`inst_match_generator.h:45-78`). *Gives up when* the candidate generator's stream for the head operator is exhausted. — [C] [P] (Reynolds, Vampire 2016)
- **`InstMatchGeneratorSimple`** — `ematching/inst_match_generator_simple.cpp:29, :72` — selected at `trigger.cpp:96` when `TriggerTermInfo::isSimpleTrigger` (`trigger_term_info.cpp:110`) — walks the operator's `TNodeTrie` in the term DB directly instead of running the generic matcher; **the header notes 70-90% of triggers have this shape.** — [C]
- **`HigherOrderTrigger`** — `ematching/ho_trigger.cpp:34`, `sendInstantiation` `:206, :381`, `sendInstantiationArg` `:413` — HO logics — `--ho-matching` default `true`, **expert** — post-processes a first-order match containing function-typed variables into all lambda abstractions consistent with it (a variant of Huet's algorithm, `ho_trigger.h:24-78`). *Produces an instance when* the first enumerated abstraction is accepted; *gives up when* all abstractions of the matched applications are exhausted. — [C] [P] (Dowek, Handbook of Automated Reasoning ch. 16)
- **HO type-match predicate lemmas** — `ho_trigger.cpp:467` — forces `APPLY_UF` to expand into curried `HO_APPLY` when there are no matchable ground applications. — [C]
- **`TriggerDatabase::mkTrigger`** — `ematching/trigger_database.cpp:34`, HO detection `:74-83` — normalises trigger term lists, consults the trie (`TR_MAKE_NEW` / `TR_GET_OLD` / `TR_RETURN_NULL`), and instantiates `HigherOrderTrigger` when the trigger contains applications of function-typed variables. — [C]
- **`TriggerTrie`** — `ematching/trigger_trie.cpp:20, :30` — caches and owns all `Trigger` objects keyed by the sorted node list, so identical triggers are shared. — [C]
- **`Trigger` (E-matching facade)** — `ematching/trigger.cpp:43`, generator choice `:94-129`, `addInstantiations` `:152` — chooses simple / non-simple / multi-linear / multi-cache and drives `resetInstantiationRound` → `reset(eqc)` → `addInstantiations`. — [C]
- **Ground-subterm purification in triggers** — `trigger.cpp:154-172, :193` — emits `k = t` purification lemmas (`QUANTIFIERS_GT_PURIFY`) for ground subterms of a trigger absent from the equality engine. — [C]
- **`TriggerTermInfo`** — `ematching/trigger_term_info.cpp:24, :42, :60, :70, :110, :139` — free vars, required polarity / equivalence class, and a syntactic weight used by trigger selection; also decides atomic / relational / simple triggerhood. — [C]
- **`IMGenerator` base + `sendInstantiation`** — `ematching/im_generator.cpp:24, :32`. — [C]
- **`InstStrategy` base** — `ematching/inst_strategy.cpp:22`, `InstStrategyStatus` at `.h:30` — `STATUS_UNFINISHED` (ask for a higher internal effort) vs `STATUS_UNKNOWN` (done for now). — [C]
- **`CandidateGeneratorQE`** — `ematching/candidate_generator.cpp:48, :63, :115, :120` — streams ground terms with a given operator, optionally restricted to one eqc, or an eqc-scan mode; supports `excludeEqc` for disequality triggers. — [C]
- **`CandidateGeneratorQELitDeq`** — `candidate_generator.cpp:187, :197, :204` — for a negated-equality trigger, streams the equalities in the equivalence class of `false`. — [C]
- **`CandidateGeneratorQEAll`** — `candidate_generator.cpp:226, :239, :245` — for a bare-variable trigger, streams every ground term of the required sort. — [C]
- **`CandidateGeneratorConsExpand`** — `candidate_generator.cpp:284, :294, :319` — quantified datatypes — `--cons-exp-triggers` default **`false`**, **expert**, gates the extra expansion at `:301`; also used automatically for 1-constructor types (`inst_match_generator.cpp:224-235`) — turns an eqc representative `t` into `C(sel₁(t), …)` so constructor triggers can match. — [C]
- **`CandidateGeneratorSelector`** — `candidate_generator.cpp:340, :357, :364`, chosen at `inst_match_generator.cpp:216-221` — for `APPLY_SELECTOR` triggers, unions correctly- and incorrectly-applied selector terms. — [C]
- **Literal matching mode** — `inst_strategy_e_matching.cpp:498-527` — `--literal-matching` default `use`, **expert** (`none` / `use` / `agg-predicate` / `agg`) — whether and how equality and predicate literals become polarity-carrying triggers. — [C]
- **Function-well-defined trigger heuristic** — `inst_strategy_e_matching.cpp:355` — `--quant-fun-wd` default **`false`**, **expert** — assumes function-definition quantifiers are well-defined and selects the defining application as the trigger. — [C]

### 10.3 `fmf/` — finite model finding

- **`ModelEngine`** — `fmf/model_engine.cpp:70`, `checkModel` `:170`, `exhaustiveInstantiate` `:297` — quantified with finite/bounded sorts; forced by cardinality constraints — constructed when `--finite-model-find` (default **`false`**, `regular`, toml:707) **or** `--fmf-bound` **or** `--strings-exp` (`quantifiers_modules.cpp:90-95`); forced on by `hasCardinalityConstraints()` and by `--fmf-fun` (`set_defaults.cpp:1517-1522, 1584-1590`) — builds a candidate finite model then exhaustively instantiates every active quantifier over the bounded domain.
  - *Produces instances when*: the rep-set iterator finds points where the body is false in the model.
  - *Gives up when*: the iterator is incomplete (marks `d_incompleteQuants`, so the answer becomes unknown), or when `--fmf-mbqi=trust` deliberately skips exhaustive instantiation (`:259-266`).
  Two sub-efforts under FMC mode (`e_max = 2`, `:238-240`). — [C] [P]
- **FMF instantiation throttling** — `fmf/model_engine.cpp:349` — `--mbqi-one-inst-per-round` default **`false`**, `regular` — stops rep-set iteration after the first successful instance per quantifier per round. — [C]
- **FMF / E-matching interleaving** — `fmf/model_engine.cpp:58, :75-82` — `--mbqi-interleave` default **`false`**, **expert** — moves `ModelEngine`'s check from QEFFORT_MODEL to QEFFORT_STANDARD when another module already has a pending lemma. — [C]
- **`QModelBuilder`** — `fmf/model_builder.cpp:30, :46, :53` — base model builder; `optUseModel` decides whether the quantifier-aware construction is used at all. — [C]
- **`FullModelChecker` (FMC)** — `fmf/full_model_check.cpp:777, :1013`, `Def`/`EntryTrie` at `:52, :112, :143` — FMF over UF — `--fmf-mbqi` default **`fmc`**, **expert** (toml:739) — represents each function's model as a decision tree of "star" (default) entries and evaluates the quantifier body symbolically, generating instantiations only for the *generalised* regions where the body is false. *Gives up when* the quantifier is in `d_unhandledQuant` (returns `<0`, marking incompleteness). **Forced to `none` for higher-order logic** (`set_defaults.cpp:1556-1560`) **and for `--fmf-bound`** (`:1554-1558`). — [C] [P]
- **FMC bound-blasting** — `fmf/full_model_check.cpp:1092` — `--fmf-bound-blast` default **`false`**, **expert** — forces full enumeration of a bounded region rather than stopping at the first counterexample point. — [C]
- **`FirstOrderModelFmc`** — `fmf/first_order_model_fmc.cpp:36, :52` — the model object holding star-based function definitions and per-type model-basis terms. — [C]
- **`BoundedIntegers`** — `fmf/bounded_integers.cpp:418`, `checkOwnership` `:449`, `process` `:213`, `setBoundedVar` `:440` — quantified LIA (`∀x. 0≤x<n ⇒ P(x)`), sets, and strings-exp internal quantifiers — `--fmf-bound` default **`false`**, `regular`; the module is also constructed whenever `--strings-exp` is on (`quantifiers_modules.cpp:84-88`); **auto-enabled by `--arrays-exp`** (`set_defaults.cpp:1514-1518`) and by `--fmf-bound-lazy` (`:1548-1552`) — infers finite ranges for bound variables (int range / set membership / fixed finite set) and takes ownership so those quantifiers are handled by exhaustive enumeration. **Note the asymmetry at `:455-464`:** when `--fmf-bound` is off it still processes *internal* quantifiers marked `isQuantBounded`, which is how strings and sequences reductions work by default. — [C]
- **`IntRangeDecisionHeuristic`** — `fmf/bounded_integers.cpp:41, :63, :70` — a decision strategy splitting on `t ≤ 0, t ≤ 1, …` to minimise an integer range term, making the domain finite lazily. `--fmf-bound-lazy` default `false`, **expert**. — [C]
- **Set-membership element choice functions** — `fmf/bounded_integers.h:71-79` — witness terms for the n-th distinct member of a set, to enumerate `∀x ∈ S`. — [C]
- **`--fmf-fun` (well-defined recursive definitions)** — `src/smt/process_assertions.cpp:254`, `fmf/model_builder.cpp:68`, `src/smt/check_models.cpp:83` — `--fmf-fun` default **`false`**, **expert**; **force-enables `--finite-model-find`** (`set_defaults.cpp:1584-1590`); relevance variant `--fmf-fun-rlv` (default `false`, **expert**) force-enables `--fmf-fun` — treats `define-fun-rec` axioms as well-defined so FMF can build a model for them. — [C]

### 10.4 `ieval/` — instantiation evaluation

This is the newer pruning layer. As a matching algorithm binds variables one at
a time, `InstEvaluator` incrementally evaluates the quantifier body under the
partial substitution and reports **infeasible** as soon as the partial
assignment can no longer produce an instance meeting the current criterion. That
prunes the match search *before* a full tuple is built, instead of rejecting
completed instances in `Instantiate::addInstantiation`. `[C]`

- **`InstEvaluatorManager`** — `ieval/inst_evaluator_manager.cpp:22`, `getEvaluator` `:45`, `reset` `:29` — all quantified — `--ieval` default **`use`**, `regular` (toml:870) — allocates and hard-resets one `InstEvaluator` per (quantifier, evaluator-mode) pair each round; **returns `nullptr` when the mode is `off`, silently disabling all pruning** (`:52-57`). — [C]
- **`InstEvaluator`** — `ieval/inst_evaluator.cpp:22`, `watch` `:42, :48` — maintains the evaluated form of the watched body under a growing substitution: push a binding, ask "is this still feasible?", pop on backtrack. — [C]
- **Generalised learning mode** — `ieval/inst_evaluator_manager.cpp:66-70` — `--ieval=use-learn` (a non-default value, toml:884) — additionally records *why* a partial assignment failed so the failure generalises to other tuples. **Not the default.** — [C]
- **`TermEvaluatorMode` (the pruning criterion)** — `ieval/term_evaluator.h:33-37` — five criteria: `NONE`, `CONFLICT` (body must become false), `PROP` (propagating), `NO_ENTAIL` (instance must not already be entailed), `MODEL`. — [C]
- **`TermEvaluatorEntailed`** — `ieval/term_evaluator.cpp:32, :43` — evaluates a pattern term to a ground eqc when current equalities entail it. — [C]
- **`ieval::State`** — `ieval/state.cpp:27, :47`, doc `state.h:59-130` — propagates values bottom-up over pattern terms; a pattern mapped to **none** will *never* evaluate to a ground class in this context, which deactivates the watched quantifier; `getFailureExp` returns the responsible terms. — [C]
- **`ieval::QuantInfo` / `PatTermInfo` / `FreeVarInfo`** — `ieval/quant_info.cpp:24, :32`, `pattern_term_info.cpp:26, :31, :37`, `free_var_info.cpp:20` — context-dependent per-quantifier activity, per-pattern "what am I currently equal to and which child explains it", per-variable notify lists. — [C]
- **ieval hook in E-matching** — `ematching/trigger.cpp:60` (`setEvaluatorMode(NO_ENTAIL)`) — on by default — every trigger's `InstMatch` prunes partial matches whose completion would be an already-entailed instance. — [C]
- **ieval hook in QCF** — `quant_conflict_find.cpp:332-334, :779` — on by default — QCF requests `CONFLICT` mode at conflict effort and `PROP` at prop-eq effort, so partial matches that cannot falsify the body are cut immediately. — [C]

### 10.5 `cegqi/` — counterexample-guided quantifier instantiation

- **`InstStrategyCegqi`** — `cegqi/inst_strategy_cegqi.cpp:293`, `registerCbqiLemma` `:98`, `doCbqi` `:452`, `checkOwnership` `:363` — quantified ARITH / BV / DT / FP — **`--cegqi` toml default is `false` (toml:1611) but `set_defaults.cpp:1630-1642` switches it ON for any quantified logic containing ARITH, DT, BV, or FP** — adds the counterexample lemma `¬ceLit ∨ ¬body[k/x]`, then constructs instantiations from the ground model and assertions.
  - *Produces an instance when*: `CegInstantiator::check()` succeeds for a variable ordering.
  - *Gives up when*: `doCbqi(q)` returns `CEG_UNHANDLED`, or after two internal efforts `ee ∈ {0,1}` produce no lemma (`:305-333`).
  If `doCbqi(q) == CEG_HANDLED` it **takes full ownership**, excluding E-matching. — [C] [P] (Reynolds/King/Kuncak, FMSD 2017)
- **CEGQI applicability test** — `cegqi/ceg_instantiator.cpp:282` (`isCbqiQuant`), `:263`, `:200`, `:156`, `:133` — handled sorts: real, int, bool, BV, FP, and datatypes thereof; handled kinds: Boolean connectives, `ADD`/`GEQ`/`EQUAL`/`MULT`/div/mod/to_int/abs, plus anything in THEORY_BV / FP / DATATYPES / BOOL. **Explicitly returns `CEG_UNHANDLED` for any quantifier carrying an `INST_PATTERN`** (`:296-306`) and for sygus conjectures. **Arrays, sets, and functions are unhandled.** `--cegqi-all` (default `false`, **expert**) downgrades unhandled to `CEG_PARTIALLY_HANDLED` so it is tried non-exclusively. — [C]
- **`CegInstantiator::check`** — `ceg_instantiator.cpp:1425-1444` — runs `CEG_INST_EFFORT_STANDARD` then `CEG_INST_EFFORT_FULL`; at FULL it may fall back to model values. — [C]
- **The four instantiation phases, in order** — `ceg_instantiator.cpp:583` — for each variable, strictly: **[1] EQC** (a term equal to `pv` in its class, `:602`), **[2] EQUAL** (solve an equality for `pv`, `:683`), **[3] ASSERTION** (solve a theory literal, `:770`), then **[4] MVALUE** (model value, `:546-566`). *Gives up on a variable when* all four fail. `--cegqi-multi-inst` (default `false`, **expert**) allows continuing past the first successful substitution per variable rather than committing. — [C]
- **CEGQI innermost restriction** — `inst_strategy_cegqi.cpp:251-289` — `--cegqi-innermost` default **`true`**, `regular` — only the innermost quantifiers of a nested block are processed. — [C]
- **CEGQI full effort (model-value fallback)** — `ceg_instantiator.cpp:525-566` — `--cegqi-full` default **`false`**, **expert**; **auto-enabled for pure BV logics** (`set_defaults.cpp:1643-1648`). — [C]
- **`ArithInstantiator`** — `cegqi/ceg_arith_instantiator.cpp:34`, `processAssertions` `:298`, bound solving `:163-297` — quantified LIA/LRA/NIA — implements **Loos–Weispfenning virtual term substitution, Ferrante–Rackoff interior points, and Cooper's method**. *Produces an instance from* the best lower/upper bound literal for the variable; *gives up when* the literal is non-linear in `pv` (`CEG_TT_INVALID`, `:765, :824, :840, :931`). Knobs `--cegqi-min-bounds` (false), `--cegqi-round-up-lia` (false), `--cegqi-midpoint` (**true**, `:483, :543, :630`), `--cegqi-nopt` (**true**, `:617`), `--cegqi-inf-int` / `--cegqi-inf-real` (both false) — all **expert**. — [C] [P]
- **`VtsTermCache` (virtual terms: infinity and delta)** — `cegqi/vts_term_cache.cpp:29, :33`, `rewriteVtsSymbols` used at `inst_strategy_cegqi.cpp:405` — quantified arithmetic — the "free" variants gated by `--cegqi-inf-int` / `--cegqi-inf-real` (both default `false`, **expert**) — provides `delta` (infinitesimal), real `inf`, int `inf`, and the VTS rewrite rules (`t < s + delta → t ≤ s`, `t ≤ s + inf → true`, …). Two variants: pure virtual terms (never appearing in assertions) and "free" virtual terms constrained by axioms (`vts_term_cache.h:34-60`). — [C] [P]
- **`BvInstantiator` (invertibility conditions)** — `cegqi/ceg_bv_instantiator.cpp:54, :246, :274, :292, :355, :539, :573, :593` — quantified BV — `--cegqi-bv` default **`true`**, `regular`, `no_support = ["proofs"]` — solves BV literals for the variable using word-level invertibility conditions. *Produces an instance from* the inverted literal; *gives up when* the path to `pv` is non-linear and `--cegqi-bv-solve-nl` (default `false`) is off, or when the literal has no invertibility condition. Inequality handling `--cegqi-bv-ineq` default `eq-boundary`, **expert**; also `--cegqi-bv-interleave-value` (false), `--cegqi-bv-rm-extract` (**true**), `--cegqi-bv-linear` (**true**). **Enabling it forces `--bool-to-bv=off` for quantified logics** (`set_defaults.cpp:682-696`). — [C] [P] (Niemetz et al., CAV 2018)
- **`BvInverter`** — `bv_inverter.cpp:31, :35, :49`, rules in `bv_inverter_utils.cpp` — computes the path to `pv` inside a literal and the per-operator inverse and side condition, returning a witness term. — [C] [P]
- **`BvInstantiatorPreprocess` (extract purification)** — `ceg_bv_instantiator.cpp:658`, doc `.h:161-166` — `--cegqi-bv-rm-extract` default **`true`**, **expert** — introduces fresh variables for disjoint bit-vector extracts so each can be solved independently. — [C]
- **`BvInstantiatorUtil`** — `cegqi/ceg_bv_instantiator_utils.cpp:24, :26, :62` — `--cegqi-bv-linear` default `true`, **expert** — normalises `pv`-multiplications and linearises adder chains before inversion. — [C]
- **`DtInstantiator`** — `cegqi/ceg_dt_instantiator.cpp:28, :43, :94, :114` — quantified datatypes — solves for `pv` occurring in a datatype subfield by descending through constructors and selectors (`solve_dt`). *Gives up when* the two sides have distinct constructors or `pv` is under no invertible selector path. — [C]
- **`NestedQe`** — `cegqi/nested_qe.cpp:27, :29`, invoked from `inst_strategy_cegqi.cpp:379-386, :572` — **pure** quantified arithmetic or pure BV only — `--cegqi-nested-qe` default **`false`**, `regular`, `no_support = ["proofs"]`; **hard-disabled by `set_defaults` for any non-pure logic** (`:1656-1661`) — eliminates nested quantifiers by calling a subsolver's QE and asserting `q = qqe`, so CEGQI sees a quantifier-free body. Enabling it forces `--prenex-quant-user` and `--pre-skolem-quant=on`. — [C]
- **`InstRewriterCegqi`** — `inst_strategy_cegqi.cpp:35, :40`, `rewriteInstantiation` `:400`, registered at `quantifiers_modules.cpp:75` — rewrites away `delta` / `inf` symbols in an instantiation body before it becomes a lemma. — [C]
- **`processAssertions` (theory-literal collection)** — `ceg_instantiator.cpp:1447` — gathers per-theory asserted literals and eqc structure that phases [2] and [3] search over. — [C]
- **`SolvedForm` / `TermProperties`** — `cegqi/ceg_utils.cpp:110, :127, :151`, enums `ceg_utils.h:23-47, 147-183` — the accumulating substitution with per-variable coefficients and `CEG_TT_{EQUAL,UPPER,LOWER,*_STRICT}` bound tags; the `theta` stack supports Cooper-style integer reasoning. — [C]
- **`Instantiator` base protocol** — `cegqi/instantiator.cpp:23, :28` — the per-theory hooks the phase machine calls: `hasProcessEqualTerm` / `processEqualTerm(s)` / `hasProcessEquality` / `processEquality` / `hasProcessAssertion` / `processAssertion(s)`. — [C]

### 10.6 Quantifier defaults that are easy to misread

- **`--cegqi` reads `false` in the toml** (`quantifiers_options.toml:1611`) but is **effectively on** for essentially all quantified arithmetic / BV / DT / FP problems via `set_defaults.cpp:1630-1642`. Reading the toml alone is misleading here. `[C]`
- **`--e-matching` reads `true`** (toml:288) but is **turned off** whenever `--finite-model-find` is enabled and the user did not ask for it. The source comment is explicit: *"do not use E-matching by default. For E-matching + FMF, the user should specify `--finite-model-find --e-matching`"* (`set_defaults.cpp:1600-1603`). `[C]`
- **`--enum-inst` is default-off**, and `common` (toml:602) — **enumerative instantiation, the completeness-oriented strategy, does not run unless requested**, and nothing in `setDefaultsQuantifiers` enables it for any logic. `[C]`
- **`--mbqi` is default-off** (toml:206) and mutually exclusive with cegqi and sygus-inst by default (`set_defaults.cpp:1541-1547`). `[C]`
- **`--relevant-triggers` (SInE) is default-off** (toml:322) — the entire `QuantRelevance` utility is not allocated otherwise. `[C]`
- **`--relational-triggers`, `--purify-triggers`, `--partial-triggers`, `--cons-exp-triggers` are all default-off expert flags** (toml:330-358), so those paths are unreachable in a default run — *except* that `RelationalMatchGenerator` is still constructed from `TriggerTermInfo::isUsableRelationTrigger` at `inst_match_generator.cpp:744-750`. `[C]`
- **`--multi-trigger-cache` is default-off** (toml:378), so `InstMatchGeneratorMulti` (the exponential product implementation) is dead by default; `InstMatchGeneratorMultiLinear` is what runs. `[C]`
- **`--macros-quant` is default-off and unconditionally disabled for higher-order logic**; `QuantifiersMacros` is not even constructed otherwise. `[C]`
- **Default-off list**: `--conjecture-gen`, `--quant-ind`, `--dt-stc-ind`, `--int-wf-ind`, `--oracles`, `--sub-cbqi`, `--sygus-inst`, `--cegqi-nested-qe`, `--global-negate`, `--leibniz-elim`, `--inst-local`, `--fmf-fun`, `--fmf-bound-blast`, `--cbqi-tconstraint`, `--cbqi-vo-exp`, `--cbqi-skip-rd`, `--ext-rewrite-quant`, `--mbqi-enum`, `--enum-inst-interleave`, `--enum-inst-stratify`, `--fmf-bound-lazy`, `--ho-elim`. `[C]`
- **`--pool-inst` is default-TRUE but expert** (toml:671), and a no-op unless the input carries `INST_POOL` annotations. `[C]`
- **`AlphaEquivalence` is default-on but is not in the module vector** — reachable only through `QuantifiersEngine::reduceQuantifier` (`quantifiers_engine.cpp:637-656`), so it never participates in the effort ladder. `[C]`
- **`--sub-cbqi`, `--cegqi-nested-qe`, `--cegqi-bv`, `--macros-quant`, `--macros-quant-mode`, `--ext-rewrite-quant`, `--var-ent-eq-elim-quant` all carry `no_support = ["proofs"]`** and are stripped when proofs or unsat cores are on (`set_defaults.cpp:544-552`); `--sygus-inst` throws outright with `--proof-log` (`:529-534`). **So the proof-producing quantifier configuration is materially weaker than the default one.** `[C]`

## 11. Synthesis (SyGuS), abduction, interpolation, and rewrite-rule synthesis

Three things make this section worth reading even for a lane that will never
implement SyGuS. First, **abduction and interpolation are SyGuS problems in
cvc5**, not separate procedures. Second, **cvc5 uses SyGuS enumeration to
discover its own rewrite rules**, and ships the machinery for it. Third,
`--sygus-inst` (§10) makes the SyGuS enumerator an *instantiation strategy*, and
`set_defaults.cpp:413-429` turns that on by default for quantified pure FP and
quantified NIA.

### 11.1 The CEGIS spine

- **`SynthEngine`** — `quantifiers/sygus/synth_engine.cpp:64` (`check`), effort at `:60` — SyGuS inputs — `--sygus` default `false`, `regular`, but **set true by `setDefaultsSygus` for any `synth-fun` input** (`set_defaults.cpp:1736`) — runs at **QEFFORT_MODEL**; polls each `SynthConjecture`'s SAT value, keeps the active ones, and loops `checkConjecture` while spending `Resource::SygusCheckStep`. — [C] [P] (Reynolds et al., CAV 2015)
- **`SynthConjecture`** — `sygus/synth_conjecture.cpp:45` (ctor), `assign` `:116`, **`doCheck` `:332`**, `processCounterexample` `:690`, `excludeCurrentSolution` `:835`, `getSynthSolutions` `:972`, `getSynthSolutionsInternal` `:1032`, `getSymmetryBreakingPredicate` `:1140` — one object per synthesis conjecture — on by default for SyGuS — determines which approach applies to this conjecture and drives the counterexample loop. — [C]
- **`SynthConjecture::checkSideCondition`** — `synth_conjecture.cpp:666` — used by abduction, where a candidate must additionally be consistent with the axioms. — [C]
- **`SynthVerify`** — `sygus/synth_verify.cpp:64, :155` — verifies a candidate by a **subsolver** call on the negated specification; `--sygus-verify-timeout=N` default `0`, `regular`; `--sygus-verify-inst-max-rounds=N` default `10`, **expert**; `--full-sygus-verify` default **`false`**, **expert**, which sets `sygusVerifyInstMaxRounds = -1` and turns on `--full-saturate-quant` (`set_defaults.cpp:1738-1744`). — [C]
- **`Cegis` (the default SyGuS module)** — `sygus/cegis.cpp:46` (`initialize`), **`constructCandidates` `:304`** — on by default — initialises one sygus enumerator per candidate and returns the enumerators' model values as candidates. Implements `getRefinementEvalLemmas`, which evaluates all previous refinement lemmas on a term *before* returning it, so a candidate already refuted by a stored counterexample never reaches the verifier. — [C]
- **`EmbeddingConverter` (the deep embedding)** — `sygus/embedding_converter.cpp:94, :211` — on by default for SyGuS — applies the deep embedding of Reynolds et al. CAV 2015 §4, turning a synthesis conjecture into a first-order datatype problem. — [C] [P]
- **`TermDbSygus`** — `sygus/term_database_sygus.cpp:63, :65` — the sygus-specific term database: grammar type info, builtin↔sygus conversion, enumerator registration. — [C]
- **`SygusUtils` / `TypeInfo` / `TypeNodeIdTrie`** — `sygus/sygus_utils.cpp`, `type_info.cpp`, `type_node_id_trie.cpp` — attribute plumbing, per-grammar-type cached info, and a trie over type-node identifiers. — [C]

### 11.2 Grammars

- **`SygusGrammarCons`** — `sygus/sygus_grammar_cons.cpp:45` (`mkDefaultSygusType`), `:54` (`mkDefaultGrammar`) — on by default when the user supplies no grammar — `--sygus-grammar-cons` default `SIMPLE`, `regular`; `--sygus-add-const-grammar` default `true`, `regular`; `--sygus-grammar-use-disj` default `true`, **expert**; `--sygus-grammar-ho-partial` default `false`, **expert** — builds the inductive datatype encoding the syntactic restriction. — [C]
- **`SygusGrammarNorm`** — `sygus/sygus_grammar_norm.cpp:73, :78`, `OpPosTrie` doc in `.h` — `--sygus-grammar-norm` default **`false`**, **expert** — simplifies an already-encoded grammar; the `OpPosTrie` indexes a normalised type by the constructor positions used to build it, so equal normalisations are shared. **Default off.** — [C]
- **`SygusRedundantCons`** — `sygus/sygus_grammar_red.cpp:29` — `--sygus-min-grammar` default **`true`**, `regular` — computes the subset of a sygus type's constructors that are redundant, and removes them. — [C]
- **Datatype-level symmetry breaking** — see §9.10 (`datatypes/sygus_extension.cpp`, `sygus_simple_sym.cpp`) — this is where grammar redundancy is enforced *during* search rather than at construction. — [C]

### 11.3 Enumerators

- **`SygusEnumerator` (the fast enumerator)** — `sygus/sygus_enumerator.cpp:52` (`initialize`), `TermCache::initialize` `:187`, `TermCache::addTerm` `:334` — `--sygus-enum` default `AUTO`, `regular` — enumerates all terms of a sygus datatype type **in order of sygus term size**, filtering by redundancy: it will not generate two terms whose builtin analogues are provably equivalent by rewriting. Can also enumerate **"shapes"** — terms with free variables, each appearing in exactly one subterm — when `enumShapes` is set; for `S -> 0 | 1 | x | S+S` the stream is `z1, C_0, C_1, C_x, C_+(z1,z2), C_+(z1,C_1), C_+(C_1,C_1), …`. — [C]
- **`SygusEnumeratorCallback`** — `sygus/sygus_enumerator_callback.cpp` — the extension point deciding whether an enumerated term is kept (used by the rewrite-rule miner to record candidate rewrites instead of discarding duplicates). — [C]
- **`SygusRandomEnumerator`** — `sygus/sygus_random_enumerator.cpp:27` — `--sygus-enum=random`; `--sygus-enum-random-p=P` default `0.5`, **expert** — generates random terms whose sizes approximate a geometric distribution with expected size `1/p`. — [C]
- **`EnumStreamSubstitution` / `EnumStreamConcrete`** — `sygus/enum_stream_substitution.cpp:333, :613` — streams concrete values from an enumerated abstract one by permuting its variables, yielding a new value modulo rewriting per permutation. — [C]
- **`EnumValueManager`** — `sygus/enum_value_manager.cpp:51` (`getEnumeratedValue`), `:233` (`notifyCandidate`) — decides whether an enumerator's current value comes from the *datatypes solver's model* or from the fast enumerator, depending on whether the enumerator is "actively generated". — [C]
- **`--sygus-enum-fast-num-consts=N`** default `5`, **expert** — how many constants the fast enumerator considers per type. — [C]
- **`--sygus-stream`** default **`false`**, `regular` — stream all solutions rather than stopping at the first; forces "basic sygus" (see §11.7). — [C]

### 11.4 Specialised solvers (the "non-basic" algorithms)

`set_defaults.cpp:1777-1812` calls these **non-basic**: "specialized for returning
a single solution", and disables all four when abduction, `--sygus-stream`, or
incremental mode is in play.

- **`SygusPbe` (programming by examples)** — `sygus/sygus_pbe.cpp:44` (`initialize`), `:183` (`constructCandidates`) — inputs of the form `∃f. ∀x. f(0)=2 ∧ f(5)=7 ∧ …` — `--sygus-pbe` default **`true`**, `regular`; `--sygus-pbe-multi-fair` default `false`, **expert**; `--sygus-pbe-multi-fair-diff=N` default `0`, **expert** — infers that the conjecture is in PBE form via `ExampleInfer`, then devises an enumeration + construction strategy, including **decision trees when the grammar permits ITE** and **divide-and-conquer string synthesis when it permits concatenation**. — [C] [P] (Alur et al., *Scaling Enumerative Program Synthesis via Divide and Conquer*, TACAS 2017)
- **`SygusUnif` / `SygusUnifIo` / `SygusUnifRl` / `SygusUnifStrat`** — `sygus/sygus_unif.cpp`, `sygus_unif_io.cpp`, `sygus_unif_rl.cpp`, `sygus_unif_strat.cpp` — the unification-based construction underneath PBE: `SygusUnifIo` maintains the unification context during `constructSolution`; `SygusUnifRl` takes a *set of refinement lemmas* as the specification instead of I/O examples (its interface function is `addExample`); `SygusUnifStrat` holds the per-type strategy tree. — [C]
- **`CegisUnif` (unification + predicate inference)** — `sygus/cegis_unif.cpp:504` (`CegisUnifEnumDecisionStrategy::initialize`) — `--sygus-unif-pi` default **`NONE`**, `regular`; `--sygus-unif-shuffle-cond` default `false`, **expert**; `--sygus-unif-cond-independent-no-repeat-sol` default `true`, **expert** — enforces a decision strategy bounding the number of distinct values given to evaluation-point heads and condition enumerators: guards `G_uq_1 … G_uq_n` mean "for each type, the heads are interpreted in a set of cardinality at most i", with the number of condition enumerators pinned to `n−1`. **Default off.** — [C]
- **`CegisCoreConnective`** — `sygus/cegis_core_connective.cpp:359` — conjectures of the shape `∃P. ∀x. (A[x] ⇒ C(x)) ∧ (C(x) ⇒ B[x])`, optionally with a side condition — `--sygus-core-connective` default **`true`**, `regular` — **the algorithm behind abduction and interpolation.** It builds pools of literals `pool(A) = {c_i | c_i ⇒ B}` and `pool(B) = {d_j | A ⇒ d_j}` by enumerative SyGuS, collects points `pts(A)`, `pts(B)`, and **unsat cores** `cores(B) = {U ⊆ pool(B) | A ∧ U unsat}`, then assembles the solution from Boolean connectives over those cores. Two variants, one for interpolation and one for abduction. — [C] [P]
- **`CegSingleInv` (single-invocation synthesis)** — `sygus/ce_guided_single_inv.cpp:49` (`initialize`), `:196` (`solve`), `:316` (`getSolution`) — conjectures where the function to synthesise is applied to only one argument tuple — `--sygus-si` default **`NONE`** in the toml, **but `setDefaultsSygus` sets it to `USE`** (`set_defaults.cpp:1764-1767`) — solves by quantifier elimination on the single-invocation form, then reconstructs the answer into the user's grammar. `--sygus-si-rcons` default `ALL`, `regular`; `--sygus-si-rcons-limit=N` default `10000`, **expert**; `--sygus-si-rcons-p=P` default `0.5`, **expert**; `--sygus-si-abort` default `false`, `regular`. — [C] [P]
- **`SingleInvPartition`** — `quantifiers/single_inv_partition.cpp` — splits a conjecture into its single-invocation and non-single-invocation parts. — [C]
- **`SygusQePreproc`** — `sygus/sygus_qe_preproc.cpp:28` — non-ground single-invocation conjectures `∃f. ∀xy. P[f(x), x, y]` — `--sygus-qe-preproc` default **`false`**, **expert** — runs QE to turn `∃y. P[z,x,y]` into `Q[z,x]` and replaces the conjecture with `∃f. ∀x. Q[f(x), x]`. **Default off.** — [C] [P] (Reynolds et al., SYNT 2017, Example 6)
- **`TransitionInference`** — `sygus/transition_inference.cpp:189, :196` — invariant synthesis — determines whether a conjecture encodes a transition system, and stores a deterministic trace as a trie of variable-value vectors, so a system with a deterministic terminating trace gets a trivial invariant. — [C]
- **`SygusTemplateInfer`** — `sygus/template_infer.cpp:28` — `--sygus-inv-templ` default `POST`, `regular`; `--sygus-inv-templ-when-sg` default `false`, **expert** — uses the transition inference to pick an invariant template (pre- or post-condition strengthening). — [C]
- **`SynthConjectureProcess`** — `sygus/sygus_process_conj.cpp:582` (`initialize`) — `--sygus-arg-relevant` default **`false`**, **expert** — computes which arguments of the function to synthesise are *irrelevant*, by argument invariance and other static techniques, so the grammar can drop them. **Default off.** — [C]

### 11.5 Reconstruction, repair, and evaluation

- **`SygusReconstruct`** — `sygus/sygus_reconstruct.cpp:35` (`reconstructSolution`), `:92` (`main`), `:497` (`initialize`) — on by default when a solution must match a user grammar — finds a term `g` in sygus type `T0` equivalent to a builtin term `t0`, via a worklist of obligations `(skolem k of type T, set of builtin terms ts)`, a pool of enumerated *patterns* per sygus type, and matching of pattern builtin analogues against the terms to reconstruct. — [C] [P]
- **`RconsObligation` / `RconsTypeInfo`** — `sygus/rcons_obligation.cpp`, `rcons_type_info.cpp` — the obligation record and per-type pool/candidate bookkeeping. — [C]
- **`SygusRepairConst`** — `sygus/sygus_repair_const.cpp:40` (`initialize`), `:101`/`:108` (`repairSolution`) — `--sygus-repair-const` default **`true`**, `regular`; `--sygus-repair-const-timeout=N` default `0`, **expert**; `--sygus-crepair-abort` default `false`, **expert** — given a candidate `f = λx. t[x, r]` with *repairable* constant positions `r`, invokes a **separate `SolverEngine`** on `∀x. P(λx. t[x,c'], x)` to find replacement constants `c'`. After beta-reduction this is often a pure first-order query in a decidable theory. Enabling it force-enables `--cegqi` (`set_defaults.cpp:1749-1752`). — [C]
- **`SygusEvalUnfold`** — `sygus/sygus_eval_unfold.cpp:35` (`registerEvalTerm`), `:74` (`registerModelValue`) — `--sygus-eval-unfold` default `SINGLE_BOOL`, `regular`; `--sygus-auto-unfold` default `true`, **expert** — eagerly unfolds applications of the sygus evaluation function based on the model values of evaluation heads in refinement lemmas. — [C]
- **`SygusExplain` / `TermRecBuild`** — `sygus/sygus_explain.cpp:30` — generates variants of a term by replacing subterms at a maintained "active position", used to generalise why a candidate failed. — [C]
- **`SygusInvarianceTest` family** — `sygus/sygus_invariance.cpp:50` (`EvalSygusInvarianceTest::invariant`), `:88` (`EquivSygusInvarianceTest::init`) — tests whether the value of `eval(t, args)` is invariant under replacing a subterm of `t` by a hole. For `t = (mult x y)` with `eval(t,0,1) = 0`, the test is invariant on the second argument, since `eval((mult x _), 0, 1) = 0` too. **This is how a single failed candidate excludes a whole family.** — [C]
- **`ExampleInfer`** — `sygus/example_infer.cpp:28` — decides whether a formula "has examples" (functions applied to concrete arguments only) — the precondition for PBE and for **example-based symmetry breaking** (discarding a term equivalent to a previous one *up to the examples*). — [C]
- **`ExampleEvalCache`** — `sygus/example_eval_cache.cpp:31` (`addExample`), `:36` (`addSearchVal`) — caches evaluation of terms on a fixed example list. — [C]
- **`ExampleMinEval`** — `sygus/example_min_eval.cpp:48` (`evaluate`), `:76` (`EmeEvalTds::eval`) — minimises the number of evaluation calls over substitutions with a fixed domain. — [C]
- **`--sygus-rec-fun`** default `true`, **expert**; **`--sygus-rec-fun-eval-limit=N`** default `1000`, **expert**; **`--sygus-rec-fun-infer`** default `true`, **expert** — recursive-function support in grammars, with an evaluation step budget. — [C]
- **`--sygus-bool-ite-return-const`** default `true`, **expert**. — [C]

### 11.6 Rewrite-rule synthesis — cvc5 mining its own rewrites

This is a loop most solvers do not ship: **enumerate terms from a grammar, group
them by random-sample equivalence, check the surviving pairs with a subsolver,
filter the redundant ones, and print the result as a candidate rewrite rule.**
The rules in `src/theory/*/rewrites` (the 439 RARE rules of §2) are the output
format this loop feeds.

- **`ExprMiner` (base)** — `quantifiers/expr_miner.cpp:35` (`convertToSkolem`), `:52` (`initializeChecker`) — the virtual base for modules that "mine" information from enumerated expressions: candidate rewrite rules (`find-synth :rewrite`), *unsound* rewrite rules (`:rewrite_unsound`), and queries (`:query`). — [C]
- **`ExpressionMinerManager`** — `quantifiers/expr_miner_manager.cpp` — the dispatcher; the header notes it "should be renamed to solution filter". — [C]
- **`SygusSampler`** — `quantifiers/sygus_sampler.cpp:44` (`initialize`), `:93` (`initializeSygus`) — `--sygus-samples=N` default `1000`, **expert**; `--sygus-sample-grammar` default `true`, **expert**; `--sygus-sample-fp-uniform` default `false`, **expert** — tests equivalence of two expressions by **random sampling**: for terms `n₁…nₘ`, `registerTerm(nᵢ)` returns an earlier `nⱼ` when the two agree on every sample point. Two uses: *synthesise* candidate rewrites (terms that do **not** rewrite to the same thing but agree on all samples) and *detect unsound* rewrites (terms that **do** rewrite to the same thing but disagree on a sample). — [C]
- **`CandidateRewriteDatabase`** — `quantifiers/candidate_rewrite_database.cpp:50` (`initialize`), `:65` (`initializeSygus`) — performs the "equivalence checking" and "congruence and matching filtering" of the paper's Figure 1, combining its sampler with **subsolver `SolverEngine` calls** in `addTerm`. `--sygus-rr-synth-check` default `true`, **expert** (do the subsolver check at all); `--sygus-rr-synth-accel` default `false`, **expert**; `--sygus-rr-synth-rec` default `false`, **expert**; `--sygus-expr-miner-check-timeout=N` default `0`, **expert**. — [C] [P] (Noetzli et al., *Syntax-Guided Rewrite Rule Enumeration for SMT Solvers*, SAT 2019)
- **`CandidateRewriteFilter`** — `quantifiers/candidate_rewrite_filter.cpp:40` (`initialize`), `:58` (`filterPair`) — three filters, each its own option: **variable ordering** (`--sygus-rr-synth-filter-order`, default `true`, **expert**), **congruence** (`--sygus-rr-synth-filter-cong`, default `true`, **expert**), **matching** (`--sygus-rr-synth-filter-match`, default `true`, **expert**), plus **non-linearity** (`--sygus-rr-synth-filter-nl`, default **`false`**, **expert**). — [C] [P] (Reynolds et al., *Rewrites for SMT Solvers using Syntax-Guided Enumeration*, SMT 2018)
- **`DynamicRewrite`** — `quantifiers/dynamic_rewrite.cpp:34` (`addRewrite`), `:61` (`areEqual`) — filters redundant candidate rewrites by keeping an equality engine that does congruence over *all* operators (mapping every operator to an uninterpreted one and doing congruence on `APPLY_UF`): `addRewrite(x,y)` → true, then `addRewrite(f(x),f(y))` → false, because `x=y` is already known. Carries an in-source TODO (#1591) for a stronger technique. — [C]
- **`LazyTrie`** — `quantifiers/lazy_trie.cpp` — the abstract-evaluator-indexed trie backing sample-based equivalence classes. — [C]
- **`RewriteVerifier`** — `quantifiers/rewrite_verifier.cpp:24` (`addTerm`), `:38` (`checkEquivalent`) — the `:rewrite_unsound` target: tests the *rewritten* form of each enumerated term and reports a disagreement. **This is a soundness fuzzer for the rewriter, shipped in the solver.** — [C]
- **`QueryGenerator` (base)** — `quantifiers/query_generator.cpp` — `--sygus-query-gen` default `BASIC`, **expert**; `--sygus-query-gen-thresh=N` default `5`, **expert**; `--sygus-query-gen-filter-solved` default `false`, **expert**; `--sygus-query-gen-dump-files` default `NONE`, **expert**. — [C]
- **`QueryGeneratorSampleSat`** — `quantifiers/query_generator_sample_sat.cpp:36` (`addTerm`), `:150` (`checkQuery`) — **generates satisfiable queries most likely to trigger an unsound answer in an SMT solver**: from a stream `t₁…tₙ`, a query `(not) tₙ = tᵢ` is "interesting" when satisfied by at most D sample points (D = `--sygus-query-gen-thresh`); it also builds conjunctive queries by remembering literals satisfied by the same point. — [C]
- **`QueryGeneratorUnsat`** — `quantifiers/query_generator_unsat.cpp:39` (`addTerm`), `:123` (`checkCurrent`) — generates interesting *unsatisfiable* benchmarks by conjoining predicates that refine models and avoid previously encountered unsat cores. — [C]
- **`SolutionFilterStrength`** — `quantifiers/solution_filter.cpp:36` (`initialize`), `:42` (`setLogicallyStrong`) — `--sygus-filter-sol` default `NONE`, **expert**; `--sygus-filter-sol-rev` default `false`, **expert** — filters predicate solutions entailed by earlier ones (when seeking stronger solutions) or entailing an earlier one (when seeking weaker). **`--produce-abducts` forces `STRONG`** (`set_defaults.cpp:1780-1785`). — [C]
- **`SynthRewRulesPass::getGrammarsFrom`** — `preprocessing/passes/synth_rew_rules.cpp:44` — **the pass itself is dead** (§5.2), but this static builds a grammar whose productions are the subterms of the input with leaves generalised to k variables (`--sygus-rr-synth-input-nvars=N`, default `3`, **expert**), for `find-synth :rewrite_input`. For input `bvadd(bvlshr(bvadd(a,4),1),b) = 1` it emits `A -> T1|T2|T3|T4|Tv`, `T1 -> bvadd(T2,Tv)|x|y`, and so on. Booleans get a single variable unless `--sygus-rr-synth-input-bool`, so purely propositional rewrites are not mined by default. — [C]
- **`SynthFinder`** — `quantifiers/sygus/synth_finder.cpp:36` (`initialize`) plus `src/smt/find_synth_solver.cpp:30, :46` — the `find-synth` / `find-synth-next` commands — a wrapper around a fast sygus enumerator that interleaves several enumerators until one yields a term matching the target (`:rewrite`, `:rewrite_unsound`, `:query`, `:rewrite_input`). — [C]

### 11.7 Abduction, interpolation, and the SyGuS defaults

- **`SygusAbduct::mkAbductionConjecture`** — `sygus/sygus_abduct.cpp:36` — for input `F(x)`, builds `∃A. ∀x. (A(x) ⇒ ¬F(x))`, i.e. `A(x)` is any condition making `A(x) ∧ F(x)` unsatisfiable. With axioms/conjecture partitioned as `Fa ∧ Fc`, the conjecture becomes `∃A. (∃y. A(y) ∧ Fa(y)) ∧ ∀x. (A(x) ⇒ ¬F(x))` — the consistency side condition. **The class's own header says `--sygus-stream` and `--sygus-filter-sol=strong` are enabled by default when it is used**, so the weakest abduct is found by streaming and filtering. — [C]
- **`SygusInterpol`** — `sygus/sygus_interpol.cpp:37` (`collectSymbols`), `:65` (`createVariables`) — for `Fa ⇒ Fc`, builds `(Fa(x) ⇒ A(x)) ∧ (A(x) ⇒ Fc(x))` over the *shared* vocabulary, and solves it **in a fresh copy of the SMT engine** so the original assertion stack is untouched. `--interpolants-mode` (`assumptions`/`conjecture`/`shared`/`all`) selects which symbols `A` may use. — [C]
- **`SygusSolver`** — `src/smt/sygus_solver.cpp` — the API layer for `synth-fun`, `check-synth`, `check-synth-next`, `get-abduct`, `get-interpolant`; `--sygus-out` default `STANDARD`, `regular`; `--check-synth-sol` default `false`, `common`. — [C]
- **`smt_engine_subsolver.cpp`** — `src/theory/smt_engine_subsolver.cpp` — the shared mechanism behind MBQI, sub-cbqi, SyGuS verification, const repair, expression mining, abduction, interpolation, and model checking: spawn a fresh independent `SolverEngine` on a derived query. **Almost every "check something else to decide this" technique in cvc5 runs through this one file.** — [C]
- **`setDefaultsSygus`** — `set_defaults.cpp:1734-1815` — for any SyGuS input: `sygus = true`; `cegqiMidpoint = true` ("must use Ferrante/Rackoff for real arithmetic"); **`cegqiBv = false`** ("may introduce witness terms, which cannot appear in synthesis solutions"); `cegqiSingleInvMode = USE`; `conflictBasedInst = false`; `instNoEntail = false`; `cegqiFullEffort = true`; `miniscopeQuant = OFF`; `macrosQuant = false`. — [C]
- **"Basic sygus" downgrade** — `set_defaults.cpp:1777-1812` — when `--produce-abducts`, `--sygus-stream`, or `--incremental` is set, cvc5 **disables all four non-basic algorithms**: `sygusUnifPbe = false`, `sygusUnifPi = NONE`, `sygusInvTemplMode = NONE`, `cegqiSingleInvMode = NONE`. **So `get-abduct` and streaming synthesis run a materially weaker synthesiser than `check-synth` does.** — [C]

## 12. What this inventory did not verify

Recorded as itself, per the honesty rule. None of these are claims either way.

- Whether `ProcessAssertions::finishInit`'s TODO about "actually assembling preprocessing pipelines" corresponds to any partially landed configurable-pipeline mechanism. No such mechanism was found, but the search was not exhaustive outside `src/preprocessing` and `src/smt`.
- The per-mode internals of `--solve-bv-as-int` (`sum`/`iand`/`bv`/`bitwise`) inside `theory/bv/int_blaster.cpp` beyond the pass wrapper and the top-level translation.
- The normalisation and pivoting internals of `preprocessing/passes/bv_gauss.cpp` (entry point and header only).
- The precise semantics of `miplib_trick`'s `traceBackToAssertions` / `collectBooleanVariables` beyond the circuit-propagator back-edge mechanism.
- Whether `normalize.cpp`'s "super-pattern" symbol-occurrence machinery is used for anything beyond deterministic renaming.
- Whether `LearnedRewrite`'s learned-literal consumption interacts with `--deep-restart` in a way that changes which literals are visible on the second round.
- Whether `arith_rewriter.cpp`'s `rewriteIneqToBv` (`:1589`, `:1603`) is gated by a dedicated option; it was reached only from the rewriter.
- Every `[I]`-tagged entry in §9 is an inference from surrounding code (typically an inference-ID enum plus its emission site) rather than a directly asserted statement in the source.
- **Nothing here was measured by running cvc5.** Every status is read from source and option declarations. A configuration-dependent default that only manifests at runtime (an option set from an environment variable, a competition wrapper script, or a distro patch) would not appear.
- The `references/cvc5` clone is depth-1 at `1689f133` (2026-09-03). No history was consulted, so "recently added" and "legacy" are not distinguished anywhere in this document.
