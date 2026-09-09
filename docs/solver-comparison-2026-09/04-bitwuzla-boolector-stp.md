# Bitwuzla, Boolector, and STP — inventory and gaps (2026-09-09)

Scope: the three solvers whose core domain is exactly ours — quantifier-free
bit-vectors and arrays decided by bit-blasting to SAT, plus floating point.

| Clone | Commit | Last commit | Size | Language | License | Lines |
|---|---|---|---|---|---|---|
| `references/bitwuzla` | `a5e6e8a7ad511975c495455924d0868bcdc304ea` | 2026-09-04 | 51M | C++17 | MIT (`COPYING:7`) | 97,095 under `src/` |
| `references/boolector` | `43dae91c1070e5e2633e036ebd75ffb13fe261e1` | 2024-08-23 | 27M | C99 | MIT (`COPYING:7`) | 100,204 under `src/` |
| `references/stp` | `e4af105c0270900e2226af82d824c1f5a80c7dfd` | 2026-09-08 | 26M | C++ | MIT (`LICENSE:1`) | 125,020 under `lib/`+`include/` |

Bitwuzla is Boolector's successor by the same group; Boolector is a finished
project, not an abandoned one. STP is older in lineage but **not** dormant — its
last commit is one day before this read, and its tree contains machinery
(three CNF backends, a division-lemma catalogue, a UF refinement loop, a SymFPU
FP backend, a 4,000-line incremental layer) that no summary of "the 2007 CAV
paper" would predict. Where a claim about STP below is surprising, it is because
the code moved, not because the paper says so.

Bitwuzla sub-tree sizes, for calibrating the gap sizes at the end:
`src/solver/` 19,994 lines, `src/rewrite/` 13,221, `src/lib/ls/` 10,227,
`src/preprocess/` 6,699.

Our side is cited into [`docs/solver-inventory-2026-09/`](../solver-inventory-2026-09/00-README.md)
throughout; `crates/…` citations are at base commit `ea8515407`.

## Summary

- **All three are the same architecture we are: eager bit-blasting to a SAT
  core, with an AIG in between.** Bitwuzla is the current state of the art in
  that architecture. The comparison is therefore unusually direct, and most of
  what follows is a difference in *depth*, not in kind.
- **Rewrite-level hierarchy.** Bitwuzla keeps Boolector's rewrite-level idea but
  narrows it: `Rewriter::LEVEL_MAX = 2`, plus an internal, non-configurable
  `LEVEL_ARITHMETIC = 3` used only by the normalization pass
  (`references/bitwuzla/src/rewrite/rewriter.h:49-70`;
  `src/preprocess/pass/normalize.cpp:251`). Default level 2
  (`src/option/option.cpp:287-294`). Level 0 = operator elimination only, 1 =
  one-level rewrites, 2 = multi-level. There are **296 distinct rewrite rules**
  (`RewriteRuleKind`, `rewriter.h:372-829`, cross-checked against 296 `CASE(...)`
  entries in the printer at `rewriter.cpp:2056+`). We ship **59**
  (`docs/solver-inventory-2026-09/02-frontend-ir-and-rewriting.md`,
  `axeyum-rewrite/src/canonical.rs:847-861`), with no level concept at all.
- **AIG-to-CNF.** Bitwuzla's encoder is **plain two-sided Tseitin** with one ITE
  pattern match and top-level AND flattening, and it carries TODOs for exactly
  the two optimizations we already have — multi-input AND collection and native
  XOR (`references/bitwuzla/src/lib/bitblast/aig/aig_cnf.cpp:296-297`). STP has
  **three** CNF backends behind one AUTO chooser: an in-house Tseitin with four
  recovery rungs, ABC's `Cnf_Derive`, and ABC's Gia + `Mf_ManGenerateCnf`
  (technology-mapping/LUT-based) — `references/stp/lib/ToSat/ToSATAIG.cpp:262-345`.
  Ours is a single polarity-aware Plaisted–Greenbaum encoder with XOR/ITE/AND-tree
  fusion (`crates/axeyum-cnf/src/lib.rs:3500-3627`). On the *encoder* we are
  ahead of Bitwuzla and behind STP; on *rewriting before* the encoder we are far
  behind both.
- **Arrays: a genuine architectural fork.** Bitwuzla has **no eager array
  elimination anywhere** — no preprocessing pass touches `SELECT`/`STORE`, and
  the only eager array rule is a constant-index store-chain rewrite
  (`references/bitwuzla/src/rewrite/rewrites_array.cpp:20-53`). Everything is
  lazy lemmas on demand over a warm SAT solver, with five named schemas
  (`src/solver/array/array_solver.h:30-37`). STP is a *staged hybrid*: it
  Ackermannizes eagerly when the read count and estimated expansion are both
  small, otherwise it runs read refinement
  (`references/stp/lib/STPManager/STP.cpp:720-745`). We are eager-first with two
  lazy CEGAR layers above it (ADR-0010,
  `docs/solver-inventory-2026-09/05-bitvector-arrays-fp-and-datatypes.md`).
- **The costly detail is not eager-vs-lazy, it is warm-vs-cold.** Bitwuzla's and
  STP's refinement rounds add clauses to a SAT solver that keeps everything
  (`references/bitwuzla/src/solver/bv/bv_bitblast_solver.cpp:154,255,349-350`;
  `references/stp/lib/STPManager/STP.cpp:1275-1310`). Our lazy array CEGAR calls
  `SatBvBackend::new()` and re-lowers and re-blasts from scratch every round
  (`crates/axeyum-solver/src/auto.rs:5563`, and the per-round
  `backend.check(...)` at `crates/axeyum-solver/src/abv.rs:138`). We do own a
  warm engine and one route uses it — `ufbv_online.rs` drives
  `IncrementalBvSolver` through `CdclT` (`crates/axeyum-solver/src/ufbv_online.rs:442,473`)
  — so this is a wiring gap, not a missing component.
- **Local search is the largest single missing subsystem.** Bitwuzla's
  propagation-based local search is **10,227 lines** (`src/lib/ls/`) with
  four functions per BV operator — `is_invertible` / `is_consistent` /
  `inverse_value` / `consistent_value` across 17 operator classes
  (`src/lib/ls/bv/bitvector_node.cpp`, table in axis F below) — plus essential-input
  path selection and a `preprop` sequential portfolio mode
  (`src/solver/bv/bv_solver.cpp:139-152`). Our `pbls.rs` is 1,456 lines of
  WalkSAT-family SLS over the ground evaluator with no invertibility
  reasoning at all (`crates/axeyum-solver/src/pbls.rs:1-26`). A search for
  `invertib|inverse_value` across `crates/*/src/` returns only modular-inverse
  hits in `axeyum-arith`/`axeyum-cas`; positive control `local_search` finds
  `pbls.rs`, `preprocess.rs`, `abv.rs`.
- **Floating point.** Bitwuzla uses SymFPU (vendored as a meson subproject,
  `subprojects/symfpu.wrap`) with *two* traits instantiations — concrete and
  symbolic — and word-blasts **lazily, inside the lemma loop**, emitting
  `node = wordblasted_bv` as a lemma per FP term
  (`src/solver/fp/fp_solver.cpp:118-141`). STP also uses SymFPU
  (`references/stp/lib/FloatBlaster/FloatBlaster.cpp:97-104`) but lowers in a
  dedicated pass placed after the size-reducing passes and keeps seven
  predicates native to the bit-blaster (`references/stp/lib/STPManager/STP.cpp:822-836`).
  Ours eliminates FP to BV **in the parser**, before the solver exists
  (`crates/axeyum-smtlib/src/parse.rs:16246-19876`, 37 call sites).
- **Wide-multiplier abstraction is on by default in Bitwuzla and off in both
  STP and us.** `abstraction` defaults true with a 33-bit threshold and **97**
  named lemma schemas for `bvmul`/`bvudiv`/`bvurem`/`bvadd`
  (`src/solver/abstract/abstraction_lemmas.h:24-136`,
  `src/option/option.cpp:364-376`). STP has an equivalent
  (`bv_term_abstraction`, default **false**,
  `references/stp/include/stp/STPManager/UserDefinedFlags.h:614`) with a
  33/11/14-entry `DivLemma`/`RemLemma`/`MulLemma` catalogue
  (`references/stp/include/stp/ToSat/BVLemmaCatalogue.h`). We have `lazy_bv.rs`
  (ADR-0019), also default **false** (`crates/axeyum-solver/src/backend.rs:398`),
  and it has no lemma catalogue — it refines by adding the exact
  `fresh == op(lhs, rhs)` definition (`crates/axeyum-solver/src/lazy_bv.rs:9-27`).
- **Proofs: this is where we are ahead, and it is not close.** Bitwuzla has no
  proof API at all — `include/bitwuzla/cpp/bitwuzla.h` has `get_unsat_core`
  (`:1743`) and `get_interpolant` (`:1825`) and no `get_proof`; the only proof
  consumption is CaDiCaL's resolution trace feeding interpolant construction
  (`src/sat/interpolants/tracer.h:33`). STP has no DRAT/LRAT emission either
  (grep for `drat|lrat|--proof` over `references/stp/lib`, `include`, `tools`
  returns zero; positive control: `proof` alone matches ten places, all internal
  congruence-proof-tree language). We emit and check DRAT, elaborate to LRAT,
  and emit Alethe (`docs/solver-inventory-2026-09/01-sat-core-and-cnf.md`).
- **They validate their models less than we do.** Bitwuzla's `CheckModel` builds
  a fresh nested `SolvingContext` and re-asserts the original assertions plus the
  model, but the option defaults to `is_debug_build`
  (`src/check/check_model.cpp:42-65`, `src/option/option.cpp:597-601`). STP's
  `CheckCounterExample` is gated on `check_counterexample_flag`, default
  **false** (`references/stp/include/stp/STPManager/UserDefinedFlags.h:1096`).
  Our default QF_BV backend replays every `sat` against the original terms
  unconditionally and turns a model that evaluates false into a `SolverError`
  (`docs/solver-inventory-2026-09/01-sat-core-and-cnf.md`, step 9 of the data flow).
- **Unsat cores.** All three get cores for free from failed SAT assumptions in a
  single solve (`references/bitwuzla/src/solver/bv/bv_bitblast_solver.cpp:243-252,316-330`;
  `references/stp/lib/Incremental/IncrementalSolver.cpp:85-131`). Ours is
  deletion-based minimization that re-solves the whole query once per assertion
  (`crates/axeyum-solver/src/auto.rs:801-830`).
- **Interpolation: Bitwuzla has it and STP does not**, and Bitwuzla's is
  bit-level from CaDiCaL's proof with an optional lift to the term level
  (`interpolants-algo` default `mcmillan`, `src/option/option.cpp:442-448`).

## Schema

### A — Input front end

**Bitwuzla.** Hand-written recursive-descent parsers, no generator:
`references/bitwuzla/src/parser/smt2/` (lexer + parser + `parser.h` carrying
`unsat_core` state) and `references/bitwuzla/src/parser/btor2/`. Public C, C++
and Python APIs under `src/api/`. Theories: BV, FP, arrays, UF, quantifiers.
Unsupported constructs are raised, not ignored — `FunSolver::register_term`
calls `d_solver_state.unsupported("Equalities over functions not yet
supported.")` (`src/solver/fun/fun_solver.cpp:173-174`) and the same for
equalities over uninterpreted sorts (`:179-180`), so a query in a nominally
supported logic can still be refused at solve time rather than at parse time.

**STP.** Three lex/yacc grammars: `references/stp/lib/Parser/cvc.{lex,y}` (1,126
lines of grammar — the native CVC language), `smt.{lex,y}` (SMT-LIB 1, 1,103) and
`smt2.{lex,y}` (SMT-LIB 2, 3,958). C and C++ APIs at
`references/stp/lib/Interface/c_interface.cpp` (4,404) and `cpp_interface.cpp`
(2,124). Logics named in the `set-logic` diagnostic
(`references/stp/lib/Parser/smt2.y:309-311`): `QF_BV, QF_ABV, QF_AX, QF_UF,
QF_UFBV, QF_AUFBV`, the FP logics `QF_FP, QF_BVFP, QF_ABVFP, QF_UFFP, QF_UFBVFP,
QF_AUFBVFP`, "and their LRA variants". Floating-point sorts are gated on the
logic: the lexer only routes `fp` keywords after an FP `set-logic`
(`smt2.y:905-908`), which is a deliberate rejection, not a silent ignore.

**Boolector.** Four formats — BTOR, BTOR2, SMT-LIB 1 and SMT-LIB 2
(`references/boolector/src/parser/btorbtor.c`, `btorbtor2.c`, `btorsmt.c` 2,936
lines, `btorsmt2.c` 5,046). Hand-written, with format auto-detection by suffix
and then by content sniffing (`src/btorparse.c:110-238`; `(` + `b` ⇒ SMT-LIB 1,
`(` + anything else ⇒ SMT-LIB 2, a `" sort "` token on the first line ⇒ BTOR2).
Logics: `QF_BV`, `QF_ABV`, `QF_UFBV`, `QF_AUFBV`, `BV`, `ALL`
(`src/btorlogic.h:15-18`, `src/parser/btorsmt2.c:4632-4675`), and the logic is
**re-derived** after parsing from what the script actually contains
(`:4992-5019`). Roughly 27 other logic tokens are interned and then *rejected* —
recognized, not ignored (`:4661-4663`). Same for commands: `get-unsat-core` and
`get-proof` are interned as tokens (`:880`, `:879`) with **no case in the
dispatch switch**, so they reach `"unsupported command '%s'"` (`:4915-4917`).
BTOR2's model-checking extensions (`bad`, `init`, `next`, `state`, …) are
rejected with a pointer to `btormc` (`src/parser/btorbtor2.c:586-596`).

**Ours.** One hand-written reader (`axeyum-smtlib/src/sexpr.rs`, iterative, no
recursion) plus a 23,668-line typed parser. Unknown commands are **rejected**
(`SmtError::Unsupported`, `parse.rs:6297`) rather than ignored. The distinctive
difference is that our parser is also the first preprocessing stage and can
return verdicts: `source_string_semantic_unsat` and
`source_fp_prefix_monotonic_unsat` are decided at parse time
(`docs/solver-inventory-2026-09/02-frontend-ir-and-rewriting.md`).

### B — Preprocessing (before search)

**Bitwuzla.** Nine pass classes in `references/bitwuzla/src/preprocess/pass/`,
driven by `Preprocessor::apply` (`src/preprocess/preprocessor.cpp:237-415`) as a
`do { … } while (modified && !inconsistent && !terminate)` **fixpoint loop**
counted by `num_iterations` (`:269`). Order inside one iteration:

| # | Pass | Gate | Note |
|---|---|---|---|
| 1 | `PassRewrite` | unconditional | `preprocessor.cpp:272` |
| 2 | `PassFlattenAnd` | `pp_flatten_and` (default true) | `:283-296` |
| 3 | `PassVariableSubstitution` | `pp_variable_subst` (true) | **nested inner fixpoint**, `:298-314` |
| 4 | `PassSkeletonPreproc` | `pp_skeleton_preproc` (true) | **at most once**, initial assertions only, `:316-330` |
| 5 | `PassEmbeddedConstraints` | `pp_embedded_constr` (true) | `:332-350` |
| 6 | `PassElimLambda` | unconditional | `:353` |
| 7 | `PassElimUdiv` | `if (false && …)` | **dead code**, disabled at `:356-357` |
| 8 | `PassNormalize` | `rewrite_level >= 2 && pp_normalize`, **first `preprocess()` call only** | `:261`, `:369-384` |
| 9 | `PassQuant` | `pp_quant` (true) | `:386-395` |

Model reconstruction is maintained three ways: a per-preprocessor
`backtrack::BacktrackManager` chained to the context's by a `PopCallback`
(`preprocessor.h:106-115`); backtrackable substitution maps inside
`PassVariableSubstitution` (`variable_substitution.h:101-137`) and
`PassEmbeddedConstraints`; and `Preprocessor::process(const Node&)`
(`preprocessor.cpp:147-158`), which replays a **subset** of the pipeline
(`rewrite → varsubst → elim_lambda → embedded_constraints → rewrite`, with a TODO
at `:149` saying more passes belong there) on a single term for `get-value`.
Unsat cores are mapped back through `AssertionTracker::find_original`
(`preprocessor.cpp:160-211`).

**STP.** Preprocessing is the largest part of the system and the order is
explicit in `references/stp/lib/STPManager/STP.cpp:565-1020`
(`TopLevelSTPAux`). Reading it top to bottom:

1. `PropagateEqualities` and `RemoveUnconstrained`, **but only for array
   equalities**, run before array-equality lowering (`STP.cpp:620-660`).
2. `ExtensionalityContext::lowerArrayEqualities` (`:657-659`).
3. Eager Ackermannization of array reads, **conditional** on both a read count
   (`arrayReadLimit`, 10 or 50 with `--ackermannisation`) and an estimated
   structural expansion cost (`arrayEagerCostPerRead = 20`) — `:713-745`.
4. `Flatten` (sharing-aware) (`:771-777`).
5. `ConstantBitPropagation::topLevelBothWays` (`:779-792`).
6. `sizeReducing(...)`, optionally iterated to a fixed point when the node count
   is under `size_reducing_fixed_point` (`:794-807`).
7. Floating-point lowering (`:822-836`) — deliberately *after* the size-reducing
   passes so `RemoveUnconstrained` still sees float symbols.
8. A **fixpoint loop** `do { PropagateEqualities; SimplifyFormula_TopLevel;
   BVSolver::TopLevelBVSolve } while (changed)` (`:869-936`).
9. `ConstantBitPropagation` again (`:932-946`), then `StrengthReduction` over
   `NodeDomainAnalysis` intervals (`:948-957`).
10. `FindPureLiterals` (`:961-970`), `UseITEContext` (`:977-982`),
    `AIGSimplifyPropositionalCore` (`:984-990`), `CommonSubSum` over
    `{BVPLUS,BVMULT,BVXOR,BVAND,XOR,AND,OR}` (`:1004-1012`),
    `RemoveUnconstrained` (`:1015-1020`).
11. **Difficulty reversion.** `DifficultyScore` is taken before and after; if the
    simplified formula did not get at least 20% cheaper, STP **reverts to the
    pre-simplification formula**, keeping only the variable-to-constant
    assignments it discovered (`:1024-1090`). We have an analogue at the encoding
    level only — `reduction_shrinks_encoding` (`crates/axeyum-solver/src/auto.rs:2233-2264`).

`constantBitP/` is 7,619 lines and is the distinctive piece: a 3-valued
`FixedBits` domain with a worklist fixpoint (`ConstantBitPropagation.cpp:414`) and
transfer functions for 26 kinds registered by a macro table
(`ConstantBitPropagation.cpp:589-630`) plus six hand-written ones for
`BVMULT/BVDIV/BVMOD/SBVDIV/SBVREM/SBVMOD` (`:645-666`). `READ`/`WRITE` are
explicitly skipped ("Seems difficult to track properly", `:583-585`). Division
alone is 1,839 lines and multiplication 1,019. The result is used **both** to
simplify and to decide: `cb.isUnsatisfiable()` short-circuits the whole query to
`false` (`STP.cpp:786-789`), and the same object is handed to `ToSATAIG` so the
bit-blaster can use the fixed bits (`STP.cpp:1168-1178`).

**Boolector.** Fourteen passes plus a driver in
`references/boolector/src/preprocess/`. `btor_simplify`
(`src/preprocess/btorpreprocess.c:34`) is a `do { … } while
(varsubst_constraints->count || embedded_constraints->count)` fixpoint
(`:196-197`) with mid-loop `continue`s that restart a round as soon as a pass
produces new substitutions. Order: `btor_substitute_var_exps` (`:78`) →
`btor_process_embedded_constraints` (`:92`, itself an inner `while`) →
`btor_eliminate_slices_on_bv_vars` (`:109`) → `btor_process_skeleton` (`:128`,
**at most once**, and Lingeling-only — the whole file is `#ifdef
BTOR_USE_LINGELING`, `btorskel.h:9-15`) → `btor_optimize_unconstrained` (`:150`)
→ `btor_extract_lambdas` (`:163`) → `btor_merge_lambdas` (`:167`) →
`btor_eliminate_applies` (`:185`) → `btor_add_ackermann_constraints` (`:190`) →
`btor_normalize_adds` (`:194`). Each gate is a rewrite-level test, which is how
the level hierarchy reaches preprocessing and not only rewriting.

Two things worth taking. First, `btorextract.c` (1,568 lines) recognizes
**store patterns** — `memset`, `itoi`, `itoip1`, `memcpy` (`:167`, `:200`,
`:234`, `:269`, detectors `:390-457`) — and rewrites them into lambdas with range
conditions, so a loop-shaped store chain becomes one term instead of thousands.
We have no analogue. Second, model reconstruction is done by **proxy nodes**
rather than a trail: a substituted node becomes `BTOR_PROXY_NODE`
(`src/btornode.h:65`) and `btor_node_get_simplified` chases the chain at model
time (`src/btormodel.c:1405-1418`). Unconstrained-variable optimization is the
one pass **disabled under model generation** (`btorpreprocess.c:148`, asserted
inside the pass at `btorunconstrained.c:86`).

**Ours.** Five steps, run **exactly once**, not to a fixpoint:
`canonicalize_terms → propagate_values → solve_eqs_bounded → elim_unconstrained →
canonicalize_terms` (`crates/axeyum-solver/src/auto.rs:2158-2199`), gated on one
boolean with no per-pass switch. A second, near-identical 8-round pipeline exists
and is not what the front door uses
(`docs/solver-inventory-2026-09/02-frontend-ir-and-rewriting.md`, and
integration gap #3 in `11-wiring-and-integration.md`). Model reconstruction is a
`ModelReconstructionTrail` replayed in reverse, plus `project_model` for
arrays/functions.

### C — Core SAT engine

None of the three has its own CDCL. This is the sharpest structural difference
from us in the other direction: **we wrote the SAT solver; they link one.**

**Bitwuzla** wires four back ends behind `SatSolverFactory::new_sat_solver`
(`references/bitwuzla/src/sat/sat_solver_factory.cpp:34-77`): CaDiCaL,
CryptoMiniSat, Kissat, Gimsatul. Default is a compile-time preference chain
resolving to CaDiCaL in a stock build (`src/option/option.cpp:246-259`;
`meson_options.txt:5-8` has `cadical=true` and the rest false). Only CaDiCaL
supports interpolation; the others `throw Unsupported`
(`sat_solver_factory.cpp:40-43,49-53,60-63`). Bitwuzla additionally installs its
own **SAT-level propagators and decision heuristics** — `src/sat/propagator.*`,
`distinct_n_propagator.*`, `distinct_decision_heuristic.*`,
`eq_decision_heuristic.*`, registered from
`src/solver/bv/bv_bitblast_solver.cpp:214-215`. That is a CDCL(T)-style hook into
the SAT solver's search that neither Boolector nor we have.

**STP** wires CaDiCaL, CryptoMiniSat5, MiniSat and a "simplifying MiniSat"
(`references/stp/lib/Sat/SATSolverFactory.cpp:98-...`). Default is a compile-time
chain: CryptoMiniSat if linked, else CaDiCaL, else MiniSat
(`references/stp/include/stp/STPManager/UserDefinedFlags.h:1395-1409`), with the
comment that CaDiCaL "is the only backend on by default, so it is what a stock
build solves with".

**Boolector** wires five: Lingeling, PicoSAT, MiniSat, CaDiCaL, CryptoMiniSat
(`references/boolector/src/btoropt.c:23-29`), behind a function-pointer vtable
`BtorSATMgr.api` (`src/btorsat.h:23-74`) whose only required members are `add`,
`deref`, `init`, `reset`, `sat`. Default is a compile-time cascade preferring
CaDiCaL (`src/btoropt.h:65-77`). All five provide `assume`+`failed`; only
Lingeling provides `clone`, and only Lingeling and CaDiCaL provide a termination
callback. Confirming the claim that it has no CDCL of its own: a search for
`watch(ed)?_list|decision level|analyze_conflict|backtrack|luby|restart_interval`
over `src/*.c` and `src/sat/*.c` returns zero files, with `restart` in
`btorslvprop.c` (4 hits) as the positive control.

**Ours.** `axeyum-cnf/src/proof_sat.rs`, 8,333 lines: flat clause arena,
blocking-literal watches, 1-UIP analysis, VSIDS, Luby restarts, LBD tiers,
`reduce_db`, DRAT emission by construction
(`docs/solver-inventory-2026-09/01-sat-core-and-cnf.md`). It is the only engine
on the default path. No chronological backtracking (grep
`chronological|chrono_backtrack` over `proof_sat.rs` is empty; positive control:
`restart` matches 91 times). Phase saving exists but the **default policy never
rephases** — `PhasePolicy::pinned()` is selected at `proof_sat.rs:572` and
`pinned_policy_never_rephases` pins `should_rephase` to false
(`phase_policy.rs:225-228`).

### D — Inprocessing (during search)

**Bitwuzla.** None at the SMT layer; whatever inprocessing happens is CaDiCaL's.
The lemma loop is the only thing that runs between solves, and it adds
assertions, it does not simplify existing ones. `PassSkeletonPreproc` is the one
pass that uses SAT-level reasoning, and it runs **once**, before search
(`src/preprocess/preprocessor.cpp:316-330`; the pass is a no-op stub when
CaDiCaL is not the backend, `skeleton_preproc.h:81`).

**STP.** Same shape — the refinement driver
(`references/stp/lib/STPManager/STP.cpp:1275-1337`) adds lemmas and re-solves;
it does not re-simplify. Bounded variable addition is handed to CaDiCaL once,
before the first clause, via `enableBVAIfWanted` (`STP.cpp:754-760`) with an
`AUTO` mode that turns it on when array operations survive preprocessing.

**Boolector.** None at the SMT layer either — `btor_simplify` runs once,
before the engine is chosen (`src/btorcore.c:2971`), never inside the lemma loop
(`src/btorslvfun.c:2500-2571`). It does have one thing the others do not: during
AIG construction, if the SAT solver is already initialized, `btor_aig_and` queries
it back for fixed and equivalent literals — `simp_aig_by_sat`
(`src/btoraig.c:402-424`, called at `:436-440`), using `btor_sat_fixed` and
`btor_sat_repr`. That is SAT-solver inprocessing results flowing *up* into the AIG
layer, which none of the other three does.

**Ours.** We have the machinery — subsumption, vivification, BVE, compaction and
XOR propagation, with a proof-carrying variant (ADR-1750) — and it is **off by
default**: `cnf_inprocessing: false` (`crates/axeyum-solver/src/backend.rs:390`),
and `cnf_vivify: true` is a documented no-op without it. Integration gaps #1 and
#2 in `docs/solver-inventory-2026-09/11-wiring-and-integration.md`. So on this
axis all four systems currently run nothing during search at the SMT layer, and
we are the only one that has written the passes.

### E — Encoding and bit-blasting

This is the axis where the four systems are most directly comparable, so it is
split into four parts.

#### E.1 Word-level rewriting

| | Rules | Levels | Memoized | Per-rule stats |
|---|---|---|---|---|
| Bitwuzla | **296** (`rewriter.h:372-829`) | 0-2 configurable + internal 3 (`rewriter.h:49-70`), default **2** (`option.cpp:287-294`) | yes, `d_cache` + aliased `d_eval_cache` (`rewriter.h:330,340`), 4096-deep recursion guard (`rewriter.cpp:460-466`) | yes — `HistogramStatistic` keyed by `RewriteRuleKind`, bumped in the `BZLA_APPLY_RW_RULE` macro (`rewriter.h:37-38`) |
| Boolector | **127** matched `applies_*`/`apply_*` pairs in `btorrewrite.c` (7,391 lines) | **0-3**, default **3** (`btoropt.c:406-416`, semantics `btortypes.h:222-237`) | yes, a dedicated `btorrwcache.c` keyed on `(kind, n[3])` with GC | `num_add/num_get/num_update/num_remove` on the cache, not per rule |
| STP | `Simplifier.cpp` + `Rewriting.cpp` + a generated rule table (`tools/rewrite_rule_gen`) | no numbered hierarchy; per-pass `UserDefinedFlags` booleans | yes, simplify caches with `ClearCaches()` (`STP.cpp:1145-1146`) | `RunTimes` per phase, not per rule |
| Ours | **59** (`axeyum-rewrite/src/canonical.rs:847-861`) | none | yes | `pass_stats.rs` exists (345 lines) with **no caller outside its own tests** |

Two structural facts about Bitwuzla's hierarchy worth copying and one worth not.
Level 1 does not merely disable level-2 rules; it substitutes *cheaper alternates*
for them (`rewriter.cpp:1305-1336`, where `d_level == 1` enables
`BV_EXTRACT_CONCAT_FULL_LHS/RHS` and `d_level >= 2` enables the general
`BV_EXTRACT_CONCAT`). And level 3 both adds rules and **suppresses** level-2 ones
(`if (!d_arithmetic)` at `rewriter.cpp:1329,1351,1360`) because normalization
wants a different normal form than solving does. The thing worth not copying is
that the level is a bare `uint8_t` with no enum
(`rewriter.h:327`); every gate is an open-coded `>=` comparison.

Boolector's is the hierarchy Bitwuzla inherited and narrowed, and its boundaries
are worth recording separately because they are *not* the same cut. Level 0 → 1 is
a switch at every constructor: `btorexp.c` tests `rewrite_level > 0` at fifteen
sites (`:218, 253, 491, 618, 709, 796, 964, 1122, 1143, 1388, 1477, 1613, 1763,
1815, 1875`) to decide between `btor_rewrite_*_exp` and the raw
`btor_node_create_*`, so level 0 bypasses `btorrewrite.c` entirely. Level 1 → 2
unlocks the **preprocessing substitution machinery** — variable substitution and
embedded constraints both require `> 1` (`btorpreprocess.c:74`,
`btorcore.c:1193`). Level 2 → 3 is where the bulk sits: roughly 58 `>= 3` / `> 2`
guards inside `btorrewrite.c`, plus slice elimination, skeleton preprocessing,
UCOPT, lambda extraction, lambda merging and adder normalization at the
preprocessing level (`btorpreprocess.c:106, 122, 146, 161, 165, 192`). One rule is
*disabled* at level 3 because a stronger level-3 rule subsumes it —
`applies_concat_upper_slice` requires `rewrite_level < 3`
(`btorrewrite.c:1464-1470`), the same "a higher level suppresses a lower rule"
pattern Bitwuzla's `!d_arithmetic` guards use. The header also warns: "Do not
alter the rewrite level of the rewriting engine after creating expressions"
(`btortypes.h:236-237`).

Composition of Bitwuzla's 296: 82 `*_EVAL` (constant folding), 48 `*_ELIM`
(operator elimination, active even at level 0), 14 `NORM_*`; by theory, 171
BV-prefixed, 44 FP-prefixed, **1 array** (`ARRAY_PROP_SELECT`), the rest core and
Boolean. The single-array-rule figure is the number to hold onto for axis F: in
Bitwuzla arrays are not a rewriting problem.

#### E.2 AIG construction and structural hashing

**Bitwuzla.** `references/bitwuzla/src/lib/bitblast/aig/`. Tagged-pointer
`AigNode` where bit 0 is the inversion flag, so negation allocates nothing
(`aig_node.h:30,52,67-70`). Three node categories: constant, input, two-input
AND. Reference-counted with `gc()` on zero (`aig_node.h:99-110`).
`AigNodeUniqueTable` is an open-chained table, hash `547789289*|l| +
786695309*|r|`, power-of-two buckets (`aig_manager.cpp:92-101`), with children
normalized by `|id|` before lookup (`aig_manager.cpp:398-402`).
`find_or_create_and` counts unique-table hits as `num_shared`
(`aig_manager.cpp:167-171`) — an explicit sharing metric.

**`AigManager::mk_and` performs local two-level AIG rewriting on the way in**,
citing Brummayer and Biere's *Local Two-Level And-Inverter Graph Minimization
without Blowup* (`aig_manager.h:103-108`). It is a `do { … } while(true)` loop
with four labelled levels (`aig_manager.cpp:177-407`): level 1 neutrality /
idempotence / boundedness / contradiction (`:185-215`); level 2 asymmetric and
symmetric contradiction and subsumption, idempotence over `(a∧b)∧c`, and
resolution (`:224-306`); level 3 asymmetric and symmetric substitution, which
`continue` the loop with a rewritten operand (`:308-368`); level 4 idempotence
over `(a∧b)∧(c∧d)`, also iterating (`:370-390`). There is **no AIG rewrite-level
option** — all four are always on.

**STP.** Two AIG layers. Its own is `references/stp/lib/AIG/Manager.cpp` — "a
flat array of two-input AND nodes, hash-consed" with the id *being* the array
index and no hash-chain link (`include/stp/AIG/Manager.h:40-48`), and a
`freeStrash()` that releases the hash table before the clause arena is allocated
because that is the peak-memory point (`lib/ToSat/ToCNFTseitin.cpp:~45-48`). The
other is **ABC's**, used through `Aig_ManDupDfs` / `Aig_ManCleanup` /
`Aig_ManCheck` in `lib/ToSat/ToCNFAIG.cpp:57-101` and `lib/ToSat/BVExactEncoder.cpp:73-98`.

**Boolector.** `src/btoraig.c` (1,540 lines). Same tagged-pointer scheme —
`BTOR_AIG_FALSE = (BtorAIG*)0`, `BTOR_AIG_TRUE = (BtorAIG*)1`, inversion on bit 0
(`btoraig.h:74-86`) — with a chained unique table (`hash_aig`, prime
`2000000137u`, chain-length limit 30, `btoraig.c:41-43, 136, 202-253`).
`btor_aig_and` is a ~315-line function containing the same Brummayer–Biere
two-level set, explicitly labelled `/* 2 level minimization rules for AIGs */`
(`:456`): contradiction (`:457, 472`), subsumption (`:486, 502`), resolution
(`:530`), asymmetric and symmetric idempotency (`:563, 577`) and substitution
(`:603, 631`), each with a commutative variant, iterating through fourteen
back-jumps to a `BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN` label (`:439`). It also runs a
**bounded deeper contradiction search**, `find_and_contradiction_aig`
(`:373-401`) with `BTOR_FIND_AND_CONTRADICTION_LIMIT 8` (`:45`) — a rule
Bitwuzla dropped. There is no user-facing AIG rewrite level in either.

**Ours.** `crates/axeyum-aig/src/lib.rs`, 1,046 lines, one file. `AndUniqueTable`
structural hashing (`:270`), constant folding, dense node ids, `AigLit` = node +
inversion bit. `Aig::and` (`:345`) does: the four level-1 rules
(`simplify_and`, `:732-744` — neutrality, idempotence, boundedness,
contradiction), plus **absorption** (`absorb_or_rhs`, `:390-401`) and **OR
consensus** (`simplify_and_by_or_consensus`, `:403-408`), which are two of
Bitwuzla's level-2 rules. We have neither of Bitwuzla's level-3 substitution
rules nor level-4, and our rewriting is **not iterated** — there is no loop that
re-enters after a rewrite. Construction counters exist
(`and_requests`, `and_trivial_simplifications`, `and_absorption_simplifications`,
`and_structural_hash_hits`, `and_nodes_created`), so the sharing metric is
present on both sides.

Multiplier and divider circuits: ours is a truncated shift-and-add multiplier
and a combinational restoring divider (`crates/axeyum-bv/src/lib.rs:2298-2325`,
`:2348`). The comment at `:2305-2311` records that modified-Booth radix-4 was
implemented, verified by exhaustive evaluator equality plus a DRAT miter, and
**reverted** because the public QF_BV frontier is 8-bit where Booth is a
regression. That is a measured decision, not a missing feature.

#### E.3 AIG-to-CNF

**Bitwuzla: plain two-sided Tseitin.** `AigCnfEncoder::_encode`
(`references/bitwuzla/src/lib/bitblast/aig/aig_cnf.cpp:238-341`) has no polarity
parameter and always emits both implication halves: for `x ↔ a ∧ b`, the three
clauses `(¬x∨a)(¬x∨b)(x∨¬a∨¬b)` (`:319-338`). Two optimizations exist:

- **ITE pattern extraction** (`is_ite`, `aig_cnf.cpp:153-237`) matching
  `¬(c∧¬a) ∧ ¬(¬c∧¬b)` in all four commutative orderings, emitting four clauses
  (`:300-317`) — and it **refuses to extract when it would destroy sharing**
  (`if (l.parents() > 1) return false;`, `:172-185`), which is why
  `AigNodeData` carries a parent count.
- **Top-level AND flattening** (`encode(node, top_level=true)`, `:37-87`): walk
  down non-negated ANDs from the root and emit one unit clause per leaf
  (`:64-81`) instead of a variable for the root conjunction.

What it does **not** do is stated in its own source as two TODOs at
`aig_cnf.cpp:296-297`: "and optimization: collect all children and encode one
big and" and "xor optimization: use native xor encoding". There is no technology
mapping — grep for `cut|technology map|cut enum` over `src/lib/bitblast/` and
`src/solver/bv/aig_bitblaster.cpp` returns nothing; positive control, `and`
matches all nine files in that directory.

**STP: three encoders behind an AUTO chooser** — the richest of the four.
`ToSATAIG::bitblast` (`references/stp/lib/ToSat/ToSATAIG.cpp:263-345`) picks
among:

| Rung | Backend | Path |
|---|---|---|
| `NEW_VERY_LOW` / `NEW_LOW` / `NEW_MEDIUM` / `NEW_HIGH` | in-house AIG + `aig::deriveTseitin` | `ToCNFTseitin.cpp:38-60`, `lib/AIG/Tseitin.cpp` |
| `GIA_*` | ABC Gia + `Mf_ManGenerateCnf` (LUT/technology mapping) | `ToCNFGia.cpp:57-93` |
| default | ABC Aig + `Cnf_Derive`/`Cnf_DeriveWithMan` | `ToCNFAIG.cpp:136-176` |

The four in-house rungs differ only in what the writer *recovers* before
emitting — `enum class Recover` at
`references/stp/include/stp/AIG/Tseitin.h:100-107`, whose own comments read:
`Nothing` = "plain Tseitin: three clauses for every AND node"; `Patterns` =
"+ XOR, if-then-else and full adders" (`matchIte` at `lib/AIG/Tseitin.cpp:37`,
`xorShape` at `:87`); `PatternsAndAnds` = "+ maximal n-ary ANDs, and so n-ary
ORs, collapsed"; `Cells` = "+ every private cone of up to five leaves as the
prime implicates of the function it computes" — i.e. in-house cut-based
technology mapping. Selection at `ToCNFTseitin.cpp:49-60`. AUTO resolves from
`bm->expected_blast_ands` against `cnf_auto_threshold` under CaDiCaL
(`ToSATAIG.cpp:315-330`), and separately forces `GIA_LOW` when BV term
abstraction is on (`:283-292`). The comments record head-to-head numbers against
Bitwuzla on 311 KLEE binary128 queries (`:271-276`). STP's in-house Tseitin is
**not** polarity-aware — grep for `polarity|Plaisted|Greenbaum|one-sided` over
`lib/AIG/Tseitin.cpp` and `include/stp/AIG/Tseitin.h` finds only four incidental
uses of the word "polarity" in comments, none an encoding mode.

**Boolector: Tseitin with XOR and ITE extraction, and n-ary AND compiled out.**
`btor_aig_to_sat_tseitin` (`src/btoraig.c:1111-1319`) emits, for a general AND
with output `x` and leaves `y₁…yₙ`, one clause `(¬y₁ ∨ … ∨ ¬yₙ ∨ x)` plus n
binary clauses `(¬x ∨ yᵢ)` — both polarities, so full Tseitin. Grep for
`polarity|plaisted|greenbaum` over `src/` is empty; positive control, `tseitin`
matches `btoraig.c:1111, 1323, 1326, 1332`. Two pattern extractions are on:
`is_xor_aig` (`:916-962`) and `is_ite_aig` (`:964-1035`), each emitting the
4-clause / 12-literal encoding (`:1214-1269`), gated by `#define
BTOR_AIG_TO_CNF_EXTRACT_XOR` and `..._EXTRACT_ITE`, both enabled (`:56, 58`).

The interesting part is what is written and **switched off**. The n-ary AND
collection Bitwuzla lists as a TODO *exists here*, at `btoraig.c:1249-1266`,
walking down the AND tree collecting leaves and stopping at inverted nodes, vars,
nodes with `refs > 1`, or already-encoded nodes — and it is commented out:
`// #define BTOR_AIG_TO_CNF_NARY_AND` (`:60`). So is top-level AND flattening
(`BTOR_AIG_TO_CNF_TOP_ELIM`, `:50`) and the multi-OR top-level extraction
(`BTOR_EXTRACT_TOP_LEVEL_MULTI_OR`, `:48`). The shipped default is binary ANDs
plus a single unit clause for the root (`:1447-1458`). Boolector also **recycles
CNF variable ids** once every reference has been consumed
(`release_cnf_id_aig_mgr`, `:102`, called at `:1310-1317`), which none of the
other three does.

Word level to AIG vectors is a separate layer, `src/btoraigvec.c` (925 lines):
ripple-carry adder (`half_adder :222`, `full_adder :237`, `add :266`), barrel
shifters (`translate_shift :332`, `aigvec_sll :452`, `aigvec_srl :521`),
shift-and-add array multiplier (`mul_aigvec :555`), and one shared restoring
divider computing quotient and remainder together (`udiv_urem_aigvec :645`) —
structurally the same choices as ours, including the shared divider.
`btor_synthesize_exp` (`src/btorcore.c:2473`) is the explicit-stack DFS that
assigns AIG vectors, with an opt-in lazy mode (`BTOR_OPT_FUN_LAZY_SYNTHESIZE`,
default **0** = eager, `btoropt.c:629-637`) that stops at function-equality and
apply nodes.

**Ours: one encoder, polarity-aware, with gate fusion.**
`tseitin_encode` (`crates/axeyum-cnf/src/lib.rs:2786`) runs
`plan_sparse_encoding` (`:3500-3508`), which is five planning passes:
`plan_root_polarities` (`:3510`, one-sided encoding for nodes used at a single
root polarity), `plan_xor_and_not_ite_gates` (`:3539`, `detect_xor_gate` /
`detect_not_ite_gate` at `:4416`), `plan_not_and_gates` (`:3570`),
`plan_and_tree_gates` (`:3596`, `collect_private_and_tree` — **multi-input AND
collection**), and `plan_direct_root_nodes` (`:3627`). The incremental encoder
`IncrementalCnf` does lazy Plaisted–Greenbaum: an AND node's two implication
halves are emitted only in the polarity actually used, with the other added later
if an opposite-polarity use appears (`lib.rs:1165-1189`).

The honest reading: **on the AIG-to-CNF step alone we are ahead of Bitwuzla and
Boolector** — we ship, on by default, both of the optimizations Bitwuzla lists as
TODOs and Boolector compiled out, plus a polarity analysis neither has — and
**behind STP**, which has no polarity analysis but does have technology mapping,
ABC, four recovery rungs and a size-driven AUTO chooser measured against Bitwuzla
on a real corpus.

#### E.4 Word-level propagation before blasting

**Bitwuzla: none, and the direction is the reverse of what you would expect.**
`BitVectorDomain` (`src/lib/bv/domain/bitvector_domain.h:26`) is a 3-valued
lo/hi domain, but grep for `BitVectorDomain|bitvector_domain` over
`src/preprocess/`, `src/rewrite/` and `src/solver/bv/bv_bitblast_solver.cpp`
returns nothing (positive control: `BitVector` over `src/preprocess/` hits five
files). Its only consumers are the local-search engine and `bv_prop_solver.cpp`,
and there the constant bits are **read out of the already-built AIG**:
`BvPropSolver::mk_node` calls `domain.fix_bit(...)` for every AIG bit that
`is_true()`/`is_false()` (`src/solver/bv/bv_prop_solver.cpp:221-267`). So
Bitwuzla's const-bit information is a byproduct of AIG-level constant folding
consumed by local search, not a word-level pre-pass feeding the blaster.

**Boolector: absent, and this is a real difference from Bitwuzla.** There is no
`btorbvprop.c` in this tree; a search over `src/` for
`bvprop|const_bits|propagate_bits` finds only unrelated hits (a doc comment in
`boolector.h:868`, IBV-frontend text in `btoribv.cc:2971-2986`), with
`btor_bv_new` in `src/btorbv.c:99,129,133` as the positive control.
`src/btorbv.c` (3,156 lines) is a *concrete* bit-vector library for models and
evaluation, not an abstract domain. Bitwuzla's `BitVectorDomain` was added after
Boolector.

**STP: yes, and it is the distinguishing feature** — `constantBitP/`, described
under axis B. It is both a simplifier and a decider, and its fixed-bit map is
handed to `ToSATAIG` so the bit-blaster can exploit it (`STP.cpp:1168-1178`).

**Ours: none of this shape.** We have `propagate_values` (pin `x = c`) and
`solve_eqs_bounded` at the term level, and constant folding inside `Aig::and`,
but no bitwise abstract domain and no fixpoint over one at the word level.
`crates/axeyum-bv/src/lib.rs` has demand- and range-sliced lowering modes
(`lower_terms_demanded_with_deadline`, `lower_terms_range_demanded_with_deadline`,
`lib.rs:130`, `:253`), which decide *which bits to build*, not *what values they
can take*; both are config-gated and the default is `Eager`
(`docs/solver-inventory-2026-09/01-sat-core-and-cnf.md`).

### F — Theory solvers

#### F.1 The main loop shape

**Bitwuzla is lazy lemmas-on-demand over an eagerly bit-blasted BV core, not
CDCL(T).** `SolverEngine::solve` (`src/solver/solver_engine.cpp:60-154`) is a
`do { … } while (!d_lemmas.empty() || d_new_terms_registered);` loop. Each round:
clear the value cache, `process_lemmas()`, `d_bv_solver.solve()` (break if not
SAT), then in order `d_fp_solver.check()`, `check_distinct_n()`, the abstraction
module, `d_array_solver.check()`, `d_fun_solver.check()`, `d_quant_solver.check()`
— each `continue`ing the outer loop as soon as it produced a lemma. A lemma is a
plain Boolean `Node` pushed through `SolverEngine::lemma`
(`:222-242`), rewritten, deduplicated in a backtrackable cache, and re-asserted
as a top-level assertion. There is no generic `Lemma` class; each producer has
its own kind enum.

**STP has the same shape** but with more owners: `CallSAT_ResultCheck` plus a
refinement driver (`references/stp/lib/STPManager/STP.cpp:1275-1337`) that drains
*every* owner with a pending lemma before re-solving, deliberately, because
"the round has to leave no certificate behind" (`:1258-1260`). Owners are array
read refinement, extensionality, the BV term/eq abstractions, and the UF loop.

**Boolector is the same shape and the loop is the clearest of the four to read.**
`sat_fun_solver` (`references/boolector/src/btorslvfun.c:2409-2586`): synthesize
new constraints to AIG and CNF (`:2510`), re-assume (`:2522`), SAT (`:2523`),
then two termination tests — `if (btor->ufs->count == 0 && btor->lambdas->count
== 0) break;` (`:2536`, pure BV needs no refinement) and `if (BTOR_EMPTY_STACK
(slv->cur_lemmas)) break;` (`:2538`, no new lemma means the candidate model is
real). Lemmas become either assumptions or new unsynthesized constraints
(`:2549-2552`). Lemma deduplication against `slv->lemmas` (`:1513-1523`) is what
guarantees the fixpoint. Eagerness is an option: `BTOR_OPT_FUN_EAGER_LEMMAS` with
values `none`/`conf`/`all`, default **`conf`** — keep generating lemmas eagerly
until the first conflict that depends on another conflict
(`btoropt.c:651-667`, `btoropt.h:118`, `find_conflict_app` at
`btorslvfun.c:1597`). We have no equivalent knob.

**Ours is three separate architectures depending on the route**: eager one-shot
(`SatBvBackend`), cold-restart CEGAR (`abv.rs`), and a genuine CDCL(T) with a
warm incremental solver (`cdclt.rs` + `IncrementalBvSolver`, used by
`ufbv_online.rs`, `dpll_t.rs`, the arithmetic routes). Which one runs is decided
by `auto.rs`'s dispatch tree
(`docs/solver-inventory-2026-09/03-dispatch-routing-and-backends.md`).

#### F.2 Arrays

**Bitwuzla — five lemma schemas, no eager path.**
`enum class LemmaId { CONGRUENCE, ACCESS_STORE, ACCESS_CONST_ARRAY,
CONST_ARRAY_DIFF, DISEQUALITY }` (`src/solver/array/array_solver.h:30-37`):

| Schema | Site | Shape |
|---|---|---|
| `CONGRUENCE` | `array_solver.cpp:814-832` | `path_conds(a₁) ∧ path_conds(a₂) ∧ i₁=i₂ ⇒ e₁=e₂` |
| `ACCESS_STORE` | `:686-702` | read-over-write: `path_conds ∧ i = store_idx ⇒ acc.element = store[2]` |
| `ACCESS_CONST_ARRAY` | `:704-728` | `path_conds ⇒ acc.element = ca[0]` |
| `CONST_ARRAY_DIFF` | `:730-808` | `conds ⇒ (DISTINCT_N(card, indices…) ∨ acc.element = ca[0])` |
| `DISEQUALITY` | `:1048-1072` | extensionality via a fresh witness `@diseq_wit_<id>`; `¬(a=b) ⇒ DISTINCT(a[k], b[k])` |

Triggering is a DFS worklist per access (`check_access`, `:205-341`) that
propagates **down** through `STORE` when index model values differ and through
array `ITE` on the model value of the condition, and **up** through a parent map
over `EQUAL`/`STORE`/`ITE` edges (`:293-330`). A congruence conflict is a hash
collision in `d_array_models[array]` keyed on the *model value* of the read index
(`array_solver.h:104-126`). The outer `check()` is a fixed point over three
cursors whose sizes are deliberately not cached because the vectors grow during
iteration (`:107-131`). `check()` always returns `true` (`:132`) — "done" is the
engine observing that no lemma was produced.

**STP — a staged hybrid, and the staging condition is the interesting part.**
Eager Ackermannization runs only when the read count is under `arrayReadLimit`
(10, or 50 with `--ackermannisation`) **and** an estimated structural expansion
cost is under `arrayReadLimit × 20` (`STP.cpp:713-745`). The comment records why
the count alone was not enough: "a read over a chain of WRITEs becomes one ITE
per link, so nine reads over a deep store chain expand into tens of thousands of
nodes and take 48x longer than leaving them to read refinement" (`:731-736`).
Otherwise `SATBased_ArrayReadRefinement`
(`lib/AbsRefineCounterExample/AbstractionRefinement.cpp:469-650`) adds axioms
from the candidate model. Array *equality* is separate and always lazy:
`lib/Extensionality/` (3,084 lines) implements Brummayer and Biere's JSAT 2009
lemmas-on-demand extensionality with witness reads and a consistency checker
(`ExtChecker.cpp`), and an active equality **forces** the refinement loop —
legacy read refinement is never entered (`STP.cpp:1269-1274`).

**Boolector — three schemas plus extensionality, and arrays *are* lambdas.**
Every lemma goes through one function, `add_lemma(btor, fun, app1, app2)`
(`btorslvfun.c:1418-1537`): function congruence (`:1458-1468`), read-over-write
when `fun` is an `update` node (`:1469-1474`), and beta-reduction conflict when
`fun` is a lambda — partially beta-reduce the body under `app1`'s arguments and
conclude `app1 = value` (`:1475-1497`). Extensionality is separate
(`add_extensionality_lemmas`, `:2008-2182`), with the disequality side set up
eagerly by `create_function_inequality` (`:453`). Candidate applies are found by
one of **three** strategies chosen by option — dual propagation
(`search_initial_applies_dual_prop`, `:825`), justification/don't-care reasoning
(`search_initial_applies_just`, `:994`), or the plain BV skeleton
(`search_initial_applies_bv_skeleton`, `:934`) — a configurability none of the
other three has. Function `rho` tables (argument-assignment → apply) are
**retained across rounds when no conflict was found** and dropped when one was
(`:2354-2378`), an incremental reuse we do not attempt.

**Ours — four layers, eager-first.****Ours — four layers, eager-first.** `eliminate_arrays`
(`crates/axeyum-rewrite/src/arrays.rs:261`) does read-over-write to a fixed point
and then full pairwise Ackermann congruence (`:1-16` doc), with array equality
handled by **bounded extensionality that enumerates the index domain**, capped at
`MAX_ARRAY_EQ_INDEX_BITS = 8` (`arrays.rs:31`) — above that the query is
`Unsupported`. That cap is exactly the case STP and Bitwuzla handle with a
witness lemma. Above the eager path sit `check_qf_abv_lazy` (select congruence)
and `check_qf_abv_lazy_row` → `abv/lazy_ext.rs` (ROW plus diff-skolem
extensionality), and below it a bank of nine narrow checked-refutation
recognizers (`array_axiom.rs` and seven `array_*.rs` files,
`docs/solver-inventory-2026-09/05-bitvector-arrays-fp-and-datatypes.md`).

What each side buys: eager elimination gives us a **checkable UNSAT certificate**
for the array reasoning (`abv/array_elim_certificate.rs`, `certify_array_elim_unsat`)
that neither Bitwuzla nor STP produces, and a single monolithic SAT call. Lazy
lemmas buy them the deep-store-chain and wide-index cases our `O(n²)` Ackermann
pairing and 8-bit index cap refuse outright, at the cost of having no artifact
at the end.

#### F.3 Uninterpreted functions

**Bitwuzla — one schema.** `FunSolver::add_function_congruence_lemma`
(`src/solver/fun/fun_solver.cpp:188-206`): `⋀ᵢ(a[i] = b[i]) ⇒ (a = b)`, detected
by hashing `APPLY` nodes on the *model values* of their arguments
(`:226-275`). Lambdas never reach it — `register_term` asserts
`term[0].kind() != Kind::LAMBDA` (`:165`) because beta reduction is the
preprocessing pass `elim_lambda` (`src/preprocess/pass/elim_lambda.cpp`).
Equalities over functions and over uninterpreted sorts are explicitly
**unsupported** (`fun_solver.cpp:173-180`).

**STP** has a whole 4,615-line UF subsystem added recently:
`UFPreLowering`, `UFLowering`, `UFContext`, `UFLemma`, `UFRefinement`, `UFChecker`,
`UFModel`, `UFDecl` (`references/stp/lib/UninterpretedFunctions/`). It is a
refinement loop with its own pending-lemma protocol integrated into the same
driver as arrays (`STP.cpp:1300-1305`), and the CNF rung chooser has a special
case for "refinement that is only the uninterpreted-function loop"
(`ToSATAIG.cpp:311-330`) with a cited regression it fixed on
QF_UFBV/20210312-Bouvier.

**Boolector** does not separate UF from arrays at all — see axis G. It does also
ship an *eager* Ackermann pass, `btor_add_ackermann_constraints`
(`src/preprocess/btorack.c:37-60`), which adds `args_i = args_j → uf(args_i) =
uf(args_j)` for all apply pairs of each UF; it is off unless `BTOR_OPT_ACKERMANN`
is set, so eager and lazy UF coexist as alternatives in the same solver, exactly
the choice we make in `aufbv.rs` versus `ufbv_online.rs`.

**Ours** is `eliminate_functions` (eager Ackermann, `axeyum-rewrite/src/functions.rs`)
composed in `aufbv.rs`, plus `ufbv_online.rs` — a real lazy Ackermann inside a
warm CDCL(T) with `euf_egraph::EufTheory` congruence closure
(`docs/solver-inventory-2026-09/05-…md`, `06-euf-and-quantifiers.md`). On UF we
are architecturally closest to them of any axis.

#### F.4 Wide-operator abstraction

**Bitwuzla, on by default.** `abstraction` = true, threshold
`abstraction-bv-size` = **33** bits (`src/option/option.cpp:364-376`), applied to
`BV_MUL`, `BV_UDIV`, `BV_UREM` by default and optionally `ITE` and `BV_ADD`
(`option.cpp:417-441`). The abstracted node becomes `Kind::AM_ABSTRACT`
(`abstraction_module.cpp:275`). The refinement (`check_term_abstraction`,
`:353-490`) tries, in order: the named lemma schemas — **97** `LemmaKind` entries,
`MUL1_POW2…MUL19`, `UDIV1_POW2, UDIV2…UDIV37`, `UREM1_POW2, UREM2…UREM15`,
`ADD_*`, each with its SMT-LIB formula in the header comment
(`abstraction_lemmas.h:24-136`); then **value instantiation**
`(x = val_x ∧ s = val_s) ⇒ t = val_expected`, budgeted at
`bv_size / abstraction-value-limit` with the limit defaulting to 8; then
incremental bit-blasting of the low `ctz(t ⊕ expected) + 32` bits; then a
square-multiplier special encoding; then full bit-blasting.

**STP, off by default** but with the same shape and a comparable catalogue:
`bv_term_abstraction = false`
(`references/stp/include/stp/STPManager/UserDefinedFlags.h:614`), with
sub-switches for mult (default true) and divmod (default true) once enabled
(`:619,:624`). The catalogue is `DivLemma` (33 entries), `RemLemma` (11) and
`MulLemma` (14) in `references/stp/include/stp/ToSat/BVLemmaCatalogue.h`, each
with a checkable predicate (`divLemmaHolds`, `lib/ToSat/BVLemmaCatalogue.cpp:208`).
`BVAbstractionRefiner.cpp` is 3,209 lines and charges each schema install its
clause and variable cost (`:56-96`) — a fact like `UDIV15` is noted as "three
barrel shifters spliced through BVExactEncoder — 229,374 clauses at 256 bits"
(`:44-50`).

**Boolector: nothing of this kind.** Wide multipliers are bit-blasted.

**Ours, off by default and with no catalogue.** `lazy_bv.rs` (ADR-0019) abstracts
`bvmul`, `bvudiv`, `bvurem`, `bvsdiv`, `bvsrem`, `bvsmod` by fresh variables and
refines by adding the **exact definition** `fresh == op(lhs, rhs)`
(`crates/axeyum-solver/src/lazy_bv.rs:9-27`) — i.e. our only refinement step is
their *last resort*. There is no width threshold, no partial lemma, and no value
instantiation. `config.lazy_bv` defaults `false`
(`crates/axeyum-solver/src/backend.rs:398`) and the dispatch hook is
`auto.rs:539-542`.

#### F.5 Floating point

**Bitwuzla.** SymFPU is a meson subproject (`subprojects/symfpu.wrap`, pinned to
`40bdec00e99f8ea1b96c3dac0a05eed11c541639`), instantiated twice:
`SymFpuTraits` for concrete/constant folding and `SymFpuSymTraits` over Bitwuzla
`Node`s (`src/solver/fp/symfpu_wrapper.h:160`, `:414`). Word-blasting is
**lazy and lemma-driven**: `FpSolver::register_term` only enqueues
(`fp_solver.cpp:182-186`), and `check()` drains the queue and emits
`node = wordblasted_bv` as a lemma per term (`:118-141`). Rounding mode is a
first-class type with its own node kind `FP_SYMFPU_RM`, treated as a BV leaf by
the BV solver (`bv_solver.cpp:49`). Concrete FP *values* are MPFR-backed, not
SymFPU-backed (`src/solver/fp/floating_point.cpp:40-104`).

**STP.** Also SymFPU (`lib/FloatBlaster/symbolic_fp.h`,
`FloatBlaster.cpp:97-104` calls `symbolic_fp::unpacked::encode(decode(...))`),
but lowering is a dedicated pass placed **after** the size-reducing passes and
before the first bit-blast (`STP.cpp:822-836`), for a stated reason: doing it
inside simplification "meant building floating-point nodes over bitvector
children and stamping a float format on them to make them type check, and that
stamp landed on hash-consed nodes the input still used as plain bitvectors"
(`:826-835`). Seven predicates survive lowering and are encoded **natively by the
bit-blaster** over the packed bits — `BBcompareFP`, `BBeqFP`, `BBclassifyFP`
(`:812-818`). There is also an FP-specific domain simplifier
(`lib/FloatBlaster/FpDomainSimplify.cpp`) and a totalization pass
(`FpTotalise.cpp`).

**Boolector: no floating point.** Its logics stop at `QF_AUFBV`
(`src/btorlogic.h:15-18`).

**Ours.** `crates/axeyum-fp` is 8,257 lines of IEEE-754 formula builders and
there is **no FP theory solver anywhere**. FP is eliminated to BV in
`crates/axeyum-smtlib/src/parse.rs` at **parse time**, 37 call sites
(`docs/solver-inventory-2026-09/05-…md`). Three things SymFPU-based solving does
that parse-time elimination cannot:

1. **Skip the circuit when the model does not need it.** Bitwuzla word-blasts a
   term only after the BV solver has produced a model in which that term is
   reachable; ours is built before the solver exists.
2. **Keep the FP structure available to later passes.** Bitwuzla's FP nodes
   survive preprocessing and reach `FpSolver`; STP explicitly orders FP lowering
   after `RemoveUnconstrained` so that pass "must see a float symbol rather than
   its exposed bits" (`STP.cpp:824-826`). Our rewriter never sees an FP term at
   all.
3. **Give the replay an independent semantics.** ADR-0028 records our
   consequence: because FP has no first-class IR op, the ground evaluator replays
   *the same lowered circuit the solver decided over* — "the solver and the
   replay check share the bug", and the 2026-06-14 `fma` sign-extension defect
   was caught only by the differential oracle, not by replay
   (`docs/solver-inventory-2026-09/05-…md`). SymFPU is a separately audited,
   externally shared library used by Bitwuzla, STP and cvc5; our 8,257 lines are
   validated against native `f32`/`f64` and `rustc_apfloat`, not shared.

#### F.6 Local search as an alternate BV engine

This is the largest single subsystem we do not have, so it gets its own row.

**Bitwuzla.** `src/lib/ls/`, **10,227 lines**, plus `src/solver/bv/bv_prop_solver.{h,cpp}`
(579). `LocalSearch<VALUE>` (`src/lib/ls/ls.h:105-484`) is instantiated only for
`BitVector` (`ls.cpp:774`). Twenty-one active node kinds (`ls.h:37-85`) — note
`BV_OR`, `BV_SUB`, `BV_NEG`, `BV_SDIV`, `BV_SREM`, `BV_ZEXT` and the non-strict
comparisons are commented out, i.e. normalized away before local search sees
them. Each operator class implements four functions:

| Operator | `is_invertible` | `is_consistent` | `inverse_value` | `consistent_value` |
|---|---|---|---|---|
| Add | 575 | 607 | 645 | 661 |
| And | 715 | 811 | 847 | 863 |
| Concat | 902 | 956 | 999 | 1016 |
| Eq | 1057 | 1138 | 1174 | 1190 |
| Mul | 1243 | 1436 | 1587 | 1604 |
| Shl | 1645 | 1848 | 1995 | 2012 |
| Shr | 2053 | 2163 | 2310 | 2466 |
| Ashr | 2507 | 2585 | 2770 | 2787 |
| Udiv | 2828 | 3092 | 3348 | 3365 |
| Ult | 3527 | 3728 | 3845 | 4055 |
| Slt | 4149 | 4588 | 4718 | 4735 |
| Urem | 4776 | 5102 | 5284 | 5301 |
| Xor | 5365 | 5396 | 5431 | 5448 |
| Ite | 5501 | 5615 | 5664 | 5684 |
| Not | 5801 | 5827 | 5834 | 5848 |
| Extract | 5905 | 6089 | 6096 | 6110 |
| SignExtend | 6259 | 6297 | 6304 | 6318 |

(all in `references/bitwuzla/src/lib/ls/bv/bitvector_node.cpp`, 6,336 lines).

Essential-input selection is one line: `is_essential(t, pos_x)` is
`!is_invertible(t, 1 - pos_x, true)` — an input is essential iff the *other* one
is not invertible (`src/lib/ls/node/node.cpp:107-112`). `select_path`
(`:154-199`) takes the unique non-value input if there is one, else with
probability `prob_pick_ess_input` picks uniformly among essential inputs, else a
random non-const input. The move loop (`ls.cpp:682-772`) checks the `nprops` and
`nupdates` budgets first, picks a **random unsat root**, and calls `select_move`
(`:341-490`), which walks down choosing an inverse value with probability
`prob_pick_inv_value` (default **990/1000**, `option.cpp:320-328`), else a
consistent value, else declares a conflict and retries from another root.

**There is no cooling schedule and no restart schedule** — grep for
`restart|cooling|temperature|anneal|score` over `src/lib/ls/` returns zero hits
(positive control: `move` matches 13 times in `ls.cpp`). Escape from local minima
is entirely "pick a different random unsat root" plus the two probabilities.

Wiring: `Option::BV_SOLVER` with modes `bitblast` / `prop` / `preprop`, **default
`bitblast`** (`option.cpp:238-245`). `preprop` is a *sequential portfolio*: run
local search first, and on `UNKNOWN` switch to bit-blasting and re-solve
(`src/solver/bv/bv_solver.cpp:139-152`), auto-setting `prop-nprops = 10000` and
`prop-nupdates = 2000000` if the user did not (`option.cpp:981-991`). Local
search can return UNSAT **only trivially** — when a randomly picked unsat root is
itself a constant false (`ls.cpp:732-737`); the source says so
(`bv_prop_solver.cpp:214-215`).

**Boolector** has *two* local-search engines plus an AIG-level one:
`btorslvsls.c` (1,767 lines, score-based SLS with bandit candidate selection and
six move kinds, `:426-731`); `btorslvprop.c` (563) over `btorproputils.c`
(**3,633**), which is the direct ancestor of Bitwuzla's — 12 `cons_*_bv`
consistent-value functions (`:886-1515`), 12 `inv_*_bv` inverse-value functions
(`:1698-3345`), and 14 `select_path_*` functions (`:21-760`); and
`btorslvaigprop.c` over `aigprop.c` (1,144), which propagates on the AIG rather
than the word level. Default engine is `fun`
(`btoropt.h:82`, `btoropt.c:265-287`), but sls and prop are also reachable as a
*pre-step* inside the fun engine via `BTOR_OPT_FUN_PREPROP` / `FUN_PRESLS`
(`btorslvfun.c:2438-2479`) — the same sequential-portfolio idea Bitwuzla's
`preprop` later made a first-class mode.

**STP: none of its own.** A case-insensitive grep for `local search|walksat|sls`
over `references/stp/lib` and `include` returns three hits, all about the *SAT
backend's* internal local search — a CryptoMiniSat tuning comment
(`lib/Sat/CryptoMinisat5.cpp:210`), a `SATSolver.h` comment about what a
refinement loop wants (`include/stp/Sat/SATSolver.h:189`), and a CaDiCaL phase
note (`include/stp/STPManager/UserDefinedFlags.h:1192`). Positive control:
`refinement` matches many files in the same tree.

**Ours.** `crates/axeyum-solver/src/pbls.rs`, 1,456 lines: WalkSAT-family SLS
over the typed IR, scoring an assignment by how many top-level assertions the
**ground evaluator** falsifies, greedy flips with `NOISE_PCT = 30` random walk
and restarts, fixed seed (`pbls.rs:1-26`). Scope is Bool, `Int`, and
`BitVec(w ≤ 128)`. It is one-sided by construction — `Sat` only, and only with an
evaluator-verified model; it never returns `Unsat`. Reachable from
`preprocess.rs:145` (opt-in via `local_search_timeout`) and as a public
free function; it is not a `Solver` method and not on the default path
(`docs/solver-inventory-2026-09/05-bitvector-arrays-fp-and-datatypes.md`).

The gap is not "we lack local search", it is **we lack invertibility
reasoning**. Ours nudges a variable and re-evaluates; theirs computes, per
operator and per target value, whether an inverse exists and what it is, and
walks the value *down* the term to a leaf. That is what makes propagation-based
local search competitive on hard satisfiable QF_BV, and it is roughly 6,000 lines
of operator-specific mathematics we would have to write.

### G — Theory combination

Nothing in this family does Nelson-Oppen. Bitwuzla's combination is the lemma
loop: every theory solver reads the *same* BV model and adds Boolean lemmas over
shared terms, so agreement is enforced by re-solving rather than by exchanging
interface equalities (`solver_engine.cpp:98-132`). Non-BV equalities take their
value from the BV abstraction (`solver_engine.cpp:731-745`). STP is the same, with
the refinement driver draining all owners before each re-solve
(`STP.cpp:1275-1310`).

**Boolector's answer is the sharpest of the three, and it is a design decision
rather than an absence: arrays and UF are the same object.** `btor_exp_array`
sets `is_array = 1` on a **UF node** (`src/btorexp.c:98-110`) and
`btor_exp_write` builds a lambda marked `is_array` (`:1707-1714`); `select` and
`store` are `apply` over a lambda or an `update`. The node kinds are
`APPLY`, `LAMBDA`, `UPDATE`, `UF`, `FUN_EQ` — where `FUN_EQ` is documented as
"equality on arrays" (`src/btornode.h:57-64`). So one `propagate()` handles
both theories by dispatching on the node kind
(`btorslvfun.c:1469-1497`), the loop's termination test is the single condition
`ufs->count == 0 && lambdas->count == 0` (`:2536`), and extensionality fires on
`feqs->count > 0` for array and function equalities alike. There is no
combination framework because there are not two theories to combine.

Ours has an actual `theory_combination` module — and four of its functions have
**zero callers** (`docs/solver-inventory-2026-09/00-README.md` §5, with
`classify_interface_equalities` at 23 callers as the positive control). Where we
do combine (UF+BV, UF+LRA) it is one online CDCL(T) with both theories on the same
propagation queue, not a combination framework. On this axis the comparison would
mislead; see **Not comparable**.

### H — Quantifiers

**Bitwuzla: MBQI with a nested sub-solver.** `QuantSolver::check`
(`src/solver/quant/quant_solver.cpp:66-103`) partitions registered quantifiers by
model value — `true` ⇒ candidate for instantiation, `false` ⇒ Skolemization lemma
— then `mbqi_check` pushes a nested `SolvingContext` per active `forall`, asserts
the instantiation, and solves (`:434-439`). A `SAT` sub-result is a
counterexample whose model values drive instantiation; `UNSAT` retires the
quantifier. `LemmaKind` is `{MBQI_INST, MBQI_INST_INV, SKOLEMIZATION}` (`quant_solver.h:32-37`).
There is an invertibility-condition fallback via `BvInverter` (2,402 lines,
`src/solver/bv/bv_inverter.cpp`). Term selection is made deterministic with a
selection counter and an id tie-break (`quant_solver.cpp:487-494`). This is the
only solver whose `check()` can return `false`, which the engine turns into
`UNKNOWN` (`solver_engine.cpp:134-138`).

**STP: none.** It is a quantifier-free solver. Grep for `forall|exists` over
`references/stp/lib/Parser/smt2.y` returns only four incidental uses of the word
"exists" in comments; there is no `FORALL` node kind.

**Boolector: CEGQI plus syntax-guided model synthesis, optionally in two
threads.** `find_model` (`src/btorslvquant.c:2235-2340`) keeps **two** ground
solver instances (`BtorGroundSolvers { exists, forall }`, `:71-108`): solve the
exists side for a candidate (`:2255`; UNSAT there means the whole formula is
UNSAT), synthesize a *symbolic* Skolem function from the point model
(`flat_model_generate` `:2270` → `synthesize_model` `:2273`), instantiate
(`:2289`), then assume the negation and solve the forall side (`:2304-2306`);
UNSAT there means SAT. Otherwise the counterexample refines the exists solver
(`refine_exists_solver`, `:2326`). The synthesis engine is a separate 1,377-line
file, `src/btorsynth.c`, with `BTOR_OPT_QUANT_SYNTH` defaulting to
`BTOR_QUANT_SYNTH_ELMR` (`btoropt.h:114`). With `BTOR_OPT_QUANT_DUAL_SOLVER` the
original and dual formulas run in **two pthreads** racing to a result
(`:2382-2410`). Quantifiers with functions are refused
(`src/btorcore.c:3011-3019`).

**Ours** has roughly 45 quantifier files and an eleven-rung ladder
(`docs/solver-inventory-2026-09/06-euf-and-quantifiers.md`), which is a
different and larger surface than Bitwuzla's single MBQI loop. The gap runs the
other way here.

### I — Model production

**Bitwuzla.** `SolverEngine::value` → `_value` (`src/solver/solver_engine.cpp:601-880`),
a bottom-up DFS with a `d_value_cache` cleared at the top of every lemma-loop
iteration (`:79`). Leaves route by type: bool/BV to the BV solver (reading CNF
values), RM/FP to the FP solver (which re-word-blasts and reads the BV value),
functions to a nested-ITE lambda built from `d_fun_models`
(`src/solver/fun/fun_solver.cpp:115-150`), arrays to
`ArraySolver::construct_model_value`. Array models get a **default value chosen
by frequency**: `canonicalize_array_value` re-picks the default as the most
frequent element when stores cover at least half of a finite index domain
(`array_solver.h:224-238`). A `VARIABLE` or unregistered `FORALL` throws
`ComputeValueException`, which `ensure_model` handles by registering the missing
quantifiers and solving again (`solver_engine.cpp:287-323`).

**Self-validation: yes, and off in release.** `CheckModel::check`
(`src/check/check_model.cpp:26-66`) builds a **fresh nested `SolvingContext`**,
asserts every *original* (pre-preprocessing) assertion, then asserts
`input = get_value(input)` for each constant, and requires the result not to be
`UNSAT` — "unknown allowed for now" (`:65`). The option defaults to
`config::is_debug_build` (`src/option/option.cpp:597-601`).

**Boolector.** `bv_model` (node id → `BtorBitVector`) and `fun_model` (node id →
hash table from argument tuple to value) — `src/btormodel.c`. The array default
is decided at **print** time, not in the table: `print_fun_model_smt2`
(`src/btorprintmodel.c:215-336`) emits a nested-ITE lambda over the entries and
falls back to the constant array's initial value if there is one (`:307-308`),
otherwise zero (`:317-322`). The "top-most entry wins" rule that makes store
chains collapse correctly is documented at `btormodel.c:164-167`. Self-check
exists — `src/btorchkmodel.c` (317 lines) clones the solver, rebuilds the
formula, asserts the model, and re-solves — but the include and every call site
are inside `#ifndef NDEBUG` (`btorcore.c:14-16`, `:2932-2936`, `:3067-3074`), so
**in a release build it is not compiled at all**. It is additionally skipped when
UCOPT ran (`:3069`) and when quantifiers are present (`:2907-2908`).

**STP.** `AbsRefine_CounterExample` builds the counterexample from the SAT
assignment (`lib/AbsRefineCounterExample/CounterExample.cpp`).
`CheckCounterExample` (`:1693-1740`) re-evaluates the exact semantic root through
`ComputeFormulaUsingModel` and calls `FatalError` if it is false. It does one
thing the others do not: it **drops the formula memo first**, because those
entries "were produced while the model was still being assembled … and reusing
them would let this check confirm the answer with the very values it is supposed
to be re-deriving" (`:1714-1721`) — the same trap our contributor guide calls a
checker that cannot fail. It is gated on `check_counterexample_flag`, default
**false** (`include/stp/STPManager/UserDefinedFlags.h:1096`), called at
`CounterExample.cpp:3199-3202`.

**Ours.** The default QF_BV backend replays **unconditionally** on every `sat`:
`CnfEncoding::aig_node_values_from_assignment` re-checks the CNF assignment,
lifts it onto AIG nodes, recomputes the reachable ANDs from inputs,
`BitLowering::assignment_from_aig_values` recovers typed values, then
`replay_model` evaluates the **original** terms; a model that cannot be evaluated
becomes `Unknown` and one that evaluates false is a `SolverError`, never a
verdict (`docs/solver-inventory-2026-09/01-sat-core-and-cnf.md`, data-flow step
9). The honest qualification is that this is not centralized: about a dozen other
routes each replay in their own code, and the `full`-profile `check_model` is a
consumer-facing API, not a choke point
(`docs/solver-inventory-2026-09/08-models-proofs-and-evidence.md` §3).

**On this axis we are ahead of all three**, because their model checks are
debug-build or opt-in and ours is on the default path.

### J — Proof / certificate production

| | Proofs | Unsat cores |
|---|---|---|
| Bitwuzla | **none** | yes — assumption-based, `produce-unsat-cores` default false |
| Boolector | **none** | **none** — failed assumptions only |
| STP | **none** | assumption-granular core over incremental levels |
| Ours | DRAT by construction, LRAT elaboration, Alethe emission | deletion-based minimization |

**Bitwuzla.** `include/bitwuzla/cpp/bitwuzla.h` has `get_unsat_core` (`:1743`),
`get_interpolant` (`:1825`), `get_interpolants` (`:1873`) and `print_unsat_core`
(`:1895`) — and **no** `get_proof` / `print_proof`, and no proof option in
`src/option/option.cpp`. Positive control for the search path: `unsat_core`
matches `solving_context.{h,cpp}`, `main/options.{h,cpp}`, `main/main.cpp`,
`preprocess/preprocessor.{h,cpp}`, `preprocess/pass/embedded_constraints.cpp`,
`parser/smt2/parser.h`. The word "proof" occurs only in the service of
interpolants: `sat::interpolants::Tracer : public CaDiCaL::Tracer`
(`src/sat/interpolants/tracer.h:33`) consumes CaDiCaL's resolution proof to build
an AIG-level interpolant, with `size_proof` / `size_proof_core` statistics
(`:88-89`). That trace is never exposed as a certificate. Cores work by turning
**every non-lemma assertion into a SAT assumption** when `produce-unsat-cores` is
on (`src/solver/bv/bv_bitblast_solver.cpp:243-252`) and reading `failed()`
(`:316-330`); they are then de-abstracted (`solver_engine.cpp:179-195`) and
mapped back through the preprocessor (`solving_context.cpp:153-163`).

**Boolector.** A search over all 182 source files for
`\bproof\b|drat|drup|proof-log|tracecheck` returns exactly one hit, and it is the
handler-less parser token `INSERT ("get-proof", BTOR_GET_PROOF_TAG_SMT2)`
(`src/parser/btorsmt2.c:879`). `grep -rn "unsat_core\|unsat core" src/` returns
**zero**; positive control, `get-unsat-assumptions` matches `btorsmt2.c:881` and
`:4805`. What exists is failed assumptions: `boolector_failed`
(`src/boolector.c:527-548`), `btor_failed_exp` (`src/btorcore.c:1870-2005`),
which for a top-level AND decomposes into conjuncts and reports failure if any
conjunct's literal is in the SAT solver's failed set (`:1953-1998`). Since
formulas asserted at scope 0 are never assumptions, **they can never appear in
the "core"** (`boolector.c:481-491`).

**STP.** Grep for `drat|lrat|proof.trace|--proof` over `lib`, `include` and
`tools` returns **zero**; positive control, `proof` alone matches ten places, all
internal congruence-proof-tree and shortest-path language in `ExtChecker.cpp` and
`BVEQCongruenceClosure.cpp`. Cores are assumption-granular over incremental
levels: `lastUnsatAssumptionConjuncts` and `lastUnsatCoreLevels`
(`lib/Incremental/IncrementalSolver.cpp:85-131`), with the core **floored at the
promoted (unconditionally asserted) prefix** because a refutation may rest on it
without any assumption failing (`:114-124`).

**Ours.** The proof-carrying CDCL emits DRAT by construction and the default SMT
`unsat` route checks it **inline** before returning
(`sat_bv_backend.rs:2812`, `2874-2891`); a proof that fails to check downgrades
to `Unknown`, never to an accepted `unsat`. `elaborate_drat_to_lrat*` produces
LRAT for a hint-following checker, `lrat_to_alethe` produces Alethe, and there is
a bit-blast miter route (`bitblast_miter.rs`,
`certify_qf_bv_unsat_end_to_end_within`) reachable from the bench binary. The
honest qualification, from our own inventory: **eight unsat routes produce
`Evidence::Unsat(None)`** — NRA, the general `solve` fallback, the string front
door, difference logic above the certifying size, three QF_BV export declines,
LRA without a Farkas certificate, and CDCL(T) theory refutation
(`docs/solver-inventory-2026-09/00-README.md` §4). They are labeled
`"unsat-uncertified"` and never mislabeled.

Our unsat core is the weak side of this axis: `auto::unsat_core`
(`crates/axeyum-solver/src/auto.rs:801-830`) is deletion-based minimization that
calls the **full dispatcher** once per assertion, keeping a removal only if the
smaller set is definitively `unsat`. For an N-assertion query that is N+1
complete solves, where all three of them get a core out of the single solve they
already ran.

### K — Proof checking

**Bitwuzla, Boolector, STP: no in-tree proof checker**, because there are no
proofs. Bitwuzla does have three in-tree *result* checkers —
`src/check/check_model.cpp`, `check_unsat_core.cpp` (48 lines),
`check_interpolant.cpp` (245) — all defaulting to `is_debug_build`
(`option.cpp:597-611`). Boolector's equivalents are `btorchkmodel.c`,
`btorchkfailed.c` (132 lines) and `btorchkclone.c` (1,274, API-level clone
cross-checking), all `#ifndef NDEBUG`. STP has `--check-sanity`-style flags and
`ExtChecker`/`UFChecker` consistency checkers, but they check *its own
refinement invariants*, not a certificate.

**Ours.** `check_drat` (RUP+RAT), `check_drat_backward`, `check_lrat` and
`check_alethe` are all in-tree, and `check_alethe` natively handles three
axeyum-internal array rules Carcara does not know
(`docs/solver-inventory-2026-09/01-sat-core-and-cnf.md`,
`08-models-proofs-and-evidence.md`). The qualification our own inventory insists
on: the *external* checker cross-checks (`carcara_crosscheck.rs`,
`lean_crosscheck.rs`) **skip and pass** when the binary is absent, and
`references/` is gitignored (`00-README.md` §3).

### L — Interpolation

**Bitwuzla: yes**, and it is the only one. `produce-interpolants` (default
false, `src/option/option.cpp:186-190`), `interpolants-algo` with modes
`mcmillan` / `pudlak`, default **`mcmillan`** (`:442-447`), and
`interpolants-lift` (`:448`). It is built from CaDiCaL's resolution proof by
`sat::interpolants::Tracer`, with A/B/GLOBAL variable and A/B clause labels
(`src/sat/interpolants/tracer_kinds.h:18-29`); `lift` decides whether the result
is raised to the theory level or left as "exactly the bit-level AIG interpolant"
(`tracer.h:41-42`). CaDiCaL is required — the other three backends `throw
Unsupported` (`sat_solver_factory.cpp:40-63`), and any `pop` while interpolating
forces a **full SAT-solver reset** (`bv_bitblast_solver.cpp:333-338`) because the
tracer cannot label clauses containing activation literals (`:174-177`).

**Boolector: no.** `grep -rni interpol src/` returns zero across all 182 files;
positive control, `ackermann` finds `preprocess/btorack.c`.

**STP: no.** Same grep over `lib` and `include` returns nothing relevant.

**Ours: yes** — `propositional_interpolant{,_certified}` (McMillan from a
resolution refutation, `axeyum-cnf/src/interpolant.rs`) consumed by
`lra_interpolant_cnf.rs` and `bv_interpolant.rs`, with `just
interpolant-certificate` as the one gate in the repository whose exit status
depends on an external checker's finding (`AXEYUM_REQUIRE_DRAT_TRIM=1`). Our
inventory also records that all seven `*_certified` interpolant variants have no
production caller (`11-wiring-and-integration.md`). So both sides have McMillan
interpolation from a propositional refutation; theirs is wired to a public API
and ours is wired to two internal callers and a `justfile` target.

### M — Optimization

**All three: none.** Boolector's is the cleanest negative —
`grep -rniE "maxsat|max-sat|\bomt\b|minimize|maximize" src/` returns zero across
182 files, with `ackermann` and `restart` as positive controls; the only
"optimize" in the tree is `btor_optimize_unconstrained`, a simplification pass.
Bitwuzla and STP have no objective API either.

**Ours: yes, and it is a genuine "we have, they do not".** `optimize.rs` (1,392
lines) implements OMT as iterated sound feasibility decisions — exponential then
binary search over the objective bound, each probe a full `check_auto` — with
lexicographic, box and Pareto multi-objective wrappers, exposed as **11 methods
on the public `Solver<B>`** (`solver.rs:353-533`). `maxsat.rs` reduces
`max_satisfiable` to `optimize::maximize_bv`. There is no native OMT theory and
no core-guided MaxSAT; soundness inherits entirely from the underlying decision
procedure (`docs/solver-inventory-2026-09/05-…md`).

### N — Incrementality

**Bitwuzla.** Three chained `BacktrackManager`s — one in `SolvingContext`, one in
`Preprocessor`, one in `SolverEngine` — linked by `PopCallback`
(`src/preprocess/preprocessor.h:106-115`, `src/solver/solver_engine.h:170-172`),
with backtrackable `object`, `unordered_map`, `unordered_set`, `vector`,
`vector_map` and an `AssertionStack` in `src/backtrack/`. What **survives** a
`check-sat`: the SAT solver instance and every clause in it, the AIG, the CNF
encoder's variable allocations (its `d_aig_encoded` uses a tri-state sign
encoding so a `pop` returns entries from "encoded" to "allocated but not
encoded", `aig_cnf.h:136-145`, `aig_cnf.cpp:124-144`), the rewriter cache, and
the local-search node graph. What is **scoped**: assumptions, the encode queue,
per-round lemma caches, and — the one hard reset — the whole SAT solver when
interpolation is on and anything is popped
(`bv_bitblast_solver.cpp:333-338`). Assertions above the current SAT level are
encoded under **activation literals** (`sync_sat_level`, `:404-412`). FP validity
constraints must be re-emitted after a pop for terms word-blasted in a popped
level (`fp_solver.cpp:63-115`).

**Boolector.** `push`/`pop` are **scoped assumptions, not SAT backtracking**.
`boolector_push` only records a marker into `assertions_trail`
(`src/boolector.c:414-429`); `boolector_assert` at level > 0 does **not** assert
— it pushes onto `btor->assertions` with the comment "all assertions at a context
level > 0 are internally handled as assumptions" (`:481-491`); `boolector_pop`
releases those entries and makes **no SAT-solver call and no CNF or AIG
invalidation** (`:433-457`). `btor_check_sat` then re-assumes every surviving
scoped assertion on every call (`src/btorcore.c:2892-2904`). What is dropped
between calls is only the model and the assumption set —
`btor_reset_incremental_usage` (`:1695-1703`). Clauses are never retracted:
`btor_process_unsynthesized_constraints` adds only constraints not already
synthesized (`:1129-1150`). Function `rho` tables are retained across rounds when
no conflict was found, "remember functions for incremental usage"
(`btorslvfun.c:2368-2373`). Several preprocessing passes are disabled under
`BTOR_OPT_INCREMENTAL` — slice elimination, UCOPT, the `BETA_REDUCE_ALL` upgrade
(`btorpreprocess.c:107, 147, 178`).

**STP.** `lib/Incremental/` is 3,982 lines across eight files —
`IncrementalSolver`, `IncrementalSolverImpl`, `IncrementalScopeState`,
`IncrementalPushedLevels`, `IncrementalExactStack`, `IncrementalCBP`,
`IncrementalDriverCbp`, `IncrementalDriverStages`, `IncrementalProfile`. It
carries real scope state, promoted (unconditionally asserted) levels, per-level
assumption literals, and assumption-granular unsat cores
(`IncrementalSolver.cpp:85-131`), plus an incremental constant-bit-propagation
driver — i.e. it re-runs the CBP analysis incrementally across scopes rather than
from scratch.

**Ours — precisely what is discarded.** The public `Solver` façade's `push` is
`self.scopes.push(self.assertions.len())` and `pop` is `truncate`
(`crates/axeyum-solver/src/solver.rs:126-141`); `check` calls
`self.backend.check(arena, &self.assertions, &self.config)` (`:162`), i.e. it
hands the **whole assertion list** to a fresh backend call. Nothing is preserved:
not the AIG, not the CNF, not the SAT solver's learned clauses, not the rewrite
cache. The SMT-LIB front door does not even reach that — `smtlib_single_query`
flattens the entire push/pop stack into one assertion list before solving
(`smtlib.rs:1761, 1790-1797, 2240`).

This is a **wiring** gap, not a missing component. `IncrementalBvSolver`
(`crates/axeyum-solver/src/incremental.rs:795-836`) is a real warm engine: it
holds an `IncrementalLowering` (persistent AIG), an `IncrementalCnf` (per-node
lazy Plaisted–Greenbaum over a warm SAT solver with native assumptions),
selector-guarded frames for push/pop, warm array-select and UF-application maps,
and a replay-checked sat cache. Its consumers are `symexec.rs`,
`ufbv_online.rs`, `axeyum-py`, and the bench binary — **not** `Solver` and not
`solve_smtlib`. So we have built roughly what Bitwuzla has and the front door
does not use it (`docs/solver-inventory-2026-09/11-wiring-and-integration.md`,
gap #4; ADR-0009's claim of "a real incremental engine" is stale for the façade).

### O — Parallelism

**Bitwuzla: none of its own.** The only `std::thread`/`pthread` in `src/` is the
CLI watchdog `src/main/time_limit.cpp`. `nthreads` defaults to 1
(`option.cpp:225-235`) and reaches only CryptoMiniSat and Gimsatul
(`sat_solver_factory.cpp:55, 65`) — its help text says CryptoMiniSat only, which
is a minor inaccuracy.

**Boolector: three narrow uses.** Two pthreads racing the original and dual
formula in the quantifier solver (`src/btorslvquant.c:2382-2410`, under
`BTOR_HAVE_PTHREADS`); CryptoMiniSat's internal threads via
`BTOR_OPT_SAT_ENGINE_N_THREADS` (default 1, `btoropt.c:1352-1361`); and
Lingeling's process-level `lglfork`/`lgljoin` via `BTOR_OPT_SAT_ENGINE_LGL_FORK`,
**default 1** (`btoropt.c:1332-1341`, `sat/btorlgl.c:109-139`). There is no
portfolio over engines beyond the sequential `FUN_PREPROP`/`FUN_PRESLS` pre-step.

**STP: none.** No `std::thread` or `pthread_create` in `lib/`;
`num_solver_threads` defaults to 1 and is passed to CryptoMiniSat only
(`include/stp/STPManager/UserDefinedFlags.h:1092`,
`lib/Sat/SATSolverFactory.cpp:112`).

**Ours.** `portfolio.rs` runs arms in declared order at `workers == 1` and
concurrently above that (`portfolio.rs:36-41, 296-299`); `DEFAULT_INT_LINEAR_PORTFOLIO_WORKERS = 1` (`auto.rs:2948`, env override `AXEYUM_PORTFOLIO_WORKERS`), so the
fused group is runtime-dead by default
(`docs/solver-inventory-2026-09/11-wiring-and-integration.md`, gap #8). We also
have cube-and-conquer machinery in `axeyum-cnf/src/cube.rs` (1,863 lines) that is
example- and test-only. So all four are effectively sequential in their default
configuration, and only Boolector ships a parallel *algorithm* (the quantifier
dual solver) rather than a parallel back end.

### P — Resource limits and determinism

**Bitwuzla.** `time-limit-per` (`-T`, ms per check) and `memory-limit` (`-M`, MB),
both default 0 = unlimited (`option.cpp:210-224`), enforced by a
`ResourceTerminator` that **wraps** rather than overwrites a user terminator
(`src/resource_terminator.h:24-42`). One global `seed`, default **27644437**
(`option.cpp:192-198`), used only by the local-search RNG. Two deliberate
determinism measures are worth copying: logging is written so that a run behaves
identically with and without it — the `checked_essential` reconstruction exists
to avoid calling `is_essential()` from the log path (`ls.cpp:400-406`) — and MBQI
term ordering has an explicit id tie-break (`quant_solver.cpp:487-494`).

**Boolector.** `BTOR_OPT_SEED`, default 0 (`btoropt.c:376-385`), consumed once at
solver construction (`btorcore.c:694`); a deterministic PRNG in
`utils/btorrng.c` is the sole randomness source for sls/prop/aigprop. No library
time limit — the CLI uses SIGALRM (`btormain.c:947-979`) and the library offers a
termination callback (`btor_set_term`, `btorcore.c:809-821`) polled in every
engine loop. Search budgets: `lod_limit` and `sat_limit` (passed to
`btor_check_sat`, **not exposed as options**, with a `// TODO (ma): make options`
at `btorcore.c:3025-3026`), `PROP_NPROPS`, `SLS_NFLIPS`, `QUANT_SYNTH_LIMIT`. All
hash tables are id-keyed rather than pointer-keyed
(`btor_node_hash_by_id`/`compare_by_id`), which removes ASLR dependence — the
same discipline as our "no hash-map iteration order in output" rule. The default
Lingeling configuration is **not** bit-for-bit deterministic because
`sat-engine-lgl-fork` defaults to 1 and the fork/join heuristic depends on the
child's timing; CaDiCaL, the default when built, has no such issue.

**STP.** `timeout_max_conflicts` and `timeout_max_time` (seconds), both default
`-1` (`include/stp/STPManager/UserDefinedFlags.h:1091-1093`), plus a
`soft_timeout_expired` flag checked between passes and between refinement rounds
(`lib/STPManager/STP.cpp:873, 977, 1196, 1221, 1327`) that returns `unknown` rather
than a verdict — the same discipline as our deadline checks between rewrite
passes.

**Ours.** Determinism is a public API promise (CLAUDE.md hard rules): stable
iteration order, explicit seeds, explicit resource limits, no hash-map iteration
order in output. Budgets are denominated in **conflicts**
(`DEFAULT_PROOF_SAT_CONFLICT_LIMIT = 2_000_000`, `proof_sat.rs:46`) plus wall
clock; `axeyum-ir/src/budget.rs` (1,506 lines) is a deterministic work-budget
primitive, and `axeyum-cnf/src/ticks.rs` models cache-aware deterministic work —
though our inventory found **no shipping budget denominated in ticks**
(`docs/solver-inventory-2026-09/01-sat-core-and-cnf.md`, gap #4). There is no
memory limit option comparable to Bitwuzla's `-M`; `MemoryBudget::from_config`
exists as an admission screen on encoding size, which is a different thing.

## Gaps against axeyum

### 1. They have, we do not

Sized in rough implementation effort, not in expected benefit. "Their side" cites
`references/`; "our status" cites `docs/solver-inventory-2026-09/` or `crates/`.

| # | Capability | Their implementation | Our status | Size |
|---|---|---|---|---|
| 1 | **Propagation-based local search for QF_BV** — per-operator invertibility conditions, inverse and consistent values, essential-input path selection | Bitwuzla `src/lib/ls/` 10,227 lines, 4 functions × 17 operator classes (`bv/bitvector_node.cpp`); Boolector `btorproputils.c` 3,633 lines, 12 `inv_*_bv` + 12 `cons_*_bv` + 14 `select_path_*` | `pbls.rs` 1,456 lines is WalkSAT over the ground evaluator; **no invertibility reasoning anywhere** (grep `invertib\|inverse_value` over `crates/*/src/` finds only modular inverses in `axeyum-arith`/`axeyum-cas`) | **Large** — ~6,000 lines of operator-specific mathematics, each needing an exhaustive small-width test |
| 2 | **A warm SAT solver across refinement rounds** | Bitwuzla keeps the SAT instance, AIG and CNF encoder across lemma rounds and across `check-sat` (`bv_bitblast_solver.cpp:154, 255, 349-350`); STP re-solves the same `NewSolver` (`STP.cpp:1275-1310`); Boolector never retracts a clause (`btorcore.c:1129-1150`) | Our lazy array CEGAR constructs `SatBvBackend::new()` and re-lowers every round (`auto.rs:5563`, `abv.rs:138`); `Solver::check` re-submits everything (`solver.rs:162`) | **Medium** — the engine exists (`IncrementalBvSolver`); this is routing `abv.rs` and `Solver` through it |
| 3 | **A rewrite-level hierarchy, and 5× the rules** | Bitwuzla 296 rules across levels 0-2 + internal 3 (`rewriter.h:372-829`); Boolector 127 rules across levels 0-3 (`btorrewrite.c`) | 59 rules, no level concept, one on/off boolean (`canonical.rs:847-861`, `backend.rs:188`) | **Large** but incremental — each rule is independent and testable against the ground evaluator |
| 4 | **Constant-bit / bitwise-domain propagation** | STP `lib/Simplifier/constantBitP/` 7,619 lines: `FixedBits` 3-valued domain, worklist fixpoint (`ConstantBitPropagation.cpp:414`), 26 macro-registered transfer functions + 6 hand-written (`:589-666`), used both to simplify **and to decide** (`STP.cpp:786-789`) and handed to the bit-blaster (`:1168-1178`) | Nothing of this shape; `propagate_values` pins `x = c` at term level only | **Medium-large** — the domain and worklist are small; the per-operator transfer functions (division alone is 1,839 lines in STP) are not |
| 5 | **A lemma catalogue for abstracted wide multiply/divide** | Bitwuzla **97** named schemas (`abstraction_lemmas.h:24-136`) plus value instantiation and incremental bit-blasting, **on by default** at ≥33 bits; STP `DivLemma` 33 / `RemLemma` 11 / `MulLemma` 14 with per-schema cost accounting (`BVLemmaCatalogue.h`, `BVAbstractionRefiner.cpp:56-96`) | `lazy_bv.rs` refines only with the **exact definition** — their last resort is our only step — and defaults off (`backend.rs:398`) | **Medium** — each schema is a formula plus a validity test; the framework already exists |
| 6 | **Technology-mapped AIG-to-CNF, and more than one encoder** | STP: three backends (in-house Tseitin with 4 recovery rungs, ABC `Cnf_Derive`, ABC Gia `Mf_ManGenerateCnf`) behind a size-driven AUTO chooser (`ToSATAIG.cpp:263-345`), measured against Bitwuzla on 311 KLEE queries (`:271-276`) | One encoder, no rung selection (`axeyum-cnf/src/lib.rs:2786`) | **Medium** — cut enumeration for a `Cells`-equivalent rung; the plumbing for a chooser is small |
| 7 | **Store-pattern recognition** | Boolector `btorextract.c` 1,568 lines recognizes `memset`, `itoi`, `itoip1`, `memcpy` shapes in store chains and rewrites them to lambdas with range conditions (`:167-457`) | None. Our eager elimination expands a deep store chain into one `ite` per link, and our nine `array_*.rs` recognizers match *proof-obligation* shapes, not store shapes | **Medium** — pattern detectors plus a range-condition representation the IR does not have |
| 8 | **A one-solve unsat core** | Failed SAT assumptions: Bitwuzla `bv_bitblast_solver.cpp:243-252, 316-330`; STP `IncrementalSolver.cpp:85-131`; Boolector `btor_failed_exp` (`btorcore.c:1870-2005`) | `auto::unsat_core` is deletion-based minimization — N+1 full dispatcher calls (`auto.rs:801-830`) | **Small-medium** — the incremental core already exposes failed assumptions (`proof_sat/incremental.rs`); it needs to be reachable from the front door |
| 9 | **Difficulty-based reversion of preprocessing** | STP scores the formula before and after and **reverts** if simplification did not take 20% off, keeping only the discovered constants (`STP.cpp:1024-1090`) | `reduction_shrinks_encoding` (`auto.rs:2233-2264`) does the analogous thing at the *encoding* level only, and only for the whole reduction | **Small** — a scorer plus a snapshot |
| 10 | **Configurable lemma eagerness and configurable candidate search** | Boolector `FUN_EAGER_LEMMAS` = none/conf/all, default `conf` (`btoropt.c:651-667`); three initial-apply strategies — dual propagation, justification, BV skeleton (`btorslvfun.c:825, 934, 994`) | One strategy, no knob | **Small** per option, but it presupposes gap #2 |
| 11 | **A SymFPU-class FP path with a theory solver** | Bitwuzla word-blasts lazily inside the lemma loop with two SymFPU traits instantiations (`fp_solver.cpp:118-141`, `symfpu_wrapper.h:160, 414`); STP lowers in a dedicated pass after size reduction and keeps 7 predicates native to the blaster (`STP.cpp:812-836`) | FP eliminated to BV at **parse time**, 37 call sites in `axeyum-smtlib/src/parse.rs`; no FP theory solver; replay shares the circuit with the solver (ADR-0028) | **Large** — this is an architectural change to where FP lives, not a feature |
| 12 | **Preprocessing as a fixpoint** | Bitwuzla `do…while(modified)` with an inner fixpoint for variable substitution (`preprocessor.cpp:265-397`); Boolector the same shape (`btorpreprocess.c:196-197`); STP two nested fixpoints (`STP.cpp:794-807, 869-936`) | Five steps, once (`auto.rs:2158-2199`). An 8-round pipeline exists and the front door does not use it | **Small** — the loop exists in `preprocess.rs`; this is gap #3 of our own inventory |
| 13 | **A memory limit** | Bitwuzla `-M` per check, enforced by a wrapping terminator (`option.cpp:218-224`, `resource_terminator.h:24-42`) | `MemoryBudget::from_config` is an admission screen on encoding size, not a running limit | **Small** |
| 14 | **AIG rewriting past two levels, iterated** | Bitwuzla four levels including substitution rules that re-enter the loop (`aig_manager.cpp:177-407`); Boolector the same plus a bounded deeper contradiction search, limit 8 (`btoraig.c:373-401`) | Level-1 rules, absorption and OR-consensus, **not iterated** (`axeyum-aig/src/lib.rs:345-408, 732-744`) | **Small** — a well-specified rule set with a published reference |

### 2. We have, they do not

This table is not padding — it is the reason the project exists — but it is
concentrated in one area, and one entry in it is a gap in the other direction
that happens to fall our way.

| # | Capability | Our implementation | Their status | Notes |
|---|---|---|---|---|
| 1 | **Machine-checkable UNSAT proofs** | DRAT emitted by construction from our own CDCL, checked inline before `unsat` is returned and downgraded to `Unknown` if the check fails (`sat_bv_backend.rs:2812, 2833`); LRAT elaboration; Alethe emission; in-tree `check_drat`, `check_drat_backward`, `check_lrat`, `check_alethe` | **None of the three produces any proof.** Bitwuzla: no `get_proof` in the public header, and the only proof consumption is CaDiCaL's trace feeding interpolants. Boolector: one handler-less `get-proof` token. STP: zero `drat`/`lrat` occurrences | The largest and least contestable difference. It is also *why* we wrote our own SAT core |
| 2 | **Unconditional model replay on the default path** | Every `sat` from the default QF_BV backend is re-evaluated against the **original** terms; a false model is a `SolverError`, not a verdict | Bitwuzla `dbg_check_model` defaults to `is_debug_build`; Boolector's checker is `#ifndef NDEBUG`; STP's `check_counterexample_flag` defaults false | Their checks are *better designed* than ours in one respect (Bitwuzla re-solves in a nested context; STP drops its formula memo first so the check cannot confirm itself). Ours is weaker per-check and stronger by being always on |
| 3 | **A proof-producing SAT core we own** | `axeyum-cnf/src/proof_sat.rs`, 8,333 lines | All three link an external SAT solver and none produces a proof through it | Owning the core is what makes #1 possible |
| 4 | **Optimization modulo theories** | `optimize.rs` 1,392 lines, 11 public `Solver<B>` methods, lexicographic/box/Pareto (`solver.rs:353-533`) | None of the three has any objective API | Ours is iterated feasibility, not a native OMT theory |
| 5 | **A polarity-aware CNF encoder with gate fusion on by default** | Plaisted–Greenbaum root-polarity planning, XOR/ITE detection, NOT-AND fusion, multi-input AND collection (`axeyum-cnf/src/lib.rs:3500-3627`) | Bitwuzla has plain Tseitin and lists AND-collection and native XOR as **TODOs** (`aig_cnf.cpp:296-297`); Boolector *wrote* AND-collection and **compiled it out** (`btoraig.c:60`) | Only against Bitwuzla and Boolector; STP's `Cells` rung goes further than ours |
| 6 | **Theories outside their scope** | Linear and nonlinear arithmetic (exact-rational simplex with Farkas certificates, CAD, Sturm chains), strings and regex, datatypes, an eleven-rung quantifier ladder, a CAS | Boolector and STP are BV+arrays+UF only; Bitwuzla adds FP and MBQI quantifiers and stops there | Not a gap *they* have — a different product scope. Listed for completeness, not as a win on their home ground |
| 7 | **Interpolation with an externally checked gate** | McMillan from a propositional refutation, plus `just interpolant-certificate` with `AXEYUM_REQUIRE_DRAT_TRIM=1` making the exit status depend on the finding | Bitwuzla has interpolation (McMillan/Pudlák, CaDiCaL-only) and a debug-gated `check_interpolant`; Boolector and STP have none | Bitwuzla's interpolation is arguably better wired than ours — theirs is a public API, ours has no production caller for the `*_certified` variants |

## Not comparable

Four places where a feature-by-feature line would produce a confident wrong
answer.

1. **"Eager vs lazy arrays" is not a single axis.** STP is *both*, and the switch
   is a cost estimate, not a mode: `numberOfReadsLessThan(inputToSat, 10)` **and**
   `arrayEagerCostLessThan(..., 200)` (`STP.cpp:726-745`). Our four array routes
   are also not ordered on one axis — the eager route produces a certificate the
   lazy ones cannot, and the lazy ones decide shapes the eager one refuses (wide
   index equalities above `MAX_ARRAY_EQ_INDEX_BITS = 8`). Comparing "who is
   lazy" would rank us against a distinction neither side actually makes.
2. **"Number of rewrite rules" across the four is not a common unit.** Bitwuzla's
   296 `RewriteRuleKind` entries include 82 constant-folding `*_EVAL` rules and 48
   operator-elimination `*_ELIM` rules, which in our stack are the ground
   evaluator and the bit-blaster's operator coverage respectively, not rewrite
   rules. Boolector's 127 are `applies_*`/`apply_*` pairs at a different
   granularity again. Our 59 are all `Preservation::Denotation` +
   `ModelProjection::Identity`, a stricter contract than any of theirs enforces.
   The counts are in the tables above because the ratio is informative; the
   difference is not 296 − 59.
3. **Their theory-combination axis has no content, and ours has content nobody
   calls.** They combine BV, arrays and UF by construction (Boolector literally
   makes arrays into lambdas) so there is nothing to compare against our
   `theory_combination` module — whose four functions have zero callers. Scoring
   this axis either way would be meaningless.
4. **"Local search" names two different algorithms.** Ours scores a full
   assignment by counting falsified assertions and nudges variables; theirs
   propagates a target value *down* a term using per-operator invertibility
   conditions. They share a name and a return contract (SAT or unknown, never
   UNSAT except trivially) and share almost nothing else. Treating `pbls.rs` as a
   smaller version of `src/lib/ls/` would understate the gap; treating it as
   nothing would understate what we have.

A fifth, softer one: **STP's age is misleading in both directions.** It has
machinery Bitwuzla does not (three CNF backends, constant-bit propagation as a
decider, an extensionality checker) and lacks machinery Bitwuzla has (local
search, quantifiers, abstraction on by default). "Older, therefore behind" is
wrong; so is treating its 2007 papers as a description of the current tree.

## Confidence

**Solid source reads**, each with the cited lines opened and, where a negative is
claimed, a positive control named in the text:

- Bitwuzla's rewrite-level definition, default, and the 296-rule count (two
  independent counting methods agreeing: the enum body and the printer switch).
- Bitwuzla's preprocessing pass list, order, fixpoint condition, and the
  `if (false && …)` dead `PassElimUdiv`.
- The AIG-to-CNF clause shapes for all four systems, and the two TODOs in
  Bitwuzla's encoder and the two `#define`s Boolector compiled out.
- The array lemma-kind enums for Bitwuzla, the three `add_lemma` schemas for
  Boolector, and STP's staged Ackermannization condition.
- The local-search function inventory (line numbers per operator were read
  individually) and the absence of any restart or cooling schedule.
- The absence of proof production in all three, and the absence of unsat cores
  in Boolector. Both were checked with a positive control on the same grep.
- The default values quoted from `option.cpp` / `btoropt.c` /
  `UserDefinedFlags.h`, each read at the cited constructor.
- Our own side: every `crates/…` line number was opened in this session; every
  `docs/solver-inventory-2026-09/…` claim is quoted from a file whose own method
  section states its limits.

**Inferences, flagged as such:**

- "Bitwuzla is the state of the art in this architecture" is a judgment, not a
  measurement. What is measured here is only that it is the largest and most
  recently developed of the three.
- The **size** column of the first gap table is my estimate from line counts and
  the shape of the code, not from any attempt to implement.
- STP's comments quote head-to-head numbers against Bitwuzla
  (`ToSATAIG.cpp:271-276`) and against its own earlier rungs. I have **not**
  re-run any of them; they are quoted as what the source claims, not as
  established fact.
- Whether Bitwuzla's `PassNormalize` amounts to a word-level interval reasoner
  was left `[undetermined]` by the read; the next file is
  `src/preprocess/pass/normalize.h:33-178`.
- Which interpolation system Bitwuzla's tracer actually implements beyond the
  `interpolants-algo` option string is `[undetermined]`; the next files are
  `src/sat/interpolants/cadical_tracer.cpp` and `src/solver/bv/bv_interpolator.cpp`.
- Boolector's exact `PROP_PROB_*` numeric defaults were not all read;
  `[undetermined]`, next file `src/btoropt.c:670-1330`.

**Not verified by execution, in any direction.** Nothing here was built or run —
that was the method constraint. Every "default" is a default in source, every
"unreachable" is a search result, and every performance statement is a quotation
of someone else's comment.
