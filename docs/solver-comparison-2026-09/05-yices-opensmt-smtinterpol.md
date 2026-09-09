# Yices2, OpenSMT, and SMTInterpol — arithmetic and interpolation (2026-09-09)

Scope: three reference solvers read from `references/`, no build. They are grouped
because they are the reference points for the two things we have built and cannot
currently evaluate: **exact linear arithmetic** and **interpolation**.

| | Yices2 | OpenSMT2 | SMTInterpol |
|---|---|---|---|
| Origin | SRI International | USI Lugano | University of Freiburg |
| Commit | `728b7eebd5d3b8303022775204cf46030f05244f` | `15b42c6f339679a4547d3cc9955547e7ca03505c` | `1f55c1b9bfc724468b18e0e1868e4606e0285fb9` |
| Clone HEAD date | 2026-09-08 | 2025-12-06 | 2026-06-12 |
| Language | C | C++ | Java |
| Size | 88 MB clone; `src/solvers/simplex/` alone is 15 files of solver + 6 of printing | 51,236 lines under `src/` (`*.cc`/`*.h`) | 109,461 lines of `*.java` across the whole clone |
| License | GPLv3 (`LICENSE.txt`) | MIT (`LICENSE:6-14`) | LGPLv3 (`COPYING.LESSER:1`) |

Read the language row before reading any performance statement. SMTInterpol is
Java; a wall-clock comparison against it measures the JVM as much as the
algorithm, and none of the numbers below are timings — everything here is a
source read.

## Summary

- **All three implement Dutertre–de Moura general simplex, and all three differ
  from ours at exactly the same place: the boundary.** None of them has a pivot
  cap and none of them declines on coefficient magnitude. Yices's loop is
  `for(;;)` with only an external interrupt flag (`simplex.c:4251-4256`);
  OpenSMT's is `while (true)` (`Simplex.cc:42`); SMTInterpol's is `while (true)`
  (`SOIPivoter.java:395`). Ours has `MAX_PIVOTS = 2_000_000`
  (`simplex.rs:81`) and `MAX_TABLEAU_CELLS = 4_000_000` (`simplex.rs:74`), both
  yielding `Unknown`.
- **The magnitude boundary is the sharpest single gap.** Yices's `rational_t` is
  a 64-bit tagged union with an `int32`/`uint31` fast path that promotes to GMP
  `mpq` on overflow (`terms/rationals.h:36-64`, `rationals.c:937-964`). OpenSMT's
  `FastRational` is the same idea with an explicit state byte and a pooled
  `mpq` allocator, promoting at a `goto overflow` label and demoting again via
  `try_fit_word` (`common/numbers/FastRational.h:31-46`, `:696-702`).
  SMTInterpol's `Rational` is `int mNum/int mDenom` with a `BigRational`
  subclass (`Library-SMTLIB/.../Rational.java:54-64`). **We promote internally
  and then narrow at the module boundary**, declining to `Unknown` if a feasible
  point or a Farkas multiplier does not fit `i128` (`simplex.rs:420` `narrow`,
  documented at `:407-418`). Three independent implementations chose "grow the
  number"; we chose "give up".
- **None of the three runs its own branch-and-bound tree.** Yices creates a
  *branch atom* `(x >= ceil(...))` and hands it to the CDCL core
  (`simplex.c:7170-7218`), then artificially bumps the core's conflict counter
  by 40 to pull the restart schedule forward (`simplex.c:9140-9141`). OpenSMT
  pushes `x <= floor(v) ∨ x >= floor(v)+1` onto `splitondemand` and returns
  `NEWSPLIT` (`LASolver.cc:309-319`). SMTInterpol does the same through
  `CutCreator`/branch literals. Ours runs `lia_branch_and_bound` inside the
  theory with `MAX_LIA_BNB_NODES = 50_000` (`lra.rs:1706`) and returns `Unknown`
  when it runs out. **The three reference solvers cannot return unknown on LIA;
  they can only run longer.** Yices's `simplex_final_check` returns exactly two
  values, `FCHECK_SAT` and `FCHECK_CONTINUE` (`simplex.c:10098-10122`), and
  `grep -rni "unknown" references/yices2/src/solvers/simplex/` returns **0** hits
  against a positive control of 105 for `unsat`.
- **Integer cuts: two of three use Hermite Normal Form "cuts from proofs"; we use
  Gomory fractional cuts.** OpenSMT: `HermiteNormalForm()(std::move(matrixA))`
  then read off a row whose product with the current point is non-integral
  (`CutCreator.cc:17-32`). SMTInterpol: the same algorithm with an explicit LIRA
  adaptation that never adds a real row into an integer row
  (`theory/linar/CutCreator.java:33-70`). Yices has a Rosser/Chou–Collins
  echelon Diophantine solver that also produces the **general solution**, used to
  tighten bounds to the lattice (`diophantine_systems.h:19-88`,
  `simplex.c:7656-7695`). Ours has `lia_gcd.rs` (fraction-free row reduction, a
  refuter only — it does not return a lattice basis) plus `lia_gomory_cuts`
  (`lra.rs:2710`).
- **Yices's Gomory cut path is not what a reader would assume.** The block is
  compiled (`#if 1`) but labelled `// NOT READY FOR PRIME TIME.`
  (`simplex.c:8496-8500`), the multi-cut round is `if (false && ...)` dead code
  (`simplex.c:9114`), and the live path emits **at most one cut per final check**,
  gated on ≥20 branch atoms and a branch score > 1e8 — a score reached
  essentially only by variables missing a bound. This is a case where the code is
  emphatically not the paper.
- **Interpolation is where the distance is largest, and it is not close.**
  OpenSMT ships **six propositional interpolation systems** — McMillan, Pudlák,
  McMillan′, PS, PSW, PSS (`options/SMTConfig.h:163-168`) — plus proof-graph
  restructuring for strength (`:939`), three EUF variants (strong/weak/random,
  `UFInterpolator.h:155-157`) and **five** LRA variants including a
  **continuously strength-parameterised** one (`getFlexibleInterpolant(Real)`,
  `FarkasInterpolator.h:69`, default factor `1/2`, `SMTConfig.h:177`).
  SMTInterpol computes **tree interpolants** natively from its proof
  (`Interpolator.java:88-108` `mStartOfSubtrees`). We have eight interpolators,
  one A/B partition, one algorithm each, and no strength control at all
  (`solver.rs:243`, `:305`).
- **Our EUF interpolator declines exactly where theirs do the work.**
  `euf_interpolant.rs:503` is `Color::Empty | Color::Mixed => return None`.
  OpenSMT handles a mixed-color congruence edge by splitting it
  (`UFInterpolator.h:146` `splitEdge`, `:147` `colorCongruenceEdge`);
  SMTInterpol purifies AB-mixed literals with auxiliary variables and an
  auxiliary `@EQ` predicate (`Interpolator.java:71` `EQ`, `:116`
  `mMixedTermAuxEq`, `InterpolantPurifier.java`). Handling mixed literals *is*
  the hard part of interpolation; we decline on it.
- **On interpolant *checking* we are ahead of OpenSMT and behind SMTInterpol.**
  OpenSMT's check is opt-in (`certify_inter() >= 1`,
  `InterpolationContext.h:67`), uses OpenSMT itself as the checker
  (`VerificationUtils.cc:14-31`), and — the important part — **does not gate the
  return value**: a failed check is `assert(sound)` plus a printed line, and the
  interpolant is returned anyway (`InterpolationContext.cc:857-871`). Ours
  verifies unconditionally and declines to `None`
  (`08-models-proofs-and-evidence.md`, §6). SMTInterpol goes further than both:
  it checks the **partial interpolant at every proof leaf** as it builds
  (`InterpolantChecker.checkInductivity`, called at `Interpolator.java:394`),
  plus the tree-interpolation property and a symbol-containment check at the end
  (`checkFinalInterpolants`, `InterpolantChecker.java:444`).
- **Yices2 produces no proofs at all.** `(get-proof)` exists only to print
  `"get-proof is not supported"` (`smt2_commands.c:5055-5060`), and
  `:produce-proofs` is documented in the struct as `// default = false (not
  supported)` (`smt2_commands.h:389`). A `drat|lrat` grep over `src/` returns 4
  hits, all the substring inside "qua**drat**ic", against a positive control of
  real `unsat_core` code in `smt_core.c:3748-3867`. It has unsat **cores** over
  assumptions, which is a different thing.
- **SMTInterpol's proof design is the closest thing in this comparison to what
  we are building, and it is more completely wired.** The `resolute` format is a
  small trusted core: three term formers (`res`, `assume`, `axiom`) plus ~70
  named axiom schemata spanning Boolean, quantifiers, equality, LA (`:farkas`,
  `:trichotomy`, `:total`, `:mulpos`, `:poly+`, `:poly*`), div/mod, arrays,
  datatypes and bitvectors (`proof/resolute/ProofRules.java:99-129`, `:80-125`).
  It is checked by a 605-line in-tree `MinimalProofChecker`, and
  `:proof-check-mode` **throws** on failure rather than warning
  (`SMTInterpol.java:571-580`). There is also a **standalone** checker binary
  with its own JFlex/CUP grammar that reads a script file and a proof file
  (`proof/checker/Main.java`, `proofs.cup`, `proofs.flex`).
- **SMTInterpol has five self-check modes, each of which turns a wrong answer
  into an error**: `:proof-check-mode`, `:model-check-mode`,
  `:interpolant-check-mode`, `:unsat-core-check-mode`,
  `:unsat-assumptions-check-mode` (`option/SMTInterpolConstants.java:43-48`).
  That is the discipline CLAUDE.md's evidence rule asks for, implemented as
  product options.
- **Yices's speed on QF_LRA/QF_LIA/QF_BV is explained by four choices a reader
  can act on**, detailed in [§ Why Yices is fast](#why-yices2-is-fast): the
  8-byte tagged rational, arena allocation with push/pop marks, watch links
  embedded in the clause header, and a *statically selected specialized
  architecture per logic* so QF_LRA never pays for egraph interface machinery.
- **Two of the three disable a reasoning capability when proofs or interpolation
  are on.** OpenSMT skips the substitution preprocessing pass entirely when the
  SAT solver logs a resolution proof (`MainSolver.cc:583`
  `assert(... and not getSMTSolver().logsResolutionProof())`) and disables
  cuts-from-proofs when interpolation is requested (`LASolver.cc:739`
  `if (this->config.produce_inter()) { return false; }`). This is the cost of
  proof production made explicit in the source, and it is a design point we
  should decide deliberately rather than discover.

## Schema

### A. Input front end

| Solver | Formats | Architecture | Rejected vs ignored |
|---|---|---|---|
| Yices2 | SMT-LIB 2, SMT-LIB 1.2, native Yices language, DIMACS. Six `main()`s: `frontend/yices.c:21`, `yices_smt2.c:1156`, `yices_smt.c:2093`, `yices_smtcomp.c:1369`, `yices_sat.c:565`, `yices_sat_new.c:1093` | **Table-driven pushdown**, deliberately not recursive descent — `parser_utils/parser.h:20-26` ("to avoid issues with stack overflow"). Action tables are generated data read through base/check/default compression (`smt2_parser.c:53-64`); the generator is in-tree (`utils/table_builder.c`). Lexers hand-written; keywords via gperf (`smt1/smt_lexer.c:26-29`) | **Hard error**: unsupported logics and constructs (`smt2_commands.c:1014-1058`), `get-assertions` (`:5027`), `get-proof` (`:5059`). **Silently degraded to "unsupported" and execution continues**: `:expand-definitions`, `:interactive-mode`, `:produce-assertions`, `:produce-proofs`, `:reproducible-resource-limit` (`:6480-6487` set, `:5624-5631` get) |
| OpenSMT | SMT-LIB 2 only | flex + bison (`parsers/smt2new/smt2newlexer.ll`, `smt2newparser.yy`, driven by `smt2newcontext.cc`) | `get-proof` without `:produce-proofs` prints "Option to produce proofs has not been set, skipping this command" and continues (`api/Interpret.cc:268-279`); `get-interpolants` without `:produce-interpolants` throws `ApiException("Cannot interpolate")` (`Interpret.cc:1327`) |
| SMTInterpol | SMT-LIB 2 (`smtlib2/smtlib.cup`, `smtlib.flex`), SMT-LIB 1.2 (`smtlib/`), DIMACS (`dimacs/`), AIGER (`aiger/`) | JFlex + CUP generated. `Library-SMTLIB/` is a separate term/logic library (the `Logics`, `Rational`, `Term`, `Script` API) reused by the checker and by external consumers | Logic names are parsed by a single **regex** over the name rather than by an enum of known logics (`Logics.java:80`; the pattern accepts an optional `QF_` prefix followed by optional `A`, `UF`, `BV`, `FP`, `DT`, `S` segments and an optional arithmetic or difference-logic suffix), and `ALL`/`HORN` set every feature bit unconditionally (`:77-79`). Whether the *solver* supports the resulting feature set is decided later, in `Clausifier.setLogic` (`convert/Clausifier.java:1637-1660`) |

### B. Preprocessing before search

| Solver | Passes, in order | Model reconstruction |
|---|---|---|
| Yices2 | `context_process_assertions`, `context/context.c:6847`. (0) MCSAT short-circuit `:6864-6869`; (1) `flatten_assertion` per assertion `:6877-6882`; (2a) `break_uf_symmetries` for `CTX_ARCH_EG` `:6900-6902`; (2b) `analyze_uf` = equality abstraction / eq-learner `:6903-6905`; (2c) `process_aux_eqs` `:6906-6908`; (2d) `context_process_candidate_subst` (variable elimination) **last**, because 2b/2c create new aux equalities `:6909-6911`; (3) for AUTO_IDL/AUTO_RDL: subst first, then `analyze_diff_logic`, then pick Floyd–Warshall vs simplex `:6914-6936`; (4) for `CTX_ARCH_SPLX`: `process_conditional_definitions` → `process_aux_eqs` → `process_aux_atoms` → subst `:6938-6957`; (6) `context_build_sharing_data` `:6972`; (7) internalization `:6977-7000` | **Yes, by an alias map, not by re-solving.** A term whose internalization root has no solver object is recorded as `[t -> u]` in the model's alias map (`context/context_solver.c:1931-1938`, `:2047-2049`); evaluation chases aliases (`model/model_eval.c:1694`, `:2015-2022`). Exposed as `yices_get_model(ctx, keep_subst)` (`api/yices_api.c:10243`) |
| OpenSMT | `MainSolver::preprocessFormula`, `api/MainSolver.cc:220-225`: `preprocessFormulaBeforeGlobalPhase` → `preprocessFormulaGlobalPhase` → `preprocessFormulaAfterGlobalPhase`. Before: `applyLearntSubstitutions` (frames > 0), `theory->preprocessBeforeSubstitutions`, `substitutionPass`, `theory->preprocessAfterSubstitutions` (`:227-243`). After: `rewriteMaxArity` for cnfization, `Substitutor` with the accumulated map (`:254-277`). Rewriters: `ArithmeticEqualityRewriter`, `DistinctRewriter`, `DivModRewriter`, `Substitutor` (`src/rewriters/`); Boolean simplification in `simplifiers/BoolRewriting.cc` | **Yes, two ways.** The substitution pass conjoins each used substitution back as an equality (`MainSolver.cc:567-573`), and the map is stored per frame (`preprocessor.setSubstitutions`, `:575`) for the model builder. **Disabled under proof logging**: `assert(getConfig().do_substitutions() and not getSMTSolver().logsResolutionProof())` (`:583`) |
| SMTInterpol | `Clausifier.addFormula`, `convert/Clausifier.java`: `FormulaUnLet.unlet` → `removeDoubleNot` → `TermCompiler.transform` → `mTracker.modusPonens(mTracker.asserted(orig), simplified)` → `OccurrenceCounter` → `AddAsAxiom` (Tseitin with Plaisted-Greenbaum). Supporting: `LogicSimplifier`, `SMTAffineTerm`, `EqualityProxy`, `CCTermBuilder`, `AddTermITEAxiom` | **Every rewrite emits a proof step.** The pipeline is threaded through an `IProofTracker` (`proof/IProofTracker.java`), with `NoopProofTracker` installed when proofs are off. So preprocessing is proof-producing by construction rather than by a second implementation |

### C. Core SAT engine

| | Yices2 | OpenSMT | SMTInterpol |
|---|---|---|---|
| Engines | **Three**: `solvers/cdcl/smt_core.c` (the only theory-coupled one), `sat_solver.c` (legacy standalone), `new_sat_solver.c` ("y2sat", modern, also usable as a delegate) | MiniSat-derived `smtsolvers/CoreSMTSolver.cc`, with `SimpSMTSolver`, `LookaheadSMTSolver`, `GhostSMTSolver` subclasses | `dpll/DPLLEngine.java` |
| Decision | VSIDS heap on `double activity`, `VAR_DECAY_FACTOR 0.95`, `VAR_RANDOM_FACTOR 0.02F` (`smt_core.c:2179-2223`, `sat_parameters.h:31-57`). y2sat uses **VMTF** instead (`new_sat_solver.c:8735`, `:8773`) | MiniSat VSIDS + `LAScore.cc` lookahead scoring for the splitter | Activity with multiplicative factors `ATOM_ACTIVITY_FACTOR 1.1`, `CLS_ACTIVITY_FACTOR 1.01`, cap `LIMIT 1e250` (`Config.java:48-55`); Jeroslow-Wang initial phase bias (`Config.java:69`); 2 random splits per 10,000 (`:64-67`) |
| Restarts | Selectable at `context/context_solver.c:367-459`: Luby (`:427-433`), Picosat inner/outer, MiniSat geometric. `INITIAL_RESTART_THRESHOLD 50`, `LUBY_INTERVAL 10` (`sat_parameters.h:65-85`); the source comment at `:76` records Luby base 10 as the best setting found. y2sat uses EMA fast/slow with CaDiCaL-style stabilizing phases (`new_sat_solver.c:10913-10955`) | Luby or geometric, `sat_luby_restart` / `sat_restart_first` / `sat_restart_inc` (`CoreSMTSolver.cc:75-81`, `:1833-1843`) | Luby, `RESTART_FACTOR 500` (`Config.java:59`, used at `DPLLEngine.java:1193`, `:1338`) |
| Clause DB reduction | `reduce_clause_database` `smt_core.c:4805`, CaDiCaL-style trigger `context_solver.c:151-166`, `INITIAL_REDUCE_THRESHOLD 10000` / `INCR_REDUCE_THRESHOLD 5000`. y2sat uses LBD retention (`new_sat_solver.h:623`) | MiniSat activity-based | Unlearn below `CLAUSE_UNLEARN_ACTIVITY 1e-150` scaled (`DPLLEngine.java:425`, `:1363`) |
| Watched literals | 2-watch with the links **embedded in the clause object**: `struct clause_s { link_t link[2]; literal_t cl[0]; }` (`smt_core.h:110-117`) | MiniSat watch vectors | 2-watch, plus a `mBacktrackWatchers` list per atom so a watcher on a true literal is parked rather than rescanned (`DPLLEngine.java:344-348`, `:413-416`) |
| Phase saving | Yes — `value[x]` keeps the polarity bit across backtrack (`smt_core.c:2222-2223`, `:2391`) | Yes (MiniSat) | Implicit through the atom's stored value |
| Chronological backtracking | **No**, and explicitly disabled in the CaDiCaL delegate: `ccadical_set_option(s->cadical, "chrono", 0)` (`solvers/cdcl/delegate.c:434`). Positive control: `backtrack_level` does hit in the same file set (`sat_solver.c:2171-2202`) | Not found | **No** — the opposite: `DEEP_BACKTRACK = true`, "backtrack as far as possible" (`Config.java:57`, used at `DPLLEngine.java:797`) |

### D. Inprocessing during search

| Solver | Answer |
|---|---|
| Yices2 | **Split.** The theory-coupled `smt_core.c` has essentially none: the only in-search cleanup is `simplify_clause_database` (`smt_core.c:5209-5232`), which drops base-level-satisfied clauses from watch lists, fired at `decision_level == base_level` on a propagation-count threshold (`:6184-6190`). No BVE, no subsumption, no probing. **y2sat has the full modern set**: `nsat_simplify` = SCC/binary-equivalence → failed-literal probing → clause-DB simplification (`new_sat_solver.c:11076-11091`), preceded by `nsat_preprocess` = unit/pure collection → free-variable elimination → up to 20 rounds of BVE alternating with subsumption (`:8436-8479`). So for QF_BV, Yices gets inprocessing **by routing the blasted CNF to a delegate** (`delegate.c:164-213`: y2sat, CaDiCaL, CryptoMiniSat, Kissat) |
| OpenSMT | `SimpSMTSolver` is MiniSat's `SimpSolver` lineage. Proof interaction is the finding: `CoreSMTSolver.h:639` is `if (this->logsResolutionProof()) { return; }` — the simplification is skipped rather than proof-logged |
| SMTInterpol | **None.** No pass named in `dpll/`; the only in-search DB work is activity-based unlearning. Positive control: `restart`/`luby` do hit in the same file |

### E. Encoding / bit-blasting

| Solver | Pipeline |
|---|---|
| Yices2 | Term-level normalization first (`terms/bvarith_buffers.c` vs `bvarith64_buffers.c` — separate bignum and ≤64-bit paths), then DAG compilation (`solvers/bv/bvpoly_dag.c`, `bvpoly_compiler.c`), then union-find pseudo-literal sharing (`remap_table.c`; `remap_table_mergeable/merge` at `bvsolver.c:1155-1156`), then **gate-level structural hashing** (`cdcl/gates_hash_table.c`, `new_gates.c`, `truth_tables.c`) and direct CNF with **on-the-fly subsumption via 4-bit clause signatures** in a 4-var/8-clause buffer (`solvers/bv/bit_blaster.h:37-79`). No separate AIG package. Entry `bv_solver_bitblast_variable` (`bvsolver.c:1659`). Incremental only partially: one global `bitblasted` latch, cleared on pop (`bvsolver.c:7613-7615`) |
| OpenSMT | Tseitin (`cnfizers/Tseitin.cc`) via `Cnfizer.cc` + `TermMapper`. BV bit-blasting in `tsolvers/bvsolver/BitBlaster.cc` |
| SMTInterpol | **No bit-blasting at all.** `Clausifier.setLogic` routes `logic.isBitVector()` to `setupLinArithmetic()` (`convert/Clausifier.java:1648-1650`) — BV is **int-blasted into LIA** through `theory/bitvector/BvToIntUtils.java`, with `nat2bv`, `bv2nat`, `&`, `pow2`, `log2` as the interface functions (`option/SMTInterpolConstants.java:31-35`). Boolean structure is Tseitin/Plaisted-Greenbaum in `Clausifier` |

### F. Theory solvers — the simplex, side by side

This is the axis the comparison exists for. Sources: ours from
[`04-arithmetic-theories.md`](../solver-inventory-2026-09/04-arithmetic-theories.md).

| | axeyum | Yices2 | OpenSMT | SMTInterpol |
|---|---|---|---|---|
| File | `simplex.rs` (2,855 LOC) | `solvers/simplex/simplex.c` + `matrices.c` | `tsolvers/lasolver/Simplex.cc` + `Tableau.cc` | `theory/linar/LinArSolve.java` + `SOIPivoter.java` |
| Tableau | Dense rows × columns, capped at `MAX_TABLEAU_CELLS = 4_000_000` (`simplex.rs:74`) | **Sparse, cross-linked.** Row entries hold the coefficient; column entries hold only a back-pointer into the row, so each `rational_t` exists once (`matrices.h:47-49`, `:85-94`). Deleted slots recycled through an embedded free list (`:36-45`). Column 0 is the constant, so every row is homogeneous (`:52-55`) | Sparse `Tableau` of `Polynomial` rows + column occurrence lists (`Tableau.h`, `SparseMatrix.h`) | Sparse `TableauxRow` / `MatrixEntry` |
| Leaving rule | Smallest-index basic variable violating a bound, by linear scan (`simplex.rs:886-899`) | `int_heap_get_min(&solver->infeasible_vars)` — smallest-index infeasible basic variable, always (`simplex.c:4272-4276`). Effectively Bland on the leaving side unconditionally | **Shortest row**: `getBasicVarToFixByShortestPoly` picks the candidate with the smallest `getPolySize` (`Simplex.cc:100-113`); Bland mode switches to smallest id (`:117-131`) | **Sum of infeasibility** — no single leaving variable. `computeSOI` builds a virtual objective over *all* out-of-bound variables and minimizes it (`SOIPivoter.java:62-100`), per King–Barrett–Dutertre FMCAD 2013 (cited at `:29-31`) |
| Entering rule | Fewest column nonzeros (`MinimiseFillIn`), ties by a seeded LCG reservoir sample (`simplex.rs:109-128`) | Fewest **non-free basic variables depending on x**, `+1` if x is not free; ties by reservoir sampling with an LCG seeded `0xabcdef98` (`simplex.c:3878-3884`, `3889-3919`, `4002-4008`). Source calls it `// Leonardo's heuristic` (`:3996`) | Fewest column occurrences — "favor more independent variables: those present in less rows" (`Simplex.cc:135-137`, `:158-160`) | `FreedomLimiter` over the SOI gradient, weighted; ties merged with a Bland preference for the smaller variable (`SOIPivoter.java:432-462`) |
| Bland trigger | `repeat_leavings > bland_threshold`, default `1_000`, **fixed** (`simplex.rs:139-150`) | `repeats > bthreshold`, `SIMPLEX_DEFAULT_BLAND_THRESHOLD 1000` (`simplex_types.h:908`), **scaled by problem size**: `×100` above 1,000 variables, `×1000` above 10,000 (`simplex.c:4245-4250`). At 20k variables the effective threshold is 1,000,000 | `repeats > tableau.getNumOfCols()` — dynamic, one per column (`Simplex.cc:47`) | Plateau-driven: the inner Bland loop runs whenever `mBestLimiter.mFreedom.signum() == 0` (`SOIPivoter.java:407-422`). **`Config.BLAND_USE_FACTOR = 5` (`Config.java:101`) has no reader anywhere in the tree** — dead config left behind by the SOI rewrite |
| Pivot cap | `MAX_PIVOTS = 2_000_000` → `SimplexOutcome::Unknown` (`simplex.rs:81`) | **None.** Only `if (solver->interrupted) break;` (`simplex.c:4251-4256`). The `loops` counter exists solely to print a dot every 4096 iterations under tracing (`:4258-4263`) | **None.** `while (true)` (`Simplex.cc:42`) | **None.** `while (true)` (`SOIPivoter.java:395`) |
| Anti-cycling | Bland fallback only | Bland fallback only. No perturbation, no lexicographic rule | Bland fallback only | SOI monotone decrease + Bland at plateaus |
| Rationals | `i128` pair, promoted to big internally (ADR-1702), **narrowed at the module boundary — a witness or Farkas multiplier outside `i128` is `Unknown`** (`simplex.rs:420`) | 64-bit tagged union: low bit 0 ⇒ inline `int32 num`/`uint31 den`, low bit 1 ⇒ `mpq` pointer; `q_add` stays in registers for int+int and calls `convert_to_gmp` past `MIN/MAX_NUMERATOR` (`terms/rationals.h:36-70`, `rationals.c:937-964`) | `FastRational`: `word num` / `uword den` plus a lazily-allocated pooled `mpq`, a 3-bit `State` saying which halves are valid, `goto overflow` on `CHECK_WORD` failure, and `try_fit_word()` to demote (`common/numbers/FastRational.h:20-46`, `:567-609`, `:643-702`) | `Rational` with `int mNum` / `int mDenom` and a `BigRational extends Rational` fallback (`Library-SMTLIB/.../Rational.java:54-64`, `:383`, `:535`) |
| Float fast path | None | **None.** All 12 `double`/`float` hits under `solvers/simplex/` are a PRNG seed (`simplex_types.h:856`), propagation-row activity (`simplex_prop_table.h:68,103-104`), or an English comment. Zero hits under `solvers/floyd_warshall/` | None found | None |
| Strict inequalities | `Delta { c, k }` in ℚ(δ) (`simplex.rs:434-442`) | `xrational_t { rational_t main; rational_t delta; }` (`terms/extended_rationals.h:38-41`). **δ is instantiated once at model build** as a global positive rational, shrunk by `epsilon_for_le` per bound and **halved** per egraph disequality (`epsilon_for_diseq`, `simplex.c:12081-12106`); `epsilon_for_egraph` is an O(n²) pairwise scan (`:12113-12131`) | `Delta` class + `Simplex::computeDelta()` (`Simplex.h:96`) | `InfinitesimalNumber` / `ExactInfinitesimalNumber` |
| Farkas coefficients | **Explicit and re-checked.** `Tableau::farkas` returns multipliers; `check_farkas` re-verifies; the offline `check_with_lra` carries a self-checked `FarkasCertificate` | **Not materialized.** `grep -c 'farkas\|Farkas' simplex.c` = 0 against a positive control of 8 for `record_theory_conflict`. The conflict set is built structurally from the unrepairable pivot row by pushing *bound indices* (`conflict_set_for_increase`, `simplex.c:4103-4137`) | **Explicit.** `Simplex::Explanation = std::vector<ExplTerm>` where `ExplTerm { LABoundRef boundref; Real coeff; }` (`Simplex.h:32-36`) — real Farkas coefficients, and they are what `FarkasInterpolator` consumes | **Explicit.** Coefficients carried in `LAAnnotation` and emitted as the `:farkas` proof axiom (`ProofRules.java:84`) |
| Explanation minimization | Farkas-participating subset (`rows_to_core`, `lra_online.rs`) | **Duplicate removal only** — `ivector_remove_duplicates(v); // TEST` (`simplex.c:4450`). Derived bounds are expanded recursively into the clause with no redundancy pruning (`simplex_build_explanation`, `:4399-4460`) | `getConflictingBounds` (`Simplex.h:88`) | `Explainer` / `CompositeReason` |

**The integer story on top:**

| | axeyum | Yices2 | OpenSMT | SMTInterpol |
|---|---|---|---|---|
| Order | `prove_lia_unsat_by_gcd` / `..._by_diophantine` (`lia_gcd.rs:39`, `:66`) → bounded Gomory fractional cuts (`lra.rs:2710`) → branch and bound (`lra.rs:2266`), sequenced by `decide_int_constraints` (`lra.rs:1913`) | `simplex_make_integer_feasible` (`simplex.c:9005-9146`): bound strengthening → integrality constraints → Diophantine check (per-row GCD short-circuit, then echelon) → strengthen again → naive search if `underconstrained` → select branch variable → Gomory cut *or* branch atom | `checkIntegersAndSplit` (`LASolver.cc:284-320`): collect non-integral int vars → `cutFromProof()` if `shouldTryCutFromProof()` → else `splitOnRandom` and emit a split lemma | LA `checkpoint` → if non-integral, `CutCreator.generateCuts()` then re-check (`LinArSolve.java:1495-1528`) |
| GCD test | `lia_gcd.rs:39` (single equation), `:66` (fraction-free system reduction) | Per-row inside the Diophantine driver, short-circuiting to `build_gcd_conflict` before any echelon work (`simplex.c:7873-7881`) | Not present as a separate step | Inside `CutCreator` |
| Cuts | **Gomory fractional cuts**, bounded rounds (`lra.rs:2710`) | **Mixed-integer Gomory (MIR/GMI)**, spec at `gomory_cuts.h:19-81`. But: the whole block is labelled `// NOT READY FOR PRIME TIME.` (`simplex.c:8498`); the multi-cut round is `if (false && ...)` (`:9114`); the live path emits **one** cut per final check, gated on `num_branch_atoms >= 20` **and** `bb_score > 100000000` (`:9113-9134`). Since `HALF_MAX_BRANCH_SCORE ≈ 2.1e9` and any variable missing a bound scores above it, the gate fires essentially only on unbounded branch variables. The cut is added as a **clause** `(x_1 ≥ l_1) ∧ … ⇒ (p ≥ 0)`, not a tableau row (`:8691-8693`) | **Cuts from proofs (Hermite Normal Form).** `HermiteNormalForm()(matrixA)`, then the first row of `U` whose product with the current point is non-integral is the cut (`CutCreator.cc:11-33`). Tried on every 10th call: `static unsigned long counter; return ++counter % 10 == 0;` (`LASolver.cc:738-742`) — **and returns `false` outright when `produce_inter()` is set** (`:739`) | **Cuts from proofs (Hermite Normal Form)**, with an explicit LIRA adaptation: real columns are never added into integer columns, so the form is not strictly Hermite (`theory/linar/CutCreator.java:33-70`) |
| Branch | Own `lia_branch_and_bound` loop inside the theory (`lra.rs:2266`) | `create_branch_atom` (`simplex.c:7170-7218`) — **midpoint of the two bounds, ceiled**, not floor-of-value; handed to CDCL as a literal. Branch variable by `select_branch_variable` (`:7399-7452`), smallest `simplex_branch_score` with LCG tie-break. Then `solver->core->stats.conflicts += 40` to accelerate the restart schedule (`:9140-9141`) | `splitOnRandom(varsToFix)` (`LASolver.cc:280`) then `x ≤ floor(v) ∨ x ≥ floor(v)+1` pushed to `splitondemand`, status `NEWSPLIT` (`:310-318`) | Branch literals through the DPLL engine |
| Give-up point | **`MAX_LIA_BNB_NODES = 50_000` without a clock, `20_000_000` with one → `Unknown`** (`lra.rs:1706`, `:1717`); `MAX_DPLL_ROUNDS = 10_000` for the Boolean-structured loop (`dpll_lia.rs:44`) | **None in the integer loop.** `simplex_final_check` returns only `FCHECK_SAT` or `FCHECK_CONTINUE` (`simplex.c:10098-10122`). The one sub-procedure that gives up is the Diophantine solver, at `max_coeff_size * max_column_size > 64000` (`diophantine_systems.c:1914-1946`), and giving up **sticky-disables the whole subsystem** for the rest of the search (`simplex.c:7852-7858`) — reset only at `simplex_start_search` (`:9843`). Non-termination shows up as an unbounded CDCL search, not as unknown | **None.** `TRes::UNKNOWN` from `cutFromProof` means only "no cut found" and falls through to branching (`LASolver.cc:874`, consumed at `:301-305`) | **None for LIA.** `checkCompleteness()` returns `INCOMPLETE_THEORY` only when `mHasNonLinearVar >= 0` (`LinArSolve.java:709-715`). The only budget is the user-set `:reproducible-resource-limit`, a counter decremented at each termination check (`util/ResourceLimit.java:62-68`) |

**Other theories, briefly.**

- Yices2 EUF: congruence closure with signature hash-consing and parent/use
  vectors (`solvers/egraph/egraph.c:1804`, `:79-111`), with **lazy edge-based
  explanations that preserve causality** — the design note at
  `egraph_explanations.c:20-47` states the expansion must not introduce
  equalities asserted after the edge being explained. Arrays/functions in
  `solvers/funs/fun_solver.c`, all work in `final_check` (`:2093`), with real
  extensionality bounded by `max_extensionality` (`:1042-1097`, `:1865`) and
  instances ordered by a type stratification (`funs/stratification.c`).
- Yices2 difference logic: two dedicated incremental Floyd–Warshall solvers
  (`solvers/floyd_warshall/idl_*`, `rdl_*`) whose `final_check` is literally
  `return FCHECK_SAT;` (`idl_floyd_warshall.c:1654-1656`). Selected by a
  four-way size/density heuristic: simplex if the path bound ≥ 2³⁰ or > 1000
  variables; FW if ≤ 200 variables or zero equalities; else FW iff
  atom density ≥ 10.0 for IDL, ≥ 7.0 for RDL (`context/context.c:6169-6217`,
  `:6221-6262`). The comment at `:6192` is candid: "use FW for now, until we've
  tested SIMPLEX more". IDL uses `int32_t` distances with a documented
  overflow warning (`idl_floyd_warshall.h:25-26`); RDL's delta component is a
  plain `int32_t` counter rather than a second rational (`rdl_floyd_warshall.h:96-112`).
- OpenSMT: `tsolvers/egraph/` (congruence closure with `Explainer.cc`),
  `arraysolver/ArraySolver.cc` (whose header says it "follows from a large part
  the implementation in SMTInterpol", `ArraySolver.h:18-19`),
  `bvsolver/BitBlaster.cc`, `stpsolver/` (simple temporal problem = difference
  logic).
- SMTInterpol: `theory/cclosure/` (congruence closure with `CongruencePath`
  building equality paths for conflicts *and* proof annotations, and
  `CCProofGenerator` turning annotations into proof terms — see the package
  README), `theory/cclosure/ArrayTheory.java` with `WeakCongruencePath` for weak
  equivalence, `DataTypeTheory.java`, `theory/quant/`, `theory/epr/`.

### G. Theory combination

| Solver | Mechanism |
|---|---|
| Yices2 | **Egraph-mediated model reconciliation producing interface equalities** — a lazy, model-driven Nelson–Oppen. Documented in-tree at `solvers/egraph/egraph.h:855-930`. `baseline_final_check` (`egraph.c:6109-6237`) runs satellites in a fixed order (arith → bv → arrays → MCSAT), then asks each to reconcile its local model with the egraph partition under a budget `max_interface_eqs` (`:6173-6203`); each interface equality created forces another CDCL round (`:6217-6219`). The `experimental_final_check` path (`:6244+`) first tries to *repair* the mismatch by merging egraph classes (`egraph_reconcile`, `:6053-6071`) and only then emits `gen_interface_lemma` (`:5601-5650`). Plus **offset equalities**: a union-find over `x = y + k` with polynomials hashed modulo the offset classes, so simplex→egraph equalities propagate cheaply (`solvers/simplex/offset_equalities.h:20-52`; enabled only for `CTX_ARCH_EGSPLX`/`EGFUNSPLX`, `api/yices_api.c:8887-8893`) |
| OpenSMT | Lazy equality propagation over interface variables. `UFLATHandler::check` collects equalities implied by the UF solver over `interfaceVars`, and **only if that set is empty** collects from the LA solver, "to prevent duplication" (`UFLATHandler.cc:45-56`). Each interface equality becomes three clauses — a trichotomy clause plus the two implications `x=y ⇒ x≤y`, `x=y ⇒ x≥y` (`addInterfaceClausesForEquality`, `:60-77`). Solver schedule is explicit: `{ufsolver, arraySolver, lasolver}` (`:21-26`) |
| SMTInterpol | Nelson–Oppen with shared equalities: a `CCEquality` DPLL atom "may be linked to an LAEquality for shared terms" (`theory/cclosure/README.md`, CCEquality row), and the CC package README states combination "via Nelson-Oppen style combination" with linear arithmetic, arrays and datatypes |

### H. Quantifiers

| Solver | Answer |
|---|---|
| Yices2 | **Yes, two mechanisms plus a third engine.** (1) E-matching with patterns compiled to an **abstract machine** — `solvers/quant/ematch_compile.c`, `ematch_execute.c`, `ematch_instr.c` — driven by `quant_solver_final_check` (`quant_solver.h:175-179`), budgeted by `num_instances_per_round` / `max_rounds_per_search` (`quant_solver.h:53-64`), with learning heuristics for instance selection (`cnstr_learner.c`, `term_learner.c`). (2) An **exists-forall CEGAR solver**, `src/exists_forall/`, algorithm spelled out at `efsolver.h:20-70`. (3) **MCSAT** (`src/mcsat/`) is a different engine entirely — a trail of Boolean *and first-order* assignments with plugins for Boolean, UF, ITE, nonlinear arithmetic via LibPoly, BV via BDDs, and **finite fields** (`mcsat/solver.c:929-936`). QF_NRA/QF_NIA/QF_FFA map to `CTX_ARCH_MCSAT` (`api/context_config.c:189-217`) |
| OpenSMT | **No.** Quantified logics are not supported |
| SMTInterpol | **Yes.** `theory/quant/` with four instantiation methods, default `E_MATCHING_CONFLICT` (conflict-based instantiation) and alternatives `E_MATCHING_EAGER`, `E_MATCHING_LAZY`, `ENUMERATION` (`option/SolverOptions.java:84-85`, used at `theory/quant/InstantiationManager.java:90-91`, `:426`). Destructive equality reasoning in `DestructiveEqualityReasoning.java`. Separately, `theory/epr/` is an EPR (effectively propositional) engine with DAWG-based partial models, selected by the `:epr` option |

### I. Model production

| Solver | Build | Self-validation |
|---|---|---|
| Yices2 | `build_model` (`context/context_solver.c:2064-2135`): satellite models → egraph → MCSAT → intern-table scan. Hash-consed value universe with functions as finite maps plus a default (`model/concrete_values.c`, `fun_maps.c`) | **No automatic check in the default path.** `yices_formula_true_in_model` exists as a *user-callable* checker (`api/yices_api.c:13313`); the unsat-core validator `validate_unsat_core` is defined at `smt2_commands.c:3275` with its only call site **commented out** at `:3340` |
| OpenSMT | `src/models/` + `EgraphModelBuilder` | `VerificationUtils::impliesInternal` re-solves with a fresh `MainSolver`; used for interpolants and proof leaves, not routinely for models |
| SMTInterpol | `smtinterpol/model/Model.java`, built from the theories | **Yes, under `:model-check-mode`.** It builds the model, runs `checkTypeValues`, then evaluates **every asserted literal** against it and reports `INVALID_MODEL` / logs `fatal` on a mismatch (`SMTInterpol.java:497-520`) |

### J. Proof / certificate production

| Solver | Answer |
|---|---|
| Yices2 | **None.** `smt2_get_proof` prints "get-proof is not supported" (`smt2_commands.c:5055-5060`); `bool produce_proofs; // default = false (not supported)` (`smt2_commands.h:389`). A `proof` grep over `src/` matches only 8 files, all frontend token plumbing; zero hits under `src/solvers/`, `src/context/`, `src/mcsat/`, `src/api/`. `drat|lrat` returns 4 hits, all inside "quadratic". Positive control: the same grep form finds real `unsat_core` code at `smt_core.c:3748-3867`. **Unsat cores yes** — `build_unsat_core` walks antecedents backward over clauses, implied literals and theory explanations, collecting reached assumption literals (`smt_core.c:3852-3870`); cores are always relative to assumptions |
| OpenSMT | **A propositional resolution proof graph with theory lemmas as opaque leaves.** `ResolutionProof` (`smtsolvers/ResolutionProof.cc`), leaf kinds `CLA_LEARNT`/`CLA_DERIVED`/`CLA_ORIG`/`CLA_THEORY` (`:275-293`). Printed as a custom `(proof …)` s-expression with `let`-shared derivation chains (`printSMT2`, `:139-`), reachable through `(get-proof)` (`api/Interpret.cc:268-279`, `:1295-1298`). `:produce-proofs` is a **pre-initialization** option (`options/SMTConfig.h:346-349`) and is implied by `:produce-interpolants` or `:produce-unsat-cores` (`:606-608`). Proof-graph transformations: `:proof-reduce`, `:proof-rpi`, `:proof-lower-units`, `:proof-reduce-expose`, `:proof-num-graph-traversals`, `:proof-struct-hash` (`SMTConfig.cc:483-492`) |
| SMTInterpol | **A small trusted axiom core, and it is the design closest to ours.** `proof/resolute/ProofRules.java` defines three term formers — `res`, `assume`, `axiom` (`:99-101`) — plus ~70 named axiom schemata: core Boolean (`:104-129`), quantifiers (`:120-123`), equality/congruence (`:133-140`), LA (`:80-91`: `:trichotomy`, `:total`, `:total-int`, `:farkas`, `:mulpos`, `:to_int-high/low`, `:/def`, `:poly+`, `:poly*`), div/mod (`:94-97`), arrays (`:99-104`), datatypes (`:106-113`), bitvectors (`:115-129`). Four proof levels: `NONE`, `CLAUSES`, `FULL`, `LOWLEVEL` (`smtlib2/SMTInterpol.java:93-95`); `LOWLEVEL` runs `ProofSimplifier` (`:813-815`). **Preprocessing rewrites are inside the proof** via `IProofTracker`. On a `sat` result, `getProof` returns a **model proof** built by `ModelProver` (`:822-826`) |

### K. Proof checking

| Solver | Answer |
|---|---|
| Yices2 | **None.** Follows from §J — no proof datatype, no checker source, no proof harness under `tests/`. The only "validator" is the commented-out `validate_unsat_core`, which re-solves rather than checks a certificate. Positive control that checkers of other kinds exist in the tree: `check_watch_vectors`/`check_heap` debug validators at `smt_core.c:54-60`, `new_sat_solver.c:62` |
| OpenSMT | **In-tree, structural, and assert-based.** `ProofGraph::checkProof(bool check_clauses)` (`proof/PGCheck.cc:176-240`) does a top-down and a bottom-up traversal of the resolution DAG, verifying that leaves are seen once and inner nodes twice, that antecedent levels are consistent, and — only under `check_clauses` — that each node's clause is the correct resolvent (`checkClause`, `:99`). **Every one of those is an `assert`**, so the check is compiled out under `NDEBUG`. Called from `PGBuild.cc:268`, `PGMain.cc:70,73,169`, and after each proof transformation (`PGTransformationAlgorithms.cc:285,504,716,724,852`). Separately, `verifyLeavesInconsistency` (`PGCheck.cc:16-58`) asserts the leaf set with **OpenSMT itself** and throws if it is satisfiable — a self-check, not an independent one. There is no external checker and no standard output format |
| SMTInterpol | **Two checkers, and one of them fails the query.** (1) `MinimalProofChecker` (`proof/resolute/MinimalProofChecker.java`, 605 lines) — a non-recursive walk over the proof term computing each subproof's clause, checking `@asserted` rules against the recorded assertion set. Under `:proof-check-mode` a failure **throws** `SMTLIBException("Proof-check failed")` and notifies `ErrorReason.INVALID_PROOF` (`SMTInterpol.java:571-580`). (2) A **standalone** checker binary, `proof/checker/Main.java`, with its own JFlex/CUP grammar (`proofs.flex`, `proofs.cup`) and `CheckingScript.java`, which takes a script file and a proof file on the command line — i.e. proofs can be checked from text by a separate program, exactly the shape of our `drat-trim` route |

### L. Interpolation — the centerpiece

| Solver | Supported? | Theories | Algorithm | Strength guarantee | Checked? |
|---|---|---|---|---|---|
| **Yices2** | **Only in MCSAT, and it is not a Craig interpolant from a proof.** `yices_check_context_with_interpolation` (`include/yices.h:3572`, doc `:3540-3570`), `yices_get_model_interpolant` (`:3729`) | MCSAT-backed logics (NRA/NIA/FF/…) | Per-round **model interpolants**: push both contexts, loop collecting a model interpolant per round, assert each into ctx_B, return their conjunction (`api/yices_api.c:10026-10160`). Hard precondition `context_supports_model_interpolation` (`:10032-10033`) | None stated. The code notes "MCSAT does not produce a label interpolant for every assumption conflict" (`solvers/mcsat_satellite.c:401`) | No |
| **OpenSMT** | **Yes, and it is the most configurable of the three.** `InterpolationContext` (`proof/InterpolationContext.h`), reached from `MainSolver::getInterpolationContext` (`api/MainSolver.cc:379-383`) | **Propositional** (from the resolution proof), **EUF** (`InterpolatingEgraph` + `UFInterpolator`), **LRA/LIA** (`FarkasInterpolator`, `LIAInterpolator`). **Not** arrays (`ArrayTHandler.h:26` throws `InternalException("Interpolation not supported yet")`), **not** IDL/RDL (`IDLTHandler.h:26`, `RDLTHandler.h:21` throw), and — the significant one — **not the UF+LA combination**: `UFLATHandler::getInterpolant` is `throw std::logic_error("Not implemented")` (`UFLATHandler.cc:25-28`) | Propositional: the labelled interpolation systems, selected by `:interpolation-bool-algorithm` — `itp_alg_mcmillan` (0), `itp_alg_pudlak` (1), `itp_alg_mcmillanp` (2), `itp_alg_ps` (3), `itp_alg_psw` (4), `itp_alg_pss` (5) (`options/SMTConfig.h:163-168`), default McMillan (`:467`). EUF: colored congruence graph with `I`/`I'`/`J`/`B` path functions and `splitEdge`/`colorCongruenceEdge` for mixed edges (`UFInterpolator.h:118-175`), variants strong/weak/random (`:155-157`). LRA: primal Farkas, dual Farkas, **flexible**, decomposed, dual-decomposed (`FarkasInterpolator.h:68-72`), selected by `:interpolation-lra-algorithm` (`SMTConfig.h:172-176`) | **A strength lattice, and a continuous knob.** McMillan is strongest, McMillan′ weakest, Pudlák in between; PS/PSW/PSS are the strength-varying labelled systems. `:proof-interpolation-property` and `proof_trans_strength` restructure the proof "for stronger/weaker interpolants" (`SMTConfig.h:939`). For LRA, `getFlexibleInterpolant(Real strengthFactor)` takes a rational in (0,1), default `1/2` (`SMTConfig.h:177` `itp_lra_factor_0 = "1/2"`). **Explicitly deleted for integers**: `PTRef getFlexibleInterpolant(Real) = delete;` with the comment `// not implemented for integers` (`LIAInterpolator.h:26-27`) | **Opt-in and non-gating.** `enabledInterpVerif() == (config.certify_inter() >= 1)` (`InterpolationContext.h:67`), option `:certify-interpolants` (`SMTConfig.cc:480`). The check re-solves with a fresh OpenSMT `MainSolver` — `A ⇒ I` unsat, `I ⇒ ¬B` unsat, plus a variable-containment check (`VerificationUtils.cc:14-31`). **A failed check is `assert(sound)` plus a printed line; the interpolant is returned regardless** (`InterpolationContext.cc:857-871`). Path interpolation additionally checks `I_{i-1} ∧ (moved partitions) ⇒ I_i` (`:890-899`) |
| **SMTInterpol** | **Yes — this is what the tool exists for.** `getInterpolants(partition, startOfSubtree)` (`smtlib2/SMTInterpol.java:848`), derived from the proof (`getProof(ProofMode.CLAUSES)`, `:843`) | Classes in `interpolate/`: `Interpolator` (the driver, a `NonRecursive` walk over the proof tree), `CCInterpolator` (congruence closure), `LAInterpolator` (linear arithmetic), `ArrayInterpolator`, `DatatypeInterpolator`, `DatatypeCycleInterpolator`, `EQInterpolator` (the auxiliary mixed-equality predicate), `InterpolantPurifier`, `AuxFunctionRemover`, `SymbolCollector`/`SymbolChecker`, `InterpolantChecker`. 7,764 lines total | **Tree interpolation, natively.** `mStartOfSubtrees` encodes the tree; interpolants are required in post-order traversal, and the driver computes all of them from one proof in one pass (`Interpolator.java:88-108`). Sequence/path interpolation is the degenerate case. **Mixed AB-literals are handled, not declined**: auxiliary variables plus an internal `@EQ` predicate (`Interpolator.java:71` `public static final String EQ = "@EQ";`, `:116` `mMixedTermAuxEq`, `:117` `mPurifyDefinitions`) | No strength parameter. The guarantee is Craig + the tree-interpolation property, and it is *checked* rather than *chosen* | **The strongest of the three.** With `:interpolant-check-mode` a fresh SMTInterpol instance is created as `checkingSolver` (`SMTInterpol.java:908-913`), and then: (a) `checkInductivity` runs at **every proof leaf** as the interpolant is constructed, asserting the leaf's literals, the child interpolants and the negated node interpolant and requiring `unsat` (`InterpolantChecker.java:140-414`, called at `Interpolator.java:394`); (b) `checkFinalInterpolants` (`:444-`) checks the tree property for every partition plus a `SymbolChecker` symbol-containment condition. **Note**: the `Config.DEEP_CHECK_INTERPOLANTS` flag is short-circuited at the leaf site by `if ((true \|\| Config.DEEP_CHECK_INTERPOLANTS) && mChecker != null)` (`Interpolator.java:394`), so leaf checking is unconditional when a checking solver exists — the flag is live only at `:476`. Optional post-processing: `SimplifyDDA` under `:simplify-interpolants` (`SMTInterpol.java:927-937`) |

**Ours, for the join** (from
[`08-models-proofs-and-evidence.md`](../solver-inventory-2026-09/08-models-proofs-and-evidence.md)
§6): eight interpolators plus one propositional, reached from a single
fall-through ladder `dispatch_interpolant` (`solver.rs:305`, LRA → LRA-CNF →
LIA → LIA-CNF → EUF → UFLRA → UFLIA → BV), from a **single A/B partition**
(`solver.rs:243`, `:288-297`). Every one verifies before returning and declines
to `None` on doubt. No strength parameter, no tree or sequence interpolation,
no proof-derived interpolation. `euf_interpolant.rs:503` declines on a
mixed-color congruence edge. All seven `*_certified` variants have no caller in
`crates/axeyum-solver/src`.

### M. Optimization

| Solver | Answer |
|---|---|
| Yices2 | **No.** `maxsat\|max_smt` → zero hits under `src/`; `objective` → zero. The `optimize` hits are a comment, a TODO, and `mcsat/l2o/hill_climbing.c`'s `optimize_bool`/`optimize_number`/`optimize_fs` — local search to *find a satisfying assignment faster*, not OMT |
| OpenSMT | **No.** No MaxSAT or objective machinery under `src/`. Positive control: `unsatcores/` is found by the same grep form |
| SMTInterpol | **No OMT/MaxSAT.** It does have **MUS enumeration** — `muses/ReMus.java`, `MusEnumerationScript.java`, `Shrinking.java`, `Heuristics.java` — i.e. minimal unsatisfiable subsets, which is adjacent but different |

### N. Incrementality

| Solver | Answer |
|---|---|
| Yices2 | Real push/pop: `context_pop` (`context/context.c:6774-6789`) invalidates the unsat-core cache, then pops the SMT core (which propagates to all solvers), MCSAT, the internalization table (and its substitutions), the assumption stack, the eq cache, the divmod table, and the SAT-delegate state. Learned clauses implied at or below the new base level survive. Assumptions: `yices_check_context_with_assumptions` (`include/yices.h:3387`), `..._with_model` (`:3434`), `..._with_model_and_hint` (`:3487`). BV caveat: pop clears the global `bitblasted` latch and resets `base_level` to 0 (`bvsolver.c:7613-7615`). Incremental SAT delegate runs with preprocessing **off** for soundness (`delegate.c:60-65`, `:212-213`). SMT-LIB benchmark mode forbids a second `check-sat` (`smt2_commands.c:6917`) |
| OpenSMT | `MainSolver::push/pop` over assertion frames; preprocessing is per-frame with `firstNotPreprocessedFrame` tracking (`MainSolver.cc:96`, `:126`, `:141-157`) and substitutions stored per frame. Proof production and interpolation are **pre-initialization** options (`SMTConfig.h:346-349`), so they cannot be turned on mid-session |
| SMTInterpol | `push`/`pop` through `Clausifier.push` / `DPLLEngine.push` (`convert/Clausifier.java:1690-`), with failed pushes counted when already inconsistent. Assumptions via `checkSatAssuming` and `getUnsatAssumptions` |

### O. Parallelism

| Solver | Answer |
|---|---|
| Yices2 | **Thread safety plus a determinism test harness — not a portfolio.** `src/mt/` is locks (`yices_locks.*`), thread wrappers (`threads.*`), and macros. The only non-test caller of `launch_threads` is `check_delayed_assertions_mt` (`smt2_commands.c:6856-6895`), whose own comment is `/* Test multi-threaded code: */`; it runs the **same** problem in N threads and prints "SUCCESS: All threads agree" / "FAILURE: Threads disagree" (`:6891-6893`). No seed diversification, no clause sharing, no first-to-finish. CLI `--nthreads=<n>` defaults to 0 (`yices_smt2.c:256`, `:505-513`). No cube-and-conquer |
| OpenSMT | **Cube-and-conquer style splitting, in-tree.** `src/parallel/`: `ScatterSplitter` (scattering), `LookaheadSplitter`, `MainSplitter`, `SplitContext`, `SplitData`, plus a separate `opensmtSplitter` binary. `ScatterSplitter : public SimpSMTSolver, public Splitter` (`ScatterSplitter.h:23`); the distributed layer itself lives outside this repo |
| SMTInterpol | **None.** Single-threaded; the only `synchronized` in the tree is the logger lock (`DefaultLogger.java:62`, `:71`) |

### P. Resource limits and determinism

| Solver | Answer |
|---|---|
| Yices2 | Wall-clock `--timeout` (`frontend/yices_smt2.c:216`, impl `utils/timeout.c`, per-check wrapper `smt2_commands.c:2735-2753`, reported as `:reason-unknown "timeout"` at `:4672`). Search budgets that are not wall-clock: `c_threshold`, `d_threshold`, `r_initial_threshold`, `max_interface_eqs`, `max_instances_per_round`, `max_rounds_per_search` (`frontend/common/parameters.c`). **One LCG, header-only**: `PRNG_MULTIPLIER 1664525`, `PRNG_CONSTANT 1013904223`, `PRNG_DEFAULT_SEED 0xabcdef98` (`utils/prng.h:40-61`); seeds are per-solver state (`smt_core.h:984`), user-settable as `random-seed` / `randomness`. **`:reproducible-resource-limit` is explicitly unsupported** (`smt2_commands.c:6482-6487`) |
| OpenSMT | `options/SMTConfig` carries `sat_restart_first`, `sat_restart_inc`, `sat_luby_restart`, `sat_reorder_pivots`, `proof_num_graph_traversals`, `proof_num_global_iterations`, and a random seed. **Determinism hazard found**: `shouldTryCutFromProof` uses a *function-local static* counter — `static unsigned long counter = 0; return ++counter % 10 == 0;` (`LASolver.cc:739-741`) — which is shared across every `LASolver` instance in the process, so the cut schedule of one solve depends on how many solves preceded it. Branch-variable choice is `irand(seed, …)` (`LASolver.cc:280`), seeded and therefore reproducible only for a fixed call history |
| SMTInterpol | `:timeout` (wall clock) **and `:reproducible-resource-limit`** — a clock-free counter decremented at every termination check, so a limited run is reproducible (`util/ResourceLimit.java:62-68`). `:random-seed` via `DPLLEngine.setRandomSeed` (`:1798`), default `RANDOM_SEED 11350294L` (`Config.java:61`). Plus the five check modes listed in §K/§L, `:proof-level`, `:proof-transformation`, `:simplify-interpolants`, `:check-type`, `:instantiation-method` (`option/SMTInterpolConstants.java:37-57`) |

## Gaps against axeyum

### They have, we do not

| Capability | Their implementation | Our status | Rough size |
|---|---|---|---|
| **A rational that never declines on magnitude** | Three independent word/bignum hybrids: Yices `rationals.h:36-64` (tagged 64-bit union), OpenSMT `FastRational.h:31-46` + `:696-702` (state byte, pooled `mpq`, `try_fit_word` demotion), SMTInterpol `Rational.java:54-64` (`BigRational` subclass) | `simplex.rs:420` `narrow` returns `None` — `Unknown` — if a feasible point or Farkas multiplier does not fit `i128`. `04-arithmetic-theories.md` records this as one of three shipped declines | Medium. We already promote internally; the work is teaching `lra`, `lra_online`, model lifting and certificate serialization to read a promoted `Rational` instead of `numerator()` (which panics). The consumers are enumerated in the `narrow` doc comment |
| **LIA that cannot return unknown** | Branching as a *lemma to the SAT solver* rather than an in-theory tree: Yices `simplex.c:7170-7218`, OpenSMT `LASolver.cc:309-319`. No node cap in any of the three | `MAX_LIA_BNB_NODES = 50_000` / `20_000_000` → `Unknown` (`lra.rs:1706`, `:1717`); `MAX_DPLL_ROUNDS = 10_000` (`dpll_lia.rs:44`) | Large but decomposable. We already have `CdcltLiaTheory` on the native core (`lia_theory.rs:113`); the change is to emit the split as a theory lemma from `final_check` instead of recursing inside `lia_branch_and_bound` |
| **Cuts from proofs (Hermite Normal Form)** | OpenSMT `CutCreator.cc:11-33` + `SparseMatrix.cc:139` `HermiteNormalForm`; SMTInterpol `theory/linar/CutCreator.java:33-70` with an LIRA-safe variant | We have Gomory fractional cuts (`lra.rs:2710`) and a fraction-free Diophantine *refuter* (`lia_gcd.rs:66`) that does not return a lattice basis | Medium. `axeyum-arith` already has fraction-free row reduction and Bezout certificates (`upoly.rs`, `BezoutCertificate`); HNF is the natural next primitive there |
| **Lattice bound tightening from a general solution** | Yices: the Diophantine solver returns `x = b₀ + Σ cᵢzᵢ` (`diophantine_systems.h:26-38`), and `strengthen_bounds_on_integer_variable` rounds bounds to the lattice, `l' = b + d·ceil((l-b)/d)` (`simplex.c:7656-7695`). Also period/phase congruence learning `x ≡ Q (mod P)` with provenance for explanation (`integrality_constraints.h:71-108`) | Not present. `lia_gcd.rs` refutes; it does not tighten | Medium |
| **A sparse cross-linked tableau** | Yices `matrices.h:47-49`, `:85-94` — each coefficient stored once, column entries are back-pointers, deleted slots recycled through an embedded free list | Dense `MAX_TABLEAU_CELLS = 4_000_000` ≈ 128 MB, above which we decline (`simplex.rs:74`) | Large. This is the structural reason our cap exists |
| **Markowitz-ordered tableau construction** | Yices scores `(a-1)(b-1)` and builds the initial tableau in that order, with Gaussian pre-elimination into a separate elim matrix (`matrices.c:1214-1220`, `2496-2547`, `2917-2985`); `simple_tableau_construction` (`:2793`) is the unused alternative | We minimize fill-in at *pivot* time (`simplex.rs:109-128`) but do not order the initial construction | Small-medium |
| **Six interpolation systems and a strength knob** | OpenSMT `SMTConfig.h:163-177`: McMillan / Pudlák / McMillan′ / PS / PSW / PSS for propositional; strong / weak / random for EUF; strong / weak / **factor ∈ (0,1)** / decomposing-strong / decomposing-weak for LRA. Plus proof restructuring for strength (`:939`) | One algorithm per fragment, no parameter (`solver.rs:305`) | Large, but the LRA half is small: our Farkas interpolant already has the multipliers a flexible interpolant needs |
| **Tree and sequence interpolation** | SMTInterpol `getInterpolants(partition, startOfSubtree)` (`SMTInterpol.java:848`), tree encoded in `mStartOfSubtrees` (`Interpolator.java:88-108`); OpenSMT `getPathInterpolants` (`InterpolationContext.cc:880`) and `getInterpolants(std::vector<vec<int>>)` (`InterpolationContext.h:30`) | Single A/B pair only (`solver.rs:243`, `:288-297`) | Medium. Our IMC/PDR consumers (`imc_lra.rs:340`, `imc.rs:280`) would use sequence interpolants directly |
| **Mixed AB-literal handling in EUF interpolation** | OpenSMT `splitEdge` / `colorCongruenceEdge` (`UFInterpolator.h:146-147`); SMTInterpol purification with auxiliary variables and the `@EQ` predicate (`Interpolator.java:71`, `:116`; `InterpolantPurifier.java`) | `euf_interpolant.rs:503`: `Color::Empty \| Color::Mixed => return None` | Medium. It is the difference between "declines on hard inputs" and "handles the general case" |
| **Interpolation derived from a proof rather than from a re-run** | SMTInterpol interpolates by walking the proof term (`Interpolator extends NonRecursive`, `getInterpolants(proofTree)`); OpenSMT walks the resolution proof graph (`InterpolationContext` over `ProofGraph`) | Our interpolators re-derive the refutation per fragment. The propositional one is the exception: it reads the LRAT proof (`axeyum-cnf/src/interpolant.rs`, McMillan 2003) | Large — but we already have Alethe emitters (12 modules) and a DRAT/LRAT core, so the input exists |
| **Per-proof-leaf interpolant checking** | SMTInterpol `checkInductivity` at every leaf (`InterpolantChecker.java:140`, called `Interpolator.java:394`) plus the final tree-property check (`:444`) | We check the final interpolant only (nine `verify_interpolant`-style functions) | Small, once proof-derived interpolation exists — it has no meaning without a proof to walk |
| **Five self-check modes wired as product options that fail the query** | SMTInterpol `:proof-check-mode`, `:model-check-mode`, `:interpolant-check-mode`, `:unsat-core-check-mode`, `:unsat-assumptions-check-mode` (`SMTInterpolConstants.java:43-48`); proof-check failure throws (`SMTInterpol.java:571-580`) | We check at the point of production, which is stronger for interpolants, but we expose no equivalent user-facing mode, and `just interpolant-certificate` is **not in `check.sh` or `just check`** (`08-models-proofs-and-evidence.md` §6) | Small. Wiring, not algorithm |
| **A standalone proof checker reading text** | SMTInterpol `proof/checker/Main.java` with its own JFlex/CUP grammar (`proofs.flex`, `proofs.cup`) and `CheckingScript.java`, taking a script file and a proof file | We have `check_drat`/`check_lrat` in-crate and drat-trim externally for the propositional layer, but no standalone checker for the *theory* proof format. `carcara_crosscheck.rs` and `lean_crosscheck.rs` skip-and-pass when the binary is absent (`11-wiring-and-integration.md`, gap 6) | Medium |
| **A specialized architecture per logic, selected statically** | Yices `api/context_config.c:189-217` maps each logic to a `context_arch_t`, so QF_LRA gets bare `CTX_ARCH_SPLX` with no egraph and no interface-equality machinery; QF_BV gets `CTX_ARCH_BV` | `check_auto` is a dynamic route ladder with fall-through, so a real query enters at route `nra` even when it is pure LRA (`04-arithmetic-theories.md`, "Route entry for real queries") | Medium. Cheap to measure first |
| **A modern SAT solver reachable as a delegate for the blasted CNF** | Yices `solvers/cdcl/delegate.c:164-213` — y2sat, CaDiCaL, CryptoMiniSat, Kissat, with preprocessing on for one-shot and off for incremental (`:60-65`) | Our CNF inprocessing exists and is **off by default** (`cnf_inprocessing: false`, `backend.rs:390`); the proof-carrying `inprocess.rs` has no caller (`11-wiring-and-integration.md`, gaps 1 and 2) | Small — it is a default, not an implementation |
| **A dedicated difference-logic solver selected by a measured heuristic** | Yices `solvers/floyd_warshall/` with `final_check ≡ FCHECK_SAT`, chosen by path bound / variable count / atom density (`context.c:6169-6262`) | `dl_online.rs` is Cotton–Maler and complete on its fragment, and runs ahead of everything (`auto.rs:4592`) — this row is closer to parity than most, except that we have **no oracle-differential fuzz for it at all** (`04-arithmetic-theories.md`, finding 1) | Small |

### We have, they do not

This table is genuinely short for interpolation and genuinely long for evidence.
Saying so is the point.

| Capability | Ours | Their status |
|---|---|---|
| **A machine-checkable proof for every unsat, in a standard format** | Alethe from 12 emitter modules (11,733 lines) with in-tree `check_alethe` and Carcara-vocabulary gating; DRAT/LRAT from the proof-producing CDCL core with an **independent** RUP+RAT checker (`check_drat`, ADR-0011) and drat-trim | Yices: **no proofs at all**. OpenSMT: a custom `(proof …)` s-expression checked only by its own `assert`-based `PGCheck.cc` and by re-solving with itself. SMTInterpol: a genuine small-core format with an in-tree and a standalone checker — this is the one row where SMTInterpol matches or beats us |
| **Kernel reconstruction into a proof assistant** | `int_reconstruct.rs` + submodules produce Lean `ExprId` terms that are `infer`-checked and `def_eq`-compared to `False` over the `IntPrelude` | None of the three. SMTInterpol's `resolute` format is a step in that direction but terminates at its own checker |
| **A self-checking miter tying the term level to the CNF level** | `bitblast_miter.rs` builds one AIG holding the production encoding and a separately coded reference bit-blaster, refutes the miter by DRAT, and escalates a failed proof check to `SolverError::Backend` (`:160-162`) | None |
| **Interpolant verification that gates the return value** | Nine `verify_interpolant`-style functions, always on, declining to `None` | OpenSMT's is opt-in and does **not** gate (`InterpolationContext.cc:857-871`). SMTInterpol's `:interpolant-check-mode` does gate, but is off by default |
| **Nonlinear real arithmetic with exact CAD and certificate producers** | `nra_real_root.rs` (8,207 LOC: Sturm chains, resultant elimination, recursive N-variable CAD) plus six certificate-producing modules with checkers (Handelman, monomial bound, Positivstellensatz degree-2, zero product, even power, univariate) | OpenSMT and SMTInterpol: no NRA (SMTInterpol's `checkCompleteness` returns `INCOMPLETE_THEORY` for any nonlinear variable, `LinArSolve.java:709-715`). Yices has MCSAT+LibPoly, which is a strong NRA engine — but it produces no certificate |
| **Strings and regex** | `07-strings-and-regex.md` — word equations, arrangements, derivative-based regex | None of the three |
| **Floating point** | `axeyum-fp` over the typed IR, generic in `(exp_bits, sig_bits)` (ADR-0023) | None of the three implements FP (SMTInterpol's `Logics` has an `FP` feature bit but `Clausifier.setLogic` has no FP branch) |
| **A fact ledger with two status axes and a semantic validator** | `artifacts/facts/` + `scripts/validate-facts.py` | Not a thing any of them attempts; not a solver feature |

Where they are ahead of us and it is *not* an algorithm: OpenSMT and SMTInterpol
both make proof/interpolation a **pre-initialization** decision and then disable
conflicting reasoning explicitly (OpenSMT skips substitutions under proof
logging, `MainSolver.cc:583`; skips cuts-from-proofs under interpolation,
`LASolver.cc:739`). We have no equivalent declaration, which means our
proof-producing routes and our fastest routes can silently be different code
paths — which is exactly what `11-wiring-and-integration.md` gap 3 records for
the two preprocessing pipelines.

## Not comparable

- **Yices2 versus us on proofs is not a gap in our favour that means anything
  competitively.** Yices does not produce proofs because SRI decided unsat cores
  over assumptions were the useful artifact for their consumers. Reading "we
  have proofs, Yices does not" as a lead misstates the axis: the correct
  statement is that Yices and we are optimizing different things, and Yices's
  performance is partly *bought* by not carrying proof obligations through the
  simplex, the egraph and the bit-blaster.
- **SMTInterpol timings are not comparable to ours, and neither are its
  constants.** It is Java. `Rational`'s `int`/`BigInteger` split, the DPLL
  engine's boxed `Literal` objects, and the absence of any inprocessing all
  reflect a design where the JVM sets the floor. A pivot-count comparison
  against `SOIPivoter` is meaningful; a wall-clock one is not.
- **SOI simplex versus the Dutertre–de Moura loop is not a "better rule".** SOI
  optimizes a global objective over all violated bounds and is a different
  algorithm with a different termination argument (`SOIPivoter.java:13-31`).
  Comparing our `bland_threshold` to SMTInterpol's plateau detection is a
  category error; the comparable pair is ours against Yices and OpenSMT, both of
  which are the same loop with different heuristics.
- **Yices's MCSAT is not on the same axis as anything we have.** It is a trail of
  first-order assignments with per-theory plugins (`mcsat/solver.c:929-936`),
  not CDCL(T). Our NRA route (`nra_real_root.rs`) reaches similar answers by
  entirely different means, and neither "we have CAD, they have MCSAT" nor the
  reverse is a comparison.
- **"No pivot cap" is not straightforwardly better.** Yices, OpenSMT and
  SMTInterpol can all spin unboundedly on a pathological instance and rely on an
  external clock. Our `MAX_PIVOTS` is a *deterministic* belt, and determinism is
  a public API promise here that none of the three makes (Yices explicitly
  refuses `:reproducible-resource-limit`). The honest framing is: they trade
  determinism for completeness at the limit, we trade completeness at the limit
  for determinism, and **SMTInterpol shows the third option** — a user-set
  clock-free counter (`ResourceLimit.java:62-68`) that gives both, at the cost of
  making the limit a caller's decision rather than a constant.
- **OpenSMT's parallel splitter cannot be compared to our portfolio.** It emits
  sub-problems for a distributed layer that is not in this repository
  (`src/parallel/` + a separate `opensmtSplitter` binary). Our
  `portfolio::FusedGroup` is in-process and runtime-dead by default
  (`11-wiring-and-integration.md`, gap 8). Two different things.
- **Yices's cut and propagation machinery cannot be read off the source
  structure.** Row propagation, model adjustment and periodic integer checking
  are all `false` by default (`api/search_parameters.c:116-118`);
  `simplex_propagator0.h` is never included; `simplex_prop_table.{c,h}` has zero
  consumers tree-wide; the multi-cut Gomory round is `if (false && …)`; iterated
  bound strengthening is inside `#if 0`. A feature-by-feature table built from
  file names would overstate Yices's shipped behaviour substantially. The stock
  configuration is: exact simplex + bound strengthening + integrality and
  Diophantine checks + branch atoms.

## Confidence

**Solid source reads** (I read the code, with the cited lines):

- Every simplex row in §F for all four solvers, including the pivot rules, the
  Bland triggers and the absence of pivot caps. The `while(true)` / `for(;;)`
  loops were read directly.
- The rational representations of all three, including OpenSMT's `goto overflow`
  path and `try_fit_word` demotion, and our own `narrow` boundary.
- OpenSMT's interpolation option surface, `FarkasInterpolator`'s five methods,
  `LIAInterpolator`'s `= delete` on the flexible variant, `UFInterpolator`'s
  strong/weak/random and `splitEdge`, and the three `getInterpolant` overrides
  that throw.
- That OpenSMT's interpolant check is opt-in and does not gate the return value
  (`InterpolationContext.cc:853-871` read in full).
- SMTInterpol's `ProofRules` axiom list, `MinimalProofChecker`'s existence and
  size, the standalone `proof/checker/Main.java`, the five check modes, and that
  `:proof-check-mode` throws.
- SMTInterpol's tree-interpolation API and `mStartOfSubtrees`, and both
  `InterpolantChecker` entry points.
- That SMTInterpol has no bit-blasting (read `Clausifier.setLogic`).
- Yices2 producing no proofs, and having MCSAT-only model interpolants.
- Our own `simplex.rs` comments citing Yices `SIMPLEX_DEFAULT_BLAND_THRESHOLD`
  (`simplex_types.h:908`), the `×100`/`×1000` size scaling
  (`simplex.c:4245-4250`) and the entering-variable score
  (`simplex.c:3878-3919`) — I verified all three against the clone. **No drift
  found**; our source comments about Yices are accurate.

**Grep-with-positive-control** (absence claims, each control named inline):

- Yices produces no proofs: `proof` matches 8 frontend files only; `drat|lrat`
  matches 4 "quadratic" substrings; control = real `unsat_core` code at
  `smt_core.c:3748-3867`.
- Yices's simplex never says unknown: `unknown` → 0 hits under
  `solvers/simplex/`; control = `unsat` → 105 hits.
- No floating point in Yices's arithmetic: 12 `double`/`float` hits under
  `solvers/simplex/`, every one accounted for as PRNG state, activity scores, or
  an English comment; 0 under `floyd_warshall/`.
- Yices has no MaxSAT/OMT: `maxsat|max_smt|objective` → 0; control = the
  `hill_climbing.c` hits the same alternation does return.
- OpenSMT has no Gomory cuts and no quantifiers: 0 hits each; control =
  `HermiteNormalForm` returns 3 real hits, `unsatcores/` is found.
- OpenSMT does not interpolate arrays or BV: 0 substantive hits under
  `tsolvers/arraysolver`/`bvsolver`; control = 10 files under `tsolvers/` do
  match `interpol`.
- SMTInterpol has no MaxSAT/OMT and no threads: the only matches are MUS
  enumeration and the logger lock.
- Our EUF interpolator declines on mixed edges: read the match at
  `euf_interpolant.rs:503`; control = 15 `vocab` hits in the same file.

**Inferences, marked as such:**

- "Three independent implementations chose to grow the number" is an inference
  about *design intent* from three code reads. The code facts are solid; the
  reading of them as a convergent decision is mine.
- The claim that Yices's speed on QF_LRA is *because of* the tagged rational is
  an architectural argument, not a measurement. I ran nothing. The four
  mechanisms in the summary are read from source; their relative contribution is
  not established here.
- "OpenSMT's `checkProof` is compiled out under NDEBUG" follows from every check
  being an `assert`; I did not read OpenSMT's build files to confirm `NDEBUG` is
  set in release. `[undetermined]` — next file: `CMakeLists.txt` and
  `cmake_modules/`.
- Whether Yices validates a SAT model in any default build path is
  `[undetermined]`; the sub-agent that read it flagged the same. Next file:
  `frontend/smt2/smt2_commands.c` around `check_delayed_assertions` (`:3229`,
  `:3610`).
- One **possible defect** in Yices, reported because it bears on the "no give-up
  path" claim and I could not settle it: on interrupt,
  `simplex_check_feasibility` returns `false` (`simplex.c:4254-4256`) without
  populating `expl_queue`, and `simplex_make_feasible` then calls
  `simplex_report_conflict` unconditionally (`:4749-4751`) — which would record
  an empty theory conflict unless the interrupt path always escapes by
  `longjmp` first. `[undetermined]` — next file:
  `context/context_solver.c` around the `setjmp` site and
  `simplex_solver_init_jmpbuf` (`context.c:6160`).
- The Yices sections other than §F were produced by a sub-agent reading the
  clone under the same rules and re-read by me only where they are load-bearing
  for a gap row. §F, all of OpenSMT and all of SMTInterpol I read directly.
