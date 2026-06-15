# Z3 core — architecture, SAT, DPLL(T), preprocessing, strategy

Top-down review of `references/z3/src/` (excluding per-theory solvers, which are
in [`z3-theories.md`](z3-theories.md)). Paths are exact.

## Z3 architecture map

Z3 source under `references/z3/src/` (C++/.h+.cpp line counts):

```
ast/        139k  Core term layer: AST manager, sorts/decls, interning.
  rewriter/  38k    theory rewriters (bv/arith/array/bool/seq/fpa) + th_rewriter aggregator
  sls/       21k    stochastic local search (SLS) over terms
  simplifiers/13k   dependent-expr "simplifier" pipeline stages (new preprocessing)
  euf/       11k    E-graph (egraph/enode/etable) + plugins (bv, arith, AC) + e-matching (mam)
  fpa/        6k    FP-to-BV expansion
  proofs/    ~3k    proof terms / proof checker hooks
math/        85k  LP simplex (lp/), polynomial, interval, dd (BDD/PDD), hilbert, grobner, subpaving
muz/         76k  Datalog/fixedpoint (Spacer/PDR) — out of scope
smt/         92k  Legacy DPLL(T) core: smt_context + theory_* solvers + congruence/relevancy
sat/         57k  CDCL SAT core + inprocessing; sat/smt/ = NEW SAT-integrated SMT (euf_solver)
util/        45k  vectors, hashtables, rationals, ema, allocators, params, reslimit
tactic/      36k  Tactic combinators + per-logic strategies (smtlogics/) + bv/arith/aig tactics
qe/          25k  quantifier elimination
nlsat/       15k  nonlinear CAD SAT
cmd_context/ 12k  SMT-LIB2 command interpreter, logic detection
opt/         10k  optimization (MaxSAT/OMT)
solver/       8k  solver trait, combined_solver, tactic2solver/solver2tactic, smt_logics
model/        7k  model representation + evaluation
```

Two relationships matter for axeyum:
- There are **two SMT cores**: the legacy `smt/smt_context.cpp` (DPLL(T) with its
  own boolean reasoning) and the modern `sat/smt/euf_solver.cpp`, a
  `sat::extension` plugged into the generic CDCL `sat::solver`. The new core
  reuses the SAT engine and an egraph in `ast/euf/`. axeyum's "BV→AIG→CNF→CDCL"
  path is architecturally closest to the **new** core's philosophy (one SAT
  engine, theories as extensions) — so the new core is the better port target.
- `tactic/` is the glue that turns a `(check-sat)` into a concrete engine via
  per-logic strategy scripts.

## SAT core

Files: `references/z3/src/sat/sat_solver.{h,cpp}` (4.8k cpp), `sat_clause.{h,cpp}`,
`sat_watched.h`, `sat_config.{h,cpp}`, `sat_simplifier.cpp` (2.1k), `sat_drat.cpp`
(794), `sat_proof_trim.cpp`, plus inprocessors
`sat_scc/elim_eqs/asymm_branch/probing/anf_simplifier/aig_finder/xor_finder/big/gc/cleaner`.

**Clause DB / arena** (`sat_clause.h`, `clause_allocator`): variable-length clause
objects in a `small_object_allocator` arena, referenced by a 32-bit
`clause_offset` (so a watch is 8 bytes on 64-bit). Two allocators support
defragmenting GC. Each clause stores `m_size`, `m_capacity`, an 8-bit `m_glue`
(LBD, capped 255), and a `var_approx_set` (64-bit Bloom signature for fast
subsumption). Split into `m_clauses` (irredundant) and `m_learned`.

**Two-watched literals** (`sat_watched.h`): a `watched` is a tagged 64-bit value
with kind `{BINARY, CLAUSE, EXT_CONSTRAINT}` in the low 2 bits. Binary clauses are
stored **inline in the watch list** (no clause object). CLAUSE watches carry a
blocked literal. `EXT_CONSTRAINT` is how theory plugins (new core, PB) hook
propagation. Propagation = `m_trail` + `m_qhead`.

**Branching** (`sat_config.h` `branching_heuristic`; `sat_solver.cpp`
`next_var`/`update_chb_activity`): **VSIDS** (default; `m_activity` +
`var_queue m_case_split_queue`, `decay_activity`/`inc_activity`) and **CHB**
(Conflict-History-Based, `m_step_size` decay, reward offsets). Phase saving via
`m_phase`/`m_best_phase` (phase-saving + target/best-phase rephasing). Theory
override hook `m_ext->get_case_split`.

**Conflict analysis** (`resolve_conflict_core`, ~line 2431): standard **1-UIP**
(count `num_marks` at current level until one UIP remains), build `m_lemma`, then
`minimize_lemma()` (recursive self-subsuming minimization), compute backtrack
level, assert. `decay_activity()` per conflict.

**Restarts** (`should_restart`/`do_restart`): `RS_LUBY`, `RS_GEOMETRIC`, `RS_EMA`
(Glucose fast/slow glue EMAs with `restart_margin`), `RS_STATIC`. Uses `util/ema`.
Partial restarts reuse the agreeing trail prefix.

**Clause deletion / GC** (`gc.cpp`): `GC_GLUE`, `GC_PSM`, `GC_DYN_PSM`,
`GC_GLUE_PSM`, `GC_PSM_GLUE`. PSM = progress-saving margin (learned-clause
literals agreeing with saved phases). `gc_small_lbd` clauses protected. Periodic
threshold + optional arena defrag.

**Inprocessing** (`sat_simplifier.cpp`): bounded variable elimination
(`elim_vars`, bounded resolution), subsumption + self-subsuming resolution
(`subsumes1`, via `var_approx_set`), blocked-clause elimination family
(BCE/ABCE/ACCE/CCE), bounded variable addition. Separate passes: SCC over the
binary implication graph (`sat_scc`) + equivalent-literal substitution
(`sat_elim_eqs`), asymmetric branching/vivification (`sat_asymm_branch`),
failed-literal probing (`sat_probing`), the binary implication graph
(`sat_big`), and AIG/XOR/ANF structure recovery
(`sat_aig_finder`/`sat_xor_finder`/`sat_anf_simplifier`). Also a
`sat_lookahead.cpp` cube-and-conquer solver and `sat_local_search`/`sat_ddfw` SLS.

**Proofs** (`sat_drat.{h,cpp}`): full **DRAT** emission; can run as an on-the-fly
RUP/RAT checker, dump to file, or keep in memory. `sat_proof_trim.cpp` trims.
Roughly at parity with axeyum's `axeyum-cnf` DRAT — but adds *trimming* and
*on-the-fly checking integrated with inprocessing* (each inprocessing technique
emits the matching DRAT/RAT steps — the hard part).

## SMT / DPLL(T) core

**Legacy core** `smt/smt_context.cpp` (4.9k): owns its own boolean assignment,
the E-graph, theory plugins, relevancy, conflict resolution; does *not* sit on
`sat::solver`.
- **E-graph** `smt_enode.h`: `enode` with union-find (`m_root`/`m_next`/
  `m_class_size`), congruence pointer `m_cg`, `m_parents`, `m_th_var_list`.
  `m_app2enode` maps app→enode; congruence table by `m_func_decl_id`;
  backtrackable via trail.
- **Theory interface** `smt_theory.h`: `internalize_atom/term`, `assign_eh`,
  `new_eq_eh`/`new_diseq_eh`, `relevant_eh`, `push/pop_scope_eh`, `final_check_eh`
  (the lazy expensive check → `FC_DONE/CONTINUE/GIVEUP`), `is_shared`, `mk_value`,
  `why_is_diseq`. Register via `register_plugin`.
- **Conflict resolution** `smt_conflict_resolution.{h,cpp}`: 1-UIP but antecedents
  can be `eq_justification`s (congruence/theory equalities); `eq_justification2literals`
  expands an equality proof into the causing literals.
- **Theory combination**: **model-based / dynamic** — shared vars by `is_shared`;
  proposes **interface equalities** between shared terms of equal value during
  `final_check` and case-splits on them ("assume-eqs"), not classical Nelson-Oppen.
- **Relevancy** `smt_relevancy.{h,cpp}`: only relevant atoms reach theories /
  e-matching / model construction. Distinctive Z3 mechanism, no axeyum analog.

**New core** `sat/smt/euf_solver.{cpp,h}` — `class solver : public sat::extension`.
The generic `sat::solver` does all boolean reasoning; `euf_solver` plugs in via
`EXT_CONSTRAINT`. Key overrides: `unit_propagate`, `propagated(literal, idx)`,
`get_antecedents(literal, idx, r)` (**lazy explanation**), `decide`,
`resolve_conflict`, `asserted`. The E-graph is `ast/euf/euf_egraph.{cpp,h}`
(egg-style delayed congruence reconstruction, `m_to_merge` queue, plugins
`euf_bv_plugin`/`euf_arith_plugin`/`euf_ac_plugin`, congruence timestamping).
Theory solvers (`bv_solver`, `arith_solver`, `array_solver`, `fpa_solver`, `q_*`,
`pb_solver`) are `th_euf_solver`s. Proofs: `euf_proof.cpp` + per-theory
`*_theory_checker` (e.g. `bv_theory_checker`, `arith_theory_checker`,
`distinct_theory_checker`) producing checkable theory-lemma certificates —
**exactly axeyum's "trusted small checking" model generalized to theories**. Also
`intblast_solver` (BV via integer blasting) and dynamic Ackermannization.

## Preprocessing & tactics

**Term rewriting** `ast/rewriter/`: `th_rewriter.h` dispatches per-sort rewriters:
`bool_rewriter`, `bv_rewriter` (constant folding, BV identities, slicing),
`arith_rewriter`/`poly_rewriter`, `array_rewriter` (read-over-write),
`seq_rewriter`, `fpa_rewriter`, `pb2bv_rewriter`/`card2bv`. The broad analog of
axeyum's `axeyum-rewrite` canonicalizer.

**Dependent-expr simplifier pipeline** `ast/simplifiers/` (the newer incremental
preprocessing used by `simplifier_solver`): each stage is a `dependent_expr_state`
transform tracking dependencies for unsat cores / model reconstruction. Notable
stages and why they matter:
- `propagate_values` — constant propagation.
- `solve_eqs`/`solve_context_eqs`/`extract_eqs` — Gaussian-style equation solving,
  substitute defined variables out (**huge win on QF_BV/LIA**).
- `elim_unconstrained` — remove variables appearing once / unconstrained.
- `bv_slice`, `bv_bounds_simplifier`, `bv_bounds`, `max_bv_sharing` — BV-specific:
  slice wide vectors, range reasoning, maximize subterm sharing before bit-blast
  (**directly improves axeyum's AIG sharing/size**).
- `eliminate_predicates`, `reduce_args_simplifier`, `euf_completion`,
  `der_simplifier` (DER for quantifiers), `bit_blaster`, `cnf_nnf`,
  `flatten_clauses`, `push_ite`, `elim_term_ite`.
- `model_reconstruction_trail.h` — keeps all of this model-sound (each elimination
  records how to reconstruct the value). axeyum's lowering/lift maps generalized.

**Tactics** `tactic/`: combinators in `tactical.h` (`and_then`, `or_else`, `cond`,
`when`, `using_params`, `repeat`, `par`). BV tactics: `bit_blaster_tactic`,
`bv1_blaster_tactic`, `max_bv_sharing_tactic`, `bv_size_reduction_tactic`,
`aig_tactic` (AIG compression before SAT), `ackermannize_bv_tactic`.
`sat/tactic/sat_tactic.h` hands the bit-blasted goal to CDCL.

## Strategy selection

`tactic/smtlogics/` holds one strategy per SMT-LIB logic (`qfbv_tactic.cpp`,
`qflia_tactic.cpp`, `qfufbv_tactic.cpp`, `qfaufbv_tactic.cpp`, `nra_tactic.cpp`,
`quant_tactics.cpp`, …). Flow: `cmd_context` reads `(set-logic L)`;
`smt_logics.h`/`check_logic.h` classify; `tactic/portfolio/default_tactic.cpp` +
`smt_strategic_solver.cpp` map logic→tactic, falling back to legacy `smt`.

Example — `mk_qfbv_tactic`: preamble `simplify → propagate_values → solve_eqs →
elim_uncnstr → bv_size_reduction → simplify → max_bv_sharing → ackermannize_bv`,
then a **probe-guided `cond` tree**: pure-eq BV → `bv1_blaster + smt`; normal
QF_BV → `bit_blast → (if under memory limit) simplify+solve_eqs+aig → sat`; else
`smt`. With proofs → `simplify → smt`; without → `psat`. Probes (`mk_memory_probe`,
`mk_const_probe(MEMLIMIT)`, formula-shape) make the choice **dynamic per
instance**. `solver/combined_solver.cpp` can run two solvers and switch on
incrementality/timeout; `tactic2solver`/`solver2tactic` bridge.

## Parity gap for axeyum (sized)

**SAT core**
- VSIDS/CHB branching + activity-ordered decision queue — *S/M* (`sat_solver.cpp`).
- Glue/LBD clause deletion + PSM strategies — *M* (`gc.cpp`).
- EMA/Luby restarts (Glucose fast/slow glue) — *S*.
- Phase saving + target/best-phase rephasing — *S*.
- Inline binary clauses + blocked-literal watches — *M* (`sat_watched.h` redesign).
- **SAT inprocessing: BVE, subsumption + self-subsuming resolution, SCC/eq-lit
  substitution, vivification, probing — *L*. The single biggest SAT-side win.**
- DRAT for inprocessing steps + proof trimming — *M*.

**Preprocessing (highest ROI for a bit-blasting solver)**
- Dependent-expr simplifier pipeline + model-reconstruction trail — *L* (the
  framework everything below needs; `ast/simplifiers/`).
- `solve_eqs`/`extract_eqs` — *M*, very high impact.
- `propagate_values` — *S/M*. `elim_unconstrained` — *M*.
- BV-specific: `bv_slice`, `bv_bounds`, `max_bv_sharing` — *M* each.
- AIG compression pass before CNF (`tactic/aig`) — *M*.
- Broader BV rewriter (full `bv_rewriter` identity set) — *M/L*.

**SMT/DPLL(T)** (once axeyum climbs past pure QF_BV)
- Standalone backtrackable E-graph (union-find + congruence + parents +
  per-node theory-var lists) — *L* (`ast/euf/euf_egraph.cpp`; the egg-style
  delayed-reconstruction design is the modern one to copy).
- Theory-as-SAT-extension architecture (`get_antecedents`/lazy explanations) —
  *L*, architecturally aligned with axeyum's CDCL (`sat/smt/euf_solver.h`).
- Conflict resolution over equality justifications — *M*.
- Relevancy propagation — *M* (optional, real lever).
- Model-based theory combination (interface equalities) — *M/L* (once ≥2 theories).
- Per-theory proof checkers (`bv_theory_checker`, …) — *M per theory*; the natural
  extension of axeyum's identity beyond CNF/DRAT.

**Strategy / assembly**
- Tactic combinators + probes + per-logic scripts — *M* (`tactic/tactical.h`,
  `tactic/smtlogics/qfbv_tactic.cpp`). Even a small `cond` tree (eq-only vs
  general BV vs fallback, gated on size/memory probes) is a real win.
- Logic detection + capability gating — *S* (`solver/smt_logics.h`).
