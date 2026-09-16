# ADR-2125 — reference citations, verified line by line

Every range below was re-printed with `sed -n` before being written down, and
every range was checked to cover a **complete** function body rather than a
fragment. ADR-2122 found three of ADR-2111's z3 citations wrong — a function
name that does not exist, a range truncating a body mid-statement, and a claim
counting directions as bounds — so the range check is the point of this file, not
a formality.

Checkouts read (gitignored shallow clones under `references/`):

| repo | HEAD | cloned |
|---|---|---|
| z3 | `e18d63bda04fcab8240eb55314d567db3e43d540` | 2026-09-08 |
| cvc5 | `1689f13331f7543801f82d9dcbcaac2f70a26781` | 2026-09-08 |
| OpenSMT | `15b42c6f339679a4547d3cc9955547e7ca03505c` | 2026-09-08 |

## The claim under test

> The simplex **basis and tableau persist** across SAT decisions and backjumps;
> only bound assertions are trailed and undone on pop; the solve after a bound
> change resumes from the current basis.

**Confirmed in all three**, with one correction to this lane's own brief (§4).

## z3 — `src/math/lp/`

| claim | `file:line` | decisive text |
|---|---|---|
| `lar_solver::push()`, whole body | `lar_solver.cpp:532-543` | `m_imp->m_trail.push_scope(); … get_core_solver().push(); m_imp->m_constraints.push(); m_imp->m_usage_in_terms.push(); m_imp->m_dependencies.push_scope();` |
| `lar_solver::pop(unsigned k)`, whole body | `lar_solver.cpp:567-603` | `m_imp->m_trail.pop_scope(k); … get_core_solver().pop(k); … m_imp->require_nbasis_sort(); set_status(lp_status::UNKNOWN);` |
| the tableau is **not** pushed — pop only ASSERTS its invariants | `lar_solver.cpp:576-579` | `SASSERT(get_core_solver().m_r_solver.m_basis.size() == A_r().row_count()); SASSERT(… basis_heading_is_correct());` |
| `lar_core_solver::push()`, whole body — **two** things saved | `lar_core_solver.h:123-130` | `m_stacked_simplex_strategy = settings().simplex_strategy(); m_stacked_simplex_strategy.push(); m_column_types.push();` |
| `lar_core_solver::pop(unsigned k)`, whole body | `lar_core_solver.h:132-144` | `m_column_types.pop(k); m_r_x.resize(m_r_A.column_count()); … SASSERT(m_r_solver.basis_heading_is_correct());` |
| tableau / basis / heading are plain members, not `stacked_` | `lar_core_solver.h:23,29,32-38` | `static_matrix<mpq, numeric_pair<mpq>> m_r_A;` `vector<unsigned> m_r_basis;` `std_vector<int> m_r_heading;` |
| **`m_r_pushed_basis` exists and is DEAD** | `lar_core_solver.h:35` (sole hit in all of `src/`) | `stacked_vector<unsigned> m_r_pushed_basis;` |
| `find_feasible_solution()`, whole body — no rebuild | `lar_solver.cpp:464-474` | `get_core_solver().m_r_solver.m_look_for_feasible_solution_only = true; auto ret = solve(); return ret;` |
| the resume path: prefix, patch changed columns, pivot | `lar_solver.cpp:1286-1292` | `get_core_solver().prefix_r(); update_x_and_inf_costs_for_columns_with_changed_bounds_tableau(); get_core_solver().solve();` |
| only changed-bound columns are patched | `lar_solver.cpp:1280-1283` | `for (auto j : m_imp->m_columns_with_changed_bounds) update_x_and_inf_costs_for_column_with_changed_bounds(j);` |
| `prefix_r()` resizes cost vectors only | `lar_core_solver_def.h:37-44` | `m_r_solver.m_costs.resize(m_r_solver.m_n()); m_r_solver.m_d.resize(m_r_solver.m_n());` |
| an already-feasible point exits before any pivot | `lar_core_solver_def.h:85-95` | `if (m_r_solver.current_x_is_feasible() && … m_look_for_feasible_solution_only) { … return; }` |
| `lp_primal_core_solver::find_feasible_solution()`, whole body | `lp_primal_core_solver_def.h:228-233` | `this->m_look_for_feasible_solution_only = true; SASSERT(this->non_basic_columns_are_set_correctly()); … solve();` |
| the solve loop, whole body 92-154, resumes from the existing basis | `lp_primal_core_solver_tableau_def.h:92-154` | `init_run_tableau(); if (this->current_x_is_feasible() && …) { set_status(FEASIBLE); return 0; }` |
| `init_run_tableau()`, whole body — **asserts** the basis, does not build it | `lp_primal_core_solver_tableau_def.h:256-269` | `SASSERT(basis_columns_are_set_correctly()); … SASSERT(this->inf_heap_is_correct());` |
| the basis changes only by pivoting, in place | `lp_primal_core_solver_tableau_def.h:270-277` | `this->pivot_column_tableau(entering, …); this->change_basis(entering, leaving);` |
| bounds ARE trailed: `set_upper_bound_witness`, whole body | `lar_solver.cpp:922-931` | `m_imp->m_column_updates.push_back({true, j, get_upper_bound(j), m_imp->m_columns[j]}); m_imp->m_trail.push(imp::column_update_trail(*this->m_imp));` |
| `set_lower_bound_witness`, whole body | `lar_solver.cpp:933-942` | same shape with `false` |
| the undo restores **one bound and one column record** | `lar_solver.cpp:107-119` | `if (is_upper) m_imp.set_r_upper_bound(j, bound); else m_imp.set_r_lower_bound(j, bound); m_imp.set_column(j, column);` |
| `update_column_type_and_bound(...)`, whole body | `lar_solver.cpp:2299-2344` | dispatches to `..._with_ub` / `..._with_no_ub` |
| the trail and the changed-column set | `lar_solver.cpp:52`, `:61` | `trail_stack m_trail;` / `indexed_uint_set m_columns_with_changed_bounds;` |

**In prose.** `lar_solver::push` opens a trail scope and forwards to
`lar_core_solver::push`, which pushes exactly **two** things: the simplex-strategy
scalar and `m_column_types`. The matrix, the basis, the basis heading and the
bound vectors are plain members and are never snapshotted — `pop` *asserts* they
are still consistent with `A_r()` rather than rebuilding them. Bounds are the
only trailed simplex state. The next solve prefixes, patches only the columns in
`m_columns_with_changed_bounds`, and pivots from the surviving basis, whose first
act is `SASSERT(basis_columns_are_set_correctly())`.

**One trap recorded so a successor does not fall into it.**
`stacked_vector<unsigned> m_r_pushed_basis` is declared at
`lar_core_solver.h:35` and **referenced nowhere else in the entire `src/` tree**.
It is vestigial. A reader who greps for "is the basis pushed?" finds this
declaration and concludes the opposite of the truth. ADR-2111 already noted it;
it is repeated here because the name is the whole hazard.

## cvc5 — `src/theory/arith/linear/`

| claim | `file:line` | decisive text |
|---|---|---|
| `SimplexDecisionProcedure` holds the tableau by REFERENCE, a plain member | `simplex.h:98-101` | `/** … Tableau from the LinearEquality module. */ Tableau& d_tableau;` |
| its siblings likewise | `simplex.h:88,96,105` | `LinearEqualityModule& d_linEq;` `ArithVariables& d_variables;` `ErrorSet& d_errorSet;` |
| the owning tableau is a plain value on `TheoryArithPrivate` | `theory_arith_private.h:310-313` | `/** The tableau for all of the constraints seen thus far … */ Tableau d_tableau;` |
| `Tableau`/`Matrix` carry **zero** `context::`/`CDO`/`CDList` members | `linear/tableau.h`, `linear/matrix.h` | grep for `context::\|CDO\|CDList` returns nothing |
| the partial model gets the SAT context; the tableau is default-constructed WITHOUT one | `theory_arith_private.cpp:117`, `:122` | `d_partialModel(context(), DeltaComputeCallback(*this)),` … `d_tableau(),` |
| the bound journal is two context-dependent revert lists | `linear/partial_model.h:220-229` | `typedef context::CDList<AVCPair, LowerBoundCleanUp> LBReverts; LBReverts d_lbRevertHistory;` (+ the upper twin) |
| registered against the context in the constructor | `linear/partial_model.cpp:28-44` | `d_lbRevertHistory(c, true, LowerBoundCleanUp(this)), d_ubRevertHistory(c, true, UpperBoundCleanUp(this)),` |
| journalling on assert, whole bodies | `partial_model.cpp:711-715`, `:716-720` | `void ArithVariables::pushUpperBound(VarInfo& vi) { ++vi.d_pushCount; d_ubRevertHistory.push_back(make_pair(vi.d_var, vi.d_ub)); }` |
| pop restores **a bound and nothing else**, whole bodies | `partial_model.cpp:722-732`, `:734-744` | `if (vi.setUpperBound(c->second, prev)) { addToBoundQueue(x, prev); } --vi.d_pushCount;` |
| the cleanup functors are all the context invokes | `partial_model.cpp:809-812`, `:818-821` | `void ArithVariables::LowerBoundCleanUp::operator()(AVCPair& p) { d_pm->popLowerBound(&p); }` |
| the next solve resumes from the error set the bound reverts seeded | `dual_simplex.h:71-74`, `dual_simplex.cpp:55-66` | `Result::Status findModel(bool exactResult) override { return dualFindModel(exactResult); }` … `if (d_errorSet.errorEmpty() && !d_errorSet.moreSignals()) { … return Result::SAT; }` |

**In prose.** Backtracking is delegated wholesale to cvc5's `context::Context`:
whichever members are constructed *with* a context are backtracked, and the rest
are not. `d_partialModel` gets one; `d_tableau` does not. Inside `ArithVariables`
the backtrackable state is exactly two `CDList` journals of previous bounds; the
variable table itself is a plain vector. A pop runs the cleanup functors, which
restore one bound each and re-enqueue the variable. The tableau, the basis/
non-basis split, and every row are untouched.

## OpenSMT — the same split, third data point

| claim | `file:line` | decisive text |
|---|---|---|
| backtracking delegates entirely to the bound model | `Simplex.h:53-54` | `void pushBacktrackPoint() { model->pushBacktrackPoint(); }` `void popBacktrackPoint() { model->popBacktrackPoint(); }` |
| the tableau is a plain member | `Simplex.h:186` | `Tableau tableau;` |
| the model's backtrack is a bound trail | `LRAModel.cc:98-99` | `void LRAModel::pushBacktrackPoint() { bound_limits.push(bound_trace.size()); }` `void LRAModel::popBacktrackPoint() { popBounds(); bound_limits.pop(); }` |

## 4. A correction to this lane's own brief

**`TheoryArithPrivate::push` and `TheoryArithPrivate::pop` do not exist.** A grep
for any `push`/`pop` method DEFINITION across `src/theory/arith/` returns nothing.
The brief that opened this lane cited them by name, in the same sentence as
`SimplexDecisionProcedure`. The mechanism is real and is documented above — it is
`context::Context` membership, decided in the constructor's initialiser list —
but there is no such method to read, and a successor sent to find one would
spend the hour ADR-2122's lane spent on `try_add_bound`.

**Also NOT VERIFIED, and stated as such.** There is no explicit comment anywhere
in cvc5 saying "the tableau survives a pop". The claim rests on the structural
evidence above (no context-dependent members in `Tableau`/`Matrix`, plus the
constructor's split), which is stronger than a comment would be, but it is not a
quotation and is not presented as one.

## Ours, at `file:line`

| claim | `file:line` |
|---|---|
| the ONLINE engine is already warm — the tableau is built once, `assert`/`retract` move only row bounds | `crates/axeyum-solver/src/lra_online.rs`, `SimplexEngine::sync` / `LraTheory::feasibility` |
| ADR-2111 measured that: `simplex_cold_restarts=0` on every traced row | ADR-2111 §3.2 |
| the OFFLINE lazy-SMT loop re-decides each cube from scratch | `crates/axeyum-solver/src/dpll_t.rs`, `check_with_lra_dpll_within` → `decide_cube` |
| … which rebuilds the whole atom translation per cube | `crates/axeyum-solver/src/lra.rs`, `decide_within_with_options` → `Collector::collect` |
| … and allocates a fresh tableau per cube | `crates/axeyum-solver/src/lra.rs:1498` → `simplex::feasible_within_sparse` → `Tableau::new_sparse` |
| what this lane added: one theory per ENTRY, bounds diffed per cube | `crates/axeyum-solver/src/lra_online.rs`, `LraTheory::cube_check` / `SimplexEngine::sync_cube` |
| the changed-bound diff, z3's `m_columns_with_changed_bounds` shape | `SimplexEngine::sync_cube`, passes 2 and 3 |
