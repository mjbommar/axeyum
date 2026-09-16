# ADR-2132 — how the references decide to KEEP versus REBUILD, at `file:line`

Verified against `references/z3` at `e18d63bda04fcab8240eb55314d567db3e43d540`
(read from `.git/refs/heads/master`), the same revision [ADR-2125] cited. Every
range below was re-printed with `sed -n` and checked to cover a **complete**
function body.

[ADR-2125] established that the tableau is not trailed in z3, cvc5 or OpenSMT.
This lane's question is narrower and is the one its screen is an answer to:
**where does a reference decide whether keeping the basis is WORTH it?**

## 1. z3 never makes that decision, and the line that looks like it is a statistic

`lar_solver::find_feasible_solution()` is the whole "make this system feasible
again" entry point. Its complete body, `lar_solver.cpp:464-474`:

```cpp
lp_status lar_solver::find_feasible_solution() {
    stats().m_make_feasible++;
    if (A_r().column_count() > stats().m_max_cols)
        stats().m_max_cols = A_r().column_count();
    if (A_r().row_count() > stats().m_max_rows)
        stats().m_max_rows = A_r().row_count();
    flet f(settings().simplex_strategy(), simplex_strategy_enum::tableau_rows);
    get_core_solver().m_r_solver.m_look_for_feasible_solution_only = true;
    auto ret = solve();
    return ret;
}
```

**There is no branch on the problem's size, no rebuild, and no admission cap.**
It bumps three statistics and calls `solve()`.

The finding worth carrying forward is the trap in it. A reader grepping this
file for "does z3 refuse a system that got too big?" finds exactly one pair of
size comparisons — `lar_solver.cpp:468-469` — and they are `>` against a
**high-water mark**, `stats().m_max_rows`, which they then assign. A whole-file
search confirms it is the only one:

```text
grep -nE 'too_(big|large)|max_(rows|columns|cells)|> *[0-9]{4,}' lar_solver.cpp
  468:        if (A_r().row_count() > stats().m_max_rows)
  469:            stats().m_max_rows = A_r().row_count();
```

So the one size comparison in z3's linear-arithmetic solver **records** a size
and decides nothing. Ours, by contrast, has two structural refusals on the same
structure in two different currencies (`simplex.rs:2073` in dense cells,
`simplex.rs:2044` in nonzeros).

| claim | `file:line` |
|---|---|
| `find_feasible_solution()`, whole body — no rebuild, no size branch | `lar_solver.cpp:464-474` |
| the only size comparison in the file, and it writes a statistic | `lar_solver.cpp:468-469` |
| `solve()`, whole body — `solve_with_core_solver()` then clear the changed-bound set | `lar_solver.cpp:478-491` |
| `push()`, whole body — a trail scope and five sub-push calls; the tableau is not among them | `lar_solver.cpp:532-542` |
| `pop(unsigned)`, whole body — **four `SASSERT`s that the basis and heading are still correct**, and no restore of either | `lar_solver.cpp:567-605`, asserts at `:575-579` |
| the resume path patches only `m_columns_with_changed_bounds` | `lar_solver.cpp:1280-1283` |
| `init_run_tableau()` opens by ASSERTING the basis is set correctly, and returns before any pivot when the point is already feasible | `lp_primal_core_solver_tableau_def.h:256-269`, assert at `:256`, early return at `:260-261` |

`pop` is the sharpest of these. A solver that rebuilt after a pop would have the
restore right there; what is there instead is an assertion that nothing needs
restoring.

## 2. Ours, at the screen

| what | where |
|---|---|
| the lever, three-valued since ADR-2132 | `dpll_t.rs`, `warm_cube_mode` / `parse_warm_cube_mode` |
| the screen's state machine, one transition per entry | `dpll_t.rs`, `WarmCubeScreen::decider` |
| the threshold it consults | `dpll_t.rs`, `MIN_WARM_CUBE_SCREEN_BUILDS` |
| the count it reads, always on | `simplex.rs`, `cold_builds_so_far` / `bump_cold_builds` |
| the event both counters share | `simplex.rs`, `feasible_within_sparse` |
| the two dense/sparse admission doors on one structure | `simplex.rs`, `Incremental::with_policy` and `::with_nonzero_admission` |

**The asymmetry with z3 is the point of the ADR, not a defect list.** z3 has no
screen because it never pays for a rebuild: its basis survives every pop, so
"is keeping it worth it" is not a question its architecture can ask. Ours pays
for the rebuild on the offline route, so a decision exists — and the only
clock-free quantity available to make it with turns out not to separate the
population. See section 6 of the ADR.
