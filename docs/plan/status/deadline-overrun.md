# Lane: deadline-overrun — the solver overran its own deadline

<!-- plan-section: lane-status -->

**The largest single undiagnosed bucket on the gap board was a watchdog kill,
and a watchdog kill is our bug, not a hard file** (`deadline-overrun`,
2026-09-12). A file ending at `timeout_ms + 1 s` means `smtcomp_cli`'s worker
thread did not return and the main thread had to kill it. A solver that returns
`unknown` at its budget is correct; one that has to be killed is not, and the
kill also loses the model, the proof and the evidence the run had produced.

**The size of it.** Censusing the 24 s three-way board
(`bench-results/session-20260911-smtlib/head-to-head/`) for files we return
`unknown` on, a reference decides, and whose wall time is ≥ 24.9 s: **149 across
the board**, and in `QF_UFLRA` **51 of the 54 addressable gap files** — 94% of
that division's `+54` against z3. z3 decides most of them in under 1.5 s, so
this was never a missing decision procedure.

**Two defects, both "a phase the budget cannot see".**

1. `dpll_t::Abstractor::abstract_term` recursed with no memo — a *tree* walk over
   a **DAG**, exponential in the sharing, on families (`cpachecker-induction`,
   `cpachecker-bmc`) that are almost entirely sharing — and `contains_real`
   re-traversed the whole subtree from every node on top of that. The phase
   consulted **no clock at all**.
   `cpachecker-induction.Problem01_00_true-unreach-call.c.smt2`, 24 s budget:
   **25.007 s unknown (killed) → 0.205 s unsat** (z3: unsat, 0.11 s).
2. `simplex::feasible` passed `tableau.run(`**`None`**`, MAX_PIVOTS)`.
   `Tableau::run` has always polled its deadline every 64 pivots and the
   `Incremental` engine passes a real one; the one-shot entry point — the whole
   `lra::simplex_fallback` route — passed the literal. Three more stretches of
   `lra::decide_within` (the tableau row build, `collect_constraints`, the Farkas
   multiplier matrix) took no deadline at all, and
   `dpll_lia::ArithAbstractor::order_atom` ran a **whole conjunctive decision**
   per *occurrence* of every atom to test fragment membership — **11,236**
   deadline-free `decide_within` calls in one 6 s run.

**The phase was found with instruments, not guesswork**: the route trail's
`lra_entries=0` (a counter that sits *after* the abstraction, so a zero is
positive evidence), then a frame-pointer `perf` profile, then a
`std::backtrace` probe. A DWARF-unwound profile of the same run produced no
caller frame at all — the recursion is deeper than the unwinder's limit.

**Still open, named rather than claimed.** The `cpachecker-induction.32_1_cilled…`
family still reaches the watchdog (25.02 s → 25.04 s). The residual is
`lra::solve` (Fourier–Motzkin, 21% of the profile, `memmove` 35%) on a path
whose deadline is still `None` above it — one more constant to find, not a new
kind of defect.

**Determinism.** Every poll added is inside `deadline.is_some()` or behind
`past_deadline(None)`, which reads no clock. A `resource_limit`-only run — the
reproducible-across-machines configuration — reads exactly as many clocks as
before and its verdicts are unchanged. For a run that *does* set a timeout, a
budget previously enforced only by killing the process is now enforced by the
solver: `unknown` **at** the budget instead of a verdict **after** it.

Full note:
[`../../research/03-measurements/watchdog-kills-are-a-deadline-blind-phase-2026-09-12.md`](../../research/03-measurements/watchdog-kills-are-a-deadline-blind-phase-2026-09-12.md).

<!-- plan-section: landed-changes -->

| 2026-09-12 | `c4046c2d6` | `dpll_t`'s Boolean abstraction: memoise `abstract_term` and `contains_real`, and give the walk the caller's deadline (read once per 256 freshly-expanded nodes, never when no timeout is set). Memoising is denotation-identical and preserves visit order, so `!lra_atom_N` numbering is byte-identical. Three mutation-controlled guards, each killing exactly one test; the real-sort guard is COUNTED, not timed — 6,004 pops on a 2,000-node chain against 6,011,004 for the shipped per-call re-traversal. |
| 2026-09-12 | `ee36e0421` | `simplex::feasible_within` takes the caller's deadline (the old entry point passed the literal `None` and is now a test helper); `lra::simplex_first`/`simplex_fallback`/`simplex_after_elimination` are threaded with it; `collect_constraints` polls per Boolean node (a per-assertion poll moved the wall time by 0.006 s, because the cube is ONE assertion); the Farkas multiplier-matrix loop polls per row. `dpll_lia::order_atom`'s fragment check is made once per distinct atom. Both new polls unconditional, not strided: `n` can be small while each item is expensive — ADR-1906's trap. Guard coverage stated precisely in the test's own doc comment: the simplex guard is individually mutation-killed, the four `decide_within` polls are not separable by one test. |
