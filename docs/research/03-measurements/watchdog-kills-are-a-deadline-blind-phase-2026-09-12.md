# The watchdog bucket is a deadline-blind phase, twice over

**2026-09-12, lane `deadline-overrun`.** A file that ends in a **watchdog kill**
means `smtcomp_cli`'s solver worker thread did not return within its budget and
the main thread had to kill it at `timeout_ms + WATCHDOG_GRACE` (1 s). That is
not a solver that ran out of time — a solver that returns `unknown` at its
budget is correct. It is a solver that overran its own deadline, and a killed
run loses the verdict, the model and any evidence it had produced.

## The size of the bucket

Censusing `bench-results/session-20260911-smtlib/head-to-head/`, the 24 s
three-way board, for files we return `unknown` on and a reference decides, whose
wall time is ≥ 24.9 s (i.e. budget + grace):

| division | watchdog / addressable gap |
|---|---:|
| **QF_UFLRA** | **51 of 54** |
| QF_LIA | 28 |
| QF_IDL | 19 |
| QF_UFLIA | 14 |
| QF_NIA | 7 |
| QF_LRA | 6 |
| QF_RDL | 6 |
| UF | 6 |
| QF_NRA | 5 |
| QF_S | 3 |
| QF_BV, QF_SLIA | 2 each |
| QF_ABV, QF_DT, QF_FP, QF_UF | 0 |

**149 files across the board**, and in `QF_UFLRA` it is 94% of the whole
addressable gap. The division's `+54` against z3 is therefore almost entirely
this, not a missing decision procedure — z3 decides most of these files in under
1.5 s.

## Finding the phase — instruments, not guesswork

Three instruments in sequence, each narrowing the last:

1. **The route trail** (`--trace`) put 8.8 s of a 9 s run in the *unattributed
   open segment* after `nra-real-root` declined, with `lazy-smt
   reading=not-reached` and `lra_entries=0`. `lazy_smt_counters::record_entry`
   sits directly **after** the Boolean abstraction in
   `dpll_t::check_with_lra_dpll_within`, so a zero there is positive evidence
   the abstraction never finished.
2. **A frame-pointer `perf` profile** named it: every captured stack is
   `Abstractor::abstract_term` ↔ `Abstractor::rebuild_binary`, reached through
   `auto::check_auto → nra::check_with_nra → check_with_lra_dpll_within`.
   (A DWARF-unwound profile of the same run could not produce a single caller
   frame — the recursion is deeper than the unwinder's limit. Build with
   `RUSTFLAGS="-C force-frame-pointers=yes"` for this kind of question.)
3. **A `std::backtrace` probe** on the second family, printed from
   `lra::decide_within` when its deadline was `None`, gave the exact chain.

## Defect 1 — a tree walk over a DAG that read no clock

`dpll_t::Abstractor::abstract_term` recursed with **no memo**, so a subterm
reachable by k paths through the assertion DAG was rebuilt k times. On the
`cpachecker-induction` / `cpachecker-bmc` families — formulas that are almost
entirely sharing — that does not terminate in any budget. On top of it,
`contains_real` was called once per node of that walk and allocated a fresh
`HashSet` and re-traversed the whole subtree every time.

And the phase consulted **no clock at all**: it ran to completion or the process
watchdog killed the worker.

Fixed in `c4046c2d6`: memoise both walks, and give the abstraction the caller's
deadline (read at most once per 256 freshly-expanded nodes, and not at all when
no timeout is configured). Memoising is denotation-identical and preserves visit
order, so the `!lra_atom_N` numbering is byte-identical.

    cpachecker-induction.Problem01_00_true-unreach-call.c.smt2, 24 s budget
      before  25.007 s  unknown (watchdog kill)
      after    0.205 s  unsat            (z3: unsat, 0.11 s)

## Defect 2 — the deadline argument was a constant

The second `QF_UFLRA` family (`cpachecker-induction.32_1_cilled…`) reaches the
watchdog through a different chain, on the stack for 1,065 of 1,082 samples:

    auto::dispatch_uf_routes
      → euf::try_lazy_arith_for_overbound
      → euf::check_with_uf_arithmetic_lazy
      → dpll_lia::IncrementalArithDpll
      → dpll_lia::theory_conflicts_for_indices
      → lra::check_with_lra_within_certified
      → lra::decide_within

Four stretches of it could not see the budget (`ee36e0421`):

- **`simplex::feasible` passed `tableau.run(None, MAX_PIVOTS)`.**
  `Tableau::run` has always taken a deadline and polls it every 64 pivots; the
  `Incremental` engine passes a real one. The one-shot entry point — the whole
  `lra::simplex_fallback` route — passed the literal. This is **ADR-1906's shape
  with the polarity reversed**: there the counter could not be reached, here the
  counter was fine and the *argument* was the constant.
- `lra::simplex_first` / `simplex_fallback` / `simplex_after_elimination` took
  no deadline at all, so the dense `n × nvars` exact-rational tableau build
  (42% of a killed run's profile is `memmove`) was unbounded.
- `lra::collect_constraints` polled nothing, and `Collector::collect` descends
  through `and`/`not` structure — so a refinement loop handing it **one**
  assertion that is a conjunction of thousands of atoms gets exactly one check
  from a per-assertion poll. Measured: making that poll fire every iteration
  moved the wall time by **0.006 s**. The poll now lives on the collector and
  fires per Boolean node.
- The Farkas multiplier-matrix loop (`unit_vec(n, i)`, the `32·n²` bytes
  `fm_admission` prices) polled nothing.

Both new polls are **unconditional rather than strided**: `n` can be small while
each item is expensive, which is exactly the ADR-1906 trap.

Separately, `dpll_lia::ArithAbstractor::order_atom` ran a **whole conjunctive
decision** (`check_with_lra` — collection, Fourier–Motzkin, simplex) per
*occurrence* of every atom, purely to test fragment membership, with no
deadline: **11,236** such calls on one-assertion systems in a single 6 s run.
`atom_of` already keys the proposition by the same canonical term, so the check
is now made once per distinct atom.

## What is still open

The `32_1_cilled…` family still reaches the watchdog: 25.02 s before, 25.04 s
after, at a 24 s budget. The residual is `lra::solve` (Fourier–Motzkin, 21% of
the profile, `memmove` 35%) reached on a path whose deadline is still `None`
above it. `solve` and `eliminate` both poll correctly **when given a deadline**,
so this is one more `None` to find, not a new kind of defect. Named and
measured, not claimed as fixed.

## Determinism

The public promise is that `resource_limit` is reproducible across machines
while `timeout` is not. **Every poll added here is inside
`if deadline.is_some()` or behind `past_deadline(None)`**, and
`axeyum_ir::stop::past_deadline(None)` reads no clock — so a run configured with
a resource limit and no timeout reads exactly as many clocks as before, and its
verdicts are unchanged.

For a run that *does* configure a timeout, the change is that a budget which was
previously enforced only by killing the process is now enforced by the solver.
A caller with no external watchdog would previously have received a verdict
*after* its stated budget; it now receives `unknown` *at* it. That is the
correct reading of `timeout`, and it is the same contract every other deadline
in this tree already honours.

## The pattern worth carrying

Three instances now, and they are all one shape — **a phase the budget cannot
see**:

- ADR-1906: a deadline tested every 1,024 *conflicts*, in a search that burns
  its budget under 256.
- 2026-09-11: `route_solo --timeout-ms` does not bound parsing.
- Here: a phase with no clock at all, and a phase whose clock argument is the
  literal `None`.

The check that finds them is not "does this function take a deadline" — all four
`lra` functions above are reached from one that does. It is: **for each stretch
of work that can take seconds, name the poll that bounds it.** A stride is only
safe when the counter is proportional to the work; a per-item poll on a loop
whose single item is the expensive thing bounds nothing.
