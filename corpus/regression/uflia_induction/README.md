# `uflia_induction` — ℕ-induction goals over recursively-defined functions

Twelve flat, `:status`-annotated instances whose goals are universals over a
function pinned **only by its recursion equations**. That is precisely the shape
[`quant_valid_universal`](../../../crates/axeyum-solver/src/lib.rs) cannot
reach: `f(0) = 0` together with `∀k ≥ 0. f(k+1) = f(k) + 2` does not entail
`∀n ≥ 0. f(n) = 2n` by any *finite* instantiation, because nothing forces the
unrolling to reach every `n`.

Consumed by two harnesses:

- [`crates/axeyum-solver/tests/nat_induction_corpus.rs`](../../../crates/axeyum-solver/tests/nat_induction_corpus.rs)
  — measures each instance three ways (declared `:status`, `solve_smtlib`,
  `prove_by_nat_induction`) and gates on the induction route never contradicting
  a declared status.
- [`corpus_regression.rs`](../../../crates/axeyum-solver/tests/corpus_regression.rs)
  — picks these up with the rest of `corpus/regression/`, as a `check_auto`
  soundness gate. Most go `unknown` there (a coverage gap, correctly skipped).

## ⚠ Three instances currently expose a soundness bug

The `unguarded_*` files are **not** ordinary benchmarks; they are the minimised
reproduction of a wrong verdict. `prove_by_nat_induction` answers `unsat` on all
three, and all three are `sat`.

The mechanism: the route strips a leading `n >= 0` guard when the goal carries
one (`nat_induction.rs::strip_nonneg_guard`), but when the goal carries **no**
guard it proceeds anyway, discharging base and step over ℕ — while the SMT-LIB
quantifier ranges over `Int`. Any goal that is true on ℕ and false somewhere
below zero is therefore refuted although it is satisfiable.

`unguarded_int_nonneg.smt2` is the whole bug in one line and needs no
uninterpreted function at all:

```smt2
(assert (not (forall ((n Int)) (>= n 0))))
```

`n = -1` refutes `∀n. n ≥ 0`, so the negation is true and the set is `sat`. Base
(`0 ≥ 0`) and step (`k ≥ 0 → k+1 ≥ 0`) both discharge, so the route returns
`unsat`. z3 answers `sat`; axeyum's own `solve_smtlib` front door answers `sat`.

The route is **not** in `check_auto`'s dispatch, so no shipped verdict is
affected today. It must not be added until this is fixed. A fix has to make the
non-negativity hypothesis explicit rather than assumed: either decline goals
with no recognised guard, or conjoin `n >= 0` into the conclusion before
discharging.

## Ground truth

Every `:status` here is justified, not guessed.

- The six **`sat`** instances each carry a z3-verified explicit model.
  `unguarded_int_nonneg` z3 decides directly (`sat`). For the other five, z3
  stalls on the quantified recurrence under MBQI, so the model is supplied
  concretely — e.g. `f(x) = ite(x >= 0, 2x, -1)` satisfies `f(0) = 0` and
  `∀k ≥ 0. f(k+1) = f(k)+2` while making `f(-1)` negative — and z3 then confirms
  `sat` on the fully-defined script.
- The six **`unsat`** instances rest on SMT-LIB's `Ints` being a *fixed* theory
  with a single intended interpretation, not an axiomatisation: `Int` is ℤ, so
  the recurrence determines `f` on all of ℕ and induction is valid in every
  model. z3 returns `unknown`/`timeout` on all six — which is itself the value
  case for this route rather than a doubt about the status.

## Instances

| file | shape | `:status` |
|---|---|---|
| `guarded_linear_closed_form` | sum: `f(n) = 2n` from a `+2` recurrence | unsat |
| `guarded_linear_nonneg` | bound: `f(n) ≥ 0` | unsat |
| `guarded_monotone_step` | monotonicity: `g(n) ≥ 1` with a `+k` step | unsat |
| `guarded_parity_range` | parity: `p` alternates, so `p(n) ∈ {0,1}` | unsat |
| `guarded_sum_gauss` | sum: `2·s(n) = n(n+1)` (nonlinear step) | unsat |
| `guarded_product_factorial_bound` | product: `fact(n) ≥ 1` (nonlinear step) | unsat |
| `guarded_false_base` | control — base fails at `n = 0` | sat |
| `guarded_false_step` | control — base holds, step fails | sat |
| `guarded_wrong_slope` | control — right base, wrong slope | sat |
| `unguarded_int_nonneg` | **soundness probe** — no guard, no UF | sat |
| `unguarded_recurrence_nonneg` | **soundness probe** — no guard, over `f` | sat |
| `unguarded_int_even_or_odd` | **soundness probe** — no guard, over `h` | sat |

The three `guarded_false_*` / `guarded_wrong_slope` controls matter more than
the positive cases: a route that answered `unsat` unconditionally would pass
every positive instance here, so a false base, a false step, and a wrong slope
are each driven through and must be declined.
