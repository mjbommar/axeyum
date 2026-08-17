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
  `prove_by_nat_induction`) and gates on neither the induction route nor the
  front door ever contradicting a declared status.
- [`corpus_regression.rs`](../../../crates/axeyum-solver/tests/corpus_regression.rs)
  — picks these up with the rest of `corpus/regression/`, as a `check_auto`
  soundness gate. Most go `unknown` there, and they still do after the induction
  route was wired in: that gate calls `check_auto` (the quantifier-*free*
  dispatch) directly, while the induction rung lives in `solve`. So a change
  here shows up in the `nat_induction_corpus` table, not in this one.

## The three `unguarded_*` instances — the bug they caught, and its fix

The `unguarded_*` files are **not** ordinary benchmarks; they are the minimised
reproduction of a wrong verdict. `prove_by_nat_induction` used to answer `unsat`
on all three, and all three are `sat`.

The mechanism: the route stripped a leading `n >= 0` guard when the goal carried
one (`nat_induction.rs::strip_nonneg_guard`), but when the goal carried **no**
guard it proceeded anyway, discharging base and step over ℕ — while the SMT-LIB
quantifier ranges over `Int`. Any goal that is true on ℕ and false somewhere
below zero was therefore refuted although it is satisfiable.

`unguarded_int_nonneg.smt2` is the whole bug in one line and needs no
uninterpreted function at all:

```smt2
(assert (not (forall ((n Int)) (>= n 0))))
```

`n = -1` refutes `∀n. n ≥ 0`, so the negation is true and the set is `sat`. Base
(`0 ≥ 0`) and step (`k ≥ 0 → k+1 ≥ 0`) both discharge, so the route returned
`unsat`. z3 answers `sat`; axeyum's own `solve_smtlib` front door answers `sat`.

**Fixed in `a32280b6a`:** a recognised `n >= 0` guard is mandatory, and
`strip_nonneg_guard` returns `None` — a decline — for everything else. The three
rows are declines now, the four unique `unsat` decisions survive, and the
contradiction count is `0`.

**The route is now wired into [`solve`](../../../crates/axeyum-solver/src/auto.rs)**
as the last rung of the quantified ladder, so these three files stopped being a
quarantine notice and became a shipped-verdict gate: if the guard check ever
regresses, the front door itself answers `unsat` for a satisfiable set. The
`nat_induction_corpus` gate therefore checks the front-door column as well as
the route's own. Twenty-two further shapes around the guard condition — `<= n 0`,
`>= 0 n`, `>= n (- 5)`, a guard on a different variable, a vacuous `true` guard,
a one-argument `not` guard (which crashed the recogniser until the arity was
checked rather than assumed) — are in
[`tests/nat_induction_adversarial.rs`](../../../crates/axeyum-solver/tests/nat_induction_adversarial.rs).

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
