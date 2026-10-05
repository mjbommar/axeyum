# Lane: nat-log — `Nat.log` exists, so twenty blocked facts are now statable

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, nat-log, 2026-08-28).**

Twelve `nat.log` and eight `nat.clog` ledger facts were open behind a gap that
was not "unproved" but **unstatable**: neither `Nat.log` nor `Nat.clog` existed
in this kernel. `Nat.log` now does, with six theorems, all admitted through
`Kernel::add_declaration` with an empty `axiom_footprint`.

**The obstacle, and how it was cleared.** Mathlib v4.30 is
`Nat.log b n = if 1 < b ∧ b ≤ n then log b (n / b) + 1 else 0` — the recursive
call is at `n / b`, which is **not a constructor predecessor**, so this is not
structural recursion. Mathlib uses well-founded recursion; the Lean equation
compiler's route to that carries `Quot.sound`/`propext`, which would be fatal
to this project's headline metric (a sibling lane measured exactly that on
`Nat.gcd.eq_def` the same day).

The prelude already had the answer and it needed no new machinery:
`declare_executable_division` defines `Nat.div`/`Nat.mod` by structural
recursion carrying a rolling state. `Nat.log` uses the same device one level
up — **structural recursion on a FUEL argument**, instantiated at `n` itself,
which always suffices because the guard forces `2 ≤ b ≤ n` and therefore
`n / b ≤ n / 2 < n`:

```text
Nat.logAux b 0        n ≡ 0
Nat.logAux b (succ f) n ≡ if b ≤ n then (if 2 ≤ b then succ (logAux b f (n / b)) else 0) else 0
Nat.log b n           := Nat.logAux b n n
```

Both equations are **definitional** (β/δ/ι), so there are no equation lemmas
and nothing appeals to an axiom. **No `WellFounded`, no `Quot.sound`, no
`propext`, no new kernel machinery of any kind.**

**Two design points worth carrying forward.**

- *The guard's nesting order is load-bearing, and it is `b ≤ n` outermost.* The
  two cuts commute semantically but not for proof cost: only the outermost cut
  collapses the whole term with one rewrite. With `b ≤ n` outermost, `log_of_lt`
  is a single `Eq.rec`; nested, it would also need `bool_select c 0 0 = 0`, a
  case analysis on the *other* cut. Nothing is given up, because `ble zero y`
  reduces to `Bool.true` unconditionally, so the outer cut never blocks the
  base-`0`/base-`1` equations.
- *An exhausted fuel returns `0`, which is exactly what a wrong logarithm looks
  like.* So the computation test is the fuel-sufficiency check, not a nicety.

**What the kernel rejected: nothing.** All six declarations were accepted on the
first attempt, and `every_nat_declaration_is_checked_and_axiom_free` (which
reads `kernel.environment()`, not a list) is green over all of them.

**`Nat.clog` is reachable and is NOT a separate problem.** It is the same fuel
recursion with the step `clog b n = clog b ((n + b - 1) / b) + 1` under the same
`2 ≤ b ∧ 2 ≤ n` guard, so `Nat.ble_eq_false_of_lt` and the whole boundary-case
technique transfer verbatim. Its four boundary facts (`clog_zero_left`,
`clog_one_left`, `clog_zero_right`, `clog_one_right`) should be `refl` case
analyses exactly as here. The genuinely harder tier is the same for both:
`log_le_self`, `log_lt_self`, `log_mono_right`, `clog_pos`, `log_le_clog` need
`logAux b f n ≤ f` proved with the argument GENERALIZED in the motive
(`∀ n, logAux b f n ≤ f`), which is a real induction rather than a case split.

**Not attempted, deliberately:** the twelve `F:ml430-nat-log-*` mirror facts stay
`open`. Our `Nat.log` is a *different definition* from Mathlib's, so claiming
their statements is a reconciliation question (`artifacts/autogenesis/`
proposition-reconciliation pipeline), not a hand-written status flip. Flipping
them by hand would be the checker-that-cannot-fail defect.

**Pre-existing red, NOT mine:** `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` fails on
`examples/nat_numeral_whnf_probe.rs:105` (`many_single_char_names`), from
commit `ceff1cdfe`. `--lib --tests` is clean.

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-log | `Nat.log` by structural fuel recursion — 2 definitions, 6 theorems, all axiom-free; 6 facts closed; `Nat.clog` sized as reachable by the same route |
