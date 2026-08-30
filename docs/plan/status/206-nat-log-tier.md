# Lane: nat-log-tier — the inductive tier above `Nat.log`'s boundary equations

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, nat-log-tier, 2026-08-28).**

`log.rs`'s own module doc, written the same day `Nat.log` first landed, named
the next obstacle precisely: `log_le_self`, `log_lt_self`, `log_mono_right`,
`clog_pos`, `log_le_clog` all need `logAux b f n <= f` proved with the VALUE
argument generalized inside the motive of an induction on the FUEL argument
(`fun f => forall n, Le (logAux b f n) f`), because the recursive call inside
`logAux b (succ f) n` is at `logAux b f (n / b)` — a *different* `n` than a
fixed-`n` induction's hypothesis would cover.

**`Nat.logAux_le_fuel` landed on the first kernel attempt**, plus
`Nat.log_le_self` (its `f := n` diagonal specialization, since
`log b n := logAux b n n` definitionally). Both axiom-free, both admitted
through `Kernel::add_declaration`, both covered by
`every_nat_declaration_is_checked_and_axiom_free` (environment-derived, not a
hand list) and by a new concrete-instantiation test at `(b, f, n) = (2, 8, 3)`
/ `(b, n) = (2, 8)` with a swapped-operand negative control.

**The motive generalization was exactly the whole difficulty**, not something
else on top of it — once stated, the two-case step (below) closed without a
second attempt. The technique already existed in this prelude:
`parity.rs`'s `declare_add_self_ne_succ_add_self` quantifies its own inner
variable inside an outer induction's motive the identical way (`d.pi_fv` for
the inner `∀`, built by the SAME closure that also computes the outer
`motive_at`).

**The proof, precisely:**
- *Base* (`f = 0`): `logAux b 0 n` is the constant-zero row, so the goal
  reduces to `Le 0 0`, closed by `Nat.le_refl`.
- *Step* (`f = succ m`, `ih : ∀ n, Le (logAux b m n) m`): reconstruct
  `logAux b (succ m) n`'s normal form exactly as `log_of_lt`'s step case
  already does (`log_aux(d, &p, base, predecessor, quotient)` — the kernel's
  own delta+iota unfold reaches the identical term), then case-split BOTH
  nested `Nat.ble` cuts with a new local helper, `le_of_bool_select`. It
  generalizes `log_of_lt`'s single-branch `bool_transport` technique two
  ways at once: to *both* branches of a cut (that proof only ever needed the
  refuted one), and to an inequality goal in place of an equation. Either
  cut false: the term is `0`, closed by `Nat.zero_le`. Both cuts true: the
  term is `succ (logAux b m (n / b))`, closed by `Nat.le_succ_succ` applied
  to `ih (n / b)`.

Detail moved to [`../notes/206-nat-log-tier.md`](../notes/206-nat-log-tier.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-log-tier | `Nat.logAux_le_fuel` (fuel-generalized-over-`n` induction) and `Nat.log_le_self`, both axiom-free; 2 facts closed; `log_lt_self`/`log_mono_right` sized as genuinely harder, not attempted |
