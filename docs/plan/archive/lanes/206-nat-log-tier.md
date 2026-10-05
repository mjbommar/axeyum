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

**What the kernel rejected: nothing.** Both declarations were accepted on the
first `Kernel::add_declaration` call. `cargo test -p axeyum-lean-kernel --lib
nat_prelude::` went from 99 passed / 1 failed (only the pinned
`the_build_is_deterministic` count, recomputed from its own panic message
430 -> 432, i.e. 69 defs + 363 theorems, never hand-incremented) to **101
passed, 0 failed** after adding the two theorem names to `theorem_names` and
one concrete-instantiation test.

**`log_lt_self`/`log_mono_right` were NOT attempted, and this is a finding, not
a shortfall.** The brief's framing ("if it goes well, these follow") does not
survive a quick semantic check: `logAux b f n < f` is FALSE in general even
restricted to the diagonal-adjacent case — e.g. `logAux 2 1 2 = 1`, and
`1 < f = 1` is false. `log_lt_self` needs the strict bound specifically at the
DIAGONAL fuel (`f = n`), which `logAux_le_fuel`'s fuel-generalized induction
does not give for free; it needs its own argument (plausibly strong induction
on `n` itself, or a route through `b ^ log b n <= n`), which is genuinely more
than a corollary. Scoped out rather than forced.

**Not touched, per scope:** `clog_pos`/`log_le_clog` (sibling lane owns
`Nat.clog`, which does not exist on this branch); the `F:ml430-nat-log-*`
mirror facts (still `open` — this lane's own `F:nat-logaux-le-fuel` /
`F:nat-log-le-self` are new, separate kernel-lean facts, not a hand flip of
the mirrors, per the standing rule against claiming a Mathlib statement
without a reconciliation route).
*(Corrected 2026-08-31, kernel-measured: `Nat.clog` now exists as a `nat`-
prelude `Definition`, landed by the sibling lane this paragraph deferred to.
"which does not exist on this branch" is a historical record of that branch,
not a live claim about the current tree.)*
<!-- was-absent: Nat.clog -- landed by the sibling lane this paragraph deferred to -->

**Gates run:** `rustfmt --edition 2024 --check` on all three touched files
(clean); `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`
(clean — needed one `#[allow(clippy::too_many_arguments)]` on the new
8-argument `le_of_bool_select` helper, matching the existing convention on
`or_cases`); `cargo test -p axeyum-lean-kernel --lib nat_prelude::` (101
passed, 0 failed); `python3 scripts/validate-facts.py` (1875 facts, 0
errors, both new facts counted as `proved`/`kernel-lean`).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-log-tier | `Nat.logAux_le_fuel` (fuel-generalized-over-`n` induction) and `Nat.log_le_self`, both axiom-free; 2 facts closed; `log_lt_self`/`log_mono_right` sized as genuinely harder, not attempted |
