# Lane: nat-bounded-cases — a bounded case eliminator for `Nat`, and the facts it unblocked

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this pass`, nat-bounded-cases, 2026-08-28).**
Built the requested eliminator and landed BOTH facts it was meant to unblock
— the brief's bar was "the eliminator plus ONE fact", so this is over that
bar, not merely at it.

- **`ops::cases_lt_bound`** (`nat_prelude/ops.rs`): `∀ n, Lt n bound → …`,
  peeled one numeral at a time via `le_of_lt_succ` + `lt_or_eq_of_le` (the
  same two lemmas `two_divisor_dichotomy`'s 2-way version already used),
  bottoming out at `bound == 1` via `zero_le` + `le_antisymm` rather than
  ever deriving the impossible `Lt n 0`. Branches each prove a STATIC fact
  at the literal `i`, transported up to `n` — the right shape when the
  conclusion genuinely varies with `n` (a computed property true at every
  point).
- **`ops::cases_lt_or_ge`**: splits a goal at a threshold `b` via
  `Nat.lt_or_ge n b`, handing off to separate `Lt n b` / `Le b n` handlers.
- **`ops::cases_lt_bound_absurd`**: the complementary shape discovered while
  proving the SECOND fact — a FIXED goal (doesn't vary with `n`), each
  branch instead receiving the witnessing equality `Eq n i` to derive a
  contradiction from an outer hypothesis about `n`. `cases_lt_bound`'s
  branches cannot do this (they prove `motive(i)` in isolation, with no
  access to `n`'s own hypotheses), so this needed to be a second combinator,
  not a parameter on the first. Also verified this shape reduces to only
  `le_of_lt_succ`/`lt_or_eq_of_le`/`zero_le`/`le_antisymm` — no `False.rec`
  needed even at the `bound == 1` base case.

Both closed facts:

Detail moved to [`../notes/230-nat-bounded-cases.md`](../notes/230-nat-bounded-cases.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-bounded-cases | `ops::cases_lt_bound`/`cases_lt_or_ge`/`cases_lt_bound_absurd` (general bounded-case infrastructure); `Nat.le_fib_add_one` and `Nat.Prime.five_le_of_ne_two_of_ne_three` (kernel-checked, axiom-free), closing `F:ml430-nat-le-fib-add-one-5284f0bf` and `F:ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786` |
