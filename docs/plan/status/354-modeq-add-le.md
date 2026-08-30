# Lane: modeq-add-le — close `F:ml430-nat-modeq-add-le-of-lt-c774015b`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, modeq-add-le, 2026-08-30).**

Closed the one fact `docs/plan/status/329-nat-modeq-mirrors.md` left open:
`F:ml430-nat-modeq-add-le-of-lt-c774015b`
(`Nat.ModEq.add_le_of_lt : a ≡ b [MOD m] → a < b → a + m ≤ b`).

## What the prior handoff got wrong about its own blocker

`329-nat-modeq-mirrors.md` sized this fact as needing "2-3 new
order/monotonicity lemmas" before the modEq-specific argument could even
start: an `Lt`-to-existence bridge (to extract witnesses from `a < b`) and a
`m*u > m*v → u > v` cancellation. Verifying in-tree found **neither was
needed**:

- This prelude's `Nat.modEq d a b := ∃ u v, a + d*u = b + d*v`
  (`nat_prelude/modular.rs`) is already an existence form — the hypothesis
  *hands over* witnesses `u, v` directly via `exists_rec`. There is nothing
  to bridge; `a < b` is used as-is (see below), not converted into a
  witness.
- `Nat.lt_of_mul_lt_mul_left : ∀ a b c, Lt (mul a b) (mul a c) → Lt b c`
  (`nat_prelude/mul_order_lemmas.rs`) already **is** the cancellation, and
  it needs no positivity side-condition — the handoff's guess that this was
  missing was exactly backwards: it was declared and tested (with a
  discriminating numeral instance) before this lane ever started.

So the fact closed with **zero new order/monotonicity lemmas** — only a
proof term composing what already existed.

## The proof (new file `crates/axeyum-lean-kernel/src/nat_prelude/modeq_add_le_of_lt.rs`)

Given witnesses `u, v` with `a + m*u = b + m*v` (destructured from the
hypothesis via the standard double-`exists_rec` idiom already used
throughout `modular.rs`) and `a < b`:

Detail moved to [`../notes/354-modeq-add-le.md`](../notes/354-modeq-add-le.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | modeq-add-le | Closes `F:ml430-nat-modeq-add-le-of-lt-c774015b` (`Nat.ModEq.add_le_of_lt`) with `Nat.mod_eq_add_le_of_lt`, composing only pre-existing order/monotonicity lemmas — the prior handoff's "2-3 new lemmas" estimate was verified wrong in-tree. `nat_prelude::` sweep 197 -> 198. |
