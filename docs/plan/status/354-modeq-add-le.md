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

1. `a < b` is *definitionally* `Le (succ a) b` (`Nat.lt` unfolds to exactly
   that), so it feeds directly into `add_le_add_left` where a `Le (succ a)
   b` argument is expected — the same trick `mul_lt_mul_pos_left_core`
   uses for its `pos : Lt zero a` hypothesis.
2. `add_le_add_left(m*u, succ a, b, hlt) : Le (m*u+succ a) (m*u+b)`, and
   `m*u+succ a` reduces to `succ(m*u+a)` BY REFL (`add` recurses on its
   right argument) — so this is already `Lt (m*u+a) (m*u+b)` up to defeq.
3. Commute `m*u+a` to `a+m*u` (the witness equation's LHS verbatim),
   substitute via the witness equation to `b+m*v`, commute `m*u+b` to
   `b+m*u`: `Lt (b+m*v) (b+m*u)`.
4. `le_of_add_le_add_left` cancels the shared `b`: `Lt (m*v) (m*u)`.
5. `lt_of_mul_lt_mul_left(m, v, u, ·) : Lt v u`, i.e. `Le (succ v) u`.
6. `mul_le_mul_left(m, succ v, u, ·) : Le (m*(v+1)) (m*u)`, and
   `m*(v+1)` reduces to `m*v+m` BY REFL (`mul_succ`).
7. Add `a` on the left, substitute back to `b+m*v` via the witness
   equation, regroup `a+(m*v+m)` to `(a+m)+m*v` via `add_comm`+`add_assoc`,
   cancel the shared `m*v` on the right (`le_of_add_le_add_right`) to reach
   the goal `Le (a+m) b`.

Wired in `nat_prelude.rs` as the very last `declare_*` call (after
`declare_fermat_number_all`) since it needs infrastructure from `order.rs`,
`mul_order_lemmas.rs`, and `modular.rs`, all far above.

## Tests

`nat_prelude_tests.rs`: registered `p.mod_eq_add_le_of_lt` in
`theorem_names` (caught by `every_nat_declaration_is_checked_and_axiom_free`
before I added it by hand) and added
`mod_eq_add_le_of_lt_applies_at_boundary_instances_free_variables_and_a_reversed_control`:

- tight case `(m,a,b)=(3,2,5)`, `b-a == m` exactly — catches an off-by-one.
- slack case `(3,2,8)`, `b-a == 2m`.
- a genuinely free `m,a,b` with fresh hypothesis fvars, checked via
  `Kernel::infer` — numerals reduce and can hide a defeq gap a concrete
  check alone would miss.
- reversed control `(3,5,2)`: `a ≡ b` holds but `a > b`. `Nat.ble (5+3) 2`
  computes to `false`, confirming the conclusion is **genuinely false**
  when `a < b` is dropped, not merely inapplicable — `a < b` is
  load-bearing, not decorative.

`cargo test -p axeyum-lean-kernel --lib nat_prelude::` → **198 passed** (was
197). `cargo fmt --edition 2024 --check` and
`cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D
warnings` both clean.

## Fact ledger

`epistemic_status: open → proved`. `kernel_theorem`/`kernel_statement`
recorded from `nat_theorem_inventory`, checked character-for-character
before flipping. `depends_on` populated by
`scripts/check-fact-depends-derived.py --fix` (7 edges, all pre-existing
lemmas — nothing new). `axiom_footprint: []`.
`python3 scripts/validate-facts.py` → 2222 facts, 0 errors. Both
`checker_command`s run by hand and verified to pass (and the first verified
to fail on a `_FABRICATED_NONEXISTENT`-suffixed name).

## Landed

- `crates/axeyum-lean-kernel/src/nat_prelude/modeq_add_le_of_lt.rs` (new)
- `crates/axeyum-lean-kernel/src/nat_prelude.rs` (module + field + wiring)
- `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs`
  (coverage registration + new test)
- `artifacts/facts/F-ml430-nat-modeq-add-le-of-lt-c774015b.json` (flipped)

<!-- plan-section: landed-changes -->

| 2026-08-30 | modeq-add-le | Closes `F:ml430-nat-modeq-add-le-of-lt-c774015b` (`Nat.ModEq.add_le_of_lt`) with `Nat.mod_eq_add_le_of_lt`, composing only pre-existing order/monotonicity lemmas — the prior handoff's "2-3 new lemmas" estimate was verified wrong in-tree. `nat_prelude::` sweep 197 -> 198. |
