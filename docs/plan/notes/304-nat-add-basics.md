# Notes: 304-nat-add-basics

Detail moved out of [`../status/304-nat-add-basics.md`](../status/304-nat-add-basics.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

`declare_add_eq_lit_iff(d, p, name, k)` in the new
`crates/axeyum-lean-kernel/src/nat_prelude/add_basics.rs` closes all three,
parameterized only by the literal `k`:

- **mp** (`add m n = k -> disjunction`): bound `m <= k` via `le_add_right` +
  `Eq` transport along the hypothesis, then walk `lt_or_eq_of_le` /
  `le_of_lt_succ` down from `k` to `0` (the same bounded-case-split idiom
  `choose.rs`/`min_fac.rs`/`desc_factorial.rs` already use in this prelude).
  Each `Eq` leaf recovers the matching `n` via `add_left_cancel` and is placed
  into the right-associated `Or` at position `i`; the final `Lt m 0` leaf is a
  contradiction via `not_lt_zero`.
- **mpr** (`disjunction -> add m n = k`): walks the same `Or` shape via a
  private `or_elim` and closes each branch's concrete arithmetic identity by
  `Eq.refl` (small numerals fully reduce by defeq -- `add (num i) (num (k-i))`
  and `num k` share a normal form).

`or_elim`/`absurd` are private per-file copies of the non-dependent
`Or.rec`/`False.rec` wrappers this repository already carries in several
other `nat_prelude` files (documented convention, not a new shared helper).

`Nat.add_eq`'s statement (`x.add y = x + y`) is trivial in this kernel: there
is one `Nat.add` function and no separate `+` notation layered over it, so it
closes by `Eq.refl (add x y)`.

## Dispatch order

`declare_add_basics` runs in `build_nat_prelude_uncached` right after
`declare_order_more`, i.e. after `declare_additive_theorems` (`add_comm`/
`add_assoc`/`add_zero`/`zero_add`/`add_left_cancel`/`add_right_cancel`),
`declare_add_no_zero_summands` (`add_eq_zero`), `declare_order`
(`le_add_right`/`lt_or_eq_of_le`), `declare_no_confusion` (`not_lt_zero`), and
`declare_order_extra` (`le_of_lt_succ`) -- all its dependencies exist by then.

## Checks run (all foreground, all green)

- `scripts/cargo-serialized.sh check -p axeyum-lean-kernel`
- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib nat_prelude::`
  -- **173 passed, 0 failed** (matches the baseline the brief named; no test
  count regression, and the new declarations are exercised by
  `the_build_is_deterministic`, `every_promised_name_is_admitted_with_the_
  expected_kind`, and `every_nat_declaration_is_checked_and_axiom_free`,
  all environment-derived, per the standing "count the list, verify against
  the environment" rule)
- `rustfmt --edition 2024 --check` on the three touched files
- `scripts/cargo-serialized.sh clippy -p axeyum-lean-kernel --all-targets --
  -D warnings`
- `python3 scripts/check-test-attribute-integrity.py` -- 0 findings
- `python3 scripts/validate-facts.py` -- 0 errors
- `python3 scripts/check-fact-depends-derived.py --fix`, re-validated after

The `the_build_is_deterministic` pin moved `93 + 559` -> `93 + 567` (8 new
theorems), taken from the panic message itself (`left: 660`), not by
incrementing.

Every new `checker_command` verified both directions by hand: greps to
`-ge 1` on the real declared name, `0` on a `_bogus` suffix of the same name.

## Files touched

- `crates/axeyum-lean-kernel/src/nat_prelude/add_basics.rs` (new)
- `crates/axeyum-lean-kernel/src/nat_prelude.rs` (8 new `NameId` fields,
  `mod`/`use`/dispatch wiring -- small, additive)
- `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` (8 new
  entries in `theorem_names`, pin update)
- `artifacts/facts/F-ml430-nat-{add-assoc,add-comm,add-add-add-comm,add-eq,
  add-eq-left,add-eq-right,add-eq-zero,add-eq-one-iff,add-eq-two-iff,
  add-eq-three-iff}-*.json` (status flip + evidence)
- 120 other fact files (`depends_on` edges added by
  `check-fact-depends-derived.py --fix`, a side effect of `add_assoc`/
  `add_comm` flipping to `proved`: every already-proved fact whose proof term
  directly uses `Nat.add_assoc`/`Nat.add_comm` now gets an edge to the newly
  `proved` `F:ml430-nat-add-{assoc,comm}-*` facts)

## Not pushed

Per instructions, this lane did not run `just check`/the workspace gate or
push; commits are on the lane branch, ready for the coordinator's merge and
full-gate pass.
