# Lane: nat-modeq-mirrors — close `ml430-nat-modeq` additive/multiplicative mirrors

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this pass`, nat-modeq-mirrors, 2026-08-30).**
6 of the 10 dispatchable `ml430-nat-modeq` mirrors closed; 4 left open with a
precise blocker each (below). `nat_prelude/modular.rs` already carries a full
`Nat.modEq d a b := ∃ u v, a + d*u = b + d*v` congruence family (refl, symm,
trans, add_left/right/both, mul_left/right/both, and `euler.rs`'s coprime
multiplicative cancel `mod_eq_cancel`) — none of it was wired to any fact
before this lane, and `F:ml430-nat-modeq-add-1561afa8` turned out to already be
exactly `Nat.mod_eq_add`, no new proof needed.

Closed (new file `crates/axeyum-lean-kernel/src/nat_prelude/modeq_add_cancel.rs`,
wired in right after `declare_gcd_comm`, since `mod_eq_cancel_left` needs
`gcd_comm`):

- `F:ml430-nat-modeq-add-1561afa8` — `Nat.mod_eq_add` (pre-existing, flip only)
- `F:ml430-nat-modeq-add-iff-left-b719aac5` — `Nat.mod_eq_add_iff_left`
- `F:ml430-nat-modeq-add-iff-right-84daa45f` — `Nat.mod_eq_add_iff_right`
- `F:ml430-nat-modeq-add-left-cancel-fb96581c` — `Nat.mod_eq_add_left_cancel`
- `F:ml430-nat-modeq-add-right-cancel-f0ab48e4` — `Nat.mod_eq_add_right_cancel`
- `F:ml430-nat-modeq-cancel-left-of-coprime-f89af373` — `Nat.mod_eq_cancel_left`
  (same content as `mod_eq_cancel`, coprimality's `gcd` argument order flipped
  via `gcd_comm` to match this mirror's `m.gcd c = 1` vs. `mod_eq_cancel`'s
  `gcd c n = 1`)

All five new theorems compose only already-checked lemmas
(`mod_eq_add_left`/`_right`/`_symm`/`_trans`/`mod_eq_add`/`gcd_comm`/
`mod_eq_cancel`) plus two `euler.rs` helpers exported `pub(super)` for this
purpose: `cancel_common_right_addend` (`modEq n (a+k) (b+k) → modEq n a b`,
needs no side condition — additive cancellation is easier than the
multiplicative case `mod_eq_cancel` needs Bezout for) and `rewrite_mod_eq`
(transport a `modEq` across an `Eq` on each endpoint). No new
existential-elimination term was written in this pass.

Detail moved to [`../notes/329-nat-modeq-mirrors.md`](../notes/329-nat-modeq-mirrors.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | nat-modeq-mirrors | `nat_prelude/modeq_add_cancel.rs`: 5 new theorems + 1 pre-existing flip close 6 `ml430-nat-modeq` mirrors (add, add_iff_left/right, add_left/right_cancel, cancel_left_of_coprime); 4 left open (add_le_of_lt, 3x cancel-div-gcd) with precise blockers recorded above |
