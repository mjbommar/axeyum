# Lane: draw9-first-theorems

## Status (2026-08-30)

Working the draw-9 refill (ADR-0830): 21 dispatchable ml430 mirrors across
`natural-distance` (Nat.dist) and `natural-bitwise-basics` (Nat.land via
`&&&`).

### Landed so far
- `F:ml430-nat-dist-comm-1fa29a04` -- flipped to proved. `Nat.dist_comm`
  already existed in `nat_prelude/dist.rs` (from the `nat-dist-nth` lane);
  this closed it by evidence only, no new proof.
- `F:ml430-nat-dist-self-0cfa5426` -- same: `Nat.dist_self` already existed,
  closed by evidence only.

### In progress / planned
- `and_le_left`, `and_le_right`, `and_comm`, `and_assoc` -- Mathlib's
  `Nat.and_*` (over `&&&`) reconciles to our existing `Nat.land_*`
  (`land_comm`, `land_assoc`, `land_le_left` already proved in
  `nat_prelude/rec_agreement.rs`); `land_le_right` is new (cheap, via
  `land_comm` + `land_le_left`).
- `dist_eq_zero`, `dist_add_add_left/right`, `dist_mul_left/right` -- new
  small proofs, using existing `mul_sub_left_distrib_total` and (for
  add_add) a new induction over `Nat.add`'s left operand.
- NOT attempting: `and_div_two`, `and_mod_two_eq_one`, `and_or_distrib_*`,
  `and_self`, `dist_pos_of_ne`, `dist_eq_intro`,
  `dist_triangle_inequality`, `fermat_primefactors_one_lt` -- each needs
  either genuinely new bitwise machinery or (Fermat) real number-theory
  content; out of scope for this lane's time budget. Left `open`.

See the final report for the authoritative outcome list.
