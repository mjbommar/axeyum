# Lane: draw9-first-theorems

<!-- plan-section: lane-status -->

## Status (2026-08-30) -- DONE for this session

Worked the draw-9 refill (ADR-0830): started at 21 dispatchable ml430
mirrors across `natural-distance` (Nat.dist) and `natural-bitwise-basics`
(Nat.land via `&&&`). Closed 11, left 10 open.

### Landed (11 facts flipped to proved, all kernel-lean, axiom_footprint: [])

Evidence-only (theorem already existed before this lane; confirmed rendered
type against `formal.statement` and closed by evidence):
- `F:ml430-nat-dist-comm-1fa29a04` -- `Nat.dist_comm`
- `F:ml430-nat-dist-self-0cfa5426` -- `Nat.dist_self`
- `F:ml430-nat-and-comm-7525d05a` -- reconciled to `Nat.land_comm`
- `F:ml430-nat-and-assoc-273b60d8` -- reconciled to `Nat.land_assoc`
- `F:ml430-nat-and-le-left-6d04acb7` -- reconciled to `Nat.land_le_left`

New theorems built this lane:
- `Nat.land_le_right` (transport of `land_le_left` via `land_comm`) ->
  `F:ml430-nat-and-le-right-a3f80076`
- `Nat.dist_eq_zero` (Eq.rec transport of `dist_self`) ->
  `F:ml430-nat-dist-eq-zero-5ae5b706`
- `Nat.add_sub_add_left` (new arithmetic helper, induction on the shared
  summand) + `Nat.dist_add_add_left` -> `F:ml430-nat-dist-add-add-left-92fa4403`
- `Nat.dist_add_add_right` (via `add_comm` reduction, no new arithmetic) ->
  `F:ml430-nat-dist-add-add-right-6e5d8bbb`
- `Nat.dist_mul_left` (via `mul_sub_left_distrib_total` + `left_distrib`) ->
  `F:ml430-nat-dist-mul-left-92624d63`
- `Nat.dist_mul_right` (via `mul_comm` reduction) ->
  `F:ml430-nat-dist-mul-right-d4e0c33d`

All six new theorems have concrete, discriminating evaluation tests
(`dist_draw9_additions_apply_at_concrete_discriminating_instances`,
`land_le_right_applies_at_free_variables_and_a_concrete_instance`) and are
registered in `theorem_names` for
`every_nat_declaration_is_checked_and_axiom_free`. `nat_prelude::` sweep:
227 passed, 0 failed (up from 225 before this lane).

### Left open (10) -- each needs more than this lane's budget

- `and_self`, `and_div_two`, `and_mod_two_eq_one`, `and_or_distrib_left/right`
  -- each needs genuinely new fuel-induction/per-bit-combine machinery of
  the same order as `land_comm`/`land_assoc` (which took a dedicated
  fuel-irrelevance construction). Not attempted.
- `dist_pos_of_ne`, `dist_eq_intro`, `dist_triangle_inequality` -- each
  needs a case split on `le_total`/trichotomy plus a `lt_of_le_of_ne`-style
  helper this prelude does not yet carry, and nontrivial algebraic
  rearrangement of the hypothesis in `dist_eq_intro`'s case. Sized as
  moderate-to-high effort; not attempted this session.
- `fermat_primefactors_one_lt` -- genuine number-theory content (Fermat
  number prime-factor structure via multiplicative order mod p); out of
  scope.

### Holdout isolation

Before: `held_out=136 files_scanned=1110 settled=0 references=0 PASS`.
After (final): `held_out=136 files_scanned=1110 settled=0 references=0
PASS`. Unchanged -- `natural-distance`/`natural-bitwise-basics` are
train/development, not held-out, and this lane never touched
`artifacts/autogenesis/`.

### Frontier

Start: 21 dispatchable. End: 10 dispatchable (11 closed).
