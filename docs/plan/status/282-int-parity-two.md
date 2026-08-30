# Lane: int-parity-two — the `ml430` division-by-two family

<!-- plan-section: lane-status -->

**Your lane's block (DONE, int-parity-two, 2026-08-29).** Ten freshly-dispatched
`ml430` mirrors; **7 closed, 3 left open**. None of the ten already existed
under a different name (checked `int_prelude/parity.rs`, the only prior
`Int.Even`/`Int.Odd` content, before starting — it had only the two
definitions and the two `natAbs` bridge theorems from the `int-parity` lane).
The `Nat` parity bridge (`Nat.even_iff_mod_two_eq_zero`,
`Nat.odd_iff_mod_two_eq_one`, `Nat.mod_two_eq_zero_or_one`) did transport, but
not by direct reuse of a `Nat`-side theorem name — each Int fact needed its
own `Int.rec` case split with the `Nat` lemma applied to the bound `Nat` field
of whichever branch, because `Int.Even`/`Int.Odd` are defined via `natAbs`,
not via a fresh `Int`-level existential (the `int-parity` lane's design
choice, module doc in `parity.rs`).

**Closed (all axiom-free, `derived_laws` 160 -> 168):**

Detail moved to [`../notes/282-int-parity-two.md`](../notes/282-int-parity-two.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | int-parity-two | 7 of 10 `ml430` division-by-two mirrors closed (`Int.emod_two_ne_zero`/`_ne_one`, `Int.ediv_two_mul_two_of_even`, `Int.ediv_two_mul_two_add_one_of_odd`, `Int.add_one_ediv_two_mul_two_of_odd`, `Int.odd_of_mul_left`/`_right`), all axiom-free; `even_add`/`even_add'`/`even_add_one` left open |
