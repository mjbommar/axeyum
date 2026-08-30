# Lane: int-add-basics — nine `ml430` Int addition mirrors, all closed

<!-- plan-section: lane-status -->

**DONE for this dispatch (`int-add-basics`, 2026-08-29).**

## Task

Close nine `ml430` mirror facts for basic `Int` addition algebra:
`add_comm`, `add_left_cancel`, `add_left_comm`, `add_left_inj`, `add_left_neg`,
`add_mul`, `add_neg_cancel_left`, `add_neg_cancel_right`, `add_neg_eq_sub`.

## What already existed vs. what was built

Checked the full `Int` inventory first (`int_theorem_inventory`, no filter —
this example builds the whole `Int` prelude by default, no
`--include-constructed` flag needed or supported): 201 theorems, 0 asserted,
before this lane touched anything.

**Two of the nine already existed**, matched by rendered kernel type against
each fact's `formal.statement`, not by name:

- `Int.add_comm` — `algebra.rs`, exact match for `a + b = b + a`.
- `Int.add_neg_cancel_right` — `algebra.rs`, exact match for
  `a + b + -b = a`.

**The other seven did not exist** (confirmed absent by grepping the full
inventory for `add_left_*`, `add_mul`, `neg_eq_sub`, `neg_cancel_left` — none
present under any name), and were built in a new file,
`crates/axeyum-lean-kernel/src/int_prelude/add_basics.rs`:

Detail moved to [`../notes/303-int-add-basics.md`](../notes/303-int-add-basics.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | int-add-basics | Nine `ml430-int-add-*` mirrors closed: `add_comm`/`add_neg_cancel_right` already existed (evidence only); `add_left_neg`/`add_neg_eq_sub`/`add_left_comm`/`add_mul`/`add_neg_cancel_left`/`add_left_cancel`/`add_left_inj` newly built in `int_prelude/add_basics.rs`, all axiom-free, no `Int.rec` case split. |
