# Lane: collision-gap — wiring `build_characterization` into the cross-prelude collision gate

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, collision-gap, 2026-08-27).**
[144-denominator](144-denominator.md) fixed `prelude_theorem_inventory.rs`'s
`build_groups` (it never called `build_characterization`, so 32 genuine,
axiom-free theorems were invisible to the theorem-count denominator) and
**found, but deliberately left alone**, the identical gap one layer over in
`crates/axeyum-lean-kernel/src/cross_prelude_collision_tests.rs`. This lane
verified that claim independently, then closed it.

**Confirmed the gap was real by reading the file, not by trusting the prior
report.** `cross_prelude_collision_tests.rs`'s `build_groups` built `logic`,
`nat`, `axreal`, `integer`, `rat`, `string`, `creal`, `complex`, `cpoint` —
nine groups — and never called `build_characterization`, despite its own
module doc claiming the function "mirrors `examples/prelude_theorem_
inventory.rs`'s `build_groups`: same prelude list, same dependency order".
That comment was wrong for as long as the gap existed. Consequence: the 32
`Nat.Peano.*`/`Int.Characterization.*` declarations had never been checked
by [`cross_prelude_collisions`] for a name clash against any other prelude —
a DIFFERENT question from the theorem-count gap 144-denominator fixed, since
collision-checking spans every `Declaration` kind (definitions included),
not only theorems.

Detail moved to [`../notes/146-collision-gap.md`](../notes/146-collision-gap.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | collision-gap | Wired `build_characterization` into `cross_prelude_collision_tests.rs`'s `build_groups` at the same dependency-order position the other two theorem/declaration inventory tools use; confirmed no cross-prelude name collision exists for the 32 `Nat.Peano.*`/`Int.Characterization.*` declarations. Extended `scripts/check-theorem-inventory-completeness.py` with a three-way prelude-group-label agreement check (`kdp_prelude_labels`/`pti_prelude_labels`/`collision_group_labels`/`check_group_labels`) so a fourth prelude group omitted from any of the three `build_groups` implementations fails loudly instead of silently; 9 new unit tests (20 total), all 6 new guards mutation-verified with no survivors after fixing a stale-`__pycache__` false-kill in the mutation sweep itself. |
