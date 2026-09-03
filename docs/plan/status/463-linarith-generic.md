# Lane: linarith-generic — `linarith` over an arbitrary `Alg.OrderedRing`

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, linarith-generic, 2026-09-03).** ADR-1584 §5
named three blockers to a `linarith` emitter generic over
`(R : Alg.OrderedRing)` instead of `NatPrelude`/`IntPrelude`. This lane
builds all three: (1) `Alg.add_le_add_right`/`le_of_add_le_add_right`/
`add_le_add`, derived generically from `OrderedRing`'s five order laws
(`crates/axeyum-lean-kernel/src/rat_prelude/ordered_ring_ext.rs`); (2)
`Alg.ofNat : OrderedRing -> Nat -> carrier` plus `ofNat_add`/
`ofNat_le_ofNat_of_le` (the latter gated on an explicit `zero <= one`
witness — not derivable from the five order laws alone, see the file's
module doc); (3) `linarith::generic`
(`crates/axeyum-lean-kernel/src/linarith/generic.rs`), a `≤`/`=` Farkas
emitter built only from `R`'s selectors and the ADR-1585 lemmas above, no
`IntDev`/`NatDev` anywhere. Scope is deliberately short of `linarith::int`:
no `<`, no literal multiplication (see the module's own doc comment for
why, and what the first stuck term is).

Status at commit time: (1) and (2) are landed and their own tests
(`ordered_ring_ext_tests`, 6/6) are green — see the SHA. (3) is WRITTEN and
compiles; its test module (`generic_tests`, 17 tests: 7 retirements against
`Int.orderedRing`, 3 new-capability goals at `Rat.orderedRing`, 3 false-goal
declines, 3 corrupted-certificate rejections plus a positive control) is
written but **NOT YET CONFIRMED GREEN** — `cargo test` on this module had
not been run before this commit, per the coordinator's instruction to
commit early rather than lose work to an interruption. Next step: run
`cargo test -p axeyum-lean-kernel --lib -- linarith:: --test-threads=4`,
fix whatever the compiler/kernel objects to, and update this block with the
real pass/fail count and the ms-per-term / delete-or-keep measurements the
brief also asks for (not started).

<!-- plan-section: landed-changes -->

| 2026-09-03 | linarith-generic | status stub |
