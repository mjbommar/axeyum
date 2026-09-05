# Lane: hall-theorem — the loop bound decides the inclusion test, and both branches of Hall's split landed

<!-- plan-section: lane-status -->

**Hall's critical-subset split is proved on both sides; the strong induction
that composes them is not** (`WIP`, hall-theorem, 2026-09-05, ADR-1644).

The previous lane (ADR-1630) sized the remainder as one missing lemma plus
bookkeeping, and the sizing was right about the lemma and wrong about the
bookkeeping. `Nat.Finset.allBelow_congr` was indeed absent — measured at 3,222
declarations with a freshly built `shape_search`, `--const
Nat.Finset.allBelow_congr` UNANSWERABLE against the positive control
`--name-like allBelow` → FOUND 4 — and it is a third KIND of law: `allBelow`'s
three existing laws all relate a loop to its predicate's values, and none
relates two loops to each other.

The reason it is needed is not the mathematics but
`Nat.Finset.forallSubset_of_search`'s congruence premise. `subsetB t s` — the
natural spelling of `t ⊆ s` — loops to `bound t`, which CHANGES with the
quantified argument, so two sets with the same members and different stored
bounds get different loop lengths and the premise is unprovable. The rule this
generalises to, and the reason it belongs in an ADR rather than a code comment:
**every loop bound inside a predicate handed to `forallSubset_of_search` must be
independent of the quantified set.** `Nat.Finset.subsetFixed` takes its bound
from the fixed set and pays for it with a `Lt i (bound s)` hypothesis on the
elimination rule only.

Ten declarations landed, all admitted axiom-free, all registered in
`nat_prelude_tests::definition_names`/`theorem_names` and swept. Both branches of
the split are proved: `hallCondition_sdiff_of_critical` (the deleted-family
branch, whose counting chain closes through a NEW vanishing lemma —
`memB_unionOver_union_of_vanishing` — because the two unions' stored bounds
differ) and `hallCondition_sdiff_singleton_of_strict` (the one-value-deleted
branch, whose successor step is definitional: `Nat.add` recurses on its right
argument so `add x 1` IS `succ x`).

`card_union_of_disjoint` needed no new counting lemma and no `memB_inter`:
`card s` and `sum s (fun _ => 1)` unfold to the same `Nat.rec`, so
`Nat.Finset.sum_union_disjoint` at the constant `1` already IS the statement.
That was found by reading two `Nat.rec` bodies, not by searching for a name, and
no `--const` query would have surfaced it.

**`Nat.Hall.sufficient` and `Nat.Hall.marriage_iff` did NOT land.** Three sized
obstructions, none of them the counting or congruence problem the last three
ADRs were about: (1) the four-way `Bool` search predicate needs congruent
`Bool`-valued arithmetic comparisons and no `Nat.ble`/`Nat.blt` reflection pair
was found; (2) `forallSubset_of_search`'s verdict covers only sets with
`Le (bound t) n`, so a subset with a wide stored bound needs a normalisation
step that does not exist; (3) moving a matching from `union t (sdiff s t)` back
to `s` needs a small pointwise-membership lemma nobody has written. Detail in
[ADR-1644](../../research/09-decisions/adr-1644-the-loop-bound-decides-the-inclusion-test-and-halls-split-lands-without-the-induction.md).

<!-- plan-section: landed-changes -->

| 2026-09-05 | `ca657cbcf` | `Nat.Finset.allBelow_congr` and the fixed-bound inclusion decision: `subsetFixed` plus its intro/elim/congruence rules, all five admitted axiom-free. Six tests, including the two wrong definitions the shape invites — the argument SWAP and the loop BOUND, the latter pinned with a pair that shares its second argument so a `bound t` loop could not separate them. `subsetFixed empty (singleton 0)` is `true`, not `false`, and that is asserted rather than papered over. |
