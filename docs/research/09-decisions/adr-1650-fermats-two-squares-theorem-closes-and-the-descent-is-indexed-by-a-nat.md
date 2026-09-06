# ADR-1650: Fermat's two-squares theorem closes, and the descent is indexed by a `Nat`

Status: accepted
Date: 2026-09-05
Index-summary: `Int.fermatTwoSquares` is admitted, axiom-free — every prime `p = 2m+1` with `m` even is a sum of two integer squares. Twelve declarations in `int_prelude/fermat_two_squares.rs` complete the four pieces ADR-1647 sized. One design call carries the whole assembly: Euler's descent quantifies its multiplier as `Int.ofNat n` over a `Nat` index rather than as an `Int` carrying a `natAbs m = n` bridge hypothesis, which makes `0 < m`, `m < p` and `1 < m` all definitional coercions of the `Nat` hypotheses and leaves exactly ONE transport in the whole proof, at the recursive call. A second call separates the `q != 0` argument into a primality-free half (`Int.dvd_of_degenerate_descent`) and a primality-consuming half (`Int.not_dvd_ofNat_of_prime_of_lt`), so primality is read in exactly one declaration. Measured finding: the statement pin is the only guard with discriminating power here -- deleting a HYPOTHESIS from the descent leaves the prelude building and kills exactly one test.
Index-status: accepted

- **Lane**: `fermat-two-squares` (W3-10, third and final slice)
- **Amends**: nothing. **Completes**:
  [ADR-1633](adr-1633-the-two-squares-descent-splits-into-algebra-that-is-free-and-an-order-that-does-not-exist.md)
  and
  [ADR-1647](adr-1647-the-two-squares-band-is-x-plus-x-not-two-times-x.md),
  whose "what did NOT land, sized" sections this one closes.

## Context

W3-10 landed in three slices. The first (ADR-1633) built the algebra: the
Brahmagupta–Fibonacci identity in both groupings, `Int.IsSumOfTwoSquares`, the
mod-4 boundary refutation, and the descent's two halves
`Int.modEq_descent_cross_terms` and `Int.descentStep`. The second (ADR-1647)
built the order: the centered representative, the two-sided square bound, the
strict decrease, the termination certificate `Int.descentMultiplierBounds`, and
the descent's entry point `Int.exists_small_multiple_of_sq_add_one`.

Both recorded the same thing at the end: **Fermat's theorem itself did not
land**, and ADR-1647 sized what was left as four pieces plus one `Nat` bridge.
This lane built exactly those, and nothing in either sizing turned out to be
stale — a pleasant departure from ADR-1647's own finding that two thirds of
ADR-1633's obstruction had already been false when written. Every prerequisite
it named was verified in-tree before use with a freshly built `shape_search`
(`declarations=3275`, above the 3,050 floor; positive control
`Int.exists_small_multiple_of_sq_add_one` FOUND, which post-dates the merge
that added it, so the index is current and not merely non-empty).

## Decision

### 1. The descent is indexed by a `Nat`, and the multiplier is `Int.ofNat n`

The multiplier is an integer, but the recursion has to be well-founded, and the
only well-founded relation this kernel names a recursor for is `Nat.lt`
(`Nat.strongInduction`, ADR-1614). Two spellings were available:

| spelling | the descent's hypotheses |
| --- | --- |
| `∀ (m : Int), 0 < m → m < p → natAbs m = n → …` | three `Int` bounds plus a bridge |
| `∀ (n : Nat), Nat.lt 0 n → Nat.lt n p → …`, with `m := Int.ofNat n` | three `Nat` bounds, no bridge |

**The second is taken**, and the reason is not aesthetic. `Int.le`/`Int.lt` at
two `ofNat`s is *definitionally* the corresponding `Nat` relation
(`order_coercion.rs` records this and proves both its lemmas by `fun h => h`),
so in the second spelling `0 < m`, `m < p` and `1 < m` are all the `Nat`
hypotheses themselves, transported by a one-line declaration
(`Int.lt_ofNat_of_lt`, this module's Nat→Int direction of
`Int.lt_of_ofNat_lt_ofNat`, likewise `fun h => h`). In the first spelling each
of those three has to be moved across `of_nat_nat_abs_of_nonneg` at every
level of the recursion, *and* the bridge has to be re-established at the
recursive call anyway.

The `Int`→`Nat` direction is still needed once, at the recursive call, where
the new multiplier `q` arrives as an `Int` with `0 ≤ q < m`:
`Int.of_nat_nat_abs_of_nonneg` names `natAbs q` and
`Int.lt_of_ofNat_lt_ofNat` drops both bounds back. **One transport, once**,
instead of three at every level.

A consequence worth naming: no `refl`-generalisation is needed.
`Nat.Hall.hall_sufficient`, the other `Prop`-motive user of
`Nat.strongInduction` in this repository, has to state its motive as
`∀ s nb, card s = n → …` and apply it at `card s` with `Eq.refl`, because its
measure is a *function of* its subject. Here the measure IS the index, so the
motive is applied at `n` directly.

### 2. `q ≠ 0` splits at the point primality enters

The degenerate branch of the descent is: if the new multiplier vanishes then
both centered representatives are zero, so `m ∣ a` and `m ∣ b`, so
`m·p = m²(u²+v²)`, so `m ∣ p` — and `1 < m < p` with `p` prime refutes that.

Those are **two different statements** and they are declared separately:

- `Int.dvd_of_degenerate_descent` is a true statement about **any** nonzero
  `m`. No primality, no bounds, no `Nat` anywhere.
- `Int.not_dvd_ofNat_of_prime_of_lt` is the refutation, and it is the **only**
  declaration in the module that reads a primality condition.

The alternative — one lemma taking the primality condition and concluding
`Not (Eq q zero)` — would have been shorter to write and would have hidden
which hypothesis does what. Keeping them apart means the answer to "where does
this proof use that `p` is prime?" is a single `grep`, and it means the
divisibility half is reusable by any descent with the same shape.

### 3. Two private helpers are re-derived, not re-exported

`order_squares.rs`'s `centered_body` and `small_multiple_body`/`_inner` are
private, and this module needs both to write the binder types of the
`Exists.rec` minors that consume them. They are rebuilt here (eight lines and
twelve lines) rather than widened to `pub(super)`, for the reason
`two_squares.rs` gives for its own copy of `int_exists`: **that file belongs to
another lane's history and this module adds no edit to it.**

This is not a silent-drift risk. The *predicates* — `centered_predicate` and
`small_multiple_outer` — are re-used from `order_squares.rs` (both are already
`pub(super)`), and they are what the `Exists.rec` eliminates. A body that
drifted from its predicate would stop type-checking, not pass quietly.

### 4. Primality stays the inline condition, and Fermat states `p = 2m+1`

`Int.fermatTwoSquares` takes `super::wilson::prime_condition` at
`succ (2·m)` and `Nat.Even m`, exactly as
`Int.firstSupplementaryLawResidue` takes them — not `Nat.Prime p` (there is no
such predicate over either carrier here) and not `p mod 4 = 1`
(`first_supplementary.rs` records why: `Nat.mod` is stuck at symbolic
arguments while `Nat.Even`'s witness is an equation the sign lemma consumes
directly).

That is not a convenience: it is the composition. The residue half is the
**only** route this development has into the descent, so a Fermat whose
hypotheses were spelled differently would be a true theorem that nothing could
reach. `fermat_shares_the_residue_law_hypotheses` checks this against both
stored types rather than asserting it in prose — the same two arguments are
fed to both theorems and both are required to accept them, and their
conclusions are required to DIFFER so the comparison is not vacuous.

## Consequences

Twelve declarations land in
`crates/axeyum-lean-kernel/src/int_prelude/fermat_two_squares.rs`, all
axiom-free, all admitted on the first attempt, all registered in
`int_prelude_tests::derived_laws` (319 → 331, recounted with
`scripts/recount-pinned-inventory.py`, not incremented) so the
environment-derived every-declaration sweep covers them.

**`Int.fermatTwoSquares` is proved.** `F:int-fermat-two-squares` flips from
`open` to `proved`, and the three ADR-1633/ADR-1647 rows it depended on are now
all `proved` as well. The graded family ADR-0603 asks for is complete on its
two reachable rows: the general constructive form (this) and the boundary
refutation (`F:int-two-squares-mod-four-refutation`, ADR-1633). The composite
characterisation (`F:int-two-squares-composite-characterisation`) stays open on
the obstruction ADR-1633 recorded for it, which is a different one and is not
touched here: its statement EVALUATES over a factor multiset rather than
inducting past a factorisation.

Three plumbing lemmas that were simply missing also land and are reusable well
outside this proof: `Int.dvd_zero`, `Int.dvd_of_modEq_zero` (through the
unconditional `Int.ModEq.dvd_iff`, not through the `0 < n`-scoped
`Int.modEq_iff_dvd`, which would have needed a `sub_zero` this prelude does not
have and which `ring::int` declines — ADR-1633's zero-collapse finding), and
`Int.mul_modEq_zero`.

## What the guards measured

The mutation table is the informative part, and it says the same thing
ADR-1647's does, one level up.

All three rows below were RUN, in this lane's own worktree, each restored
byte-for-byte afterwards with `git status` verified empty.

| mutant | outcome | kills |
| --- | --- | --- |
| `descent_apply_ih` feeds the IH `x.n` instead of `magnitude` (`natAbs q`) | prelude REJECTED, `TypeMismatch` | **125 of 128** `int_prelude::` tests |
| `prime_contradiction`'s `n = 1` branch refutes from `n < p` instead of `1 < n` -- i.e. `m = 1` is allowed in the `m | p` step | prelude REJECTED, `TypeMismatch` | **125 of 128** |
| the statement PIN's expected type for `exists_sum_of_two_squares_of_multiple` drops the `Nat.lt n p` hypothesis (the DECLARATION is untouched, so the prelude still builds) | exactly ONE test dies | **1 of 5** in `fermat_two_squares_tests` |

The first two are the mutants the brief named, and both behave the way every
statement mutation of a *proved* kernel declaration behaves in this codebase:
the proof term is built to match the statement exactly, so the kernel rejects
and the whole suite dies with it. That is a total signal and a coarse one — it
says nothing about which guard caught it, and the identical 125/128 for two
mutants at opposite ends of the proof makes that concrete. Neither error
message names the defect either: both are a bare
`TypeMismatch { expected: ExprId(..), got: ExprId(..) }`.

**The third row is the one that measures a guard.** It changes the *test's*
expectation and leaves the declaration alone, so the prelude still builds, and
it kills exactly one test:
`fermat_two_squares_declarations_state_the_intended_types` (4 passed,
1 failed). That is the guard
that would see a weakening which still type-checks, and it is why every one of
the twelve declarations has its full `∀`-telescoped type rebuilt independently
and compared against the type the **environment** stores, with `checked == 12`
asserted so a deleted row fails rather than passing quietly.

The application battery carries its own refusal halves for the same reason. At
`p = 5, 13, 17` the theorem is instantiated with a REAL `Nat.Even` witness
(`Even n := ∃ k, n = k + k`, closed by `Eq.refl` because `Nat.add k k` reduces
at a numeral) and only the primality condition is a free variable in a
`LocalContext`. Two refusals accompany it: the instantiation at `m = 2` must
NOT be `IsSumOfTwoSquares (ofNat 7)`, and `Even 4`'s witness must NOT be
accepted where `Even 6` is demanded. Without those, an application test says
only that the theorem has enough arguments and that its conclusion is *some*
`IsSumOfTwoSquares`.

## What is deliberately NOT declared

`Nat.sum_four_squares`, `Nat.Prime.sum_four_squares`,
`Int.lt_of_sum_four_squares_eq_mul`, `Int.exists_least_of_bdd` and
`Int.exists_greatest_of_bdd` are rows of the **held-out**
`descent-and-well-ordering` family; `Nat.sq_add_sq_mul` and
`Int.sq_ne_two_mod_four` are rows of the held-out
`power-and-square-decompositions` family
(`artifacts/autogenesis/nursery-v2-extension.json`'s `family_partitions` is the
split authority — a grep of `artifacts/facts/` for `"partition"` is vacuous).
None of them is declared and no lemma here is stated in their shape:
`Int.exists_sum_of_two_squares_of_multiple` is a statement about one specific
predicate over ℤ, not a well-ordering principle for an arbitrary
`P : ℤ → Prop`, and `Int.sq_mul_add_sq_mul` is a two-square scaling identity,
not the four-square composition.

Mathlib's `Nat.Prime.sq_add_sq`, which IS this theorem, is in neither family.
`python3 scripts/check-autogenesis-holdout-isolation.py` was run after the
proof landed; the lane report carries its exit status.
