# Lane: two-squares — the descent's algebra was free; its order does not exist

<!-- plan-section: lane-status -->

**Sums of two squares landed as an ADR-0603 graded family, minus Fermat's
theorem itself** (`WIP`, two-squares, 2026-09-05, ADR-1633). Twenty
declarations in `int_prelude/two_squares.rs`, every one axiom-free and every
one admitted on the first attempt: the Brahmagupta–Fibonacci identity in both
conjugate groupings (emitted by `ring::int`, no hand proof anywhere in the
file), the predicate `Int.IsSumOfTwoSquares` with its introduction rule and
multiplicativity, the mod-4 boundary refutation with its supporting
"every square is 0 or 1 mod 4", and the descent step in two reusable halves —
`Int.modEq_descent_cross_terms` (both cross terms of the conjugate grouping
vanish modulo the multiplier) and `Int.descentStep` (the multiplier drops from
`m` to `q` with the conclusion in the same shape as the hypothesis, so
`Nat.strongInduction` on the multiplier applies directly).

**`Int.fermatTwoSquares` did NOT land, and the obstruction is not the
descent.** The algebra was free. What is missing is the bounded choice of
representatives and the strict decrease of the measure: `|c|, |e| ≤ m/2` ⟹
`c² + e² ≤ m²/2 < m²`. Every step of that is an ordering argument over ℤ, and
this prelude has none of the pieces — `Int.le`, `Int.lt` and `Int.natAbs` all
exist, but `shape_search` finds no `natAbs_le_iff`, no `mul_le_mul` over `Int`
and no `sq_le_sq`. Two cheaper pieces are also outstanding: the entry step from
`Int.firstSupplementaryLawResidue`'s witness to `p ∣ x² + 1` through
`Int.modEq_iff_dvd`, and the `q > 0` argument. Registered open as
`F:int-fermat-two-squares`; the composite characterisation is open as
`F:int-two-squares-composite-characterisation` with its own, different
obstruction (the exponent of a prime in `n` is not a definable quantity here).

**Two corrections to what the brief expected.**
`Int.firstSupplementaryLawResidue` — "−1 IS a quadratic residue mod `p` for
`p ≡ 1 (mod 4)`" — is already **proved** (ADR-1235), so it was not this lane's
first deliverable. `first_supplementary.rs`'s module doc still describes that
half as the not-built route and is stale. And `Int.mul_left_cancel_of_ne_zero`
was **absent**: `shape_search --ns Int --name-contains cancel` returns only
additive and `ModEq` cancellations, so it had to be built from
`Int.mul_eq_zero` together with six supporting lemmas.

**Two tooling findings, both measured rather than predicted.** `ring::int`
declines every goal whose normal form collapses to zero — `add 0 a` normalizes
to `[Mono[a], Num(0)]`, `a` to `[Mono[a]]`, and the trailing zero is not
dropped — so four small lemmas are hand-proved. And a mutant transposing the
two conjuncts of `Int.modEq_descent_cross_terms` **survived the entire concrete
suite, 0 kills of 15**, because at the worked instance both conjuncts reduce to
`Eq Int 0 0` and the orderings are definitionally equal. The repair,
`the_cross_term_conjuncts_are_ordered_as_stated`, runs at free variables and
kills that mutant with exactly one failing test. The rule that generalises: a
test that pins a STATEMENT must run at free variables, a test that pins a VALUE
must run at numerals, and using numerals for both is how a control ends up
unable to fail.

Detail in
[ADR-1633](../../research/09-decisions/adr-1633-the-two-squares-descent-splits-into-algebra-that-is-free-and-an-order-that-does-not-exist.md).

<!-- plan-section: landed-changes -->

| 2026-09-05 | `9ce530f62` | `Int.IsSumOfTwoSquares` (Definition) with its intro rule, the Brahmagupta–Fibonacci identity in both conjugate groupings (both emitted by `ring::int::declare` at arity 4, first attempt), and `Int.isSumOfTwoSquares_mul`. Seven tests; one negative control found VACUOUS on its first honest run (`17 = 1²+4²` and its swap both reduce to `17`) and moved to free variables. |
| 2026-09-05 | `c47a576b5` | `Int.sq_modEq_four_zero_or_one` and `Int.not_isSumOfTwoSquares_of_modEq_four_three` — ADR-0603's boundary-refutation grade. No new `Int` parity lemma was needed (`Int.Even` is *defined* as `Nat.Even (natAbs ·)`), no existential is opened (the witness is the definable `a / 2`), and the four leaves close by REDUCTION of `emod` at closed numerals. Ring stepping stones `Int.sq_of_two_mul`, `Int.sq_of_two_mul_add_one`. 3 tests, each with its negative half: 3, 7, 11 refute; 4, 5, 13, 17 do not. |
| 2026-09-05 | `8b8b58ed9` | `Int.modEq_descent_cross_terms` and `Int.descentStep` — the two reusable halves of Fermat's descent — plus the cancellation family they needed and `shape_search` reported absent: `Int.mul_left_cancel_of_ne_zero`, `Int.mul_ne_zero`, `Int.eq_of_sub_eq_zero`, `Int.zero_add`, `Int.sub_self`, `Int.add_sub_cancel_right`, `Int.mul_sub_mul_comm`, `Int.mul_mul_of_mul_mul`, `Int.sq_add_sq_of_mul_left`. Records the measured `ring::int` zero-collapse decline. 3 tests carrying the worked `p = 13` descent with wrong quotients refused. |
| 2026-09-05 | `aaabdaea1` | Symbolic statement-shape guards: the two Brahmagupta groupings are pinned against their intended terms at FREE VARIABLES (an operand swap is a still-true theorem and a numeral test cannot see it), and `descentStep`'s conclusion is pinned to the NEW multiplier `q` rather than `m`. |
| 2026-09-05 | `a06007837` | `the_cross_term_conjuncts_are_ordered_as_stated`, written because a conjunct-transposition mutant survived all 15 existing tests. Re-running the mutant against it kills exactly one. |
