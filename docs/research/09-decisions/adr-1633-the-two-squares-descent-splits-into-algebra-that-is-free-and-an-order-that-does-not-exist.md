# ADR-1633: The two-squares descent splits into algebra that is free and an order that does not exist

Status: accepted
Date: 2026-09-05
Index-summary: Sums of two squares land as an ADR-0603 graded family over `Int`: the Brahmagupta–Fibonacci identity in both conjugate groupings (emitted by `ring::int`, no hand proof), the predicate `Int.IsSumOfTwoSquares` and its multiplicativity, the mod-4 boundary refutation, and — the reusable piece the brief asked for — the descent step in two halves, `Int.modEq_descent_cross_terms` and `Int.descentStep`. Fermat's theorem itself did NOT land, and the obstruction is measured and is not the descent's algebra: it is that this prelude has no `Int` absolute-value order lemmas (`natAbs_le_iff`, `mul_le_mul`, `sq_le_sq` are all absent), so the bounded choice of representatives cannot be shown to shrink the multiplier. Two findings about the tooling: `ring::int` declines every goal whose normal form collapses to zero, and a conjunct-order mutant survived the entire concrete test suite because both conjuncts reduce to the same closed proposition.
Index-status: accepted

## Context

Roadmap item W3-10 asked for sums of two squares: the Brahmagupta–Fibonacci
identity, a reusable descent step, Fermat's theorem for primes `p ≡ 1 (mod 4)`,
and the mod-4 refutation. ADR-0603 says a classical theorem lands as a **graded
statement family** — general constructive form, boundary refutation,
decidable-fragment exact form, labelled import — one fact per statement, rather
than as a single all-or-nothing target.

Nothing about sums of two squares existed. Confirmed against a freshly built
`shape_search` (`declarations=3093`, above the 3,050 floor, positive control
`--name Int.wilson` FOUND 1): `--name-like twoSquare`, `sqAddSq`,
`brahmagupta`, `sumOfTwoSquares` and `fermatTwoSquare` were all ABSENT.

Two prerequisites the brief flagged as uncertain turned out to be **present**,
which changed the shape of the work:

- **`Int.firstSupplementaryLawResidue` is proved.** The brief said that if
  "−1 is a square mod `p` iff `p ≡ 1 (mod 4)`" were missing it would be this
  lane's first deliverable, via Wilson's half-split. It is not missing.
  `first_supplementary.rs`'s module doc still describes the residue half as
  the not-built route, but `first_supplementary_residue.rs` (ADR-1235) built
  it, and the declaration renders as

  ```text
  theorem Int.firstSupplementaryLawResidue :
    ∀ (x0 : AxNat), And (2 ≤ 2*x0+1) (∀ d, d ∣ 2*x0+1 → d = 1 ∨ d = 2*x0+1)
      → AxNat.Even x0
      → Int.is_quadratic_residue (Int.ofNat (2*x0+1)) (Int.neg Int.one)
  ```

  So the entry into the descent is available, and the doc comment above it is
  stale — the standing "verify a blocker still exists, including one this
  repository names" rule, hit again.
- **`ring::int` is a real producer for this fragment.** `neg`/`sub` are ring
  operations there (ADR-1582), so a four-variable degree-four identity over ℤ
  is inside it.

## Decision

### 1. The identity is emitted, not written, and BOTH groupings are declared

`Int.brahmaguptaFibonacci` and `Int.brahmaguptaFibonacci'` are declared through
`ring::int::declare` at arity 4. Both were admitted on the first attempt, and
`two_squares.rs` contains no `mul_comm`/`left_distrib` chain for either.

The second grouping is **not** a corollary of the first and is not stylistic
duplication. The descent needs `(ac+bd)² + (ad−bc)²` specifically, because that
is the grouping whose two cross terms both vanish modulo the multiplier when
`c ≡ a` and `d ≡ b`:

| grouping | cross terms modulo `m` |
| --- | --- |
| `(ac−bd)² + (ad+bc)²` (textbook) | `ac−bd ≡ a²−b²`, not divisible by `m` |
| `(ac+bd)² + (ad−bc)²` (conjugate) | `ac+bd ≡ a²+b² ≡ 0` and `ad−bc ≡ ab−ba = 0` |

### 2. `Int.IsSumOfTwoSquares` is a `Definition`, and its meaning is tested

`IsSumOfTwoSquares n := ∃ a, ∃ b, n = a*a + b*b`. Naming it once keeps every
statement in the family quantifying over the same term, which is what
`shape_search --const` retrieves on; inlining the double existential would give
five different-looking statements.

The trusted gate cannot tell a `Definition` it is wrong, so
`two_squares_tests.rs` settles the meaning by reduction and by `def_eq` against
deliberately wrong variants. `5 = 1²+2²`, `13 = 2²+3²`, `17 = 1²+4²` are
admitted through the intro rule with `Eq.refl` as the equation; `5 = 1²+1²`,
`13 = 2²+2²`, `3 = 1²+1²` are refused.

### 3. The descent is split in two, and only the halves that are reachable land

`Int.modEq_descent_cross_terms` (the congruence half) and `Int.descentStep`
(the algebraic half) are declared separately, with the quotients `u`, `w`
universally quantified in the second rather than constructed. That keeps
`descentStep` usable by any descent that can exhibit them, and it is what makes
the conclusion have the **same shape** as the first hypothesis with the
multiplier replaced — the property a `Nat.strongInduction` on the multiplier
needs.

Multiplicative cancellation over ℤ had to be built:
`shape_search --ns Int --name-contains cancel` found only additive and `ModEq`
cancellations, so `Int.mul_left_cancel_of_ne_zero` is derived here from
`Int.mul_eq_zero`, along with `Int.mul_ne_zero`, `Int.eq_of_sub_eq_zero`,
`Int.zero_add`, `Int.sub_self`, `Int.add_sub_cancel_right` and
`Int.mul_sub_mul_comm`.

### 4. The boundary refutation is cheap because it never touches an order

`Int.not_isSumOfTwoSquares_of_modEq_four_three` and its support
`Int.sq_modEq_four_zero_or_one` need no descent and no inequality at all.
Three details are worth carrying:

- **No `Int`-level parity lemma was needed.** `Int.Even n` is *defined* as
  `Nat.Even (natAbs n)` (`parity.rs`), so `Nat.even_or_odd_exists` read at
  `natAbs a` already IS the `Int` dichotomy, up to one delta unfold.
- **No existential is opened.** Each branch writes `a` as `2k` or `2k+1` with
  the definable witness `k := a / 2`, through
  `Int.ediv_two_mul_two_of_even` / `Int.ediv_two_mul_two_add_one_of_odd`.
- **The leaves close by reduction.** `ModEq 4 3 r` unfolds to
  `Eq Int (emod 3 4) (emod r 4)` with both sides closed numerals, and
  `Int.emod` is a structural `Int.rec`/`Nat.rec` definition, so the kernel
  computes them; `Int.natAbs` injectivity plus `Nat.ne_of_beq_eq_false`
  finishes.

## Consequences

Twenty declarations, all axiom-free, all admitted on the first attempt except
the four the ring producer declined (see §"What the tooling did", below).

## What did NOT land, sized

**`Int.fermatTwoSquares` is open.** Registered as
`F:int-fermat-two-squares` with the four ingredients it depends on. The
missing piece is **not** the descent's algebra, which landed first-try; it is
the *bounded choice of representatives and the strict decrease of the measure*.
The classical step is: given `m·p = a² + b²` with `1 < m < p`, choose
`c ≡ a`, `e ≡ b (mod m)` with `|c|, |e| ≤ m/2`, whence `c² + e² ≤ m²/2 < m²`
and the new multiplier `q = (c²+e²)/m` is strictly below `m`.

Every step of that is an **ordering argument over ℤ**, and this prelude has
none of the pieces. `Int.le`, `Int.lt` and `Int.natAbs` all exist;
`shape_search` finds no `natAbs_le_iff`, no `mul_le_mul` over `Int`, and no
`sq_le_sq`. That is the sized obstruction. Two smaller pieces are also
outstanding and are cheaper: the entry step from
`Int.firstSupplementaryLawResidue`'s witness to `p ∣ x² + 1` through
`Int.modEq_iff_dvd`, and the `q > 0` argument (if `c = e = 0` then `m ∣ a` and
`m ∣ b`, so `m² ∣ m·p`, so `m ∣ p`, contradicting `1 < m < p` for prime `p`).

**The composite characterisation is open and out of scope**, registered as
`F:int-two-squares-composite-characterisation`. Its obstruction is a different
one and is recorded there: the statement names the *exponent* of a prime in
`n`, and `nat_prelude/factorization.rs` proves factorisations exist while its
own module doc records that uniqueness is not attempted and cannot be stated,
there being no multiset in which to compare two of them. The general test from
`kernel-proof-engineering.md` applies: an argument that INDUCTS past a
factorisation is reachable, one that EVALUATES over the factor multiset is not,
and this statement evaluates.

## What the tooling did, measured

Two findings that cost this lane time and that the next lane should not
re-derive.

**`ring::int` declines every goal whose normal form collapses to zero.**
`add 0 a` normalizes to the item list `[Mono[a], Num(0)]` and `a` to
`[Mono[a]]`; the trailing zero numeral is not dropped, the lists compare
unequal, and the search reports `NotAnIdentity` (surfacing at the call site as
`KernelError::UnknownConst`, which `ring::int::declare` uses as its decline
channel). `Int.zero_add`, `Int.sub_self`, `Int.add_sub_cancel_right` and
`Int.mul_sub_mul_comm` are hand-proved from `add_comm`/`add_zero`/`add_neg`
for exactly that reason. The two degree-four shape lemmas
(`Int.mul_mul_of_mul_mul`, `Int.sq_add_sq_of_mul_left`), which involve no zero,
went through unchanged.

**A concrete test cannot see a statement-shape change when the instance
reduces, and this bit three times in one lane.** All three were found by
running the check, not by predicting it:

1. A control comparing `inner_predicate 17 1` at `4` against its swap
   `4² + 1²` was VACUOUS — both reduce to `17`. Moved to free variables.
2. A mutant swapping `(ac−bd)` to `(bd−ac)` is a still-TRUE theorem, so the
   concrete quadruple test could not separate it.
   `the_two_identities_state_the_intended_groupings` now compares each
   grouping against its intended statement at free variables.
3. **A mutant transposing both the conjunction and its `And.intro` in
   `Int.modEq_descent_cross_terms` SURVIVED the entire suite — 0 kills of 15,
   everything green.** At the worked instance `(m,a,b,c,e) = (2,5,1,1,1)` the
   two conjuncts are `ModEq 2 6 0` and `ModEq 2 4 0`, both of which reduce to
   the closed proposition `Eq Int 0 0`, so `And left right` and
   `And right left` are definitionally equal there.
   `the_cross_term_conjuncts_are_ordered_as_stated` was added in response and
   kills that mutant with **exactly one** failing test.

The generalisable rule: **a test that pins a STATEMENT must run at free
variables; a test that pins a VALUE must run at numerals.** Using numerals for
both is how a control ends up unable to fail, and reduction is what hides it.

**The other three mutants killed bluntly, and that is worth recording too.** A
sign flip in the identity (`isub` → `iadd`) makes the statement false, the ring
producer declines, and the prelude does not build — 15 of 15 tests die with
`UnknownConst`. An operand swap breaks `isSumOfTwoSquares_mul`'s hand-built
chain, which consumes the identity's exact conclusion — 15 of 15 with
`TypeMismatch`. Making the descent's measure non-decreasing (conclusion
`m*p` instead of `q*p`) makes the final cancellation ill-typed — 15 of 15 with
`TypeMismatch`. On kernel-proof code the dominant kill signal is "the prelude
does not build", which is total but tells you nothing about which guard caught
it; the suite's *discriminating* power lives entirely in the leaf statements no
other declaration consumes, and mutant 3 above is what measured it.
