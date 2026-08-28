# ADR-0519: the real lattice is defined on the representation, and it is one-Lipschitz

Status: accepted
Date: 2026-08-19
Index-summary: `CReal.max`, `CReal.min` and `CReal.abs` are **built**, and they cost **no index shift** — the first operations since `CReal.neg` that do not. `Rat.max` is not *derived* from a decision (`Rat.le_or_lt` is an `Or`, hence a `Prop`, and cannot be eliminated into `Type`); it is *defined on the representation* by `Int.rec` on the sign of the cross-difference, where the sign is a constructor. One case-analysis principle `Rat.max_cases : ∀ a b (P : Rat → Prop), (le a b → P b) → (le b a → P a) → P (max a b)` carries every lattice law, and one lemma `Rat.sub_max_le` — joint one-Lipschitz-ness — is the whole regularity proof *and* the whole congruence proof. `CReal.abs x := max x (neg x)`, so it introduces no sequence of its own

## Context

[ADR-0512](adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md)
constructed ℝ as a Bishop setoid of regular rational sequences and deliberately
did **without** an absolute value: `|r| ≤ q` is written as the pair
`−q ≤ r ∧ r ≤ q`, so `Rat.abs` never had to exist, and the module documentation
says so in its second paragraph. Every operation added since has paid for itself
in *indices*: `CReal.add` samples at Bishop's `2n+1`, `CReal.mul` at a shift
computed from both factors' magnitudes, `CReal.inv` at `(C+1)n + C` with two
degree-2 identities in ℕ to justify it ([ADR-0516](adr-0516-the-real-inverse-is-well-defined-by-uniqueness-not-by-estimate.md)).

Two things made the lattice look like the next expensive rung rather than the
next cheap one.

**First, `max` looks like it needs a decision, and ℝ has none.** `CReal.le` is
undecidable and ADR-0512 states no totality law for it, precisely because
`∀ x y, le x y ∨ le y x` is not constructively provable over the reals.
`Rat.le_or_lt` *is* proved — but it is `Or`-valued, hence a `Prop`, and
eliminating a `Prop` into `Type` is what this kernel refuses. That is the same
wall [ADR-0510](adr-0510-the-real-inverse-is-partial-and-its-modulus-is-data.md)
hit with `Apart`.

**Second, the previous lane costed `abs`/`max`/`min` at ~500 lines whose bulk
was "one ℚ lemma with a four-way sign split", `|a| − |b| ≤ |a − b|`.** That
costing assumed `Rat.abs` had to exist first and that the lattice would be
built on top of it.

## Decision

**1. `Rat.max` and `Rat.min` are defined on the representation, by `Int.rec` on
the sign of the cross-difference.** `Rat.le a b` *is*
`Int.le (num a · den b) (num b · den a)` by definition, so

```text
gap a b := num b · den a  +  −(num a · den b)          -- an Int
max a b := Int.rec (fun _ => Rat) (fun _ => b) (fun _ => a) (gap a b)
min a b := Int.rec (fun _ => Rat) (fun _ => a) (fun _ => b) (gap a b)
```

is non-negative exactly when `a ≤ b`. No decision procedure is invoked and
nothing is eliminated out of `Prop`: the sign of an integer is a **constructor**,
and `Int.rec` eliminates at every universe. The two operations differ only in
which branch returns which argument, so one Rust builder emits both and one
proof skeleton proves both.

The dispatch is **not transcribed** into the proofs. `lattice_body` is factored
out and `Rat.max a b` *is* `lattice_body b a (gap a b)`, the same discipline
`super::defs::inv_body` established: change the definition and the kernel
refuses the case split, rather than the case split proving something about a
stale copy.

**2. One case-analysis principle carries every lattice law.**

```text
Rat.max_cases : ∀ (a b : Rat) (P : Rat → Prop),
  (Rat.le a b → P b) → (Rat.le b a → P a) → P (Rat.max a b)
```

`le_max_left`, `le_max_right`, `max_le` (and the three `min` duals) are one
application each, with `P` instantiated to `fun t => le a t`, `fun t => le b t`,
`fun t => le t c`, and both branches discharged by a hypothesis or by `le_refl`.
There is exactly **one** `Int.rec` in the module.

`max_cases` eliminates into `Prop`. It is not a decision procedure and gives
nothing `Rat.le_or_lt` did not already give; in particular it does not lift to
ℝ, and no claim here says it does.

**3. `Rat.sub_max_le` — joint one-Lipschitz-ness — is the entire real
construction.**

```text
Rat.sub_max_le : a − c ≤ q → b − e ≤ q → max a b − max c e ≤ q
```

`max` does not degrade the modulus, so `maxSeq x y n := Rat.max (x_n) (y_n)` is
regular at the *same* modulus its arguments are and **`CReal.max` needs no index
shift** — the first operation since `CReal.neg` for which that is true. The same
lemma, applied to the same two-sided bound with the two `Equiv` hypotheses in
place of the two regularity facts, is `max_congr`. One helper
(`creal::lattice::lattice_within`) is regularity *and* congruence for both
operations.

**4. `CReal.abs x := CReal.max x (CReal.neg x)`.** No new sequence, no new
regularity obligation, and its axiom footprint is that of the two declarations
it composes. `abs_le` is `max_le` verbatim, `le_abs_self` is `le_max_left`,
`neg_le_abs` is `le_max_right`, and `abs_congr` is `max_congr` with `neg_congr`
in its second slot. The only genuinely new fact is `abs_nonneg`, which rests on
`Rat.zero_le_max_neg` — the one place `Rat.le_total` is used in the lattice.

**5. Everything is one-sided, and that is not an omission.**
`Equiv (abs x) x ∨ Equiv (abs x) (neg x)` is a decision on the sign of a real
number and is not available; it is not proved, not assumed, and not used.
Likewise there is no `max_comm`, no `max_assoc`, no
`max (a+q) (b+q) = max a b + q`: nothing consumes them, and each is one more
`max_cases` when something does.

**6. Non-triviality is proved from the laws, not asserted.** Nothing here
carries a side condition, so no statement is vacuous for want of an inhabited
guard — the failure mode is the other one, a *degenerate operation* satisfying
every law. `max x y := x` satisfies `le_max_left` by reflexivity; `abs x := x`
satisfies `le_abs_self`, `neg_le_abs` and `abs_le`. Two theorems rule that out
through the kernel:

- `CReal.not_le_zero_neg_one : Not (le zero (neg one))` — mentions no lattice
  operation, from `add_le_add`, `add_comm`, `add_zero`, `add_neg`, `le_congr`
  and `not_le_one_zero`;
- `CReal.not_equiv_abs_neg_one : Not (Equiv (abs (neg one)) (neg one))` —
  **`abs` is not the identity**, from `abs_nonneg` and the above.

and the tests additionally admit `Equiv (max x x) x`, `¬ Equiv (max 0 1) 0` and
`¬ Equiv (min 0 1) 1` through the kernel, plus a direct reduction check that
`Rat.max` and `Rat.min` **compute** on both branches with the wrong answer
refused.

## Consequences

- **ℝ is a lattice-ordered field.** `CReal` goes from 76 to 94 declarations;
  `Rat` gains 15. Trusted surface is unchanged at **0**: no `Axiom`, no
  `Opaque`, no `Quotient`, and every new declaration's `Kernel::axiom_footprint`
  is empty.
- **`Rat.abs` still does not exist.** `CReal.abs` is `max x (neg x)` one level
  up and the pointwise `Rat.max a (Rat.neg a)` is what it computes; the four-way
  sign split the previous costing anticipated was never needed. The `−q ≤ r ∧
  r ≤ q` encoding remains the way bounds are written throughout.
  *(`Rat.abs` has since landed; this bullet is a historical record of the
  design at the time this ADR was written.)*
  <!-- was-absent: Rat.abs -- since landed -->
- **The costing was wrong in the cheap direction on the mathematics and right on
  the volume.** ~500 lines was the estimate; the ℚ module is 893 lines and the
  ℝ module 797, but of those ~180 lines are module documentation and the
  remainder is dominated by the six duals rather than by any single hard
  argument. The predicted obstacle (a four-way sign split over `|a| − |b| ≤
  |a − b|`) does not appear at all.
- **What this unlocks.** `abs` is the shape every metric statement takes, so
  cotransitivity of `lt`, `apart_mul`, Cauchy-ness and completeness can now be
  *stated* in the form the literature states them. It does not make any of them
  cheaper: each still needs its own estimate.
- **What it does not unlock.** No decidability, no `sqrt`, no suprema, no
  Markov's principle in any disguise. `¬(x ≈ 0) → x # 0` remains unproved,
  unassumed and unused.

## Alternatives considered

- **Define `CReal.max` through `CReal.neg` and a single primitive** (`min x y :=
  neg (max (neg x) (neg y))`). Rejected: the `min` laws would then need
  `CReal.neg_le_neg` and `CReal.neg_neg` over `Equiv`, neither of which exists,
  and building them costs more than the second `Int.rec` branch it saves.
- **`Rat.max a b := (a + b + |a − b|)/2`.** Needs `Rat.abs` *and* division by
  two, i.e. the field module, to define an order-theoretic operation. Rejected.
- **Dispatch on `Rat.num (Rat.sub b a)` rather than on the Int cross-difference.**
  Correct, but `Rat.sub` renormalises, so every reduction of `Rat.max` would run
  a `gcd`. The cross-difference keeps `Rat.max` cheap to *compute*, which is
  what makes the reduction tests in `rat_prelude_tests` possible at all.
- **Prove `sub_min_le` as the dual of `sub_max_le` by negation.** The
  rearrangement leaves `min (c+q) (e+q) ≤ min c e + q` owing, which is another
  case split; splitting on `min c e` directly pays nothing, because in each
  branch the bound *is* one of the two hypotheses.
