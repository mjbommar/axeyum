# 02 — The library: ℕ → ℤ → ℚ → ℝ

> **This rung is owned by another lane.** `crates/axeyum-lean-kernel/` is being
> worked continuously by a second session — 69 commits in 24 hours, 49 of them
> touching `nat_prelude.rs`. Everything below is therefore a *description of
> where the library stands and what it unlocks*, not a work queue for this
> strand. The two hazards in the last section are real and are **not ours to
> fix**. See
> [`refactor-2026-08/00-parallel-work.md`](../refactor-2026-08/00-parallel-work.md).
>
> What *is* ours is the receiver: an UNSAT evidence route for `Int`/`Real`
> (engineering `01` K2), so that results about ℤ can carry a negative control
> the moment ℤ exists. Today `axeyum-scenarios` `unreachable!()`s on both sorts.

> **STATUS 2026-08-16 — ℤ is done (0 axioms), and ℚ is scoped. The construction
> named below is not the one to build.**
>
> This document says ℚ is "a quotient of ℤ×ℤ≠0 by cross-multiplication". That is
> the mathematics; it is not how a kernel does it, and here it is *inexpressible*
> — this kernel's quotient package has no `Quot.sound`.
>
> **Prior art, read rather than guessed.** Lean 4.30.0's own source is installed
> on this fleet, and Lean core does not use a quotient either
> (`Init/Data/Rat/Basic.lean`):
>
> ```lean
> structure Rat where
>   num : Int
>   den : Nat := 1
>   den_nz : den ≠ 0
>   reduced : num.natAbs.Coprime den
> ```
>
> A structure carrying a *normalised representative* plus two proof fields, with
> `Rat.normalize` reducing by the gcd. That is the same move this project already
> made for ℤ — normalised pairs over a setoid quotient, chosen because
> `Quot.sound` is admitted as a trusted `Declaration::Quotient` and would land in
> every downstream footprint. The decision generalises, and the most-used
> implementation of ℚ in the world agrees with it.
>
> **Kernel support confirmed**, not assumed: `Exists.intro` is already a
> constructor taking a witness *and* a proof, so multi-field constructors with
> `Prop` fields work, and structure eta is implemented in `tc.rs`.
>
> **Measured gap list** (from `IntPrelude`/`NatPrelude` declaration inventories,
> not from a doc). Present: the whole ℕ division/gcd development — `div`, `mod`,
> `gcd`, `dvd`, `div_mod_exists`/`_unique`/`_bounds`, `div_mod_exact_exists`,
> `gcd_bezout`, `dvd_gcd_iff` — and ℤ with its ring and order laws, axiom-free.
> Absent, and needed:
>
> | missing | note |
> |---|---|
> | `Int.natAbs` | trivial by `Int.rec`; `ofNat n ↦ n`, `negSucc n ↦ succ n` |
> | `Int.div` / `Int.mod` | ~~genuinely new work~~ — **probably not needed at all, see below** |
> | `Int.sub` | not declared; `add a (neg b)` may serve without a new definition |
> | `Nat.Coprime` | no named notion, but `gcd a b = 1` is immediate from what is proved |
>
> **The payoff worth naming:** `Int.euclidean_decomposition`, just proved, is
> exactly the *specification* `Int.div`/`Int.mod` have to meet. Defining them by
> sign cases over `Nat.div`/`Nat.mod` and proving they satisfy it turns a freshly
> derived theorem into the contract for the next layer — which is the flywheel
> doing what it is for.
>
> **CORRECTED 2026-08-16, same day.** The `Int.div` row above was wrong, and it is
> the third plan this week to shrink on contact with the construction. Lean's
> `Rat.normalize` does call `Int.divExact`, but that is convenience with a
> divisibility proof attached — mathematically the sign factors out, and
> normalisation can run entirely in ℕ:
>
> ```text
> normalize (num : Int) (den : Nat), by Int.rec on num:
>   ofNat n   ↦  g = gcd n den        num' = ofNat    (n / g)      den' = den / g
>   negSucc n ↦  g = gcd (succ n) den num' = negOfNat ((succ n)/g) den' = den / g
> ```
>
> Only `Nat.div` and the two `Int` constructors, both of which exist. So `Int.div`
> is deferred until something actually demands it, rather than built because a
> textbook route mentioned it.
>
> **The real content is elsewhere**: `gcd (a/g) (b/g) = 1` for `g = gcd a b > 0`.
> That is reachable here because `Nat.gcd_bezout` gives the balanced all-naturals
> identity `g + m·mn + n·nn = m·mp + n·np`; dividing it through by `g`
> (`Nat.mul_left_cancel_of_pos`, present) yields the same identity with `1` in
> place of `g`, and then any common divisor of the quotients divides `1`.
>
> The one missing closing step is **`Nat.eq_one_of_dvd_one : d ∣ 1 → d = 1`**.
> `Nat.not_dvd_one_of_two_le` covers `d ≥ 2` and `Nat.dvd d 1` unfolds to
> `∃ q, 1 = d·q`, so the remaining cases are `d = 0` (absurd) and `d = 1` (refl).
>
> Revised order: `natAbs` ✅ → `eq_one_of_dvd_one` ✅ → coprimality ✅
> (`Nat.coprime_of_bezout_one`) → the `Rat` structure ✅ → cofactor coprimality ✅
> (`Nat.gcd_cofactors_coprime`) → exact division ✅
> (`Nat.div_mul_cancel_of_dvd`) → positivity ✅ → `normalize` ✅.
>
> **ℚ has a smart constructor.** `Rat.normalize : (num : Int) → (den : Nat) →
> 1 ≤ den → Rat` divides through by `gcd (natAbs num) den` and discharges both
> proof fields, so a caller supplies neither. The integer trusted surface stays
> **0**, so ℚ rests on nothing.
>
> It **normalises**, and that is checked the strongest way available: `2/4` and
> `1/2` are *definitionally the same term*, decided by `def_eq` with no lemma at
> all, because `Nat.gcd`, `Nat.div` and `Int.rec` all compute. The same test
> requires `1/2 ≢ 1/3`, without which the first check would be vacuous.
>
> **Arithmetic has started.** `Rat.num`/`Rat.den` project through `Rat.rec`,
> `Rat.den_pos` recovers the positivity field by eliminating into `Prop`, and
> `Rat.mul` routes through `normalize` — which it must, because the product of
> two *reduced* pairs need not be reduced: `2/3 · 3/2` is `6/6`. Checked by
> `def_eq` that it lands on `1/1`, that `1/2 · 1/3` is `1/6`, and that `1/6` and
> `1/2` stay distinguishable.
>
> **Four more, all measured as absent before building.** `Int.nat_abs_neg_of_nat`
> (`natAbs (negOfNat k) = k`) is needed because `negOfNat` is a `Nat.rec`
> definition and so does *not* reduce on a variable — under a case split it does,
> and both branches are `rfl`. Then `Nat.one_le_right_of_mul`,
> `Nat.one_le_left_of_mul` and `Nat.one_le_of_dvd_pos`: a divisor of a positive
> number is positive, and a product cannot be positive with a zero factor.
>
> Those three break a circularity worth naming. `1 ≤ den/g` would like to come
> from `den = g·(den/g)`, but `div_mul_cancel_of_dvd` needs `1 ≤ g` first.
> `one_le_of_dvd_pos` supplies `1 ≤ g` straight from the divisibility *witness*,
> with no division involved, and the rest follows.
>
> **`div_mul_cancel_of_dvd : ∀ g n, 1 ≤ g → g ∣ n → g · (n / g) = n`.** Measured
> first: no such cancellation existed — the division development had
> `div_mod_exact_exists` (a quotient with remainder *zero*) and `div_mod_exec`
> (the executable `div`/`mod` pair) but nothing connecting them. `div_mod_unique`
> identifies the two quotients, so the exact one **is** `n / g`, and the defining
> equation `n = g·q + 0` collapses by `add_zero`. This is the step `normalize`
> needs to say what its quotients multiply back to.
>
> **`gcd_cofactors_coprime : ∀ g a b, 1 ≤ g → gcd (g·a) (g·b) = g → gcd a b = 1`**
> is the statement `normalize` needs, and it composes two steps: `bezout_of_scaled`
> divides a Bézout identity through by its own coefficient (distributivity,
> associativity, then `mul_left_cancel_of_pos`), and `coprime_of_bezout_one`
> reads the gcd off the divided identity.
>
> **`Rat` is declared**, as an inductive with one constructor and four fields:
> `num : Int`, `den : Nat`, `1 ≤ den`, and `gcd (natAbs num) den = 1`. Positivity
> is `1 ≤ den` rather than Lean's `den ≠ 0` because our order development
> produces and consumes exactly that shape — it is what `div_mod_exists`,
> `mul_left_cancel_of_pos` and `dvd_add_right_cancel_of_pos` all take — so the
> conversion Lean pays at each use is simply absent here.
>
> **Measured, and it decided the design: `Nat.gcd` computes in this kernel.**
> `gcd 1 2` is definitionally `1` even though `gcd` is defined by well-founded
> recursion and `WellFounded.fix` does not generally reduce by iota. So a
> concrete rational's `reduced` field is discharged by `rfl`, and `1/2` is built
> with no lemma at all. The test also requires `2/4` to be **rejected** — it
> differs only in that its `reduced` field is false, so accepting it would mean
> the structure carries an obligation it does not enforce.
>
> **Coprimality: every ingredient is present, and the obstacle is plumbing not
> mathematics.** `d := gcd a b` divides `a` and `b` (`gcd_dvd_left`/`_right`),
> hence all four products (`dvd_mul_right_of_dvd`) and both bracketed sums
> (`dvd_add`). Bézout's `(1 + a·mn) + b·nn = a·mp + b·np` rearranges by
> `add_assoc`/`add_comm` to `T = S + 1`, and
> `dvd_add_right_cancel_of_pos : ∀ k m n, 1 ≤ k → k∣m → k∣(m+n) → k∣n` yields
> `d ∣ 1`, which `eq_one_of_dvd_one` closes. A case split rules out `d = 0`,
> where `d ∣ T` would force the successor `S + 1` to be zero.
>
> What stopped a first attempt was **peeling `bezout`'s four nested `Exists`**:
> each intermediate predicate has to match exactly what `bezout_witnesses`
> constructed, and a hand-rolled recursive peeler got that wrong.
>
> **Resolved by putting the eliminator beside the builder.** `bezout_elim` in
> `nat_prelude/bezout.rs` rebuilds the four predicates in the same order and
> from the same `bezout_equation` the introduction form uses, so the two cannot
> drift — the "build the checker from the builder" discipline this repository
> applies to gates, applied to a proof term. `Nat.coprime_of_bezout_one` landed
> on top of it: `∀ a b, bezout a b 1 → gcd a b = 1`, axiom-free.

**The state.** One number system is proved. The rest are assumed or absent.

```
nat_prelude     106 proved theorems      0 axioms
int_prelude       0 proved               3 axioms
arith_prelude     0 proved               3 axioms
string_prelude    0 proved               1 axiom
```

`nat_prelude.rs` went **3,856 → 9,969 lines in 60 commits during a single
session**, and — this is the part that matters — it left arithmetic behind:

```
add native accessibility foundation   ·  add generic well-founded fixpoint
prove well-founded fixpoint equation  ·  prove Nat strict order well-founded
add executable Nat division state     ·  certify executable Nat division
add checked executable Nat gcd        ·  prove Nat gcd universal property
bridge divisibility through executable remainder
```

Well-founded recursion, certified division, gcd with its universal property.
That is the machinery every later construction needs, and it landed in hours.

## Why the library is the rung everything waits on

A proof assistant with no library can state almost nothing. `Int` being
axiomatized is not a cosmetic gap: **every theorem above it inherits three
assumptions**, and the reconstruction routes that lift solver results into the
kernel land in a world where ℤ is postulated rather than constructed.

It also bounds the mathematics strand's other rungs:

- [`01`](01-decide-vs-certify.md): a certificate is a term in a language. If the
  language has no ℚ, there is no ℚ certificate.
- [`03`](03-symbolic-and-infinite.md): a theorem about an infinite family of
  integers needs ℤ to be a *thing*, not an axiom set.
- The engineering strand's `01` is the same item viewed as plumbing; this is the
  same item viewed as content.

## The construction order

Standard, and each step is a genuine mathematical obligation, not a port:

| step | construction | what it needs from below |
|---|---|---|
| **ℤ** | quotient of ℕ×ℕ by `(a,b) ~ (c,d) ⟺ a+d = c+b` | ℕ addition, its cancellation law, and a quotient former |
| **ℚ** | quotient of ℤ×ℤ≠0 by cross-multiplication | ℤ ring structure; ℕ gcd for normal forms |
| **ℝ** | Cauchy sequences or Dedekind cuts over ℚ | ℚ ordered-field structure; completeness is the real work |

**ℤ is reachable now.** `add_left_cancel` and `add_right_cancel` are proved;
well-founded recursion is proved; the kernel has quotient support
(`quotient.rs`, with a canonical-package gate on the import side). The
obligation is real work but it is *bounded* work, and the payoff is countable:
three assumptions discharged, and every downstream statement about integers
stops resting on them.

**ℚ is the interesting one for us**, because `gcd` and its universal property
just landed — normal forms for rationals are exactly what that unlocks.

**ℝ is a different order of effort** and should be scoped, not attempted. Note
what depends on it: the curriculum marks `reals` as `status = "covered"`, and
the corpus audit found it is the one `covered` node our fragment cannot support.

## The metric

**Assumptions remaining, per prelude, per release.** Today: `int` 3, `arith` 3,
`string` 1, `nat` 0.

It is a good metric for three reasons. A referee can check it in one command. A
competitor cannot fake it. And it moves monotonically in the direction the
project claims to care about — a smaller trusted base — rather than measuring
speed, which the project explicitly does not lead with.

Publish it beside the capability count, not buried in a plan.

## Two hazards already visible in the library

Both found by a peer session and both blocked on file ownership at the time:

1. **`nat_prelude.rs:8090`** — `.expect("sum permutation target must contain the
   same atoms")` panics if the target is not a permutation of the source.
   Private, two callers, safe today. The module grew 2.6× in one session and the
   caller count grows with it.
2. **`prove_left_sum_permutation` is bubble sort with a full rebuild in the
   inner loop** — O(n²) adjacent swaps, each calling an O(n) fold, so O(n³)
   interner lookups and an O(n²)-node proof term with a left-nested `trans`
   spine. In the finder's words: *"invisible at Rado's n; a cliff for anything
   larger."* The fix is small — rebuild from the swap index forward, since
   everything below it is unchanged.

The second is this strand's problem in miniature: **an algorithm chosen for the
scale we happened to test, inside the artifact meant to scale.** A library is
not a benchmark; it will be called at sizes nobody anticipated, and its proof
terms are consumed by a kernel whose cost is linear in their size.

## What to do first

1. **ℤ from proved ℕ.** Discharge the three `int_prelude` assumptions. Bounded,
   countable, and it is the keystone both strands identified independently.
2. **Then `arith_prelude`'s three**, which likely fall out of ℤ.
3. **Fix the two hazards above** before the module doubles again.
4. **Scope ℚ** once ℤ lands — `gcd` and its universal property make normal forms
   tractable, and ℚ is the last rung before the effort profile changes shape.
5. **Do not start ℝ** without an explicit decision. Scope it, cost it, and
   decide deliberately — and until then, correct the curriculum's `reals` node
   rather than leaving it marked `covered`.
