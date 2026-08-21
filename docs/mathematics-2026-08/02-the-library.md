# 02 — The library: ℕ → ℤ → ℚ → ℝ → ℂ

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

> **STATUS 2026-08-19 — the ladder is built to ℂ, and this document's advice
> about ℝ was overtaken.** ℝ and ℂ both exist, constructed, and every prelude
> below has a trusted surface of **0**. Measured today, and this is the number
> to re-measure rather than to quote:
>
> ```text
> cargo run -q --release -p axeyum-lean-kernel \
>   --example nat_axiom_inventory -- --include-constructed
> complex 0 · creal 0 · integer 0 · logic 0 · nat 0 · rat 0 · string 0 · real 30
> ```
>
> `real 30` is the *axiomatized* `Real` package and is now the only nonzero row.
> It is deliberately retained as the negative control every axiom-freedom
> measurement here is checked against — delete it and no such claim can fail
> ([ADR-0509](../research/09-decisions/adr-0509-the-trusted-surface-is-measured-as-reached-not-only-declared.md),
> [`status/64-retire-real.md`](../plan/status/64-retire-real.md)) — and no
> shipped route builds it.
>
> **ℝ is `CReal`** ([ADR-0512](../research/09-decisions/adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md)):
> a Bishop setoid of regular ℚ-sequences whose equality is the *defined*
> relation `CReal.Equiv`, not the kernel's `Eq`. That is the whole trick. A
> Cauchy **quotient** needs `Quot.sound`; Dedekind cuts need `propext` and
> `funext`; a setoid over a defined equality needs neither, so ℝ costs nothing
> trusted. **94 declarations**, re-measured today with
> `--example creal_setoid_witness`: the 22 ordered-commutative-ring laws,
> `mul_congr`, `Apart`, `PosBound`, the partial multiplicative inverse
> ([ADR-0510](../research/09-decisions/adr-0510-the-real-inverse-is-partial-and-its-modulus-is-data.md),
> [ADR-0516](../research/09-decisions/adr-0516-the-real-inverse-is-well-defined-by-uniqueness-not-by-estimate.md)),
> and `max`/`min`/`abs`
> ([ADR-0519](../research/09-decisions/adr-0519-the-real-lattice-is-defined-on-the-representation-and-is-one-lipschitz.md)).
>
> **ℂ is `Complex`** ([ADR-0521](../research/09-decisions/adr-0521-complex-is-a-pair-setoid-over-creal-and-carries-no-order.md)):
> pairs of `CReal` under a componentwise defined `Complex.Equiv`, **39
> declarations** (`--example complex_ring_witness`), all 9 commutative-ring laws,
> trusted surface 0. The 13 order laws of the `Real` package are **refuted, not
> skipped**: `Complex.no_compatible_order` derives `False` from any `le`/`lt`
> satisfying seven of them, witness `I` through `I_sq`, with no classical step.
>
> **Two findings that change what "hard" means on this rung**, and neither was
> on any plan:
>
> - **What must be data is the MODULUS, not the proof.** A function may *take* a
>   `Prop` and return a `Type`; it may not *branch* on one. So
>   `inv : (x : CReal) → Apart x zero → CReal` is **not** definable — `Apart` is
>   an `Or` — while
>   `inv : (x : CReal) → (k : Nat) → PosBound x k → CReal` **is**, because the
>   representative depends on `k` alone and the proof is only ever consumed
>   inside `CReal.mk`'s `Prop`-valued regularity field.
> - **ℚ was not a field.** `Rat.inv` had existed since the rational prelude was
>   written — as a definition with *no law about it*. The development had 22
>   ordered-**ring** laws and an operation named `inv`, and the gap between those
>   two is exactly the gap between a ring and a field. That was the real first
>   blocker on ℝ's inverse, and it was one level down from where anyone was
>   looking. `Rat.mul_inv_cancel` closed it
>   ([`notes/creal-field.md`](../plan/notes/creal-field.md)).
>
> What is **not** built is in "What to do first", below, with costings from the
> lanes that built the pieces rather than fresh estimates.

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
> **`Rat.add` and `Rat.neg` complete the basic operations.** Addition
> renormalises for the same reason multiplication does — `1/6 + 1/3` reaches
> `9/18` over the common denominator. Negation is the opposite case: it rebuilds
> the pair *directly*, because `Int.nat_abs_neg` says the magnitude the `reduced`
> field speaks of is unchanged, so no renormalisation is needed. Checked by
> `def_eq`: `1/6 + 1/3 = 1/2`, `neg` is an involution that moves the value, and
> `1/2 + (−1/2) = 0` — the last of which drives a genuinely negative numerator
> through `normalize`'s `negSucc` branch.
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

**The state, as this document found it (2026-08-15).** One number system was
proved; the rest were assumed or absent.

```
nat_prelude     106 proved theorems      0 axioms
int_prelude       0 proved               3 axioms
arith_prelude     0 proved               3 axioms
string_prelude    0 proved               1 axiom
```

**Re-measured 2026-08-19**, and every row moved. Counts are from the inventory
examples, not from source text — `.theorem(name, …)` takes an interned `NameId`,
so grepping the source returns zero:

```text
nat      139 theorems      0 trusted   # --example nat_theorem_inventory
integer   57 derived       0 trusted   # --example int_theorem_inventory, "0 still asserted"
rat        —               0 trusted   # an ordered FIELD since Rat.mul_inv_cancel
creal     94 declarations  0 trusted   # --example creal_setoid_witness
complex   39 declarations  0 trusted   # --example complex_ring_witness
string     —               0 trusted   # append is constructed, ADR-0513
real       —              30 trusted   # the axiomatized package, kept as a control
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
| **ℝ** | ~~Cauchy sequences or Dedekind cuts over ℚ~~ — **a Bishop setoid of regular ℚ-sequences under a *defined* `CReal.Equiv`** (ADR-0512) | ℚ ordered-field structure. Completeness turned out **not** to be the entry price: the 22 ordered-ring laws, the lattice and a partial inverse are all reachable without it, and completeness is still unbuilt |
| **ℂ** | pairs of `CReal` under a componentwise defined `Complex.Equiv` (ADR-0521) | ℝ's ring structure and nothing else — ℂ was the **cheapest** rung on this table, 39 declarations |

**ℤ is reachable now.** `add_left_cancel` and `add_right_cancel` are proved;
well-founded recursion is proved; the kernel has quotient support
(`quotient.rs`, with a canonical-package gate on the import side). The
obligation is real work but it is *bounded* work, and the payoff is countable:
three assumptions discharged, and every downstream statement about integers
stops resting on them.

**ℚ is the interesting one for us**, because `gcd` and its universal property
just landed — normal forms for rationals are exactly what that unlocks.

**ℝ was built, 2026-08-17/19, under ADR-0512** — and this document said *"ℝ is
a different order of effort and should be scoped, not attempted"*, which is worth
leaving on the page next to why it was wrong. The reasoning behind it was that ℝ
means completeness and completeness is a different kind of obligation. That part
is still true: **completeness is not built**, and nothing that needs it (`sqrt`,
suprema, ℂ's `abs`) is either. What the reasoning missed is that the *ordered
field* structure does not wait on completeness. The 22 ordered-ring laws,
`max`/`min`/`abs` and a partial inverse are all reachable over a setoid of
regular sequences, and the choice of construction — setoid rather than quotient
or cuts — is what kept the trusted surface at 0.

The curriculum's `reals` node was still `status = "covered"` when this was
written, and the corpus audit found it the one `covered` node our fragment could
not support. That residue is now about the *map*, not the prelude:
[`04`](04-reachability.md) measures 40 of 40 `reals` instances as `QF_LRA`
against a node advertising NRA, and 65 negative-control instances over
`Int`/`Real`-sorted symbols that the earlier "not even expressible" claim said
could not exist.

## The metric

**Assumptions remaining, per prelude, per release.** When this was written:
`int` 3, `arith` 3, `string` 1, `nat` 0. Measured 2026-08-19 with
`nat_axiom_inventory --include-constructed`: **`complex` 0, `creal` 0, `integer`
0, `logic` 0, `nat` 0, `rat` 0, `string` 0, and `real` 30** — the last being the
axiomatized package retained as a control (ADR-0509), not a debt on the
constructed ladder. Read it from the kernel, never from this paragraph.

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

The original list, with what happened to each:

1. ~~**ℤ from proved ℕ.**~~ **Done 2026-08-16** — `int_prelude` is 0 axioms, 57
   derived, `Int.euclidean_decomposition` being the last assumption discharged.
2. ~~**Then `arith_prelude`'s three.**~~ Superseded: the `Real` package's 30 are
   what `arith_prelude` became, and they are *modelled* rather than discharged —
   `F:real-axioms-modelled-by-constructed-setoid` interprets all 22 laws at
   `CReal` with empty footprints, and no shipped route builds the package
   (ADR-0509).
3. **Fix the two hazards above** — still open; nothing here has retired them.
4. ~~**Scope ℚ.**~~ **Done 2026-08-16**, and it became an ordered *field* on
   2026-08-18 (`Rat.mul_inv_cancel`), which was the actual prerequisite for ℝ's
   inverse.
5. ~~**Do not start ℝ** without an explicit decision.~~ The decision was taken
   and written down: **ADR-0512**, with ADR-0510/0516 for the inverse, ADR-0519
   for the lattice, and ADR-0521 for ℂ. The instruction was followed, not
   ignored — it was scoped, costed and then built.

**What is actually next**, with costings from the lanes that built the pieces
([`notes/creal-field.md`](../plan/notes/creal-field.md),
[`notes/creal-inv.md`](../plan/notes/creal-inv.md),
[`notes/creal-lattice.md`](../plan/notes/creal-lattice.md)) rather than
re-estimated here:

| not built | cost | note |
|---|---|---|
| **cotransitivity of `lt`** (`x < y → ∀ z, x < z ∨ z < y`) | ~400 lines | the most valuable next rung; it is what makes `Apart` usable for case analysis. Constructively provable: from the gap `q` take `r` with `8r < q` and compare on `Rat.le_or_lt` |
| **`apart_mul`** (`x # 0 → y # 0 → x·y # 0`) | ~300 lines | `CReal.mul_pos` is one of its four sign cases; the other three want `lt x zero ↔ lt zero (neg x)` and `(−x)·(−y) ≈ x·y`, neither of which exists |
| **`CReal.neg_neg`, `neg_le_neg`** | small | the cheapest missing piece of the ordered-group toolkit; `min` was built pointwise precisely to avoid needing them |
| **inverse for `x < 0`, and `CReal.div`** | small, blocked | `Rat.mul_inv_cancel` assumes `0 < q`; the general `x # 0` case cannot branch on the disjunction, so it needs `inv (neg x)` under its own hypothesis or a caller who picks the sign |
| **completeness, suprema, `sqrt`** | each its own ADR | uncosted, and the real "different order of effort" this document was reaching for. ℂ's `abs` needs `sqrt` needs completeness, so ADR-0521's gap is downstream of this one |
| **ℂ inverse, `Complex.abs`** | — | `conj`, `normSq` and `mul_conj` exist; the inverse wants ℝ's general (non-positive) inverse and `abs` wants `sqrt` |

Two things are deliberately **not** on that list, and both are load-bearing:
**Markov's principle in any disguise** (`¬(x ≈ 0) → x # 0` is not proved, not
assumed, not used) and any *decision* on the sign of a real
(`Equiv (abs x) x ∨ Equiv (abs x) (neg x)` is not available — that is a
constructive limit, not an omission).
