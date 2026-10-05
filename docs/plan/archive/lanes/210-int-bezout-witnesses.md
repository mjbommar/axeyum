# Lane: int-bezout-witnesses — computable Bézout witnesses (`Int.gcdA`/`Int.gcdB`)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, int-bezout-witnesses, 2026-08-28).**
`F:ml430-int-gcd-eq-gcd-ab-63005aef` is **closed**, axiom-free, at Mathlib
v4.30's exact statement `∀ x y : ℤ, ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y`.
Six declarations landed in
`crates/axeyum-lean-kernel/src/int_prelude/bezout_witnesses.rs` — three
`Definition`s that return data (`Nat.xgcdAux`, `Nat.gcdA`/`Nat.gcdB`, plus
`Int.gcdA`/`Int.gcdB`) and three `Theorem`s (`Nat.xgcdAux_sound`,
`Nat.gcd_eq_gcd_ab`, `Int.gcd_eq_gcd_ab_witnesses`). Every one measures
`axiom_footprint = 0`.

**The characterization the brief carried was correct.** The pre-existing
`Int.gcd_eq_gcd_ab` is the EXISTENTIAL form
(`∀ a b, ∃ u v, ofNat (gcd a b) = a*u + b*v`, `int_prelude/gcd.rs:1448`), its
magnitude witnesses come from `Nat.gcd_bezout` — a `Theorem` whose four
naturals sit inside a `Prop` — and its sign handling is a `Prop`-typed
`Or`-elimination. Neither is projectable, so this was a program to write, not
a proof to rearrange. The old name is kept for the existential because
`crt.rs` and `modinv.rs` consume it; the Mathlib-shaped statement is
`Int.gcd_eq_gcd_ab_witnesses`.

**Fuel, and why `m` suffices.** `Nat.xgcdAux` recurses structurally on a fuel
argument (`log.rs`'s device, never `WellFounded`), with a trailing `Bool`
selecting which coefficient to return so ONE recursion carries the pair
without a product type. `Nat.gcdA m n := xgcdAux m m n true`. The invariant
is `m ≤ fuel`, carried as an explicit hypothesis on `Nat.xgcdAux_sound` and
preserved because `succ k ≤ succ f` gives `k ≤ f` while `Nat.mod_lt` gives
`n % succ k < succ k`; at `fuel := m` it discharges to `le_refl`. The bound
constrains the PROOF, not the definition — short of fuel the function still
computes, it just answers for a truncated recursion.

**Three things worth carrying forward.**

- The orientation was chosen to match THIS prelude's `Nat.gcd`, which
  recurses on its FIRST argument. That makes the induction's step a direct
  appeal to `gcd_succ` rather than a re-derivation of Euclid, and it is why
  the step is eleven `ichain` links rather than a new development.
- `neg_neg` and `neg_mul` already existed as PRIVATE proof-term helpers inside
  `gcd.rs` — hiding place 2, an inline step never exposed. They are
  `pub(super)` now and `neg_mul_neg` is built from them plus the public
  `Int.mul_neg`. Nothing was re-derived.
- The kernel rejected exactly once, and the sign is where: the `Int` lift's
  chain named the goal's coefficient as the `Nat`-level `base_a`/`base_b`
  instead of `Int.gcdA x y`/`Int.gcdB x y`. Those agree on an `ofNat` branch
  and differ by a negation on `negSucc`, so the error was invisible in half
  the branches. `Nat.xgcdAux_sound` and `Nat.gcd_eq_gcd_ab` were accepted
  first try; a three-step bisect over the `declare_*` calls found it, because
  one bad declaration poisons the shared prelude build and the failure COUNT
  says nothing.

**Verification.** `cargo test -p axeyum-lean-kernel --lib int_prelude` — 38
passed, 0 failed (35 before this lane). Three of those are new and two are
evaluation, not type-checking: a theorem alone does not pin the algorithm
down, since *some* pair of coefficients satisfies Bézout for any correct gcd,
so `Nat.gcdA`/`Int.gcdA` are reduced to normal form against hand-computed
answers at seven `Nat` and six `Int` points (all four sign branches) and the
identity is then evaluated at each. Magnitudes are held to 6 — every `Nat`
numeral here is unary, so the literal fast path never fires. The third test
derives its list from the ENVIRONMENT, not by hand: every `Nat.`-namespace
declaration the *integer* prelude adds and the *natural* prelude does not,
with a non-vacuity assertion so an empty list fails.

**Next for `integer-gcd` (7 still open, all `train`).**
`F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e` is the obvious next one and is
now cheap — the existential witness it asks for is `Nat.gcdA`/`Nat.gcdB`
reduced mod `n`. `F:ml430-int-gcd-div-*` and the two
`dvd_of_dvd_mul_*_of_gcd_one` rows want `Nat`-level cancellation rather than
new Bézout machinery.

<!-- plan-section: landed-changes -->

| 2026-08-28 | int-bezout-witnesses | `Nat.xgcdAux`/`Nat.gcdA`/`Nat.gcdB`/`Int.gcdA`/`Int.gcdB` — extended Euclid as fuel-structural `Definition`s returning data |
| 2026-08-28 | int-bezout-witnesses | `Int.gcd_eq_gcd_ab_witnesses` — Mathlib v4.30's Bézout at named computable witnesses, axiom-free; closes `F:ml430-int-gcd-eq-gcd-ab-63005aef` |
