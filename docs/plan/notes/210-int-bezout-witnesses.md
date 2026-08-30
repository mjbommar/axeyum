# Notes: 210-int-bezout-witnesses

Detail moved out of [`../status/210-int-bezout-witnesses.md`](../status/210-int-bezout-witnesses.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
