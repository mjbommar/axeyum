fn _boundary_before() {}
    /// `Complex.ofNat_eq_cast : ∀ n, Equiv (ofNat n) (ofReal (CReal.ofNat n))`
    /// — the agreement theorem between the **direct** `ofNat` (structural
    /// `Nat.rec` into `Complex`, [`Self::of_nat`]'s own doc comment) and the
    /// **cast-chain** embedding `ofReal ∘ CReal.ofNat`, closing the gap that
    /// doc comment records as known and open.
    ///
    /// **The chain is `ofReal ∘ CReal.ofNat`, not `ofReal ∘ CReal.ofRat ∘
    /// Rat.ofInt ∘ Int.ofNat`** — `Rat.ofInt` does not exist anywhere in this
    /// kernel (checked by search, not assumed); `CReal.ofNat` is its own
    /// direct definition,
    /// `CReal.ofNat n := CReal.ofRat (Rat.natDivSucc n 0)`
    /// ([`CRealPrelude::of_nat`](crate::CRealPrelude::of_nat)), reusing the
    /// Archimedean development's `k/(j+1)` embedding at index `0` rather than
    /// a three-deep integer/rational cast that was never built.
    ///
    /// Induction on `n`, entirely at the `Complex.Equiv`/`CReal.Equiv` level
    /// (never touching `re`/`im` except inside the one local `ofReal`
    /// congruence this file has to build by hand, since `ComplexPrelude` has
    /// no `of_real_congr` — `Equiv`'s own definition supplies it: `ofReal a`'s
    /// `re`/`im` ι-reduce to `a`/`CReal.zero`, so `Equiv (ofReal a) (ofReal
    /// b)` unfolds to `And (CReal.Equiv a b) (CReal.Equiv CReal.zero
    /// CReal.zero)`).
    ///
    /// - Base: `zero` and `ofReal CReal.zero` are the same `mk CReal.zero
    ///   CReal.zero` **by definition** (`declare_constants`/[`Self::of_real`]
    ///   share that shape), so the base case reduces to `CReal.Equiv
    ///   CReal.zero (CReal.ofNat Nat.zero)` — closed by `CReal.Equiv.refl`
    ///   alone once `Rat.zero` and `Rat.natDivSucc Nat.zero Nat.zero` are
    ///   seen to be the same normalised representative by computation
    ///   (`Nat.gcd`/`Nat.div` at the concrete pair `(0, 1)`).
    /// - Step: `ofNat (Nat.succ n)` ι-reduces to `add (ofNat n) one`; `one`
    ///   and `ofReal CReal.one` share the same defeq shape `one` already has
    ///   with `ofReal`, so [`Self::of_real_add`] turns `add (ofReal (CReal.ofNat
    ///   n)) one` into `ofReal (CReal.add (CReal.ofNat n) CReal.one)`, and
    ///   [`CRealPrelude::of_rat_add`](crate::CRealPrelude::of_rat_add) plus
    ///   [`RatPrelude::nat_div_succ_add`](crate::RatPrelude::nat_div_succ_add)
    ///   (at `(n, 1, 0)`, with `Nat.add n 1` ι-reducing to `Nat.succ n`) carry
    ///   that the rest of the way to `CReal.ofNat (Nat.succ n)`.
fn _boundary_after() {}
