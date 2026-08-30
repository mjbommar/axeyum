# Lane: pi-rung2 — π rung 2, `cosFnWide (8/5) < 0`

<!-- plan-section: lane-status -->

**Status: THE BOUND DID NOT LAND. Two general theorems that rung 2 needs, and
that nothing in the tree had, DID — and the route `169-pi.md` proposed is
not the one that works (pi-rung2, 2026-08-27).**

Landed, axiom-free, both accepted by `Kernel::add_declaration`:

    CReal.converges_upper_bound_shift :
      ∀ s f L b, (∀ n, le (f (Nat.add n s)) b) → Converges f L → le L b

    CReal.alternatingUpperBoundTail :
      ∀ a, (∀ k, le zero (a k)) → (∀ k, le (a (succ (succ k))) (a (succ k))) →
        ∀ L, Converges (sumRange t) L → le L (sumRange t 3)
      where t j := mul (pow (neg one) j) (a j)

`le (cosFnWide (ofRat (natDivSucc 8 4))) zero` is **not proved**, here or
anywhere in this tree, and no root of cosine is asserted to exist.

## The arithmetic, re-verified independently of the brief

- `a k := (8/5)^{2k}/(2k)!`; `a 0 = 1`, `a 1 = 32/25 = 1.28`,
  `a 2 = (4096/625)/24 = 512/1875 ≈ 0.27307`. `a 1 > a 0`, so the GLOBAL
  antitonicity `alternatingLowerBound`/`alternatingUpperBound` demand fails at
  `k = 0`, exactly as `169-pi.md` measured.
- `a 1 − a 2 = 2400/1875 − 512/1875 = 1888/1875 ≈ 1.006933`; margin over `1` is
  `13/1875 ≈ 0.006933`. Both confirmed.
- **The same margin reads more usefully off the ODD partial sum.**
  `O 1 = a 0 − a 1 + a 2 = 1 − 32/25 + 512/1875 = −13/1875 < 0`, and
  `cos(8/5) ≈ −0.0292 ≤ −13/1875`. That is the same number the brief's
  `1 − 1888/1875` produces, and it is a statement about `a`'s OWN partial
  sums rather than about a shifted series' limit — which is what made the
  route below possible.

Detail and older landed rows moved to [`../notes/174-pi-rung2.md`](../notes/174-pi-rung2.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | pi-rung2 | `CReal.converges_upper_bound_shift` -- `forall s f L b, (forall n, le (f (add n s)) b) -> Converges f L -> le L b`. `alternating.rs` says in its own doc comment that this does not exist and then runs the negation route INLINE on one concrete sequence: hiding place 2, one declaration from reusable. Accepted first try, `creal_prelude_builds` 95.38 s green |
| 2026-08-27 | pi-rung2 | `CReal.alternatingUpperBoundTail` -- the Leibniz upper bound needing antitonicity only from index 1, which is what cosine at `8/5` has (`a 0 = 1 < a 1 = 32/25`, tail antitone). General in `a`, not tied to cosine |
| 2026-08-27 | pi-rung2 | measured NEGATIVE: the shifted-series route `169-pi.md` proposed is blocked by `Converges`'s own definition, not merely unbuilt -- it is a UNIFORM-rate condition constraining index `0`, so any eventually-equal transfer has an index-`0` obligation that an arbitrary `g 0` cannot discharge. The re-indexed series' partial sums agree with the shifted originals only from `n = 1` |
