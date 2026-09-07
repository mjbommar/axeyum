//! Evaluation tests for [`super::product_space`].
//!
//! **The trusted gate cannot tell you a `Definition` is wrong.**
//! `(Nat → Nat → Rat) → Nat → (Nat → Nat) → Rat` is that type whatever
//! `Rat.prodWeight` returns, and the whole point of the file is that the value
//! is a PRODUCT of the marginals and not some other combination of them. So
//! every definition here is reduced at concrete arguments and compared against
//! a number computed by hand.
//!
//! ## Why these particular arguments
//!
//! The discriminating instance for a product weight is **two factors with
//! different marginals, evaluated off the diagonal**. With
//! `P i j := (i + i + j + 1)/1` the four values are
//!
//! ```text
//! P 0 0 = 1   P 0 1 = 2
//! P 1 0 = 3   P 1 1 = 4
//! ```
//!
//! and at the point `g = (1, 0)` the weight is `P 0 1 · P 1 0 = 2·3 = 6`. That
//! single number separates three defects at once, and each is checked as an
//! explicit negative in the same `def_eq` call that passes the positive:
//!
//! - a weight built as a **sum** would give `2 + 3 = 5`;
//! - a weight that read the point on the **diagonal** (`P 0 0 · P 1 1`) would
//!   give `1·4 = 4`;
//! - a weight that **swapped the coordinates** (`P 0 0 · P 1 1` is the same
//!   term here, so the transposed reading `P 1 1 · P 0 0` is covered by the
//!   same `4`).
//!
//! Had the marginals been equal, or the point been on the diagonal, none of
//! these would be visible: `∑_g` over a product of EQUAL marginals is
//! symmetric under permuting the coordinates, so a test that varied nothing
//! would look rigorous and measure nothing. That is the same trap
//! `sum_maps_tests.rs` documents for `Rat.sumMaps` itself.
//!
//! Every magnitude formed is at most `9`, so none of this touches the unary
//! numeral cost `CLAUDE.md` documents.

use super::RatPrelude;
use crate::Declaration;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{req, rmul};
use crate::{ExprId, Kernel, build_rat_prelude};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("the rational prelude must build");
    (kernel, prelude)
}

/// The rational `k`, as `Rat.natDivSucc k 0` (`k/1`).
fn literal(d: &mut IntDev<'_>, p: RatPrelude, k: u32) -> ExprId {
    let numerator = d.num(k);
    let index = d.num(0);
    d.const_app(p.nat_div_succ, &[numerator, index])
}

/// The rational `num / den`, as `Rat.natDivSucc num (den - 1)`. `den` must be
/// positive.
fn frac(d: &mut IntDev<'_>, p: RatPrelude, num: u32, den: u32) -> ExprId {
    assert!(
        den > 0,
        "natDivSucc encodes den - 1, so den must be positive"
    );
    let numerator = d.num(num);
    let index = d.num(den - 1);
    d.const_app(p.nat_div_succ, &[numerator, index])
}

/// The rational whose numerator is the `Nat`-valued term `e` — `e/1`.
fn coe(d: &mut IntDev<'_>, p: RatPrelude, e: ExprId) -> ExprId {
    let index = d.num(0);
    d.const_app(p.nat_div_succ, &[e, index])
}

/// `fun (i : Nat) => body(i)` at `Rat`.
fn seq_lam(d: &mut IntDev<'_>, body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let b = body(d, i);
    d.lam_fv(i_fv, nat, b)
}

/// `fun (i j : Nat) => body(i, j)` at `Rat` — a family of marginals, or a
/// family of random variables.
fn coef_lam(
    d: &mut IntDev<'_>,
    body: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let b = body(d, i, j);
    let over_j = d.lam_fv(j_fv, nat, b);
    d.lam_fv(i_fv, nat, over_j)
}

/// `fun (g : Nat → Nat) => body(g)`.
fn map_lam(d: &mut IntDev<'_>, body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId) -> ExprId {
    let map_t = super::super::sum_maps::map_ty(d);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let b = body(d, g);
    d.lam_fv(g_fv, map_t, b)
}

/// The product-space point `[a, b, 0, 0, …]`, built from `sum_maps`'s own
/// `cons`.
fn point(d: &mut IntDev<'_>, a: u32, b: u32) -> ExprId {
    let nat = d.nat_ty();
    let zero_n = d.num(0);
    let tail_fv = d.fresh_fvar();
    let zeros = d.lam_fv(tail_fv, nat, zero_n);
    let b_t = d.num(b);
    let inner = super::super::sum_maps::cons_fn(d, b_t, zeros);
    let a_t = d.num(a);
    super::super::sum_maps::cons_fn(d, a_t, inner)
}

/// `P i j := (i + i + j + 1)/1` — the asymmetric marginal family the module
/// docs describe. `P 0 = [1, 2, …]`, `P 1 = [3, 4, …]`.
fn asymmetric_marginals(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    coef_lam(d, &|d, i, j| {
        let two_i = d.add(i, i);
        let sj = d.succ(j);
        let total = d.add(two_i, sj);
        coe(d, p, total)
    })
}

/// `Rat.prodWeight P m g` at a `u32` bound.
fn prod_weight(d: &mut IntDev<'_>, p: RatPrelude, pp: ExprId, m: u32, g: ExprId) -> ExprId {
    let m_t = d.num(m);
    let w = d.const_app(p.product_space.prod_weight, &[pp, m_t]);
    d.apply(w, &[g])
}

/// `Rat.sumMaps m n f` at `u32` bounds.
fn sum_maps(d: &mut IntDev<'_>, p: RatPrelude, m: u32, n: u32, f: ExprId) -> ExprId {
    let m_t = d.num(m);
    let n_t = d.num(n);
    d.const_app(p.sum_maps, &[m_t, n_t, f])
}

/// `Rat.expectationMaps m n F W` at `u32` bounds.
fn expectation_maps(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: u32,
    n: u32,
    f: ExprId,
    w: ExprId,
) -> ExprId {
    let m_t = d.num(m);
    let n_t = d.num(n);
    d.const_app(p.product_space.expectation_maps, &[m_t, n_t, f, w])
}

// ---------------------------------------------------------------------------
// The definitions, by evaluation.
// ---------------------------------------------------------------------------

/// `Rat.prodWeight` multiplies the marginals READ AT THE POINT, and the three
/// plausible defects are separated by the same `def_eq` call that accepts the
/// right answer.
#[test]
fn prod_weight_multiplies_the_marginals_read_at_the_point() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);
    let pp = asymmetric_marginals(&mut d, p);

    // The marginals really are what the module docs claim.
    for &(i, j, expected) in &[(0_u32, 0_u32, 1_u32), (0, 1, 2), (1, 0, 3), (1, 1, 4)] {
        let i_t = d.num(i);
        let j_t = d.num(j);
        let value = d.apply(pp, &[i_t, j_t]);
        let want = literal(&mut d, p, expected);
        assert!(
            d.kernel().def_eq(value, want),
            "the fixture marginal P {i} {j} must be {expected}"
        );
    }

    // At g = (1, 0), the weight of two factors is P 0 1 * P 1 0 = 2 * 3 = 6.
    let g = point(&mut d, 1, 0);
    let weight = prod_weight(&mut d, p, pp, 2, g);
    let six = literal(&mut d, p, 6);
    assert!(
        d.kernel().def_eq(weight, six),
        "prodWeight P 2 (1,0) must be P 0 1 * P 1 0 = 2*3 = 6"
    );

    let five = literal(&mut d, p, 5);
    assert!(
        !d.kernel().def_eq(weight, five),
        "5 is the SUM 2+3 -- if this passes the weight is not a product"
    );
    let four = literal(&mut d, p, 4);
    assert!(
        !d.kernel().def_eq(weight, four),
        "4 is P 0 0 * P 1 1 -- if this passes the point is read on the diagonal"
    );

    // The empty product is `Rat.one`: a base case copied from `Rat.sumRange`
    // would give zero and every product weight would collapse.
    let empty = prod_weight(&mut d, p, pp, 0, g);
    let one = literal(&mut d, p, 1);
    let zero = literal(&mut d, p, 0);
    assert!(
        d.kernel().def_eq(empty, one),
        "prodWeight P 0 g must be one (the empty product)"
    );
    assert!(
        !d.kernel().def_eq(empty, zero),
        "prodWeight P 0 g must not be zero"
    );

    // One factor reads only the first coordinate.
    let one_factor = prod_weight(&mut d, p, pp, 1, g);
    let two = literal(&mut d, p, 2);
    assert!(
        d.kernel().def_eq(one_factor, two),
        "prodWeight P 1 (1,0) must be P 0 1 = 2"
    );
}

/// `Rat.expectationMaps` weights each point, i.e. it is `∑_g F g · W g` and
/// not the unweighted `∑_g F g`.
///
/// With `m = n = 2`, `W := prodWeight (fun _ _ => 1/2) 2` (so every point has
/// weight `1/4`) and `F g := (g 0 + g 1)/1` (values `0, 1, 1, 2` over the four
/// points), the expectation is `4/4 = 1` and the UNWEIGHTED sum is `4`.
#[test]
fn expectation_maps_weights_every_point() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let uniform = coef_lam(&mut d, &|d, _i, _j| frac(d, p, 1, 2));
    let m_t = d.num(2);
    let w = d.const_app(p.product_space.prod_weight, &[uniform, m_t]);
    let f = map_lam(&mut d, &|d, g| {
        let zero_n = d.num(0);
        let one_n = d.num(1);
        let g0 = d.apply(g, &[zero_n]);
        let g1 = d.apply(g, &[one_n]);
        let total = d.add(g0, g1);
        coe(d, p, total)
    });

    let value = expectation_maps(&mut d, p, 2, 2, f, w);
    let one = literal(&mut d, p, 1);
    assert!(
        d.kernel().def_eq(value, one),
        "expectationMaps 2 2 (g0+g1) (uniform 1/2 product) must be (0+1+1+2)/4 = 1"
    );

    let four = literal(&mut d, p, 4);
    assert!(
        !d.kernel().def_eq(value, four),
        "4 is the UNWEIGHTED sum -- if this passes the weight is dropped"
    );

    // The bare mass of the same weight is one, which is the normalisation
    // theorem's content at this instance.
    let mass = sum_maps(&mut d, p, 2, 2, w);
    assert!(
        d.kernel().def_eq(mass, one),
        "the uniform 1/2 product weight has total mass one over 2 factors"
    );
}

/// The **normalisation**, at a concrete instance and against a negative
/// control that fails it.
///
/// `∑_g ∏_{i<2} P i (g i) = 1` when every marginal sums to one (`P i j = 1/2`
/// over `[0,2)`), and is `4` — plainly not one — when the marginals are the
/// unnormalised `P i j = 1`. Both directions come out of the same `def_eq`.
#[test]
fn the_product_weight_is_normalised_exactly_when_the_marginals_are() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);
    let one = literal(&mut d, p, 1);

    let good = coef_lam(&mut d, &|d, _i, _j| frac(d, p, 1, 2));
    let m_t = d.num(2);
    let good_w = d.const_app(p.product_space.prod_weight, &[good, m_t]);
    let good_mass = sum_maps(&mut d, p, 2, 2, good_w);
    assert!(
        d.kernel().def_eq(good_mass, one),
        "marginals summing to one give a product weight of total mass one"
    );

    let bad = coef_lam(&mut d, &|d, _i, _j| literal(d, p, 1));
    let bad_w = d.const_app(p.product_space.prod_weight, &[bad, m_t]);
    let bad_mass = sum_maps(&mut d, p, 2, 2, bad_w);
    assert!(
        !d.kernel().def_eq(bad_mass, one),
        "marginals summing to TWO must not give total mass one -- if this \
         passes, the normalisation statement is vacuous"
    );
    let four = literal(&mut d, p, 4);
    assert!(
        d.kernel().def_eq(bad_mass, four),
        "the unnormalised control's mass is 2^2 = 4, computed the same way"
    );
}

/// `Rat.prodWeight_sumMaps_one` STATES the normalisation it claims to, and its
/// hypothesis is discharged at a concrete instance the kernel accepts.
#[test]
fn prod_weight_sum_maps_one_states_and_applies_the_normalisation() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let n = d.num(2);
    let m = d.num(2);
    let pp = coef_lam(&mut d, &|d, _i, _j| frac(d, p, 1, 2));
    // The binder order is `∀ n P m`, NOT `∀ n m P`: the first attempt passed
    // `[n, m, P]` and the kernel answered `TypeMismatch { got: ExprId(3) }` --
    // a single-digit `got` means it wanted a SORT, i.e. a `Nat` was supplied
    // where the `Nat → Nat → Rat` family belongs.
    let stated = d.lemma(p.product_space.prod_weight_sum_maps_one, &[n, pp, m]);
    let inferred = d
        .kernel()
        .infer(stated)
        .unwrap_or_else(|e| panic!("prodWeight_sumMaps_one(2,P,2) should infer: {e:?}"));

    // The expected shape: (∀ i, sumRange (P i) 2 = 1) → sumMaps 2 2 (prodWeight P 2) = 1.
    let expected = {
        let nat = d.nat_ty();
        let hyp = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let pi = d.apply(pp, &[i]);
            let s = d.const_app(p.sum_range, &[pi, n]);
            let one_r = crate::rat_prelude::ops::rone(&mut d, p);
            let body = req(&mut d, s, one_r);
            d.pi_fv(i_fv, nat, body)
        };
        let w = d.const_app(p.product_space.prod_weight, &[pp, m]);
        let mass = d.const_app(p.sum_maps, &[m, n, w]);
        let one_r = crate::rat_prelude::ops::rone(&mut d, p);
        let concl = req(&mut d, mass, one_r);
        d.arrow(hyp, concl)
    };
    assert!(
        d.kernel().def_eq(inferred, expected),
        "prodWeight_sumMaps_one must state: marginals sum to one implies the \
         product weight has total mass one"
    );
}

/// **The k-fold product rule for expectations**, checked as a statement AND
/// numerically at a concrete instance whose diagonal-only defect gives a
/// different number.
///
/// `m = 2`, `n = 3`, uniform marginals `P i j = 1/3`, coordinate variables
/// `f i k = k/1`. The left side is `∑_{a,b<3} (a·b)/9 = (0+1+2)²/9 = 1`; an
/// enumeration that walked only the diagonal would give
/// `(0 + 1 + 4)/9 = 5/9`. The right side is `((0+1+2)/3)² = 1`.
#[test]
fn k_independent_prod_weight_factors_a_product_of_coordinates() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let pp = coef_lam(&mut d, &|d, _i, _j| frac(d, p, 1, 3));
    let f = coef_lam(&mut d, &|d, _i, k| coe(d, p, k));

    // The left side, spelled through `expectationMaps`.
    let m_t = d.num(2);
    let w = d.const_app(p.product_space.prod_weight, &[pp, m_t]);
    let var = map_lam(&mut d, &|d, g| {
        let inner = {
            let nat = d.nat_ty();
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let gi = d.apply(g, &[i]);
            let body = d.apply(f, &[i, gi]);
            d.lam_fv(i_fv, nat, body)
        };
        let two = d.num(2);
        d.const_app(p.prod_range, &[inner, two])
    });
    let lhs = expectation_maps(&mut d, p, 2, 3, var, w);
    let one = literal(&mut d, p, 1);
    assert!(
        d.kernel().def_eq(lhs, one),
        "E[g0 * g1] over the uniform 1/3 product of two factors is (0+1+2)^2/9 = 1"
    );
    let five_ninths = frac(&mut d, p, 5, 9);
    assert!(
        !d.kernel().def_eq(lhs, five_ninths),
        "5/9 is the DIAGONAL-only answer -- if this passes the product index \
         set is not being enumerated"
    );

    // The right side, the product of the two marginal expectations.
    let marg = seq_lam(&mut d, &|d, i| {
        let fi = d.apply(f, &[i]);
        let pi = d.apply(pp, &[i]);
        let three = d.num(3);
        d.const_app(p.expectation, &[fi, pi, three])
    });
    let two = d.num(2);
    let rhs = d.const_app(p.prod_range, &[marg, two]);
    assert!(
        d.kernel().def_eq(rhs, one),
        "the product of the two marginal expectations is ((0+1+2)/3)^2 = 1"
    );

    // And the theorem says exactly `lhs = rhs`, read off the kernel.
    let three = d.num(3);
    let instance = {
        let witness = d.lemma(p.product_space.k_independent_prod_weight, &[three, m_t, pp]);
        d.apply(witness, &[f])
    };
    let inferred = d
        .kernel()
        .infer(instance)
        .unwrap_or_else(|e| panic!("kIndependent_prodWeight instance should infer: {e:?}"));
    let expected = req(&mut d, lhs, rhs);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "kIndependent_prodWeight at this instance must state E[∏ f_i] = ∏ E[f_i]"
    );
}

/// `Rat.KIndependent` is not vacuous: it says something a WRONG weight fails.
///
/// The predicate is `∀ f, …`, so a counterexample is one family `f` at which
/// the two sides differ. Take the maximally dependent weight — mass `1` on the
/// single point `(1, 1)` and `0` elsewhere over `m = n = 2` — and the
/// coordinate variables. Then `E[g0·g1] = 1` while the marginal expectations
/// are both `1`, so the product is `1` too. The DISCRIMINATING family is the
/// pair `f 0 k = k`, `f 1 k = 1 − k`: on this weight `E[g0·(1−g1)] = 0`, while
/// `E[g0] · E[1−g1] = 1 · 0 = 0`. Both agree, so instead the test uses the
/// weight concentrated on `(1,0)` and `(0,1)` — the "exactly one succeeds"
/// law — where `E[g0·g1] = 0` but `E[g0]·E[g1] = (1/2)·(1/2) = 1/4`.
#[test]
fn k_independence_fails_for_a_dependent_weight() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    // W g := 1/2 when g 0 + g 1 = 1 (over the four points of [0,2)^2), else 0.
    // Spelled with `Rat.natDivSucc` over a `Nat`-valued indicator so no
    // decidable branch on `Rat` is needed: g0 + g1 is 0, 1, 1 or 2, and
    // `Nat.beq (g0 + g1) 1` is the indicator.
    let w = map_lam(&mut d, &|d, g| {
        let zero_n = d.num(0);
        let one_n = d.num(1);
        let g0 = d.apply(g, &[zero_n]);
        let g1 = d.apply(g, &[one_n]);
        let total = d.add(g0, g1);
        let hit = d.beq(total, one_n);
        let half = frac(d, p, 1, 2);
        let zero_r = literal(d, p, 0);
        crate::rat_prelude::probability::bool_select_rat(d, hit, half, zero_r)
    });

    let one = literal(&mut d, p, 1);
    let mass = sum_maps(&mut d, p, 2, 2, w);
    assert!(
        d.kernel().def_eq(mass, one),
        "the anti-diagonal weight is a distribution: 1/2 + 1/2 = 1"
    );

    // E[g0 * g1] = 0 (the two coordinates are never both 1).
    let joint = map_lam(&mut d, &|d, g| {
        let zero_n = d.num(0);
        let one_n = d.num(1);
        let g0 = d.apply(g, &[zero_n]);
        let g1 = d.apply(g, &[one_n]);
        let a = coe(d, p, g0);
        let b = coe(d, p, g1);
        rmul(d, a, b)
    });
    let joint_e = expectation_maps(&mut d, p, 2, 2, joint, w);
    let zero = literal(&mut d, p, 0);
    assert!(
        d.kernel().def_eq(joint_e, zero),
        "on the anti-diagonal weight the two coordinates are never both 1"
    );

    // E[g0] = E[g1] = 1/2, so the factored answer is 1/4 and NOT 0.
    let first = map_lam(&mut d, &|d, g| {
        let zero_n = d.num(0);
        let g0 = d.apply(g, &[zero_n]);
        coe(d, p, g0)
    });
    let first_e = expectation_maps(&mut d, p, 2, 2, first, w);
    let half = frac(&mut d, p, 1, 2);
    assert!(
        d.kernel().def_eq(first_e, half),
        "the first coordinate has mean 1/2 under the anti-diagonal weight"
    );
    let quarter = frac(&mut d, p, 1, 4);
    let factored = rmul(&mut d, first_e, first_e);
    assert!(
        d.kernel().def_eq(factored, quarter),
        "the factored answer would be 1/4"
    );
    assert!(
        !d.kernel().def_eq(joint_e, factored),
        "0 is not 1/4 -- KIndependent genuinely fails here, so the predicate \
         is not satisfied by every weight"
    );
}

// ---------------------------------------------------------------------------
// Kinds and axiom footprints, read out of the kernel.
// ---------------------------------------------------------------------------

/// Every declaration this module adds is a checked `Definition` or `Theorem`
/// with an EMPTY axiom footprint, read from the kernel rather than off the
/// diff. The kind is pinned per name so a `Definition` cannot silently become
/// an `Axiom`.
#[test]
fn the_product_space_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let ps = p.product_space;
    let expected = [
        ("prodRange_one", ps.prod_range_one, true),
        ("prodRange_mul", ps.prod_range_mul, true),
        (
            "prodRange_sumRange_expand",
            ps.prod_range_sum_range_expand,
            true,
        ),
        ("prodWeight", ps.prod_weight, false),
        ("prodWeight_nonneg", ps.prod_weight_nonneg, true),
        ("prodWeight_sumMaps_one", ps.prod_weight_sum_maps_one, true),
        ("expectationMaps", ps.expectation_maps, false),
        ("KIndependent", ps.k_independent, false),
        (
            "kIndependent_prodWeight",
            ps.k_independent_prod_weight,
            true,
        ),
        (
            "sumMaps_one_of_kIndependent",
            ps.sum_maps_one_of_k_independent,
            true,
        ),
    ];
    for (label, name, is_theorem) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        if is_theorem {
            assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "Rat.{label} must be a checked Theorem, found a different kind"
            );
        } else {
            assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "Rat.{label} must be a Definition, found a different kind"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}
