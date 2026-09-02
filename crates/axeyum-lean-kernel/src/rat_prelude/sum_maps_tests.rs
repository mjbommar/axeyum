//! Evaluation tests for [`super::sum_maps`].
//!
//! **The trusted gate cannot tell you a `Definition` is wrong.**
//! `(Nat -> Rat) -> Nat -> Rat` is that type whatever `Rat.prodRange`
//! returns, and `Nat -> Nat -> ((Nat -> Nat) -> Rat) -> Rat` is that type
//! whatever `Rat.sumMaps` returns, so the prelude building says only that the
//! terms are well-formed. Everything below reduces the two definitions to a
//! normal form at concrete arguments and compares against a value computed by
//! hand.
//!
//! ## Why these particular arguments
//!
//! A sum over *every* map `[0,m) -> [0,n)` is symmetric under permuting the
//! `m` indices whenever every index draws from the same `[0,n)`. **So no total
//! can discriminate a transposed index**, and a test that varied `g 0` against
//! `g 1` in the summand would look rigorous and measure nothing. Two things
//! are genuinely testable and both are checked:
//!
//! - **Cardinality.** `sumMaps m n (fun _ => 1)` must be `n^m`. This catches a
//!   wrong bound, an off-by-one in the recursion, or a `cons` that fails to
//!   extend the map. `n = 0` is included in both directions: `sumMaps 0 0 _`
//!   is `1` (the empty map exists) and `sumMaps 2 0 _` is `0` (there are no
//!   maps into an empty range).
//! - **Independence.** `sumMaps 2 3 (fun g => g 0 * g 1)` must be
//!   `(0+1+2)^2 = 9`. An enumeration that walked only the DIAGONAL — the
//!   plausible defect, since the recursion threads one map through two nested
//!   folds — gives `0 + 1 + 4 = 5`, and the two are separated in both
//!   directions.
//!
//! `Rat.prodRange` gets the mirror treatment: the discriminating question for
//! a finite product is WHICH INDICES it visits (the operation is commutative,
//! so the order cannot be seen), and an exclusive `[0,n)` bound against an
//! inclusive `[0,n]` one is separated by `1*2*3 = 6` versus `1*2*3*4 = 24`.
//!
//! Every magnitude formed is at most `24`, so none of this touches the unary
//! numeral cost `CLAUDE.md` documents.

use super::RatPrelude;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{req, rmul};
use crate::{ExprId, Kernel, build_rat_prelude};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("the rational prelude must build");
    (kernel, prelude)
}

/// The rational `k`, as `Rat.natDivSucc k 0` (`k/1`) — the same encoding
/// `rat_prelude_tests`'s own concrete-instance tests use. Every magnitude
/// formed here is at most `24`.
fn literal(d: &mut IntDev<'_>, p: RatPrelude, k: u32) -> ExprId {
    let numerator = d.num(k);
    let index = d.num(0);
    d.const_app(p.nat_div_succ, &[numerator, index])
}

/// The rational whose numerator is the `Nat`-valued term `e` — `e/1`.
fn coe(d: &mut IntDev<'_>, p: RatPrelude, e: ExprId) -> ExprId {
    let index = d.num(0);
    d.const_app(p.nat_div_succ, &[e, index])
}

/// `Rat.prodRange f n` at a `u32` bound.
fn prod_range(d: &mut IntDev<'_>, p: RatPrelude, f: ExprId, n: u32) -> ExprId {
    let bound = d.num(n);
    d.const_app(p.prod_range, &[f, bound])
}

/// `Rat.sumMaps m n f` at `u32` bounds.
fn sum_maps(d: &mut IntDev<'_>, p: RatPrelude, m: u32, n: u32, f: ExprId) -> ExprId {
    let m_t = d.num(m);
    let n_t = d.num(n);
    d.const_app(p.sum_maps, &[m_t, n_t, f])
}

/// `fun (g : Nat -> Nat) => body(g)`, with `g` bound as a fresh fvar.
fn map_lam(d: &mut IntDev<'_>, body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId) -> ExprId {
    let map_t = super::sum_maps::map_ty(d);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let b = body(d, g);
    d.lam_fv(g_fv, map_t, b)
}

/// `fun (i : Nat) => body(i)` at `Rat`.
fn seq_lam(d: &mut IntDev<'_>, body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let b = body(d, i);
    d.lam_fv(i_fv, nat, b)
}

/// `Rat.prodRange` folds the factor at every index of `[0,n)` — **exclusive**
/// bound, base case `Rat.one`.
///
/// `f i := i + 1` makes the answer sensitive to exactly which indices are
/// visited: `[0,3)` gives `1*2*3 = 6`, an inclusive `[0,3]` would give
/// `1*2*3*4 = 24`, and a bound shifted the other way gives `1*2 = 2`. All
/// three are separated by the SAME `def_eq` call, so the positive is not
/// passing because `def_eq` says yes to everything.
#[test]
fn prod_range_folds_exactly_the_exclusive_range() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    // f := fun i => (i + 1)/1.
    let f = seq_lam(&mut d, &|d, i| {
        let si = d.succ(i);
        coe(d, p, si)
    });

    for &(n, expected) in &[(0_u32, 1_u32), (1, 1), (2, 2), (3, 6), (4, 24)] {
        let lhs = prod_range(&mut d, p, f, n);
        let rhs = literal(&mut d, p, expected);
        assert!(
            d.kernel().def_eq(lhs, rhs),
            "prodRange (fun i => i+1) {n} must be {expected}"
        );
    }

    let three_terms = prod_range(&mut d, p, f, 3);
    let twenty_four = literal(&mut d, p, 24);
    assert!(
        !d.kernel().def_eq(three_terms, twenty_four),
        "24 is the INCLUSIVE-bound answer 1*2*3*4 -- if this passes the bound is wrong"
    );
    let two = literal(&mut d, p, 2);
    assert!(
        !d.kernel().def_eq(three_terms, two),
        "2 is the answer one term short -- if this passes the bound is wrong the other way"
    );

    // The empty product is `Rat.one`, not `Rat.zero`: a base case copied from
    // `Rat.sumRange` would give 0 and every product below would collapse.
    let empty = prod_range(&mut d, p, f, 0);
    let zero_r = literal(&mut d, p, 0);
    assert!(
        !d.kernel().def_eq(empty, zero_r),
        "prodRange _ 0 must be one, not zero"
    );
}

/// `Rat.prodRange_shiftFront` at a concrete instance, both sides computed
/// independently.
///
/// The theorem is proved at symbolic `f` and `n`, so the instance adds nothing
/// about the PROOF. What it adds is that the STATEMENT is the peel it claims
/// to be: with `f i := i + 1` and `n = 3`, the left side is
/// `prodRange f 4 = 1*2*3*4 = 24` and the right side is
/// `f 0 * prodRange (fun k => f (succ k)) 3 = 1 * (2*3*4) = 24`.
#[test]
fn prod_range_shift_front_peels_the_front_factor() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let f = seq_lam(&mut d, &|d, i| {
        let si = d.succ(i);
        coe(d, p, si)
    });
    let three = d.num(3);
    let proof = d.lemma(p.prod_range_shift_front, &[f, three]);
    let inferred = d
        .kernel()
        .infer(proof)
        .unwrap_or_else(|e| panic!("prodRange_shiftFront(f,3) should infer: {e:?}"));

    let lhs = prod_range(&mut d, p, f, 4);
    let rhs = {
        let zero_n = d.num(0);
        let f0 = d.apply(f, &[zero_n]);
        let shifted = seq_lam(&mut d, &|d, k| {
            let sk = d.succ(k);
            d.apply(f, &[sk])
        });
        let tail = prod_range(&mut d, p, shifted, 3);
        rmul(&mut d, f0, tail)
    };
    let expected = req(&mut d, lhs, rhs);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "prodRange_shiftFront(f,3) must state prodRange f 4 = f 0 * prodRange (f ∘ succ) 3"
    );

    let twenty_four = literal(&mut d, p, 24);
    assert!(
        d.kernel().def_eq(lhs, twenty_four),
        "prodRange (fun i => i+1) 4 is 1*2*3*4 = 24"
    );
    assert!(d.kernel().def_eq(rhs, twenty_four), "1 * (2*3*4) is 24 too");
    let six = literal(&mut d, p, 6);
    assert!(
        !d.kernel().def_eq(lhs, six),
        "24 is not 6 -- the same def_eq separates the two"
    );
}

/// `Rat.sumMaps m n (fun _ => 1)` counts the maps `[0,m) -> [0,n)`, so it must
/// be `n^m`.
///
/// This is the assertion that catches a wrong bound or a `cons` that does not
/// extend the map: every other property below is invariant under an
/// enumeration that visits the right *values* the wrong number of times.
#[test]
fn sum_maps_counts_exactly_the_maps_into_the_range() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    for &(m, n, expected) in &[
        (0_u32, 3_u32, 1_u32),
        (1, 3, 3),
        (2, 3, 9),
        (3, 2, 8),
        (2, 1, 1),
        (0, 0, 1),
        (2, 0, 0),
    ] {
        let one = literal(&mut d, p, 1);
        let f = map_lam(&mut d, &|_d, _g| one);
        let lhs = sum_maps(&mut d, p, m, n, f);
        let rhs = literal(&mut d, p, expected);
        assert!(
            d.kernel().def_eq(lhs, rhs),
            "sumMaps {m} {n} (fun _ => 1) should be {expected} \
             (the count of maps [0,{m}) -> [0,{n}))"
        );
    }

    // Negative control through the same `def_eq`: an off-by-one in the count
    // is separated, so the positives are not passing vacuously.
    let one = literal(&mut d, p, 1);
    let f = map_lam(&mut d, &|_d, _g| one);
    let lhs = sum_maps(&mut d, p, 2, 3, f);
    let eight = literal(&mut d, p, 8);
    assert!(
        !d.kernel().def_eq(lhs, eight),
        "sumMaps 2 3 (fun _ => 1) is 9, not 8 -- if this passes the count is not computed"
    );
}

/// `Rat.sumMaps 2 3 (fun g => g 0 * g 1)` must be `(0+1+2)^2 = 9`.
///
/// **This separates the whole product `[0,3) x [0,3)` from its DIAGONAL**,
/// which is the plausible way a two-index fold goes wrong: the recursion
/// threads one map through two nested folds, and a `cons` that overwrote
/// rather than extended would visit only `g 0 = g 1`. The diagonal sum is
/// `0*0 + 1*1 + 2*2 = 5`, asserted NOT to be the value.
#[test]
fn sum_maps_visits_the_full_product_and_not_only_the_diagonal() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let f = map_lam(&mut d, &|d, g| {
        let zero_n = d.num(0);
        let one_n = d.num(1);
        let g0 = d.apply(g, &[zero_n]);
        let g1 = d.apply(g, &[one_n]);
        let r0 = coe(d, p, g0);
        let r1 = coe(d, p, g1);
        rmul(d, r0, r1)
    });
    let lhs = sum_maps(&mut d, p, 2, 3, f);

    let nine = literal(&mut d, p, 9);
    assert!(
        d.kernel().def_eq(lhs, nine),
        "the sum over ALL 9 maps [0,2) -> [0,3) of g 0 * g 1 is (0+1+2)^2 = 9"
    );
    let five = literal(&mut d, p, 5);
    assert!(
        !d.kernel().def_eq(lhs, five),
        "5 is the DIAGONAL sum 0*0 + 1*1 + 2*2 -- if this passes `cons` overwrites \
         instead of extending"
    );
}

/// The two defining equations compute, and the `m = 0` one is applied at a
/// summand that would notice a different junk map.
///
/// `sumMaps 0 n F` is `F` at *some* map, and the module doc says any total map
/// would do. That is true of every CONSUMER (each applies `prodRange _ 0`,
/// which never looks at its argument) and false for an arbitrary `F`, so this
/// pins the choice actually made rather than leaving it unstated.
#[test]
fn sum_maps_defining_equations_compute_and_the_base_map_is_the_constant_zero() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    // sumMaps 0 3 (fun g => (g 0)/1) = 0, because the base map is `fun _ => 0`.
    let f = map_lam(&mut d, &|d, g| {
        let zero_n = d.num(0);
        let g0 = d.apply(g, &[zero_n]);
        coe(d, p, g0)
    });
    let lhs = sum_maps(&mut d, p, 0, 3, f);
    let zero_r = literal(&mut d, p, 0);
    assert!(
        d.kernel().def_eq(lhs, zero_r),
        "sumMaps 0 n F is F applied to the constant-zero map"
    );

    // sumMaps 1 4 (fun g => (g 0)/1) = 0 + 1 + 2 + 3 = 6.
    let f = map_lam(&mut d, &|d, g| {
        let zero_n = d.num(0);
        let g0 = d.apply(g, &[zero_n]);
        coe(d, p, g0)
    });
    let lhs = sum_maps(&mut d, p, 1, 4, f);
    let six = literal(&mut d, p, 6);
    assert!(
        d.kernel().def_eq(lhs, six),
        "sumMaps 1 4 (fun g => g 0) enumerates 0,1,2,3 and sums to 6"
    );
    let ten = literal(&mut d, p, 10);
    assert!(
        !d.kernel().def_eq(lhs, ten),
        "an inclusive bound would give 0+1+2+3+4 = 10 -- that is not the value"
    );
}

/// `Rat.sumMaps_mul_left` and `Rat.sumMaps_mul_right` at a concrete instance,
/// with the scaled and unscaled totals computed independently.
///
/// `H g := g 0`, `m = 1`, `n = 4`, `z = 2`: the unscaled sum is `6` and both
/// scaled sums are `12`. The two lemmas are the only route by which a constant
/// leaves a function-space sum, and the sides they scale are NOT
/// interchangeable in the Cauchy–Binet assembly — `det_row_selection` puts
/// `det B n` on the right and `prodRange` on the left.
#[test]
fn sum_maps_pulls_a_constant_out_of_either_side() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let hh = map_lam(&mut d, &|d, g| {
        let zero_n = d.num(0);
        let g0 = d.apply(g, &[zero_n]);
        coe(d, p, g0)
    });
    let z = literal(&mut d, p, 2);

    let bare = sum_maps(&mut d, p, 1, 4, hh);
    let six = literal(&mut d, p, 6);
    assert!(
        d.kernel().def_eq(bare, six),
        "sumMaps 1 4 (fun g => g 0) is 0+1+2+3 = 6"
    );

    let four = d.num(4);
    let one = d.num(1);
    let left = d.lemma(p.sum_maps_mul_left, &[four, z, one, hh]);
    let right = d.lemma(p.sum_maps_mul_right, &[four, z, one, hh]);
    let left_ty = d
        .kernel()
        .infer(left)
        .unwrap_or_else(|e| panic!("sumMaps_mul_left should infer: {e:?}"));
    let right_ty = d
        .kernel()
        .infer(right)
        .unwrap_or_else(|e| panic!("sumMaps_mul_right should infer: {e:?}"));

    let twelve = literal(&mut d, p, 12);
    let scaled_left = {
        let f = map_lam(&mut d, &|d, g| {
            let zero_n = d.num(0);
            let g0 = d.apply(g, &[zero_n]);
            let r0 = coe(d, p, g0);
            rmul(d, z, r0)
        });
        sum_maps(&mut d, p, 1, 4, f)
    };
    let scaled_right = {
        let f = map_lam(&mut d, &|d, g| {
            let zero_n = d.num(0);
            let g0 = d.apply(g, &[zero_n]);
            let r0 = coe(d, p, g0);
            rmul(d, r0, z)
        });
        sum_maps(&mut d, p, 1, 4, f)
    };
    assert!(
        d.kernel().def_eq(scaled_left, twelve),
        "2 * (0+1+2+3) is 12"
    );
    assert!(
        d.kernel().def_eq(scaled_right, twelve),
        "(0+1+2+3) * 2 is 12"
    );
    let thirteen = literal(&mut d, p, 13);
    assert!(
        !d.kernel().def_eq(scaled_left, thirteen),
        "12 is not 13 -- the same def_eq separates them"
    );

    let expected_left = {
        let pulled = rmul(&mut d, z, bare);
        req(&mut d, scaled_left, pulled)
    };
    let expected_right = {
        let pulled = rmul(&mut d, bare, z);
        req(&mut d, scaled_right, pulled)
    };
    assert!(
        d.kernel().def_eq(left_ty, expected_left),
        "sumMaps_mul_left must state the LEFT pull"
    );
    assert!(
        d.kernel().def_eq(right_ty, expected_right),
        "sumMaps_mul_right must state the RIGHT pull"
    );

    // The two statements must be DIFFERENT propositions, and that has to be
    // checked at the general types -- NOT at the instance above. At `z = 2`
    // and this `H` both sides evaluate to `12 = 12`, so the instantiated
    // statements are def_eq to each other and to anything else true here; the
    // first draft of this control asserted the instances apart and failed,
    // which is the vacuous-negative-control hazard firing on itself.
    let (left_general, right_general) = {
        use crate::env::Declaration;
        let ty_of = |kernel: &Kernel, name: crate::NameId| -> ExprId {
            match kernel.environment().get(name).expect("declared") {
                Declaration::Theorem { ty, .. } => *ty,
                other => panic!("{other:?} is not a theorem"),
            }
        };
        (
            ty_of(d.kernel(), p.sum_maps_mul_left),
            ty_of(d.kernel(), p.sum_maps_mul_right),
        )
    };
    assert!(
        !d.kernel().def_eq(left_general, right_general),
        "`Rat.mul` is not definitionally commutative, so the LEFT and RIGHT pulls \
         are different propositions -- if this passes, one of them is not saying \
         what its name claims"
    );
}

/// Every declaration this module adds is `Theorem`- or `Definition`-kinded
/// with an EMPTY axiom footprint, read from the kernel rather than from a
/// list of names in prose.
#[test]
fn the_rat_sum_maps_family_is_axiom_free() {
    use crate::env::Declaration;

    let (kernel, p) = built();
    let expected: [(crate::NameId, bool); 13] = [
        (p.prod_range, false),
        (p.prod_range_zero, true),
        (p.prod_range_succ, true),
        (p.prod_range_shift_front, true),
        (p.prod_range_congr, true),
        (p.sum_range_mul_right, true),
        (p.sum_range_mul_left, true),
        (p.sum_maps, false),
        (p.sum_maps_zero, true),
        (p.sum_maps_succ, true),
        (p.sum_maps_congr, true),
        (p.sum_maps_mul_left, true),
        (p.sum_maps_mul_right, true),
    ];

    for &(name, is_theorem) in &expected {
        let decl = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{} must be declared", kernel.display_name(name)));
        if is_theorem {
            assert!(
                matches!(decl, Declaration::Theorem { .. }),
                "{} must be a Theorem",
                kernel.display_name(name)
            );
        } else {
            assert!(
                matches!(decl, Declaration::Definition { .. }),
                "{} must be a Definition",
                kernel.display_name(name)
            );
        }
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{} must be axiom-free, got {:?}",
            kernel.display_name(name),
            footprint
                .iter()
                .map(|&a| kernel.display_name(a).to_string())
                .collect::<Vec<_>>()
        );
    }
}
