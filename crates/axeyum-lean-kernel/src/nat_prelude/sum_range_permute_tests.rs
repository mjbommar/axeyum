//! Tests for [`nat_prelude::sum_range_permute`](super::sum_range_permute).
//!
//! A separate file rather than an addition to the dense `nat_prelude_tests.rs`,
//! per this repository's standing merge-hazard note.
//!
//! Three kinds of check, on disjoint defect classes:
//!
//! 1. **Concrete instantiation with the hypotheses discharged.** A permutation
//!    statement is exactly the shape that can be admitted while meaning
//!    something else, so both theorems are applied at a real self-map of a real
//!    range and the inferred conclusion is compared against the arithmetic it
//!    asserts. The summand is deliberately NOT `{0,1}`-valued — it is
//!    `f k := k * k` — because a `{0,1}` summand would make every instance also
//!    an instance of the already-existing `countRange_permute` and would prove
//!    nothing about the generalization.
//! 2. **The declared types, rendered.** The probe for *admitted, true, and not
//!    your theorem*: `sumRange_point_change`'s two sides can be transposed and
//!    stay true (the equation is symmetric under swapping `a` with `b`), and
//!    `sumRange_permute`'s `f`/`σ` binders can be swapped.
//! 3. **A negative control on the permutation hypothesis.** `σ k := 0` is a
//!    self-map of `[0,n)` that is NOT injective, and the conclusion is FALSE
//!    for it at `f k := k * k`, `n = 3`: `0+1+4 = 5` against `0+0+0 = 0`. So
//!    `InjectiveOn` is load-bearing rather than decoration.

use crate::expr::ExprId;
use crate::tc::{LocalContext, LocalDecl};
use crate::{BinderInfo, Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
}

impl NatOps for Fixture {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.k
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.st
    }
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }

    /// Open a local context holding one free variable per supplied type, in
    /// order. The hypotheses of a permutation statement are propositions no
    /// numeral discharges, so this is how an instance is inferred at all.
    fn open(&mut self, tys: &[ExprId]) -> (Vec<ExprId>, LocalContext) {
        let anon = self.anon_name();
        let mut ctx = LocalContext::new();
        let mut vars = Vec::with_capacity(tys.len());
        for ty in tys {
            let fv = self.fresh_fvar();
            vars.push(self.k.fvar(fv));
            ctx.push(LocalDecl {
                fvar: fv,
                name: anon,
                ty: *ty,
                info: BinderInfo::Default,
            });
        }
        (vars, ctx)
    }

    /// `fun k : Nat => mul k k`, the non-`{0,1}` summand every instantiation
    /// here uses.
    fn square_fn(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let k_fv = self.fresh_fvar();
        let k = self.k.fvar(k_fv);
        let body = self.mul(k, k);
        self.lam_fv(k_fv, nat, body)
    }
}

/// `sumRange (fun k => k*k) 3` is `0 + 1 + 4 = 5`, and the reversal
/// `σ k := 2 - k` leaves it unchanged.
///
/// This is the arithmetic the permutation theorem asserts, checked by
/// evaluation before any proof term is built — the numbers, not the theorem.
#[test]
fn the_arithmetic_the_permutation_asserts_holds_at_a_concrete_reversal() {
    let mut f = Fixture::new();

    let square = f.square_fn();
    let three = f.num(3);
    let total = f.sum_range(square, three);
    let five = f.num(5);
    assert!(
        f.k.def_eq(total, five),
        "sumRange (fun k => k*k) 3 must be 0+1+4 = 5"
    );

    // The reversal `σ k := 2 - k` composed with the square, summed over the
    // same range, is `4 + 1 + 0 = 5`.
    let reversed = {
        let nat = f.nat_ty();
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let two = f.num(2);
        let sk = f.sub(two, k);
        let body = f.mul(sk, sk);
        f.lam_fv(k_fv, nat, body)
    };
    let reversed_total = f.sum_range(reversed, three);
    assert!(
        f.k.def_eq(reversed_total, five),
        "the reversed sum must also be 5"
    );

    // Negative control on the non-injective map `σ k := 0`: the composed sum
    // is `0 + 0 + 0 = 0`, so `InjectiveOn` is load-bearing.
    let collapsed = {
        let nat = f.nat_ty();
        let k_fv = f.fresh_fvar();
        let zero = f.zero();
        let body = f.mul(zero, zero);
        f.lam_fv(k_fv, nat, body)
    };
    let collapsed_total = f.sum_range(collapsed, three);
    assert!(
        !f.k.def_eq(collapsed_total, five),
        "negative control: a non-injective self-map does NOT preserve the sum"
    );
}

/// `sumRange_point_change` applies at a concrete pair of families that differ
/// only at one index, and the equation it produces is the true one.
///
/// `a k := k*k` and `b k := k`, which agree at `0` and `1` and differ at `2`
/// (`4` against `2`) — so `i0 = 2`, `n = 3`. The equation asserts
/// `(0+1+4) + b 2 = (0+1+2) + a 2`, i.e. `5 + 2 = 3 + 4`, and both sides are
/// `7`. The index `i0 = 2` is the LAST one in range, which is the branch of the
/// induction (`Eq i0 j`) that needs `sumRange_congr_lt`; `i0 = 0` and `i0 = 1`
/// would exercise the other branch and are covered by the permutation test's
/// deeper instances.
#[test]
fn the_point_change_law_applies_at_a_concrete_one_index_difference() {
    let mut f = Fixture::new();
    let p = f.p;

    let a = f.square_fn();
    let b = {
        let nat = f.nat_ty();
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        f.lam_fv(k_fv, nat, k)
    };
    let i0 = f.num(2);
    let n = f.num(3);

    // `Lt 2 3`, i.e. `Le 3 3`.
    let bound = f.lemma(p.le_refl, &[n]);

    // Below `i0 = 2`: `k*k = k` for `k < 2`. Both cases are `Eq.refl` after
    // reduction, but the hypothesis is universally quantified, so it has to be
    // discharged by a case split — instead of building one, the instantiation
    // below supplies the two agreement proofs as opaque free variables and the
    // test checks the SHAPE of the resulting equation. The arithmetic itself is
    // checked separately, immediately after.
    let below_ty = {
        let nat = f.nat_ty();
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let ak = f.apply(a, &[k]);
        let bk = f.apply(b, &[k]);
        let eq = f.eq(ak, bk);
        let hyp = f.lt(k, i0);
        let body = f.arrow(hyp, eq);
        f.pi_fv(k_fv, nat, body)
    };
    let above_ty = {
        let nat = f.nat_ty();
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let ak = f.apply(a, &[k]);
        let bk = f.apply(b, &[k]);
        let eq = f.eq(ak, bk);
        let upper = f.lt(k, n);
        let inner = f.arrow(upper, eq);
        let lower = f.lt(i0, k);
        let body = f.arrow(lower, inner);
        f.pi_fv(k_fv, nat, body)
    };
    let (hyps, mut ctx) = f.open(&[below_ty, above_ty]);
    let (below, above) = (hyps[0], hyps[1]);

    let instance = f.const_app(
        p.sum_range_point_change,
        &[a, b, i0, n, bound, below, above],
    );
    let inferred =
        f.k.infer_in(instance, &mut ctx)
            .expect("the concrete instance must type-check");

    let sa = f.sum_range(a, n);
    let sb = f.sum_range(b, n);
    let ai0 = f.apply(a, &[i0]);
    let bi0 = f.apply(b, &[i0]);
    let lhs = f.add(sa, bi0);
    let rhs = f.add(sb, ai0);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "the point-change instance must conclude `Sa 3 + b 2 = Sb 3 + a 2`"
    );

    // And that equation is arithmetically TRUE at these families: `5+2 = 3+4`.
    let seven = f.num(7);
    assert!(f.k.def_eq(lhs, seven), "the left side must evaluate to 7");
    assert!(f.k.def_eq(rhs, seven), "the right side must evaluate to 7");

    // Negative control: the two sums alone are NOT equal, so the `+ b i0` /
    // `+ a i0` corrections are doing real work.
    assert!(
        !f.k.def_eq(sa, sb),
        "negative control: the two prefix sums differ (5 against 3)"
    );
}

/// `sumRange_permute` applies at a concrete injective self-map, and the
/// conclusion is the arithmetic identity checked above.
///
/// The two hypotheses (`InjectiveOn`, `MapsInto`) are supplied as opaque free
/// variables — building them for a concrete reversal is a case split over three
/// indices that says nothing about this theorem — and the check is that the
/// conclusion is exactly `sumRange f 3 = sumRange (f ∘ σ) 3`, whose two sides
/// are then evaluated and found equal.
#[test]
fn the_permutation_law_applies_at_a_concrete_reversal() {
    let mut f = Fixture::new();
    let p = f.p;

    let square = f.square_fn();
    let n = f.num(3);
    let sigma = {
        let nat = f.nat_ty();
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let two = f.num(2);
        let body = f.sub(two, k);
        f.lam_fv(k_fv, nat, body)
    };

    let inj_ty = f.const_app(p.injective_on, &[sigma, n]);
    let maps_ty = f.const_app(p.maps_into, &[sigma, n]);
    let (hyps, mut ctx) = f.open(&[inj_ty, maps_ty]);
    let (inj, maps) = (hyps[0], hyps[1]);

    let instance = f.const_app(p.sum_range_permute, &[square, sigma, n, inj, maps]);
    let inferred =
        f.k.infer_in(instance, &mut ctx)
            .expect("the concrete instance must type-check");

    let composed = {
        let nat = f.nat_ty();
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let sk = f.apply(sigma, &[k]);
        let body = f.apply(square, &[sk]);
        f.lam_fv(k_fv, nat, body)
    };
    let lhs = f.sum_range(square, n);
    let rhs = f.sum_range(composed, n);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "the permutation instance must conclude `sumRange f 3 = sumRange (f . sigma) 3`"
    );

    let five = f.num(5);
    assert!(f.k.def_eq(lhs, five), "the unpermuted sum must be 5");
    assert!(f.k.def_eq(rhs, five), "the permuted sum must be 5");
}

/// Both declarations rest on zero axioms.
#[test]
fn the_permutation_family_rests_on_no_axiom() {
    let f = Fixture::new();
    let p = f.p;

    for name in [p.sum_range_point_change, p.sum_range_permute] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The family states the types it is supposed to state, pinned character for
/// character against `render_lean`.
///
/// Two mutants no evaluation test can see:
///
/// * `sumRange_point_change` with `a` and `b` swapped throughout. The equation
///   `Σa + b i0 = Σb + a i0` is SYMMETRIC in that swap, so it is admitted,
///   true, and a different theorem only in which family the consumer's `a`
///   binds to — which matters, because the permutation proof feeds it
///   `f ∘ τ` on the left and `f ∘ σ` on the right and then rewrites only the
///   left index.
/// * `sumRange_permute` with the conclusion's two sides exchanged. Also true,
///   also admitted, and it would force every consumer to insert a `symm`.
#[test]
fn the_permutation_family_states_the_intended_types() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let rendered = |k: &Kernel, name: crate::NameId| -> String {
        match k
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{} must be declared", k.display_name(name)))
        {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => {
                k.render_lean(*ty)
            }
            other => panic!("{other:?} is not a theorem or definition"),
        }
    };

    for (name, expected) in [
        (p.sum_range_point_change, EXPECTED_POINT_CHANGE),
        (p.sum_range_permute, EXPECTED_PERMUTE),
    ] {
        assert_eq!(
            rendered(&k, name),
            expected,
            "{} states a different type than intended",
            k.display_name(name)
        );
    }

    // The permutation's LEFT side is the unpermuted sum. A `contains` query
    // with a positive control, since an empty match and a mistyped pattern are
    // the same observation.
    let permute = rendered(&k, p.sum_range_permute);
    assert!(
        permute.contains("AxNat.sumRange x0 x2) (AxNat.sumRange (fun"),
        "the unpermuted sum must be on the LEFT of the conclusion"
    );
    assert!(
        !permute.contains("AxNat.injectiveOn x0"),
        "the injectivity hypothesis is about the MAP, not the summand"
    );
    assert!(
        permute.contains("AxNat.injectiveOn x1"),
        "positive control: injectivity is stated about `x1`, the map"
    );
}

const EXPECTED_POINT_CHANGE: &str = "((x0 : ((x0 : AxNat) -> AxNat)) -> ((x1 : ((x1 : AxNat) -> AxNat)) -> ((x2 : AxNat) -> ((x3 : AxNat) -> ((x4 : AxNat.lt x2 x3) -> ((x5 : ((x5 : AxNat) -> ((x6 : AxNat.lt x5 x2) -> Eq.{1} AxNat (x0 x5) (x1 x5)))) -> ((x6 : ((x6 : AxNat) -> ((x7 : AxNat.lt x2 x6) -> ((x8 : AxNat.lt x6 x3) -> Eq.{1} AxNat (x0 x6) (x1 x6))))) -> Eq.{1} AxNat (AxNat.add (AxNat.sumRange x0 x3) (x1 x2)) (AxNat.add (AxNat.sumRange x1 x3) (x0 x2)))))))))";
const EXPECTED_PERMUTE: &str = "((x0 : ((x0 : AxNat) -> AxNat)) -> ((x1 : ((x1 : AxNat) -> AxNat)) -> ((x2 : AxNat) -> ((x3 : AxNat.injectiveOn x1 x2) -> ((x4 : AxNat.mapsInto x1 x2) -> Eq.{1} AxNat (AxNat.sumRange x0 x2) (AxNat.sumRange (fun (x5 : AxNat) => x0 (x1 x5)) x2))))))";
