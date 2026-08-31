//! Concrete + symbolic instances for `nat_prelude::minmax_lemmas`.
//!
//! A separate file from `minmax_tests.rs` for the same merge-hazard reason
//! that file gives: two lanes adding items to one Rust file produce a
//! conflict git cuts mid-item.
//!
//! What each test is FOR, since the kernel already re-checked every proof
//! term at `add_declaration` and `nat_prelude_tests::
//! every_nat_declaration_is_checked_and_axiom_free` already reads the kind
//! and axiom footprint of each name from the ENVIRONMENT:
//!
//! - **the STATEMENT**, not the proof. A well-typed theorem can still be the
//!   wrong proposition — `max_eq_left` with its two sides transposed is as
//!   admissible as the right one. Every check here infers the applied
//!   theorem's type and compares it against an independently built
//!   expectation, with a negative control naming the specific transposition
//!   it rules out.
//! - **both branches.** `Le a b` and `Le b a` select opposite arms of the
//!   `Bool.rec`, so a lemma checked at one ordering only is checked at half
//!   its content. The `a = b` boundary gets its own instance because that is
//!   where `Nat.ble a b` is `true` while `max_eq_left`/`min_eq_right`
//!   nonetheless return the OTHER argument — the antisymmetry path, which no
//!   strict ordering exercises.
//! - **concrete AND symbolic.** Concrete numerals reduce, which papers over
//!   every defeq-shaped gap; free variables leave the `Bool.rec` stuck, which
//!   is the only state the theorems were actually proved in.

use crate::expr::ExprId;
use crate::{
    BinderInfo, Kernel, LocalContext, LocalDecl, NatOps, NatPrelude, NatState, build_nat_prelude,
};

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

    /// A proof of `Le a b` for CONCRETE `a`, `b` with `a <= b`: `Nat.ble a b`
    /// reduces to the literal `Bool.true`, so `Eq.refl Bool true` already has
    /// the bridge lemma's hypothesis type.
    fn concrete_le(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let p = self.p;
        let true_ = self.bool_true();
        let evidence = self.bool_refl(true_);
        self.lemma(p.le_of_ble_eq_true, &[a, b, evidence])
    }

    /// Two free `Nat` variables, in a `LocalContext` `infer_in` can read.
    fn two_free(&mut self) -> (ExprId, ExprId, LocalContext) {
        let nat = self.nat_ty();
        let anon = self.anon_name();
        let mut ctx = LocalContext::new();
        let x_fv = self.fresh_fvar();
        let x = self.k.fvar(x_fv);
        ctx.push(LocalDecl {
            fvar: x_fv,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
        let y_fv = self.fresh_fvar();
        let y = self.k.fvar(y_fv);
        ctx.push(LocalDecl {
            fvar: y_fv,
            name: anon,
            ty: nat,
            info: BinderInfo::Default,
        });
        (x, y, ctx)
    }

    fn max(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let name = self.p.max_max;
        self.const_app(name, &[a, b])
    }

    fn min(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let name = self.p.min_min;
        self.const_app(name, &[a, b])
    }
}

/// The four rewrite cuts every other declaration in the module runs through,
/// at BOTH orderings and at the `a = b` boundary.
#[test]
fn the_four_rewrite_cuts_apply_at_both_orderings_and_at_the_boundary() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let five = f.num(5);
    let seven = f.num(7);

    // max_eq_right at 2 <= 7: takes the `ble = true` arm, answer is `b`.
    let le_2_7 = f.concrete_le(two, seven);
    let proof = f.const_app(p.max_eq_right, &[two, seven, le_2_7]);
    let max_2_7 = f.max(two, seven);
    let expected = f.eq(max_2_7, seven);
    let inferred = f.k.infer(proof).expect("max_eq_right 2 7 must type-check");
    assert!(
        f.k.def_eq(inferred, expected),
        "max_eq_right must conclude max 2 7 = 7"
    );
    let transposed = f.eq(max_2_7, two);
    assert!(
        !f.k.def_eq(inferred, transposed),
        "negative control: max_eq_right must NOT conclude max 2 7 = 2"
    );

    // max_eq_left at 2 <= 7 applied as `max 7 2 = 7`: the OTHER arm.
    let le_2_7b = f.concrete_le(two, seven);
    let proof = f.const_app(p.max_eq_left, &[seven, two, le_2_7b]);
    let max_7_2 = f.max(seven, two);
    let expected = f.eq(max_7_2, seven);
    let inferred = f.k.infer(proof).expect("max_eq_left 7 2 must type-check");
    assert!(
        f.k.def_eq(inferred, expected),
        "max_eq_left must conclude max 7 2 = 7"
    );

    // min_eq_left at 2 <= 7.
    let le_2_7c = f.concrete_le(two, seven);
    let proof = f.const_app(p.min_eq_left, &[two, seven, le_2_7c]);
    let min_2_7 = f.min(two, seven);
    let expected = f.eq(min_2_7, two);
    let inferred = f.k.infer(proof).expect("min_eq_left 2 7 must type-check");
    assert!(
        f.k.def_eq(inferred, expected),
        "min_eq_left must conclude min 2 7 = 2"
    );
    let transposed = f.eq(min_2_7, seven);
    assert!(
        !f.k.def_eq(inferred, transposed),
        "negative control: min_eq_left must NOT conclude min 2 7 = 7"
    );

    // min_eq_right at 2 <= 7 applied as `min 7 2 = 2`.
    let le_2_7d = f.concrete_le(two, seven);
    let proof = f.const_app(p.min_eq_right, &[seven, two, le_2_7d]);
    let min_7_2 = f.min(seven, two);
    let expected = f.eq(min_7_2, two);
    let inferred = f.k.infer(proof).expect("min_eq_right 7 2 must type-check");
    assert!(
        f.k.def_eq(inferred, expected),
        "min_eq_right must conclude min 7 2 = 2"
    );

    // The boundary `a = b`. Here `ble 5 5` is `true`, so `max_eq_left` /
    // `min_eq_right` reach their `le_antisymm` branch -- the one no strict
    // ordering above exercises.
    let le_5_5 = f.concrete_le(five, five);
    let proof = f.const_app(p.max_eq_left, &[five, five, le_5_5]);
    let max_5_5 = f.max(five, five);
    let expected = f.eq(max_5_5, five);
    let inferred = f.k.infer(proof).expect("max_eq_left 5 5 must type-check");
    assert!(
        f.k.def_eq(inferred, expected),
        "max_eq_left must conclude max 5 5 = 5 at the ble-true boundary"
    );
    let le_5_5b = f.concrete_le(five, five);
    let proof = f.const_app(p.min_eq_right, &[five, five, le_5_5b]);
    let min_5_5 = f.min(five, five);
    let expected = f.eq(min_5_5, five);
    let inferred = f.k.infer(proof).expect("min_eq_right 5 5 must type-check");
    assert!(
        f.k.def_eq(inferred, expected),
        "min_eq_right must conclude min 5 5 = 5 at the ble-true boundary"
    );
}

/// `le_max_left`, `le_max_right`, `min_le_left`, `min_le_right`, `max_comm`
/// — concretely, and then at genuinely free variables where the `Bool.rec`
/// is stuck and nothing reduces.
#[test]
fn the_bound_mirrors_apply_at_a_concrete_instance_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let seven = f.num(7);

    let max_7_2 = f.max(seven, two);
    assert!(f.k.def_eq(max_7_2, seven), "max 7 2 must reduce to 7");
    let min_7_2 = f.min(seven, two);
    assert!(f.k.def_eq(min_7_2, two), "min 7 2 must reduce to 2");

    let proof = f.const_app(p.le_max_left, &[seven, two]);
    let expected = f.le(seven, max_7_2);
    let inferred = f.k.infer(proof).expect("le_max_left 7 2 must type-check");
    assert!(f.k.def_eq(inferred, expected), "le_max_left 7 2");

    let proof = f.const_app(p.le_max_right, &[seven, two]);
    let expected = f.le(two, max_7_2);
    let inferred = f.k.infer(proof).expect("le_max_right 7 2 must type-check");
    assert!(f.k.def_eq(inferred, expected), "le_max_right 7 2");

    let proof = f.const_app(p.min_le_left, &[seven, two]);
    let expected = f.le(min_7_2, seven);
    let inferred = f.k.infer(proof).expect("min_le_left 7 2 must type-check");
    assert!(f.k.def_eq(inferred, expected), "min_le_left 7 2");

    let proof = f.const_app(p.min_le_right, &[seven, two]);
    let expected = f.le(min_7_2, two);
    let inferred = f.k.infer(proof).expect("min_le_right 7 2 must type-check");
    assert!(f.k.def_eq(inferred, expected), "min_le_right 7 2");

    let proof = f.const_app(p.max_comm, &[two, seven]);
    let max_2_7 = f.max(two, seven);
    let expected = f.eq(max_2_7, max_7_2);
    let inferred = f.k.infer(proof).expect("max_comm 2 7 must type-check");
    assert!(f.k.def_eq(inferred, expected), "max_comm 2 7");

    // Symbolic: nothing here reduces, so the statements are compared as
    // built rather than as evaluated.
    let (x, y, mut ctx) = f.two_free();
    let max_xy = f.max(x, y);
    let min_xy = f.min(x, y);
    let max_yx = f.max(y, x);

    let proof = f.const_app(p.le_max_left, &[x, y]);
    let expected = f.le(x, max_xy);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("le_max_left must apply at free variables");
    assert!(f.k.def_eq(inferred, expected), "le_max_left x y");
    // The transposed control belongs HERE, not at concrete numerals: at
    // `(7, 2)` the max reduces to `7`, so `a <= max a b` and `max a b <= a`
    // are literally the same proposition and the "control" checks nothing.
    // (Measured: it passed the wrong way round on the first run.)
    let transposed = f.le(max_xy, x);
    assert!(
        !f.k.def_eq(inferred, transposed),
        "negative control: le_max_left is `a <= max a b`, not `max a b <= a`"
    );

    let proof = f.const_app(p.min_le_right, &[x, y]);
    let expected = f.le(min_xy, y);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("min_le_right must apply at free variables");
    assert!(f.k.def_eq(inferred, expected), "min_le_right x y");
    let transposed = f.le(y, min_xy);
    assert!(
        !f.k.def_eq(inferred, transposed),
        "negative control: min_le_right is `min a b <= b`, not `b <= min a b`"
    );

    let proof = f.const_app(p.max_comm, &[x, y]);
    let expected = f.eq(max_xy, max_yx);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("max_comm must apply at free variables");
    assert!(f.k.def_eq(inferred, expected), "max_comm x y");
    assert!(
        !f.k.def_eq(max_xy, max_yx),
        "non-vacuity: at free variables the two sides of max_comm are NOT \
         already def_eq, so the theorem is doing real work"
    );
}

/// The `min` universal properties. `Nat.lt_min` is `Nat.le_min` at `succ a`
/// — `Nat.lt` is a `Definition` unfolding to `Le` at `succ`, exactly as Lean
/// core states it — so the point of checking it separately is that the
/// STATEMENT still reads in terms of `Lt`.
#[test]
fn the_min_universal_properties_apply_concretely_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let five = f.num(5);
    let seven = f.num(7);

    let min_7_5 = f.min(seven, five);
    assert!(f.k.def_eq(min_7_5, five), "min 7 5 must reduce to 5");

    // le_min_of_le_of_le : 2 <= 7 -> 2 <= 5 -> 2 <= min 7 5.
    let h1 = f.concrete_le(two, seven);
    let h2 = f.concrete_le(two, five);
    let proof = f.const_app(p.le_min_of_le_of_le, &[two, seven, five, h1, h2]);
    let expected = f.le(two, min_7_5);
    let inferred =
        f.k.infer(proof)
            .expect("le_min_of_le_of_le 2 7 5 must type-check");
    assert!(f.k.def_eq(inferred, expected), "le_min_of_le_of_le 2 7 5");
    let transposed = f.le(min_7_5, two);
    assert!(
        !f.k.def_eq(inferred, transposed),
        "negative control: the conclusion is `a <= min b c`, not its transpose"
    );

    // le_min, both legs, symbolically.
    let (x, y, mut ctx) = f.two_free();
    let z_fv = f.fresh_fvar();
    let z = f.k.fvar(z_fv);
    let nat = f.nat_ty();
    let anon = f.anon_name();
    ctx.push(LocalDecl {
        fvar: z_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let min_yz = f.min(y, z);
    let lhs = f.le(x, min_yz);
    let le_xy = f.le(x, y);
    let le_xz = f.le(x, z);
    let rhs = f.const_app(p.logic.and, &[le_xy, le_xz]);
    let expected = f.const_app(p.logic.iff, &[lhs, rhs]);
    let proof = f.const_app(p.le_min, &[x, y, z]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("le_min must apply at free variables");
    assert!(f.k.def_eq(inferred, expected), "le_min x y z");

    // lt_min at the same free variables: the statement is in `Lt`.
    let lhs = f.lt(x, min_yz);
    let lt_xy = f.lt(x, y);
    let lt_xz = f.lt(x, z);
    let rhs = f.const_app(p.logic.and, &[lt_xy, lt_xz]);
    let expected = f.const_app(p.logic.iff, &[lhs, rhs]);
    let proof = f.const_app(p.lt_min, &[x, y, z]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("lt_min must apply at free variables");
    assert!(f.k.def_eq(inferred, expected), "lt_min x y z");
    let wrong = f.const_app(p.logic.and, &[le_xy, le_xz]);
    let wrong = f.const_app(p.logic.iff, &[lhs, wrong]);
    assert!(
        !f.k.def_eq(inferred, wrong),
        "negative control: lt_min's right-hand side is a conjunction of \
         STRICT inequalities, not of `Le`s"
    );
}

/// Translation-invariance in all four positions, at concrete numerals whose
/// two sides are computed independently, and then symbolically.
#[test]
fn the_translation_invariance_family_applies_concretely_and_symbolically() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let seven = f.num(7);
    let five = f.num(5);
    let ten = f.num(10);

    // add_max_add_left 3 2 7 : max 5 10 = 3 + max 2 7, both sides 10.
    let a_b = f.add(three, two);
    let a_c = f.add(three, seven);
    let lhs = f.max(a_b, a_c);
    let max_2_7 = f.max(two, seven);
    let rhs = f.add(three, max_2_7);
    let expected = f.eq(lhs, rhs);
    let proof = f.const_app(p.add_max_add_left, &[three, two, seven]);
    let inferred =
        f.k.infer(proof)
            .expect("add_max_add_left 3 2 7 must type-check");
    assert!(f.k.def_eq(inferred, expected), "add_max_add_left 3 2 7");
    assert!(f.k.def_eq(lhs, ten), "max (3+2) (3+7) must reduce to 10");
    assert!(f.k.def_eq(rhs, ten), "3 + max 2 7 must reduce to 10");

    // add_min_add_left 3 2 7 : min 5 10 = 3 + min 2 7, both sides 5.
    let lhs = f.min(a_b, a_c);
    let min_2_7 = f.min(two, seven);
    let rhs = f.add(three, min_2_7);
    let expected = f.eq(lhs, rhs);
    let proof = f.const_app(p.add_min_add_left, &[three, two, seven]);
    let inferred =
        f.k.infer(proof)
            .expect("add_min_add_left 3 2 7 must type-check");
    assert!(f.k.def_eq(inferred, expected), "add_min_add_left 3 2 7");
    assert!(f.k.def_eq(lhs, five), "min (3+2) (3+7) must reduce to 5");
    assert!(f.k.def_eq(rhs, five), "3 + min 2 7 must reduce to 5");
    assert!(
        !f.k.def_eq(lhs, ten),
        "negative control: the min form must NOT agree with the max form"
    );

    // add_max_add_right 2 7 3 : max 5 10 = max 2 7 + 3.
    let a_c = f.add(two, three);
    let b_c = f.add(seven, three);
    let lhs = f.max(a_c, b_c);
    let rhs = f.add(max_2_7, three);
    let expected = f.eq(lhs, rhs);
    let proof = f.const_app(p.add_max_add_right, &[two, seven, three]);
    let inferred =
        f.k.infer(proof)
            .expect("add_max_add_right 2 7 3 must type-check");
    assert!(f.k.def_eq(inferred, expected), "add_max_add_right 2 7 3");
    assert!(f.k.def_eq(lhs, ten), "max (2+3) (7+3) must reduce to 10");

    // add_min_add_right 2 7 3 : min 5 10 = min 2 7 + 3.
    let lhs = f.min(a_c, b_c);
    let rhs = f.add(min_2_7, three);
    let expected = f.eq(lhs, rhs);
    let proof = f.const_app(p.add_min_add_right, &[two, seven, three]);
    let inferred =
        f.k.infer(proof)
            .expect("add_min_add_right 2 7 3 must type-check");
    assert!(f.k.def_eq(inferred, expected), "add_min_add_right 2 7 3");
    assert!(f.k.def_eq(lhs, five), "min (2+3) (7+3) must reduce to 5");

    // Symbolic, where the two sides are genuinely different terms.
    let (x, y, mut ctx) = f.two_free();
    let z_fv = f.fresh_fvar();
    let z = f.k.fvar(z_fv);
    let nat = f.nat_ty();
    let anon = f.anon_name();
    ctx.push(LocalDecl {
        fvar: z_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let xy = f.add(x, y);
    let xz = f.add(x, z);
    let lhs = f.max(xy, xz);
    let max_yz = f.max(y, z);
    let rhs = f.add(x, max_yz);
    let expected = f.eq(lhs, rhs);
    let proof = f.const_app(p.add_max_add_left, &[x, y, z]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("add_max_add_left must apply at free variables");
    assert!(f.k.def_eq(inferred, expected), "add_max_add_left x y z");
    assert!(
        !f.k.def_eq(lhs, rhs),
        "non-vacuity: at free variables the two sides are NOT already def_eq"
    );

    let lhs = f.min(xy, xz);
    let min_yz = f.min(y, z);
    let rhs = f.add(x, min_yz);
    let expected = f.eq(lhs, rhs);
    let proof = f.const_app(p.add_min_add_left, &[x, y, z]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("add_min_add_left must apply at free variables");
    assert!(f.k.def_eq(inferred, expected), "add_min_add_left x y z");

    let yz = f.add(y, z);
    let lhs = f.max(xz, yz);
    let max_xy = f.max(x, y);
    let rhs = f.add(max_xy, z);
    let expected = f.eq(lhs, rhs);
    let proof = f.const_app(p.add_max_add_right, &[x, y, z]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("add_max_add_right must apply at free variables");
    assert!(f.k.def_eq(inferred, expected), "add_max_add_right x y z");

    let lhs = f.min(xz, yz);
    let min_xy = f.min(x, y);
    let rhs = f.add(min_xy, z);
    let expected = f.eq(lhs, rhs);
    let proof = f.const_app(p.add_min_add_right, &[x, y, z]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("add_min_add_right must apply at free variables");
    assert!(f.k.def_eq(inferred, expected), "add_min_add_right x y z");
}

/// `add_eq_max_iff` / `add_eq_min_iff`, each used in the direction that
/// produces something checkable, plus the instance that makes them
/// non-vacuous: at `2, 3` neither `2 + 3 = max 2 3` nor `2 + 3 = min 2 3`
/// holds, so the biconditionals are not `True <-> True`.
#[test]
fn the_degeneracy_characterisations_apply_and_are_not_vacuous() {
    let mut f = Fixture::new();
    let p = f.p;
    let zero = f.zero();
    let two = f.num(2);
    let three = f.num(3);
    let seven = f.num(7);

    // Non-vacuity first: 2 + 3 is 5, and neither max nor min of 2 and 3 is 5.
    let sum_2_3 = f.add(two, three);
    let max_2_3 = f.max(two, three);
    let min_2_3 = f.min(two, three);
    assert!(
        !f.k.def_eq(sum_2_3, max_2_3),
        "non-vacuity: 2 + 3 is not max 2 3"
    );
    assert!(
        !f.k.def_eq(sum_2_3, min_2_3),
        "non-vacuity: 2 + 3 is not min 2 3"
    );

    // add_eq_max_iff, reverse leg at m = 0: `Or.inl (refl 0)` gives
    // `0 + 7 = max 0 7`, and both sides reduce to 7.
    let sum_0_7 = f.add(zero, seven);
    let max_0_7 = f.max(zero, seven);
    let lhs_ty = f.eq(sum_0_7, max_0_7);
    let m_zero = f.eq(zero, zero);
    let n_zero = f.eq(seven, zero);
    let rhs_ty = f.const_app(p.logic.or, &[m_zero, n_zero]);
    let expected = f.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);
    let iff_proof = f.const_app(p.add_eq_max_iff, &[zero, seven]);
    let inferred =
        f.k.infer(iff_proof)
            .expect("add_eq_max_iff 0 7 must type-check");
    assert!(f.k.def_eq(inferred, expected), "add_eq_max_iff 0 7");
    assert!(f.k.def_eq(sum_0_7, seven), "0 + 7 must reduce to 7");
    assert!(f.k.def_eq(max_0_7, seven), "max 0 7 must reduce to 7");

    // add_eq_min_iff at 0 0: both sides of the left-hand equation reduce to
    // 0, and the right-hand side is a conjunction of reflexivities.
    let sum_0_0 = f.add(zero, zero);
    let min_0_0 = f.min(zero, zero);
    let lhs_ty = f.eq(sum_0_0, min_0_0);
    let z_eq = f.eq(zero, zero);
    let rhs_ty = f.const_app(p.logic.and, &[z_eq, z_eq]);
    let expected = f.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);
    let iff_proof = f.const_app(p.add_eq_min_iff, &[zero, zero]);
    let inferred =
        f.k.infer(iff_proof)
            .expect("add_eq_min_iff 0 0 must type-check");
    assert!(f.k.def_eq(inferred, expected), "add_eq_min_iff 0 0");

    // At a genuinely free pair the two right-hand sides differ: `min`'s is a
    // conjunction, `max`'s a disjunction. A wiring slip that gave both the
    // same connective would pass every concrete check above.
    let (x, y, mut ctx) = f.two_free();
    let sum_xy = f.add(x, y);
    let max_xy = f.max(x, y);
    let min_xy = f.min(x, y);
    let x_zero = f.eq(x, zero);
    let y_zero = f.eq(y, zero);

    let lhs_ty = f.eq(sum_xy, max_xy);
    let rhs_ty = f.const_app(p.logic.or, &[x_zero, y_zero]);
    let expected = f.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);
    let proof = f.const_app(p.add_eq_max_iff, &[x, y]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("add_eq_max_iff must apply at free variables");
    assert!(f.k.def_eq(inferred, expected), "add_eq_max_iff x y");
    let wrong = f.const_app(p.logic.and, &[x_zero, y_zero]);
    let wrong = f.const_app(p.logic.iff, &[lhs_ty, wrong]);
    assert!(
        !f.k.def_eq(inferred, wrong),
        "negative control: add_eq_max_iff's right-hand side is a DISJUNCTION"
    );

    let lhs_ty = f.eq(sum_xy, min_xy);
    let rhs_ty = f.const_app(p.logic.and, &[x_zero, y_zero]);
    let expected = f.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);
    let proof = f.const_app(p.add_eq_min_iff, &[x, y]);
    let inferred =
        f.k.infer_in(proof, &mut ctx)
            .expect("add_eq_min_iff must apply at free variables");
    assert!(f.k.def_eq(inferred, expected), "add_eq_min_iff x y");
    let wrong = f.const_app(p.logic.or, &[x_zero, y_zero]);
    let wrong = f.const_app(p.logic.iff, &[lhs_ty, wrong]);
    assert!(
        !f.k.def_eq(inferred, wrong),
        "negative control: add_eq_min_iff's right-hand side is a CONJUNCTION"
    );
}

/// Every declaration this module adds rests on zero axioms. Redundant with
/// `nat_prelude_tests::every_nat_declaration_is_checked_and_axiom_free`'s
/// environment sweep by design: that one proves the property, this one names
/// the eighteen so a rename cannot quietly drop any of them from the sweep.
#[test]
fn the_minmax_order_theory_rests_on_zero_axioms() {
    let f = Fixture::new();
    let p = f.p;
    let names = [
        p.max_eq_right,
        p.max_eq_left,
        p.min_eq_left,
        p.min_eq_right,
        p.le_max_left,
        p.le_max_right,
        p.min_le_left,
        p.min_le_right,
        p.max_comm,
        p.le_min_of_le_of_le,
        p.le_min,
        p.lt_min,
        p.add_max_add_left,
        p.add_max_add_right,
        p.add_min_add_left,
        p.add_min_add_right,
        p.add_eq_max_iff,
        p.add_eq_min_iff,
    ];
    assert_eq!(names.len(), 18, "the module declares eighteen theorems");
    for name in names {
        let shown = f.k.display_name(name).to_string();
        assert!(
            f.k.environment().iter().any(|(n, _)| *n == name),
            "{shown} must be live in the built environment"
        );
        let footprint = f.k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{shown} must rest on zero axioms, found {:?}",
            footprint
                .iter()
                .map(|n| f.k.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
}
