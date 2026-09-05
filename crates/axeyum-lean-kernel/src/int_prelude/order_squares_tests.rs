//! Evaluation tests, statement pins and negative controls for
//! `order_squares.rs`.
//!
//! Three batteries, each asserting what must hold AND what must fail so no run
//! can be vacuous:
//!
//! 1. **the statement pin** — every one of the twenty-three declarations has its
//!    full `∀`-telescoped type rebuilt here and compared against the type the
//!    environment actually stores. A weakening that still type-checks (a bound
//!    relaxed from `m` to `m + m`, a `<` softened to `≤`) leaves the prelude
//!    building and is invisible to an axiom-footprint sweep; this is what sees
//!    it. The mutation table in the lane report is measured against this test.
//! 2. **application at concrete arguments** — the two-sided square bound and
//!    the strict decrease are applied at small numerals, with the hypotheses
//!    discharged by reduction, and the SAME construction is required to be
//!    REFUSED when a bound is violated. Without the refusal half, an
//!    application test only says the lemma has enough arguments.
//! 3. **the centered representative's two branches** — at `a = 7, m = 5` the
//!    construction keeps the remainder (`c = 2`), and at `a = 8, m = 5` it must
//!    subtract the modulus (`c = 3 − 5 = −2`), because `3 + 3` does not fit
//!    under `5`. Both witnesses are checked to satisfy the predicate, and the
//!    unshifted `c = 3` is required to be refused — which is the only thing
//!    that distinguishes the two branches.
//!
//! Magnitudes are deliberately tiny: `Nat` numerals here are unary and cost is
//! superlinear in the largest magnitude formed. The largest number formed
//! anywhere in this file is `25 = 5²`.

use super::super::{Kernel, build_int_prelude};
use super::ops::IntDev;
use super::two_squares::imodeq;
use crate::NameId;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

// ---------------------------------------------------------------------------
// plumbing
// ---------------------------------------------------------------------------

/// `Int.ofNat k` for a small numeral.
fn int_num(d: &mut IntDev<'_>, k: u32) -> ExprId {
    let n = d.num(k);
    d.of_nat(n)
}

/// `Int.neg (Int.ofNat k)`.
fn int_neg_num(d: &mut IntDev<'_>, k: u32) -> ExprId {
    let v = int_num(d, k);
    d.ineg(v)
}

/// A proof of `Nat.le a b` for `a <= b`, by `Nat.le.step` from `Nat.le.refl`.
///
/// `Int.le (ofNat a) (ofNat b)` ι-reduces to `Nat.le a b` (`defs.rs`'s
/// four-case order definition), so this doubles as an `Int.le` proof at
/// non-negative numerals — and, at `negSucc`/`negSucc`, as one with the
/// arguments swapped.
fn nat_le(d: &mut IntDev<'_>, a: u32, b: u32) -> ExprId {
    assert!(a <= b, "nat_le is only for a <= b");
    let p = d.int();
    let start = d.num(a);
    let mut proof = d.const_app(p.nat.le_refl, &[start]);
    for step in a..b {
        let lower = d.num(a);
        let upper = d.num(step);
        proof = d.const_app(p.nat.le_step, &[lower, upper, proof]);
    }
    proof
}

/// A fresh top-level name for a probe theorem.
fn probe_name(d: &mut IntDev<'_>, label: &str) -> NameId {
    let anon = d.kernel().anon();
    let root = d.kernel().name_str(anon, "OrderSquaresProbe");
    d.kernel().name_str(root, label)
}

/// `∀ (x_0 … x_{arity-1} : Int), build(x_0, …)` — the type shape
/// `IntDev::int_theorem` wraps a statement in, rebuilt so a test can compare
/// against it.
fn int_forall(
    d: &mut IntDev<'_>,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let mut ty = build(d, &vars);
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, int_ty, ty);
    }
    ty
}

/// The type the environment stores for `name`.
fn stored_type(k: &Kernel, name: NameId) -> ExprId {
    match k
        .environment()
        .get(name)
        .expect("the declaration must be present")
    {
        Declaration::Theorem { ty, .. }
        | Declaration::Definition { ty, .. }
        | Declaration::Axiom { ty, .. }
        | Declaration::Opaque { ty, .. } => *ty,
        other => panic!("unexpected declaration kind: {other:?}"),
    }
}

/// The chained arrow `tys[0] → … → tys[n-1] → concl`.
fn arrows(d: &mut IntDev<'_>, tys: &[ExprId], concl: ExprId) -> ExprId {
    let mut ty = concl;
    for &hyp in tys.iter().rev() {
        ty = d.arrow(hyp, ty);
    }
    ty
}

/// The four bound hypotheses `−m ≤ c+c`, `c+c ≤ m`, `−m ≤ e+e`, `e+e ≤ m`.
fn bound_hypotheses(d: &mut IntDev<'_>, m: ExprId, c: ExprId, e: ExprId) -> Vec<ExprId> {
    let neg_m = d.ineg(m);
    let cc = d.iadd(c, c);
    let ee = d.iadd(e, e);
    let h0 = d.ile(neg_m, cc);
    let h1 = d.ile(cc, m);
    let h2 = d.ile(neg_m, ee);
    let h3 = d.ile(ee, m);
    vec![h0, h1, h2, h3]
}

/// `mul c c + mul e e`.
fn measure(d: &mut IntDev<'_>, c: ExprId, e: ExprId) -> ExprId {
    let cc = d.imul(c, c);
    let ee = d.imul(e, e);
    d.iadd(cc, ee)
}

// ---------------------------------------------------------------------------
// 1. the statement pin
// ---------------------------------------------------------------------------

/// Every declaration `order_squares.rs` makes states exactly the proposition
/// this test rebuilds — checked against the type the ENVIRONMENT stores, not
/// against the source text.
///
/// This is the guard that survives a mutation which still type-checks. An
/// axiom-footprint sweep cannot see a weakened bound; `def_eq` against a
/// separately built type can.
#[test]
fn order_squares_declarations_state_the_intended_types() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let mut checked = 0_usize;
    let mut check = |d: &mut IntDev<'_>, label: &str, name: NameId, expected: ExprId| {
        let stored = stored_type(d.kernel(), name);
        assert!(
            d.kernel().def_eq(stored, expected),
            "{label} does not state the intended proposition"
        );
        checked += 1;
    };

    // ne_zero_of_pos : ∀ k, lt 0 k → Not (Eq k 0)
    let expected = int_forall(&mut d, 1, &|d, v| {
        let zero = d.izero();
        let pos = d.ilt(zero, v[0]);
        let eq = d.ieq(v[0], zero);
        let ne = d.not(eq);
        d.arrow(pos, ne)
    });
    check(&mut d, "Int.ne_zero_of_pos", p.ne_zero_of_pos, expected);

    // neg_nonpos_of_nonneg : ∀ a, le 0 a → le (neg a) 0
    let expected = int_forall(&mut d, 1, &|d, v| {
        let zero = d.izero();
        let hyp = d.ile(zero, v[0]);
        let neg = d.ineg(v[0]);
        let concl = d.ile(neg, zero);
        d.arrow(hyp, concl)
    });
    check(
        &mut d,
        "Int.neg_nonpos_of_nonneg",
        p.neg_nonpos_of_nonneg,
        expected,
    );

    // neg_nonneg_of_nonpos : ∀ a, le a 0 → le 0 (neg a)
    let expected = int_forall(&mut d, 1, &|d, v| {
        let zero = d.izero();
        let hyp = d.ile(v[0], zero);
        let neg = d.ineg(v[0]);
        let concl = d.ile(zero, neg);
        d.arrow(hyp, concl)
    });
    check(
        &mut d,
        "Int.neg_nonneg_of_nonpos",
        p.neg_nonneg_of_nonpos,
        expected,
    );

    // neg_le_of_neg_le : ∀ a b, le (neg b) a → le (neg a) b
    let expected = int_forall(&mut d, 2, &|d, v| {
        let neg_b = d.ineg(v[1]);
        let hyp = d.ile(neg_b, v[0]);
        let neg_a = d.ineg(v[0]);
        let concl = d.ile(neg_a, v[1]);
        d.arrow(hyp, concl)
    });
    check(&mut d, "Int.neg_le_of_neg_le", p.neg_le_of_neg_le, expected);

    // add_nonneg : ∀ a b, le 0 a → le 0 b → le 0 (add a b)
    let expected = int_forall(&mut d, 2, &|d, v| {
        let zero = d.izero();
        let h0 = d.ile(zero, v[0]);
        let h1 = d.ile(zero, v[1]);
        let sum = d.iadd(v[0], v[1]);
        let concl = d.ile(zero, sum);
        arrows(d, &[h0, h1], concl)
    });
    check(&mut d, "Int.add_nonneg", p.add_nonneg, expected);

    // sub_nonpos_of_le : ∀ a b, le a b → le (sub a b) 0
    let expected = int_forall(&mut d, 2, &|d, v| {
        let zero = d.izero();
        let hyp = d.ile(v[0], v[1]);
        let diff = d.isub(v[0], v[1]);
        let concl = d.ile(diff, zero);
        d.arrow(hyp, concl)
    });
    check(&mut d, "Int.sub_nonpos_of_le", p.sub_nonpos_of_le, expected);

    // le_of_add_le_add_self : ∀ a b, le (add a a) (add b b) → le a b
    let expected = int_forall(&mut d, 2, &|d, v| {
        let aa = d.iadd(v[0], v[0]);
        let bb = d.iadd(v[1], v[1]);
        let hyp = d.ile(aa, bb);
        let concl = d.ile(v[0], v[1]);
        d.arrow(hyp, concl)
    });
    check(
        &mut d,
        "Int.le_of_add_le_add_self",
        p.le_of_add_le_add_self,
        expected,
    );

    // le_of_mul_le_mul_left : ∀ k a b, lt 0 k → le (mul k a) (mul k b) → le a b
    let expected = int_forall(&mut d, 3, &|d, v| {
        let zero = d.izero();
        let pos = d.ilt(zero, v[0]);
        let ka = d.imul(v[0], v[1]);
        let kb = d.imul(v[0], v[2]);
        let bound = d.ile(ka, kb);
        let concl = d.ile(v[1], v[2]);
        arrows(d, &[pos, bound], concl)
    });
    check(
        &mut d,
        "Int.le_of_mul_le_mul_left",
        p.le_of_mul_le_mul_left,
        expected,
    );

    // neg_mul_neg : ∀ a, Eq (mul (neg a) (neg a)) (mul a a)
    let expected = int_forall(&mut d, 1, &|d, v| {
        let neg = d.ineg(v[0]);
        let lhs = d.imul(neg, neg);
        let rhs = d.imul(v[0], v[0]);
        d.ieq(lhs, rhs)
    });
    check(&mut d, "Int.neg_mul_neg", p.neg_mul_neg, expected);

    // neg_add_self_self : ∀ m, Eq (add (neg m) (add m m)) m
    let expected = int_forall(&mut d, 1, &|d, v| {
        let neg = d.ineg(v[0]);
        let mm = d.iadd(v[0], v[0]);
        let lhs = d.iadd(neg, mm);
        d.ieq(lhs, v[0])
    });
    check(
        &mut d,
        "Int.neg_add_self_self",
        p.neg_add_self_self,
        expected,
    );

    // add_sub_add_sub : ∀ r m, Eq (add (sub r m) (sub r m)) (sub (add r r) (add m m))
    let expected = int_forall(&mut d, 2, &|d, v| {
        let diff = d.isub(v[0], v[1]);
        let lhs = d.iadd(diff, diff);
        let rr = d.iadd(v[0], v[0]);
        let mm = d.iadd(v[1], v[1]);
        let rhs = d.isub(rr, mm);
        d.ieq(lhs, rhs)
    });
    check(&mut d, "Int.add_sub_add_sub", p.add_sub_add_sub, expected);

    // sq_double_add_sq_double
    let expected = int_forall(&mut d, 2, &|d, v| {
        let cc2 = d.iadd(v[0], v[0]);
        let ee2 = d.iadd(v[1], v[1]);
        let left = d.imul(cc2, cc2);
        let right = d.imul(ee2, ee2);
        let lhs = d.iadd(left, right);
        let s = measure(d, v[0], v[1]);
        let ss = d.iadd(s, s);
        let rhs = d.iadd(ss, ss);
        d.ieq(lhs, rhs)
    });
    check(
        &mut d,
        "Int.sq_double_add_sq_double",
        p.sq_double_add_sq_double,
        expected,
    );

    // sq_le_sq_of_nonneg : ∀ a b, le 0 a → le a b → le (mul a a) (mul b b)
    let expected = int_forall(&mut d, 2, &|d, v| {
        let zero = d.izero();
        let h0 = d.ile(zero, v[0]);
        let h1 = d.ile(v[0], v[1]);
        let aa = d.imul(v[0], v[0]);
        let bb = d.imul(v[1], v[1]);
        let concl = d.ile(aa, bb);
        arrows(d, &[h0, h1], concl)
    });
    check(
        &mut d,
        "Int.sq_le_sq_of_nonneg",
        p.sq_le_sq_of_nonneg,
        expected,
    );

    // sq_le_sq_of_neg_le_of_le : ∀ a b, le (neg b) a → le a b → le (mul a a) (mul b b)
    let expected = int_forall(&mut d, 2, &|d, v| {
        let neg_b = d.ineg(v[1]);
        let h0 = d.ile(neg_b, v[0]);
        let h1 = d.ile(v[0], v[1]);
        let aa = d.imul(v[0], v[0]);
        let bb = d.imul(v[1], v[1]);
        let concl = d.ile(aa, bb);
        arrows(d, &[h0, h1], concl)
    });
    check(
        &mut d,
        "Int.sq_le_sq_of_neg_le_of_le",
        p.sq_le_sq_of_neg_le_of_le,
        expected,
    );

    // exists_centered_representative
    let expected = int_forall(&mut d, 2, &|d, v| {
        let (a, m) = (v[0], v[1]);
        let zero = d.izero();
        let pos = d.ilt(zero, m);
        let predicate = super::order_squares::centered_predicate(d, a, m);
        let concl = super::two_squares::int_exists(d, predicate);
        d.arrow(pos, concl)
    });
    check(
        &mut d,
        "Int.exists_centered_representative",
        p.exists_centered_representative,
        expected,
    );

    // two_mul_sq_add_sq_le_sq
    let expected = int_forall(&mut d, 3, &|d, v| {
        let (m, c, e) = (v[0], v[1], v[2]);
        let hyps = bound_hypotheses(d, m, c, e);
        let s = measure(d, c, e);
        let ss = d.iadd(s, s);
        let mm = d.imul(m, m);
        let concl = d.ile(ss, mm);
        arrows(d, &hyps, concl)
    });
    check(
        &mut d,
        "Int.two_mul_sq_add_sq_le_sq",
        p.two_mul_sq_add_sq_le_sq,
        expected,
    );

    // sq_add_sq_lt_sq_of_bounds
    let expected = int_forall(&mut d, 3, &|d, v| {
        let (m, c, e) = (v[0], v[1], v[2]);
        let zero = d.izero();
        let pos = d.ilt(zero, m);
        let hyps = bound_hypotheses(d, m, c, e);
        let s = measure(d, c, e);
        let mm = d.imul(m, m);
        let concl = d.ilt(s, mm);
        let inner = arrows(d, &hyps, concl);
        d.arrow(pos, inner)
    });
    check(
        &mut d,
        "Int.sq_add_sq_lt_sq_of_bounds",
        p.sq_add_sq_lt_sq_of_bounds,
        expected,
    );

    // lt_of_add_le_of_nonneg : ∀ m q, lt 0 m → le 0 q → le (add q q) m → lt q m
    let expected = int_forall(&mut d, 2, &|d, v| {
        let (m, q) = (v[0], v[1]);
        let zero = d.izero();
        let pos = d.ilt(zero, m);
        let nonneg = d.ile(zero, q);
        let qq = d.iadd(q, q);
        let bound = d.ile(qq, m);
        let concl = d.ilt(q, m);
        arrows(d, &[pos, nonneg, bound], concl)
    });
    check(
        &mut d,
        "Int.lt_of_add_le_of_nonneg",
        p.lt_of_add_le_of_nonneg,
        expected,
    );

    // lt_of_mul_lt_mul_left : ∀ k a b, le 0 k → lt (mul k a) (mul k b) → lt a b
    let expected = int_forall(&mut d, 3, &|d, v| {
        let zero = d.izero();
        let nonneg = d.ile(zero, v[0]);
        let ka = d.imul(v[0], v[1]);
        let kb = d.imul(v[0], v[2]);
        let strict = d.ilt(ka, kb);
        let concl = d.ilt(v[1], v[2]);
        arrows(d, &[nonneg, strict], concl)
    });
    check(
        &mut d,
        "Int.lt_of_mul_lt_mul_left",
        p.lt_of_mul_lt_mul_left,
        expected,
    );

    // nonneg_of_mul_nonneg_left : ∀ k a, lt 0 k → le 0 (mul k a) → le 0 a
    let expected = int_forall(&mut d, 2, &|d, v| {
        let zero = d.izero();
        let pos = d.ilt(zero, v[0]);
        let ka = d.imul(v[0], v[1]);
        let bound = d.ile(zero, ka);
        let concl = d.ile(zero, v[1]);
        arrows(d, &[pos, bound], concl)
    });
    check(
        &mut d,
        "Int.nonneg_of_mul_nonneg_left",
        p.nonneg_of_mul_nonneg_left,
        expected,
    );

    // pos_of_mul_pos_left : ∀ k a, le 0 k → lt 0 (mul k a) → lt 0 a
    let expected = int_forall(&mut d, 2, &|d, v| {
        let zero = d.izero();
        let nonneg = d.ile(zero, v[0]);
        let ka = d.imul(v[0], v[1]);
        let pos = d.ilt(zero, ka);
        let concl = d.ilt(zero, v[1]);
        arrows(d, &[nonneg, pos], concl)
    });
    check(
        &mut d,
        "Int.pos_of_mul_pos_left",
        p.pos_of_mul_pos_left,
        expected,
    );

    // eq_zero_of_sq_add_sq_eq_zero
    let expected = int_forall(&mut d, 2, &|d, v| {
        let zero = d.izero();
        let s = measure(d, v[0], v[1]);
        let hyp = d.ieq(s, zero);
        let left = d.ieq(v[0], zero);
        let right = d.ieq(v[1], zero);
        let concl = d.and(left, right);
        d.arrow(hyp, concl)
    });
    check(
        &mut d,
        "Int.eq_zero_of_sq_add_sq_eq_zero",
        p.eq_zero_of_sq_add_sq_eq_zero,
        expected,
    );

    // descentMultiplierBounds
    let expected = int_forall(&mut d, 4, &|d, v| {
        let (m, q, c, e) = (v[0], v[1], v[2], v[3]);
        let zero = d.izero();
        let pos = d.ilt(zero, m);
        let mq = d.imul(m, q);
        let s = measure(d, c, e);
        let factorisation = d.ieq(mq, s);
        let hyps = bound_hypotheses(d, m, c, e);
        let nonneg = d.ile(zero, q);
        let below = d.ilt(q, m);
        let concl = d.and(nonneg, below);
        let inner = arrows(d, &hyps, concl);
        arrows(d, &[pos, factorisation], inner)
    });
    check(
        &mut d,
        "Int.descentMultiplierBounds",
        p.descent_multiplier_bounds,
        expected,
    );

    assert_eq!(
        checked, 23,
        "every declaration in order_squares.rs must be pinned here"
    );
}

/// Every declaration `order_squares.rs` makes is present and axiom-free.
///
/// The `contains` assertion comes FIRST: `axiom_footprint` of a name that was
/// never declared is also empty, so without it this battery would pass over a
/// deleted declaration.
#[test]
fn every_order_squares_declaration_is_present_and_axiom_free() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let names: [(&str, NameId); 23] = [
        ("Int.lt_of_mul_lt_mul_left", p.lt_of_mul_lt_mul_left),
        ("Int.nonneg_of_mul_nonneg_left", p.nonneg_of_mul_nonneg_left),
        ("Int.pos_of_mul_pos_left", p.pos_of_mul_pos_left),
        (
            "Int.eq_zero_of_sq_add_sq_eq_zero",
            p.eq_zero_of_sq_add_sq_eq_zero,
        ),
        ("Int.descentMultiplierBounds", p.descent_multiplier_bounds),
        ("Int.ne_zero_of_pos", p.ne_zero_of_pos),
        ("Int.neg_nonpos_of_nonneg", p.neg_nonpos_of_nonneg),
        ("Int.neg_nonneg_of_nonpos", p.neg_nonneg_of_nonpos),
        ("Int.neg_le_of_neg_le", p.neg_le_of_neg_le),
        ("Int.add_nonneg", p.add_nonneg),
        ("Int.sub_nonpos_of_le", p.sub_nonpos_of_le),
        ("Int.le_of_add_le_add_self", p.le_of_add_le_add_self),
        ("Int.le_of_mul_le_mul_left", p.le_of_mul_le_mul_left),
        ("Int.neg_mul_neg", p.neg_mul_neg),
        ("Int.neg_add_self_self", p.neg_add_self_self),
        ("Int.add_sub_add_sub", p.add_sub_add_sub),
        ("Int.sq_double_add_sq_double", p.sq_double_add_sq_double),
        ("Int.sq_le_sq_of_nonneg", p.sq_le_sq_of_nonneg),
        ("Int.sq_le_sq_of_neg_le_of_le", p.sq_le_sq_of_neg_le_of_le),
        (
            "Int.exists_centered_representative",
            p.exists_centered_representative,
        ),
        ("Int.two_mul_sq_add_sq_le_sq", p.two_mul_sq_add_sq_le_sq),
        ("Int.sq_add_sq_lt_sq_of_bounds", p.sq_add_sq_lt_sq_of_bounds),
        ("Int.lt_of_add_le_of_nonneg", p.lt_of_add_le_of_nonneg),
    ];
    for (label, name) in names {
        assert!(
            k.environment().contains(name),
            "{label} must be declared before its footprint means anything"
        );
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} must be axiom-free, found {} axioms",
            footprint.len()
        );
    }
}

// ---------------------------------------------------------------------------
// 2. application at concrete arguments
// ---------------------------------------------------------------------------

/// Admit `theorem <label> : le (a*a) (b*b) := sq_le_sq_of_neg_le_of_le a b h1 h2`
/// for `a = ±|a|` and `b = ofNat |b|`, with the hypotheses discharged by
/// reduction, and report whether the kernel accepted it.
///
/// The lower bound `−b ≤ a` is `True.intro` when `a` is non-negative (the
/// `negSucc`/`ofNat` branch of `Int.le` reduces to `True`) and `Nat.le` with
/// the magnitudes SWAPPED when `a` is negative (the `negSucc`/`negSucc`
/// branch). The upper bound is `Nat.le |a| |b|` when `a` is non-negative and
/// `True.intro` when it is negative.
fn admits_square_bound(d: &mut IntDev<'_>, negative: bool, a: u32, b: u32, label: &str) -> bool {
    let p = d.int();
    let ai = if negative {
        int_neg_num(d, a)
    } else {
        int_num(d, a)
    };
    let bi = int_num(d, b);
    let (low, high) = if negative {
        // `−b ≤ −a` is `Nat.le (a−1) (b−1)`; `−a ≤ b` is `True`.
        let low = nat_le(
            d,
            a.saturating_sub(1).min(b.saturating_sub(1)),
            b.max(a) - 1,
        );
        let high = d.true_intro();
        (low, high)
    } else {
        let low = d.true_intro();
        let high = nat_le(d, a.min(b), a.max(b));
        (low, high)
    };
    let proof = d.const_app(p.sq_le_sq_of_neg_le_of_le, &[ai, bi, low, high]);
    let aa = d.imul(ai, ai);
    let bb = d.imul(bi, bi);
    let ty = d.ile(aa, bb);
    let name = probe_name(d, label);
    d.declare_theorem(name, ty, proof).is_ok()
}

/// The two-sided square bound applies at a positive AND a negative argument —
/// `2² ≤ 3²` and `(−2)² ≤ 3²` — and is REFUSED when the argument leaves the
/// band, `4 ≰ 3`.
///
/// The negative argument is the discriminating case: it is the branch that
/// goes through `Int.neg_mul_neg`, and a lemma stated only for non-negative
/// arguments would pass the first row and fail the second.
#[test]
fn the_two_sided_square_bound_applies_on_both_signs_and_refuses_an_out_of_band_argument() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    assert!(
        admits_square_bound(&mut d, false, 2, 3, "pos_two_three"),
        "2 lies in [-3, 3], so 2*2 <= 3*3 must be admitted"
    );
    assert!(
        admits_square_bound(&mut d, true, 2, 3, "neg_two_three"),
        "-2 lies in [-3, 3], so (-2)*(-2) <= 3*3 must be admitted"
    );
    assert!(
        !admits_square_bound(&mut d, false, 4, 3, "pos_four_three"),
        "4 does NOT lie in [-3, 3]; the kernel must refuse the instance"
    );
    assert!(
        !admits_square_bound(&mut d, true, 4, 3, "neg_four_three"),
        "-4 does NOT lie in [-3, 3]; the kernel must refuse the instance"
    );
}

/// Admit the strict decrease at `m = 5` with non-negative `c`, `e`, and report
/// the verdict. `c + c ≤ 5` is `Nat.le (2c) 5`, which cannot be built for
/// `c > 2`, so an out-of-band `c` is passed a `Nat.le` term of the wrong shape
/// and the kernel refuses the application.
fn admits_strict_decrease(d: &mut IntDev<'_>, c: u32, e: u32, label: &str) -> bool {
    let p = d.int();
    let m = 5_u32;
    let mi = int_num(d, m);
    let ci = int_num(d, c);
    let ei = int_num(d, e);
    let pos = nat_le(d, 1, m);
    let low_c = d.true_intro();
    let high_c = nat_le(d, (2 * c).min(m), (2 * c).max(m));
    let low_e = d.true_intro();
    let high_e = nat_le(d, (2 * e).min(m), (2 * e).max(m));
    let proof = d.const_app(
        p.sq_add_sq_lt_sq_of_bounds,
        &[mi, ci, ei, pos, low_c, high_c, low_e, high_e],
    );
    let s = measure(d, ci, ei);
    let mm = d.imul(mi, mi);
    let ty = d.ilt(s, mm);
    let name = probe_name(d, label);
    d.declare_theorem(name, ty, proof).is_ok()
}

/// At `m = 5` the strict decrease applies to `c = 2, e = 1` (`4 + 1 < 25`) and
/// is refused for `c = 3`, whose double `6` leaves the band — even though
/// `9 + 1 < 25` is still TRUE at those arguments.
///
/// That is the point of the refusal row: it shows the BOUND is load-bearing in
/// the statement, not merely that the conclusion happens to hold.
#[test]
fn the_strict_decrease_applies_inside_the_band_and_is_refused_outside_it() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    assert!(
        admits_strict_decrease(&mut d, 2, 1, "band_two_one"),
        "2 + 2 = 4 <= 5 and 1 + 1 = 2 <= 5, so 2*2 + 1*1 < 5*5 must be admitted"
    );
    assert!(
        !admits_strict_decrease(&mut d, 3, 1, "out_of_band_three_one"),
        "3 + 3 = 6 > 5, so the instance must be refused even though 9 + 1 < 25"
    );
}

// ---------------------------------------------------------------------------
// 3. the centered representative's two branches
// ---------------------------------------------------------------------------

/// Admit `theorem <label> : <the centered predicate at c>` for `a`, `m = 5` and
/// a concrete witness `c` (negated when `negative`), with the congruence proved
/// by `Eq.refl` (both remainders compute) and the bounds by reduction.
fn admits_centered_witness(
    d: &mut IntDev<'_>,
    a: u32,
    negative: bool,
    c: u32,
    label: &str,
) -> bool {
    let p = d.int();
    let m = 5_u32;
    let mi = int_num(d, m);
    let ai = int_num(d, a);
    let ci = if negative {
        int_neg_num(d, c)
    } else {
        int_num(d, c)
    };

    let congruent = imodeq(d, mi, ci, ai);
    let lhs = d.iemod(ci, mi);
    let refl = d.irefl(lhs);

    let cc = d.iadd(ci, ci);
    let neg_m = d.ineg(mi);
    let low_ty = d.ile(neg_m, cc);
    let high_ty = d.ile(cc, mi);
    let low = if negative {
        // `−5 ≤ −2c` is `Nat.le (2c − 1) 4` in the `negSucc`/`negSucc` branch.
        let doubled = 2 * c;
        nat_le(
            d,
            doubled.saturating_sub(1).min(m - 1),
            doubled.saturating_sub(1).max(m - 1),
        )
    } else {
        d.true_intro()
    };
    let high = if negative {
        d.true_intro()
    } else {
        nat_le(d, (2 * c).min(m), (2 * c).max(m))
    };
    let bounds_ty = d.and(low_ty, high_ty);
    let and_name = p.logic.and_intro;
    let bounds = d.const_app(and_name, &[low_ty, high_ty, low, high]);
    let payload = d.const_app(and_name, &[congruent, bounds_ty, refl, bounds]);
    let ty = d.and(congruent, bounds_ty);
    let name = probe_name(d, label);
    d.declare_theorem(name, ty, payload).is_ok()
}

/// The centered representative's two branches, pinned at `m = 5`.
///
/// `7 % 5 = 2` and `2 + 2 = 4 ≤ 5`, so the construction keeps the remainder:
/// `c = 2` satisfies the predicate. `8 % 5 = 3` and `3 + 3 = 6 > 5`, so it must
/// subtract the modulus: `c = 3` is REFUSED and `c = −2` is admitted. Nothing
/// else distinguishes the two branches, and a construction that returned the
/// bare remainder in both would pass the first row and fail the third.
#[test]
fn the_centered_representative_keeps_the_small_residue_and_shifts_the_large_one() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    assert!(
        admits_centered_witness(&mut d, 7, false, 2, "seven_keeps_two"),
        "7 = 2 (mod 5) and 2 + 2 = 4 <= 5, so c = 2 is a centered representative"
    );
    assert!(
        !admits_centered_witness(&mut d, 8, false, 3, "eight_rejects_three"),
        "8 = 3 (mod 5) but 3 + 3 = 6 > 5, so c = 3 is NOT centered"
    );
    assert!(
        admits_centered_witness(&mut d, 8, true, 2, "eight_shifts_to_minus_two"),
        "8 = -2 (mod 5) and -5 <= -4 <= 5, so c = -2 is the centered representative"
    );
    assert!(
        !admits_centered_witness(&mut d, 7, true, 2, "seven_is_not_minus_two"),
        "7 is NOT congruent to -2 modulo 5, so the congruence half must be refused"
    );
}

/// Admit `descentMultiplierBounds` at `m = 5`, `c = 2`, `e = 1` and a claimed
/// quotient `q`, with the factorisation `5*q = 2*2 + 1*1` discharged by
/// `Eq.refl` (both sides are closed numerals the kernel computes), and report
/// the verdict.
fn admits_multiplier_bounds(d: &mut IntDev<'_>, q: u32, label: &str) -> bool {
    let p = d.int();
    let m = 5_u32;
    let mi = int_num(d, m);
    let qi = int_num(d, q);
    let ci = int_num(d, 2);
    let ei = int_num(d, 1);
    let pos = nat_le(d, 1, m);
    let mq = d.imul(mi, qi);
    let fact = d.irefl(mq);
    let low_c = d.true_intro();
    let high_c = nat_le(d, 4, m);
    let low_e = d.true_intro();
    let high_e = nat_le(d, 2, m);
    let proof = d.const_app(
        p.descent_multiplier_bounds,
        &[mi, qi, ci, ei, pos, fact, low_c, high_c, low_e, high_e],
    );
    let zero = d.izero();
    let nonneg = d.ile(zero, qi);
    let below = d.ilt(qi, mi);
    let ty = d.and(nonneg, below);
    let name = probe_name(d, label);
    d.declare_theorem(name, ty, proof).is_ok()
}

/// The descent's termination certificate at a worked instance: `5*1 = 2² + 1²`
/// with both representatives inside the band gives `0 ≤ 1` and `1 < 5`; the
/// same call with `q = 2` is REFUSED, because `5*2` is not `2² + 1²`.
///
/// The refusal row is what says the FACTORISATION hypothesis is read: the
/// conclusion `0 ≤ 2 ∧ 2 < 5` is perfectly true, so a lemma that ignored its
/// second hypothesis would pass both rows.
#[test]
fn the_multiplier_bounds_apply_at_a_worked_factorisation_and_refuse_a_wrong_quotient() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    assert!(
        admits_multiplier_bounds(&mut d, 1, "quotient_one"),
        "5*1 = 2*2 + 1*1, so q = 1 must be certified non-negative and below 5"
    );
    assert!(
        !admits_multiplier_bounds(&mut d, 2, "quotient_two"),
        "5*2 is not 2*2 + 1*1; the kernel must refuse the instance even though          0 <= 2 and 2 < 5 both hold"
    );
}
