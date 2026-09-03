//! ADR-1585: `Alg.OrderedRing` extensions for `linarith::generic` —
//! `Alg.ofNat` (a generic numeral builder), its two laws (`ofNat_add`,
//! `ofNat_le_ofNat_of_le`), and three derived order lemmas
//! (`add_le_add_right`, `le_of_add_le_add_right`, `add_le_add`) the ℤ
//! emitter's fixed chain cites but `Alg.OrderedRing`'s five primitive order
//! laws (ADR-1584) do not carry directly.
//!
//! ADR-1584 §5 named three blockers to a generic `linarith` emitter. This is
//! blocker 1 (the missing citations, DERIVED rather than added as new
//! record fields — the record itself is untouched) and blocker 2 (the
//! numeral builder). Every derivation here is proved ONCE, generically over
//! `(R : Alg.OrderedRing)`, from `R`'s own fields via the
//! [`structures::EqB`] toolkit — no new record field, no inheritance, the
//! same pattern `algebra_ext.rs`'s own generic theorems use.
//!
//! `ofNat_le_ofNat_of_le` needs `zero ≤ one`, which is **not** derivable from
//! `OrderedRing`'s five order laws alone (they say nothing about the ring
//! unit's sign — nothing here rules out an instance where `one < zero`). So
//! it takes `h01 : R.le R.zero R.one` as an explicit hypothesis rather than
//! assuming it holds at every `OrderedRing`. Both `Int.orderedRing` and
//! `Rat.orderedRing` supply it easily (`le_of_lt` applied to the existing
//! `zero_lt_one`) — see `linarith::generic`.

use super::RatPrelude;
use super::algebra_ext::nat_rec_prop;
use super::algebra_instances::sel;
use crate::BinderInfo;
use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::NatPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::nat_prelude::structures::{
    self, EqB, RecordNames, app2, arrow, lam_over, pi_over, symm_of,
};

/// Apply selector `i` of `ordered_ring` to `r`.
fn s(k: &mut Kernel, rn: &RecordNames, i: usize, r: ExprId) -> ExprId {
    sel(k, rn, i, r)
}

fn ofnat_of(k: &mut Kernel, ofnat_name: NameId, r: ExprId, n: ExprId) -> ExprId {
    let c = k.const_(ofnat_name, vec![]);
    let e1 = k.app(c, r);
    k.app(e1, n)
}

// ---------------------------------------------------------------------------
// Blocker 2: `Alg.ofNat` and its two laws.
// ---------------------------------------------------------------------------

/// `ofNat R 0 = R.zero`, `ofNat R (succ n) = R.add (ofNat R n) R.one` — a
/// `Nat.rec` over `R`'s own `add`/`one`/`zero`, the constant-motive-in-`n`
/// shape `Alg.npow` (ADR-1584) already uses (the return type does not
/// depend on `n`).
fn build_ofnat(
    k: &mut Kernel,
    l1: LevelId,
    ordered_ring: &RecordNames,
    nat_rec: NameId,
    nat_ty: ExprId,
) -> (ExprId, ExprId) {
    use structures::idx::ordered_ring::{ADD, CARRIER, ONE, ZERO};
    const R_FV: u64 = 24_000;
    const N_FV: u64 = 24_001;
    const NP_FV: u64 = 24_002;
    const IH_FV: u64 = 24_003;
    let anon = k.anon();

    let ind_ty = k.const_(ordered_ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = s(k, ordered_ring, CARRIER, r);
    let zero = s(k, ordered_ring, ZERO, r);
    let one = s(k, ordered_ring, ONE, r);
    let add = s(k, ordered_ring, ADD, r);

    let motive = k.lam(anon, nat_ty, carrier, BinderInfo::Default);
    let step = {
        let ih = k.fvar(IH_FV);
        let body = app2(k, add, ih, one);
        let inner = lam_over(k, IH_FV, carrier, body);
        lam_over(k, NP_FV, nat_ty, inner)
    };
    let rec_c = k.const_(nat_rec, vec![l1]);
    let rec_applied = {
        let e1 = k.app(rec_c, motive);
        let e2 = k.app(e1, zero);
        k.app(e2, step)
    };
    let n = k.fvar(N_FV);
    let result = k.app(rec_applied, n);
    let value = lam_over(k, N_FV, nat_ty, result);
    let value = lam_over(k, R_FV, ind_ty, value);

    let ty = {
        let t = arrow(k, nat_ty, carrier);
        pi_over(k, R_FV, ind_ty, t)
    };
    (ty, value)
}

/// `Alg.ofNat_add : forall (R:OrderedRing)(m n:Nat), ofNat R (add m n) =
/// R.add (ofNat R m)(ofNat R n)`. Induction on `n` (the argument `Nat.add`
/// recurses on, exactly `Alg.pow_add`'s own reason).
fn build_ofnat_add(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    ordered_ring: &RecordNames,
    nat: NatPrelude,
    ofnat_name: NameId,
) -> (ExprId, ExprId) {
    use structures::idx::ordered_ring::{ADD, ADD_ASSOC, ADD_ZERO, CARRIER, ONE, ZERO};
    const R_FV: u64 = 24_050;
    const M_FV: u64 = 24_051;
    const N_FV: u64 = 24_052;
    const J_FV: u64 = 24_053;
    const IH_FV: u64 = 24_054;

    let ind_ty = k.const_(ordered_ring.ind, vec![]);
    let nat_ty = k.const_(nat.nat, vec![]);
    let r = k.fvar(R_FV);
    let carrier = s(k, ordered_ring, CARRIER, r);
    let zero = s(k, ordered_ring, ZERO, r);
    let one = s(k, ordered_ring, ONE, r);
    let add = s(k, ordered_ring, ADD, r);
    let add_assoc = s(k, ordered_ring, ADD_ASSOC, r);
    let add_zero = s(k, ordered_ring, ADD_ZERO, r);
    let m = k.fvar(M_FV);

    let of = move |k2: &mut Kernel, nval: ExprId| ofnat_of(k2, ofnat_name, r, nval);
    let nadd = move |k2: &mut Kernel, a: ExprId, b: ExprId| {
        let c = k2.const_(nat.add, vec![]);
        app2(k2, c, a, b)
    };

    let of_m = of(k, m);

    let motive_body = move |k2: &mut Kernel, nvar: ExprId| -> ExprId {
        let add_m_n = nadd(k2, m, nvar);
        let lhs = of(k2, add_m_n);
        let of_n = of(k2, nvar);
        let rhs = app2(k2, add, of_m, of_n);
        structures::eq_of(k2, lg, l1, carrier, lhs, rhs)
    };

    let base = move |k2: &mut Kernel| -> ExprId {
        let rhs = app2(k2, add, of_m, zero);
        let az = k2.app(add_zero, of_m); // : Eq (add of_m zero) of_m
        symm_of(k2, lg, l1, carrier, rhs, of_m, az)
    };

    let step = move |k2: &mut Kernel, j: ExprId, ih: ExprId| -> ExprId {
        let of_j = of(k2, j);
        let add_m_j = nadd(k2, m, j);
        let of_addmj = of(k2, add_m_j);
        let of_m_of_j = app2(k2, add, of_m, of_j);
        let mut eb2 = EqB::new(k2, lg, l1, carrier, 24_200);
        let step1 = eb2.congr(of_addmj, of_m_of_j, ih, &move |k3, w| app2(k3, add, w, one));
        let lhs0 = eb2.app2(add, of_addmj, one);
        let mid = eb2.app2(add, of_m_of_j, one);
        let assoc_term = eb2.app(add_assoc, &[of_m, of_j, one]);
        let inner = eb2.app2(add, of_j, one);
        let rhs0 = eb2.app2(add, of_m, inner);
        eb2.trans(lhs0, mid, rhs0, step1, assoc_term)
    };

    let n_target = k.fvar(N_FV);
    let induction = nat_rec_prop(
        k,
        nat.rec,
        nat_ty,
        N_FV,
        J_FV,
        IH_FV,
        &motive_body,
        &base,
        &step,
        n_target,
    );

    let value = lam_over(k, N_FV, nat_ty, induction);
    let value = lam_over(k, M_FV, nat_ty, value);
    let value = lam_over(k, R_FV, ind_ty, value);

    let n_free = k.fvar(N_FV);
    let concl = motive_body(k, n_free);
    let ty = pi_over(k, N_FV, nat_ty, concl);
    let ty = pi_over(k, M_FV, nat_ty, ty);
    let ty = pi_over(k, R_FV, ind_ty, ty);
    (ty, value)
}

/// `Alg.ofNat_le_ofNat_of_le : forall (R:OrderedRing), R.le R.zero R.one ->
/// forall (m n:Nat), Nat.le m n -> R.le (ofNat R m)(ofNat R n)`. Induction
/// on the `Nat.le` DERIVATION (`Nat.le.rec`, `m` fixed as the recursor's
/// parameter), the same shape `nat_prelude/order.rs`'s `le_trans` uses.
#[allow(clippy::too_many_lines)]
fn build_ofnat_le_ofnat_of_le(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    ordered_ring: &RecordNames,
    nat: NatPrelude,
    ofnat_name: NameId,
) -> (ExprId, ExprId) {
    use structures::idx::ordered_ring::ADD;
    use structures::idx::ordered_ring::{
        ADD_LE_ADD_LEFT, ADD_ZERO, CARRIER, LE, LE_REFL, LE_TRANS, ONE, ZERO,
    };
    const R_FV: u64 = 24_300;
    const H01_FV: u64 = 24_301;
    const M_FV: u64 = 24_302;
    const N_FV: u64 = 24_303;
    const H_FV: u64 = 24_304;
    const X_FV: u64 = 24_305;
    const HX_FV: u64 = 24_306;
    const IH_FV: u64 = 24_307;

    let anon = k.anon();
    let ind_ty = k.const_(ordered_ring.ind, vec![]);
    let nat_ty = k.const_(nat.nat, vec![]);
    let r = k.fvar(R_FV);
    let carrier = s(k, ordered_ring, CARRIER, r);
    let zero = s(k, ordered_ring, ZERO, r);
    let one = s(k, ordered_ring, ONE, r);
    let add = s(k, ordered_ring, ADD, r);
    let add_zero = s(k, ordered_ring, ADD_ZERO, r);
    let le = s(k, ordered_ring, LE, r);
    let le_refl = s(k, ordered_ring, LE_REFL, r);
    let le_trans = s(k, ordered_ring, LE_TRANS, r);
    let add_le_add_left = s(k, ordered_ring, ADD_LE_ADD_LEFT, r);

    let h01_ty = app2(k, le, zero, one);
    let h01 = k.fvar(H01_FV);

    // `le_self_add_one(x) : le x (add x one)`, from `h01` and
    // `add_le_add_left`, rewriting `add x zero -> x` on the left.
    let le_self_add_one = move |k2: &mut Kernel, x: ExprId| -> ExprId {
        let mut eb = EqB::new(k2, lg, l1, carrier, 24_400);
        let grow = eb.app(add_le_add_left, &[zero, one, x, h01]); // : le (add x zero)(add x one)
        let xz = eb.app2(add, x, zero);
        let xo = eb.app2(add, x, one);
        let eqz = eb.app(add_zero, &[x]); // : Eq (add x zero) x
        eb.subst(xz, x, eqz, &|k3, t| app2(k3, le, t, xo), grow)
    };

    let le_ = move |k2: &mut Kernel, a: ExprId, b: ExprId| app2(k2, le, a, b);
    let nle = move |k2: &mut Kernel, a: ExprId, b: ExprId| {
        let c = k2.const_(nat.le, vec![]);
        app2(k2, c, a, b)
    };

    let m = k.fvar(M_FV);
    let of_m = ofnat_of(k, ofnat_name, r, m);

    // motive := fun (x:Nat) (_:Nat.le m x) => le (ofNat R m)(ofNat R x)
    let motive = {
        let x = k.fvar(X_FV);
        let of_x = ofnat_of(k, ofnat_name, r, x);
        let body = le_(k, of_m, of_x);
        let dom = nle(k, m, x);
        let inner = k.lam(anon, dom, body, BinderInfo::Default);
        lam_over(k, X_FV, nat_ty, inner)
    };
    let minor_refl = k.app(le_refl, of_m); // : le of_m of_m
    let minor_step = {
        let x = k.fvar(X_FV);
        let hx_ty = nle(k, m, x);
        let of_x = ofnat_of(k, ofnat_name, r, x);
        let ih_ty = le_(k, of_m, of_x);
        let ih = k.fvar(IH_FV);
        let succ_x = {
            let succ_c = k.const_(nat.succ, vec![]);
            k.app(succ_c, x)
        };
        let of_succx = ofnat_of(k, ofnat_name, r, succ_x); // reduces to add of_x one
        let step_fact = le_self_add_one(k, of_x); // : le of_x (add of_x one)
        let body = {
            let e1 = k.app(le_trans, of_m);
            let e2 = k.app(e1, of_x);
            let e3 = k.app(e2, of_succx);
            let e4 = k.app(e3, ih);
            k.app(e4, step_fact)
        };
        let l_ih = lam_over(k, IH_FV, ih_ty, body);
        let l_hx = lam_over(k, HX_FV, hx_ty, l_ih);
        lam_over(k, X_FV, nat_ty, l_hx)
    };

    let n = k.fvar(N_FV);
    let h_ty = nle(k, m, n);
    let h = k.fvar(H_FV);
    let le_rec = k.const_(nat.le_rec, vec![]);
    let applied = {
        let e1 = k.app(le_rec, m);
        let e2 = k.app(e1, motive);
        let e3 = k.app(e2, minor_refl);
        let e4 = k.app(e3, minor_step);
        let e5 = k.app(e4, n);
        k.app(e5, h)
    };

    let value = lam_over(k, H_FV, h_ty, applied);
    let value = lam_over(k, N_FV, nat_ty, value);
    let value = lam_over(k, M_FV, nat_ty, value);
    let value = lam_over(k, H01_FV, h01_ty, value);
    let value = lam_over(k, R_FV, ind_ty, value);

    let n2 = k.fvar(N_FV);
    let of_n2 = ofnat_of(k, ofnat_name, r, n2);
    let concl = le_(k, of_m, of_n2);
    let h_ty2 = nle(k, m, n2);
    let ty = arrow(k, h_ty2, concl);
    let ty = pi_over(k, N_FV, nat_ty, ty);
    let ty = pi_over(k, M_FV, nat_ty, ty);
    let ty = arrow(k, h01_ty, ty);
    let ty = pi_over(k, R_FV, ind_ty, ty);
    (ty, value)
}

// ---------------------------------------------------------------------------
// Blocker 1: three derived order lemmas `linarith::generic`'s fixed chain
// cites, none of them new `OrderedRing` fields — each is a `derive_*`
// theorem proved once from the five primitive order laws plus `Ring`'s
// `neg`, the same "prefer a derivation" shape `Ring.toCommGroup` (ADR-1584)
// used for `identL`/`invL`.
// ---------------------------------------------------------------------------

/// `Alg.add_le_add_right : forall (R:OrderedRing)(a b c:R.carrier), R.le a b
/// -> R.le (R.add a c)(R.add b c)` — from `add_le_add_left` + `addComm`,
/// rewriting both sides of `add_le_add_left(c,a,b,h)` across
/// `add c x = add x c`.
fn build_add_le_add_right(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    ordered_ring: &RecordNames,
) -> (ExprId, ExprId) {
    use structures::idx::ordered_ring::{ADD, ADD_COMM, ADD_LE_ADD_LEFT, CARRIER, LE};
    const R_FV: u64 = 24_500;
    const A_FV: u64 = 24_501;
    const B_FV: u64 = 24_502;
    const C_FV: u64 = 24_503;
    const H_FV: u64 = 24_504;

    let ind_ty = k.const_(ordered_ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = s(k, ordered_ring, CARRIER, r);
    let add = s(k, ordered_ring, ADD, r);
    let le = s(k, ordered_ring, LE, r);
    let add_comm = s(k, ordered_ring, ADD_COMM, r);
    let add_le_add_left = s(k, ordered_ring, ADD_LE_ADD_LEFT, r);

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let c = k.fvar(C_FV);
    let hab_ty = app2(k, le, a, b);
    let h = k.fvar(H_FV);

    let mut eb = EqB::new(k, lg, l1, carrier, 24_600);
    let h0 = eb.app(add_le_add_left, &[a, b, c, h]); // : le (add c a)(add c b)
    let ca = eb.app2(add, c, a);
    let ac = eb.app2(add, a, c);
    let cb = eb.app2(add, c, b);
    let bc = eb.app2(add, b, c);

    let e1 = eb.app(add_comm, &[c, a]); // : Eq ca ac
    let h1 = eb.subst(ca, ac, e1, &|k2, x| app2(k2, le, x, cb), h0);
    let e2 = eb.app(add_comm, &[c, b]); // : Eq cb bc
    let h2 = eb.subst(cb, bc, e2, &|k2, x| app2(k2, le, ac, x), h1);

    let k = eb.kernel();
    let concl = app2(k, le, ac, bc);
    let value = {
        let v = h2;
        let v = lam_over(k, H_FV, hab_ty, v);
        let v = lam_over(k, C_FV, carrier, v);
        let v = lam_over(k, B_FV, carrier, v);
        let v = lam_over(k, A_FV, carrier, v);
        lam_over(k, R_FV, ind_ty, v)
    };
    let ty = {
        let t = arrow(k, hab_ty, concl);
        let t = pi_over(k, C_FV, carrier, t);
        let t = pi_over(k, B_FV, carrier, t);
        let t = pi_over(k, A_FV, carrier, t);
        pi_over(k, R_FV, ind_ty, t)
    };
    (ty, value)
}

/// `Eq (add (neg y)(add x y)) x` — the cancellation the ℤ/ℚ preludes each
/// hand-prove once per carrier (`Int.add_neg_cancel_left`); here built
/// generically from `assoc`+`addComm`+`negAdd`+`addZero`.
#[allow(clippy::too_many_arguments)]
fn cancel_neg_add_left(
    eb: &mut EqB<'_>,
    add: ExprId,
    neg: ExprId,
    zero: ExprId,
    add_assoc: ExprId,
    add_comm: ExprId,
    add_zero: ExprId,
    neg_add: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let neg_y = eb.app(neg, &[y]);
    let inner = eb.app2(add, x, y);
    let target = eb.app2(add, neg_y, inner);

    let grouped = eb.app2(add, neg_y, x);
    let regrouped = eb.app2(add, grouped, y);
    let assoc1 = eb.app(add_assoc, &[neg_y, x, y]); // : Eq regrouped target
    let back1 = eb.symm(regrouped, target, assoc1); // : Eq target regrouped

    let flipped_grouped = eb.app2(add, x, neg_y);
    let comm1 = eb.app(add_comm, &[neg_y, x]); // : Eq grouped flipped_grouped
    let step2 = eb.congr(grouped, flipped_grouped, comm1, &|k2, t| {
        app2(k2, add, t, y)
    });
    let flipped_regrouped = eb.app2(add, flipped_grouped, y);
    let mid = eb.trans(target, regrouped, flipped_regrouped, back1, step2);

    let assoc2 = eb.app(add_assoc, &[x, neg_y, y]); // : Eq flipped_regrouped (add x (add neg_y y))
    let neg_y_y = eb.app2(add, neg_y, y);
    let x_plus_negyy = eb.app2(add, x, neg_y_y);
    let mid2 = eb.trans(target, flipped_regrouped, x_plus_negyy, mid, assoc2);

    let comm2 = eb.app(add_comm, &[neg_y, y]); // : Eq neg_y_y (add y neg_y)
    let y_negy = eb.app2(add, y, neg_y);
    let na = eb.app(neg_add, &[y]); // : Eq (add y neg_y) zero
    let neg_y_y_zero = eb.trans(neg_y_y, y_negy, zero, comm2, na); // : Eq neg_y_y zero
    let step4 = eb.congr(neg_y_y, zero, neg_y_y_zero, &|k2, t| app2(k2, add, x, t));
    let x_zero = eb.app2(add, x, zero);
    let mid3 = eb.trans(target, x_plus_negyy, x_zero, mid2, step4);

    let az = eb.app(add_zero, &[x]); // : Eq (add x zero) x
    eb.trans(target, x_zero, x, mid3, az)
}

/// `Alg.le_of_add_le_add_right : forall (R:OrderedRing)(a b c:R.carrier),
/// R.le (R.add a c)(R.add b c) -> R.le a b` — cancel `c` by adding `neg c`
/// on the left of `add_le_add_left`, then rewrite both sides via
/// [`cancel_neg_add_left`].
#[allow(clippy::too_many_lines)]
fn build_le_of_add_le_add_right(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    ordered_ring: &RecordNames,
) -> (ExprId, ExprId) {
    use structures::idx::ordered_ring::{
        ADD, ADD_ASSOC, ADD_COMM, ADD_LE_ADD_LEFT, ADD_ZERO, CARRIER, LE, NEG, NEG_ADD, ZERO,
    };
    const R_FV: u64 = 24_700;
    const A_FV: u64 = 24_701;
    const B_FV: u64 = 24_702;
    const C_FV: u64 = 24_703;
    const H_FV: u64 = 24_704;

    let ind_ty = k.const_(ordered_ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = s(k, ordered_ring, CARRIER, r);
    let add = s(k, ordered_ring, ADD, r);
    let neg = s(k, ordered_ring, NEG, r);
    let zero = s(k, ordered_ring, ZERO, r);
    let le = s(k, ordered_ring, LE, r);
    let add_assoc = s(k, ordered_ring, ADD_ASSOC, r);
    let add_comm = s(k, ordered_ring, ADD_COMM, r);
    let add_zero = s(k, ordered_ring, ADD_ZERO, r);
    let neg_add = s(k, ordered_ring, NEG_ADD, r);
    let add_le_add_left = s(k, ordered_ring, ADD_LE_ADD_LEFT, r);

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let c = k.fvar(C_FV);
    let ac = app2(k, add, a, c);
    let bc = app2(k, add, b, c);
    let hyp_ty = app2(k, le, ac, bc);
    let h = k.fvar(H_FV);

    let mut eb = EqB::new(k, lg, l1, carrier, 24_800);
    let neg_c = eb.app(neg, &[c]);
    let h2 = eb.app(add_le_add_left, &[ac, bc, neg_c, h]); // : le (add neg_c ac)(add neg_c bc)

    let eq_a = cancel_neg_add_left(
        &mut eb, add, neg, zero, add_assoc, add_comm, add_zero, neg_add, a, c,
    ); // : Eq (add neg_c ac) a
    let eq_b = cancel_neg_add_left(
        &mut eb, add, neg, zero, add_assoc, add_comm, add_zero, neg_add, b, c,
    ); // : Eq (add neg_c bc) b

    let neg_c_ac = eb.app2(add, neg_c, ac);
    let neg_c_bc = eb.app2(add, neg_c, bc);
    let h3 = eb.subst(neg_c_ac, a, eq_a, &|k2, x| app2(k2, le, x, neg_c_bc), h2);
    let h4 = eb.subst(neg_c_bc, b, eq_b, &|k2, x| app2(k2, le, a, x), h3);

    let k = eb.kernel();
    let concl = app2(k, le, a, b);
    let value = {
        let v = h4;
        let v = lam_over(k, H_FV, hyp_ty, v);
        let v = lam_over(k, C_FV, carrier, v);
        let v = lam_over(k, B_FV, carrier, v);
        let v = lam_over(k, A_FV, carrier, v);
        lam_over(k, R_FV, ind_ty, v)
    };
    let ty = {
        let t = arrow(k, hyp_ty, concl);
        let t = pi_over(k, C_FV, carrier, t);
        let t = pi_over(k, B_FV, carrier, t);
        let t = pi_over(k, A_FV, carrier, t);
        pi_over(k, R_FV, ind_ty, t)
    };
    (ty, value)
}

/// `Alg.add_le_add : forall (R:OrderedRing)(a b c d:R.carrier), R.le a b ->
/// R.le c d -> R.le (R.add a c)(R.add b d)` — cites the already-declared
/// `add_le_add_right` by name, plus `add_le_add_left` + `le_trans`.
fn build_add_le_add(
    k: &mut Kernel,
    ordered_ring: &RecordNames,
    add_le_add_right_name: NameId,
) -> (ExprId, ExprId) {
    use structures::idx::ordered_ring::{ADD, ADD_LE_ADD_LEFT, CARRIER, LE, LE_TRANS};
    const R_FV: u64 = 24_900;
    const A_FV: u64 = 24_901;
    const B_FV: u64 = 24_902;
    const C_FV: u64 = 24_903;
    const D_FV: u64 = 24_904;
    const H1_FV: u64 = 24_905;
    const H2_FV: u64 = 24_906;

    let ind_ty = k.const_(ordered_ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = s(k, ordered_ring, CARRIER, r);
    let add = s(k, ordered_ring, ADD, r);
    let le = s(k, ordered_ring, LE, r);
    let le_trans = s(k, ordered_ring, LE_TRANS, r);
    let add_le_add_left = s(k, ordered_ring, ADD_LE_ADD_LEFT, r);

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let c = k.fvar(C_FV);
    let d = k.fvar(D_FV);
    let hab_ty = app2(k, le, a, b);
    let hcd_ty = app2(k, le, c, d);
    let h1 = k.fvar(H1_FV);
    let h2 = k.fvar(H2_FV);

    let add_le_add_right = k.const_(add_le_add_right_name, vec![]);
    // h1' : le (add a c)(add b c)
    let h1p = {
        let e1 = k.app(add_le_add_right, r);
        let e2 = k.app(e1, a);
        let e3 = k.app(e2, b);
        let e4 = k.app(e3, c);
        k.app(e4, h1)
    };
    // h2' : le (add b c)(add b d)
    let h2p = {
        let e1 = k.app(add_le_add_left, c);
        let e2 = k.app(e1, d);
        let e3 = k.app(e2, b);
        k.app(e3, h2)
    };
    let ac = app2(k, add, a, c);
    let bc = app2(k, add, b, c);
    let bd = app2(k, add, b, d);
    let result = {
        let e1 = k.app(le_trans, ac);
        let e2 = k.app(e1, bc);
        let e3 = k.app(e2, bd);
        let e4 = k.app(e3, h1p);
        k.app(e4, h2p)
    };

    let value = {
        let v = result;
        let v = lam_over(k, H2_FV, hcd_ty, v);
        let v = lam_over(k, H1_FV, hab_ty, v);
        let v = lam_over(k, D_FV, carrier, v);
        let v = lam_over(k, C_FV, carrier, v);
        let v = lam_over(k, B_FV, carrier, v);
        let v = lam_over(k, A_FV, carrier, v);
        lam_over(k, R_FV, ind_ty, v)
    };
    let concl = app2(k, le, ac, bd);
    let ty = {
        let t = arrow(k, hcd_ty, concl);
        let t = arrow(k, hab_ty, t);
        let t = pi_over(k, D_FV, carrier, t);
        let t = pi_over(k, C_FV, carrier, t);
        let t = pi_over(k, B_FV, carrier, t);
        let t = pi_over(k, A_FV, carrier, t);
        pi_over(k, R_FV, ind_ty, t)
    };
    (ty, value)
}

// ---------------------------------------------------------------------------
// Assembly.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OrderedRingExtNames {
    pub ofnat: NameId,
    pub ofnat_add: NameId,
    pub ofnat_le_ofnat_of_le: NameId,
    pub add_le_add_right: NameId,
    pub le_of_add_le_add_right: NameId,
    pub add_le_add: NameId,
}

fn alg_root(k: &mut Kernel) -> NameId {
    let anon = k.anon();
    k.name_str(anon, "Alg")
}

pub(crate) fn intern_ordered_ring_ext(k: &mut Kernel) -> OrderedRingExtNames {
    let alg = alg_root(k);
    OrderedRingExtNames {
        ofnat: k.name_str(alg, "ofNat"),
        ofnat_add: k.name_str(alg, "ofNat_add"),
        ofnat_le_ofnat_of_le: k.name_str(alg, "ofNat_le_ofNat_of_le"),
        add_le_add_right: k.name_str(alg, "add_le_add_right"),
        le_of_add_le_add_right: k.name_str(alg, "le_of_add_le_add_right"),
        add_le_add: k.name_str(alg, "add_le_add"),
    }
}

pub(crate) fn declare_ordered_ring_ext_all(
    k: &mut Kernel,
    lg: &LogicPrelude,
    p: &RatPrelude,
    st: &structures::StructuresNames,
    names: &OrderedRingExtNames,
) -> Result<(), KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let nat = p.int.nat;
    let nat_ty = k.const_(nat.nat, vec![]);

    {
        let (ty, value) = build_ofnat(k, l1, &st.ordered_ring, nat.rec, nat_ty);
        k.add_declaration(Declaration::Definition {
            name: names.ofnat,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    {
        let (ty, value) = build_ofnat_add(k, lg, l1, &st.ordered_ring, nat, names.ofnat);
        k.add_declaration(Declaration::Theorem {
            name: names.ofnat_add,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    {
        let (ty, value) = build_ofnat_le_ofnat_of_le(k, lg, l1, &st.ordered_ring, nat, names.ofnat);
        k.add_declaration(Declaration::Theorem {
            name: names.ofnat_le_ofnat_of_le,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    {
        let (ty, value) = build_add_le_add_right(k, lg, l1, &st.ordered_ring);
        k.add_declaration(Declaration::Theorem {
            name: names.add_le_add_right,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    {
        let (ty, value) = build_le_of_add_le_add_right(k, lg, l1, &st.ordered_ring);
        k.add_declaration(Declaration::Theorem {
            name: names.le_of_add_le_add_right,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    {
        let (ty, value) = build_add_le_add(k, &st.ordered_ring, names.add_le_add_right);
        k.add_declaration(Declaration::Theorem {
            name: names.add_le_add,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

#[cfg(test)]
mod ordered_ring_ext_tests {
    use super::*;
    use crate::Kernel;
    use crate::build_rat_prelude;

    fn nat_num(k: &mut Kernel, nat: NatPrelude, n: u32) -> ExprId {
        let mut e = k.const_(nat.zero, vec![]);
        for _ in 0..n {
            let succ_c = k.const_(nat.succ, vec![]);
            e = k.app(succ_c, e);
        }
        e
    }

    /// `Alg.ofNat Int.orderedRing 3` reduces to `Int.ofNat 3`; negative
    /// control against `Int.ofNat 4` (a copy-paste of the wrong numeral
    /// would pass an un-discriminating check).
    #[test]
    fn ofnat_evaluation_at_int_discriminates() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let r = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let three = nat_num(&mut k, p.int.nat, 3);
        let got = ofnat_of(&mut k, p.ordered_ring_ext.ofnat, r, three);

        let n3 = nat_num(&mut k, p.int.nat, 3);
        let n4 = nat_num(&mut k, p.int.nat, 4);
        let of_nat_c = k.const_(p.int.of_nat, vec![]);
        let want3 = k.app(of_nat_c, n3);
        let of_nat_c2 = k.const_(p.int.of_nat, vec![]);
        let want4 = k.app(of_nat_c2, n4);

        assert!(
            k.def_eq(got, want3),
            "Alg.ofNat(Int.orderedRing, 3) must reduce to Int.ofNat 3"
        );
        assert!(
            !k.def_eq(got, want4),
            "Alg.ofNat(Int.orderedRing, 3) must NOT reduce to Int.ofNat 4 -- \
             a discriminating negative control"
        );
    }

    /// `Alg.ofNat_add`, symbolic, at `Int.orderedRing` and `Rat.orderedRing`.
    #[test]
    fn ofnat_add_symbolic_at_int_and_rat() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let nat_ty = k.const_(p.int.nat.nat, vec![]);
        for r_name in [
            p.algebra_ext.int_ordered_ring,
            p.algebra_ext.rat_ordered_ring,
        ] {
            const M_FV: u64 = 40_100;
            const N_FV: u64 = 40_101;
            let r = k.const_(r_name, vec![]);
            let thm = k.const_(p.ordered_ring_ext.ofnat_add, vec![]);
            let m = k.fvar(M_FV);
            let n = k.fvar(N_FV);
            let applied = {
                let e1 = k.app(thm, r);
                let e2 = k.app(e1, m);
                k.app(e2, n)
            };
            let closed = {
                let v = lam_over(&mut k, N_FV, nat_ty, applied);
                lam_over(&mut k, M_FV, nat_ty, v)
            };
            k.infer(closed)
                .unwrap_or_else(|e| panic!("ofNat_add must type-check: {e:?}"));
        }
    }

    /// `Alg.ofNat_le_ofNat_of_le`, symbolic, at `Int.orderedRing` and
    /// `Rat.orderedRing`, `h01` built from each carrier's own `zero_lt_one`.
    #[test]
    fn ofnat_le_ofnat_of_le_symbolic_at_int_and_rat() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let nat_ty = k.const_(p.int.nat.nat, vec![]);

        let int_h01 = {
            let zlt1 = k.const_(p.int.zero_lt_one, vec![]);
            let le_of_lt = k.const_(p.int.le_of_lt, vec![]);
            let zero = k.const_(p.int.zero, vec![]);
            let one = k.const_(p.int.one, vec![]);
            let e1 = k.app(le_of_lt, zero);
            let e2 = k.app(e1, one);
            k.app(e2, zlt1)
        };
        let rat_h01 = {
            let zlt1 = k.const_(p.zero_lt_one, vec![]);
            let le_of_lt = k.const_(p.le_of_lt, vec![]);
            let zero = k.const_(p.zero, vec![]);
            let one = k.const_(p.one, vec![]);
            let e1 = k.app(le_of_lt, zero);
            let e2 = k.app(e1, one);
            k.app(e2, zlt1)
        };

        for (r_name, h01) in [
            (p.algebra_ext.int_ordered_ring, int_h01),
            (p.algebra_ext.rat_ordered_ring, rat_h01),
        ] {
            const M_FV: u64 = 40_200;
            const N_FV: u64 = 40_201;
            const H_FV: u64 = 40_202;
            let r = k.const_(r_name, vec![]);
            let thm = k.const_(p.ordered_ring_ext.ofnat_le_ofnat_of_le, vec![]);
            let m = k.fvar(M_FV);
            let n = k.fvar(N_FV);
            let nle_c = k.const_(p.int.nat.le, vec![]);
            let h_ty = app2(&mut k, nle_c, m, n);
            let h = k.fvar(H_FV);
            let applied = {
                let e1 = k.app(thm, r);
                let e2 = k.app(e1, h01);
                let e3 = k.app(e2, m);
                let e4 = k.app(e3, n);
                k.app(e4, h)
            };
            let closed = {
                let v = lam_over(&mut k, H_FV, h_ty, applied);
                let v = lam_over(&mut k, N_FV, nat_ty, v);
                lam_over(&mut k, M_FV, nat_ty, v)
            };
            k.infer(closed)
                .unwrap_or_else(|e| panic!("ofNat_le_ofNat_of_le must type-check: {e:?}"));
        }
    }

    /// `Alg.add_le_add_right(Int.orderedRing)` closed over `(a,b,c)` has the
    /// SAME TYPE as `Int.add_le_add_right` -- the evaluation test deliverable
    /// 1 asks for: a new field/derivation compared against the hand-proved
    /// `Int.*` lemma it stands in for.
    #[test]
    fn add_le_add_right_matches_int_add_le_add_right_by_type() {
        const A_FV: u64 = 40_300;
        const B_FV: u64 = 40_301;
        const C_FV: u64 = 40_302;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let r = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let thm = k.const_(p.ordered_ring_ext.add_le_add_right, vec![]);
        let a = k.fvar(A_FV);
        let b = k.fvar(B_FV);
        let c = k.fvar(C_FV);
        let applied = {
            let e1 = k.app(thm, r);
            let e2 = k.app(e1, a);
            let e3 = k.app(e2, b);
            k.app(e3, c)
        };
        let generic_closed = {
            let v = lam_over(&mut k, C_FV, carrier, applied);
            let v = lam_over(&mut k, B_FV, carrier, v);
            lam_over(&mut k, A_FV, carrier, v)
        };
        let generic_ty = k.infer(generic_closed).expect("generic must type-check");

        let hand = k.const_(p.int.add_le_add_right, vec![]);
        let hand_ty = k.infer(hand).expect("Int.add_le_add_right must exist");
        assert!(
            k.def_eq(generic_ty, hand_ty),
            "Alg.add_le_add_right(Int.orderedRing) closed over (a,b,c) must \
             have the SAME TYPE as Int.add_le_add_right"
        );
    }

    /// `Alg.add_le_add(Int.orderedRing)` closed over `(a,b,c,d)` has the
    /// SAME TYPE as `Int.add_le_add`.
    #[test]
    fn add_le_add_matches_int_add_le_add_by_type() {
        const A_FV: u64 = 40_310;
        const B_FV: u64 = 40_311;
        const C_FV: u64 = 40_312;
        const D_FV: u64 = 40_313;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let r = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let thm = k.const_(p.ordered_ring_ext.add_le_add, vec![]);
        let a = k.fvar(A_FV);
        let b = k.fvar(B_FV);
        let c = k.fvar(C_FV);
        let d = k.fvar(D_FV);
        let applied = {
            let e1 = k.app(thm, r);
            let e2 = k.app(e1, a);
            let e3 = k.app(e2, b);
            let e4 = k.app(e3, c);
            k.app(e4, d)
        };
        let generic_closed = {
            let v = lam_over(&mut k, D_FV, carrier, applied);
            let v = lam_over(&mut k, C_FV, carrier, v);
            let v = lam_over(&mut k, B_FV, carrier, v);
            lam_over(&mut k, A_FV, carrier, v)
        };
        let generic_ty = k.infer(generic_closed).expect("generic must type-check");

        let hand = k.const_(p.int.add_le_add, vec![]);
        let hand_ty = k.infer(hand).expect("Int.add_le_add must exist");
        assert!(
            k.def_eq(generic_ty, hand_ty),
            "Alg.add_le_add(Int.orderedRing) closed over (a,b,c,d) must \
             have the SAME TYPE as Int.add_le_add"
        );
    }

    /// `Alg.le_of_add_le_add_right`, symbolic, at `Int.orderedRing` and
    /// `Rat.orderedRing` -- no direct hand-proved counterpart under this
    /// exact name exists (only the `Iff` form), so this is a NEW fact,
    /// checked only for type-correctness at both carriers.
    #[test]
    fn le_of_add_le_add_right_symbolic_at_int_and_rat() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        for (r_name, carrier_const) in [
            (p.algebra_ext.int_ordered_ring, p.int.z),
            (p.algebra_ext.rat_ordered_ring, p.int.rat),
        ] {
            const A_FV: u64 = 40_320;
            const B_FV: u64 = 40_321;
            const C_FV: u64 = 40_322;
            const H_FV: u64 = 40_323;
            let r = k.const_(r_name, vec![]);
            let carrier = k.const_(carrier_const, vec![]);
            let thm = k.const_(p.ordered_ring_ext.le_of_add_le_add_right, vec![]);
            let a = k.fvar(A_FV);
            let b = k.fvar(B_FV);
            let c = k.fvar(C_FV);
            let le_sel = s(
                &mut k,
                &p.int.nat.structures.ordered_ring,
                structures::idx::ordered_ring::LE,
                r,
            );
            let add_sel = s(
                &mut k,
                &p.int.nat.structures.ordered_ring,
                structures::idx::ordered_ring::ADD,
                r,
            );
            let ac = app2(&mut k, add_sel, a, c);
            let bc = app2(&mut k, add_sel, b, c);
            let h_ty = app2(&mut k, le_sel, ac, bc);
            let h = k.fvar(H_FV);
            let applied = {
                let e1 = k.app(thm, r);
                let e2 = k.app(e1, a);
                let e3 = k.app(e2, b);
                let e4 = k.app(e3, c);
                k.app(e4, h)
            };
            let closed = {
                let v = lam_over(&mut k, H_FV, h_ty, applied);
                let v = lam_over(&mut k, C_FV, carrier, v);
                let v = lam_over(&mut k, B_FV, carrier, v);
                lam_over(&mut k, A_FV, carrier, v)
            };
            k.infer(closed)
                .unwrap_or_else(|e| panic!("le_of_add_le_add_right must type-check: {e:?}"));
        }
    }
}
