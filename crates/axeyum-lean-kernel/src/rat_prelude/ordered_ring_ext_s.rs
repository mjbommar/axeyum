//! ADR-1592: `AlgS.OrderedRing` extensions for `linarith::generic`'s setoid
//! backend — the setoid twin of [`super::ordered_ring_ext`] (ADR-1585):
//! `AlgS.ofNat`, its two laws (`ofNat_add`, `ofNat_le_ofNat_of_le`), and
//! three derived order lemmas (`add_le_add_right`, `le_of_add_le_add_right`,
//! `add_le_add`), all proved once, generically, over `(R : AlgS.
//! OrderedRing)`.
//!
//! **Shorter than the `Eq`-flavored versions, not merely different.**
//! `ordered_ring_ext`'s derivations lean on `structures::EqB`'s `Eq.rec`-
//! based `subst`/`congr_arg` because `Eq`'s congruence is free for an
//! arbitrary predicate. A setoid has no such free lunch (ADR-1588's own
//! point) — but `AlgS.OrderedRing` carries `leCongr`/`addCongr` as FIRST-
//! CLASS FIELDS, so a rewrite under `le`/`add` is one direct field
//! application, never a hand-built `Eq.rec` motive. `build_add_le_add_
//! right_s` in particular is four lines shorter than its `Eq`-flavored
//! counterpart for exactly this reason.
//!
//! Also declares the two named instances this module's own consumers need:
//! `AlgS.OrderedRing.ofAlg(Int.orderedRing)`/`(Rat.orderedRing)`.

use super::RatPrelude;
use super::algebra_ext::nat_rec_prop;
use crate::BinderInfo;
use crate::Kernel;
use crate::KernelError;
use crate::NatPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::nat_prelude::structures::RecordNames;
use crate::nat_prelude::structures::sel;
use crate::nat_prelude::structures_setoid as structures_s;

/// Apply selector `i` of `ordered_ring` to `r`.
fn s(k: &mut Kernel, rn: &RecordNames, i: usize, r: ExprId) -> ExprId {
    sel(k, rn, i, r)
}

/// Small app-chain helper — the record's own equiv infrastructure/laws are
/// VALUES, not kernel primitives (see `structures_setoid`'s module doc).
fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut e = f;
    for x in xs {
        e = k.app(e, *x);
    }
    e
}

fn ofnat_of(k: &mut Kernel, ofnat_name: NameId, r: ExprId, n: ExprId) -> ExprId {
    let c = k.const_(ofnat_name, vec![]);
    let e1 = k.app(c, r);
    k.app(e1, n)
}

// ---------------------------------------------------------------------------
// `AlgS.ofNat` and its two laws — identical structure to `ordered_ring_ext`'s
// `build_ofnat`/`build_ofnat_add`/`build_ofnat_le_ofnat_of_le`, `Eq.rec`
// transport replaced by direct field application.
// ---------------------------------------------------------------------------

fn build_ofnat_s(
    k: &mut Kernel,
    l1: LevelId,
    ordered_ring: &RecordNames,
    nat_rec: NameId,
    nat_ty: ExprId,
) -> (ExprId, ExprId) {
    use structures_s::idx::ordered_ring::{ADD, CARRIER, ONE, ZERO};
    const R_FV: u64 = 25_000;
    const N_FV: u64 = 25_001;
    const NP_FV: u64 = 25_002;
    const IH_FV: u64 = 25_003;
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
        let body = t_app(k, add, &[ih, one]);
        let inner = crate::nat_prelude::structures::lam_over(k, IH_FV, carrier, body);
        crate::nat_prelude::structures::lam_over(k, NP_FV, nat_ty, inner)
    };
    let rec_c = k.const_(nat_rec, vec![l1]);
    let rec_applied = {
        let e1 = k.app(rec_c, motive);
        let e2 = k.app(e1, zero);
        k.app(e2, step)
    };
    let n = k.fvar(N_FV);
    let result = k.app(rec_applied, n);
    let value = crate::nat_prelude::structures::lam_over(k, N_FV, nat_ty, result);
    let value = crate::nat_prelude::structures::lam_over(k, R_FV, ind_ty, value);

    let ty = {
        let t = crate::nat_prelude::structures::arrow(k, nat_ty, carrier);
        crate::nat_prelude::structures::pi_over(k, R_FV, ind_ty, t)
    };
    (ty, value)
}

/// `AlgS.ofNat_add : forall (R:OrderedRing)(m n:Nat), equiv (ofNat R (add m
/// n)) (R.add (ofNat R m)(ofNat R n))`. Induction on `n`.
fn build_ofnat_add_s(
    k: &mut Kernel,
    ordered_ring: &RecordNames,
    nat: NatPrelude,
    ofnat_name: NameId,
) -> (ExprId, ExprId) {
    use crate::nat_prelude::structures::{lam_over, pi_over};
    use structures_s::idx::ordered_ring::{ADD, ADD_ASSOC, ADD_CONGR, ADD_ZERO, EQUIV};
    use structures_s::idx::ordered_ring::{EQUIV_REFL, EQUIV_SYMM, EQUIV_TRANS, ZERO};
    const R_FV: u64 = 25_050;
    const M_FV: u64 = 25_051;
    const N_FV: u64 = 25_052;
    const J_FV: u64 = 25_053;
    const IH_FV: u64 = 25_054;

    let ind_ty = k.const_(ordered_ring.ind, vec![]);
    let nat_ty = k.const_(nat.nat, vec![]);
    let r = k.fvar(R_FV);
    let equiv = s(k, ordered_ring, EQUIV, r);
    let equiv_refl = s(k, ordered_ring, EQUIV_REFL, r);
    let equiv_symm = s(k, ordered_ring, EQUIV_SYMM, r);
    let equiv_trans = s(k, ordered_ring, EQUIV_TRANS, r);
    let add = s(k, ordered_ring, ADD, r);
    let add_congr = s(k, ordered_ring, ADD_CONGR, r);
    let add_assoc = s(k, ordered_ring, ADD_ASSOC, r);
    let add_zero = s(k, ordered_ring, ADD_ZERO, r);
    let zero = s(k, ordered_ring, ZERO, r);
    let m = k.fvar(M_FV);

    let of = move |k2: &mut Kernel, nval: ExprId| ofnat_of(k2, ofnat_name, r, nval);
    let nadd = move |k2: &mut Kernel, a: ExprId, b: ExprId| {
        let c = k2.const_(nat.add, vec![]);
        t_app(k2, c, &[a, b])
    };

    let of_m = of(k, m);

    let motive_body = move |k2: &mut Kernel, nvar: ExprId| -> ExprId {
        let add_m_n = nadd(k2, m, nvar);
        let lhs = of(k2, add_m_n);
        let of_n = of(k2, nvar);
        let rhs = t_app(k2, add, &[of_m, of_n]);
        t_app(k2, equiv, &[lhs, rhs])
    };

    let base = move |k2: &mut Kernel| -> ExprId {
        let rhs = t_app(k2, add, &[of_m, zero]);
        let az = k2.app(add_zero, of_m); // : equiv (add of_m zero) of_m
        t_app(k2, equiv_symm, &[rhs, of_m, az])
    };

    let step = move |k2: &mut Kernel, j: ExprId, ih: ExprId| -> ExprId {
        let of_j = of(k2, j);
        let add_m_j = nadd(k2, m, j);
        let of_addmj = of(k2, add_m_j);
        let of_m_of_j = t_app(k2, add, &[of_m, of_j]);
        let one = s(k2, ordered_ring, structures_s::idx::ordered_ring::ONE, r);
        let refl_one = k2.app(equiv_refl, one);
        let step1 = t_app(
            k2,
            add_congr,
            &[of_addmj, of_m_of_j, one, one, ih, refl_one],
        );
        let lhs0 = t_app(k2, add, &[of_addmj, one]);
        let mid = t_app(k2, add, &[of_m_of_j, one]);
        let assoc_term = t_app(k2, add_assoc, &[of_m, of_j, one]);
        let inner = t_app(k2, add, &[of_j, one]);
        let rhs0 = t_app(k2, add, &[of_m, inner]);
        t_app(k2, equiv_trans, &[lhs0, mid, rhs0, step1, assoc_term])
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

/// `AlgS.ofNat_le_ofNat_of_le : forall (R:OrderedRing), R.le R.zero R.one ->
/// forall (m n:Nat), Nat.le m n -> R.le (ofNat R m)(ofNat R n)`.
#[allow(clippy::too_many_lines)]
fn build_ofnat_le_ofnat_of_le_s(
    k: &mut Kernel,
    ordered_ring: &RecordNames,
    nat: NatPrelude,
    ofnat_name: NameId,
) -> (ExprId, ExprId) {
    use crate::nat_prelude::structures::{app2, arrow, lam_over, pi_over};
    use structures_s::idx::ordered_ring::{
        ADD, ADD_LE_ADD_LEFT, ADD_ZERO, EQUIV_REFL, LE, LE_CONGR, LE_REFL, LE_TRANS, ONE, ZERO,
    };
    const R_FV: u64 = 25_300;
    const H01_FV: u64 = 25_301;
    const M_FV: u64 = 25_302;
    const N_FV: u64 = 25_303;
    const H_FV: u64 = 25_304;
    const X_FV: u64 = 25_305;
    const HX_FV: u64 = 25_306;
    const IH_FV: u64 = 25_307;

    let anon = k.anon();
    let ind_ty = k.const_(ordered_ring.ind, vec![]);
    let nat_ty = k.const_(nat.nat, vec![]);
    let r = k.fvar(R_FV);
    let equiv_refl = s(k, ordered_ring, EQUIV_REFL, r);
    let zero = s(k, ordered_ring, ZERO, r);
    let one = s(k, ordered_ring, ONE, r);
    let add = s(k, ordered_ring, ADD, r);
    let add_zero = s(k, ordered_ring, ADD_ZERO, r);
    let le = s(k, ordered_ring, LE, r);
    let le_congr = s(k, ordered_ring, LE_CONGR, r);
    let le_refl = s(k, ordered_ring, LE_REFL, r);
    let le_trans = s(k, ordered_ring, LE_TRANS, r);
    let add_le_add_left = s(k, ordered_ring, ADD_LE_ADD_LEFT, r);

    let h01_ty = app2(k, le, zero, one);
    let h01 = k.fvar(H01_FV);

    // `le_self_add_one(x) : le x (add x one)`, from `h01` and
    // `add_le_add_left`, transporting `le (add x zero)(add x one)` along
    // `equiv (add x zero) x` via `leCongr` directly -- one field
    // application, no `Eq.rec` motive.
    let le_self_add_one = move |k2: &mut Kernel, x: ExprId| -> ExprId {
        let grow = t_app(k2, add_le_add_left, &[zero, one, x, h01]); // : le (add x zero)(add x one)
        let xz = t_app(k2, add, &[x, zero]);
        let xo = t_app(k2, add, &[x, one]);
        let eqz = k2.app(add_zero, x); // : equiv (add x zero) x
        let refl_xo = k2.app(equiv_refl, xo);
        t_app(k2, le_congr, &[xz, x, xo, xo, eqz, refl_xo, grow]) // : le x xo
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
// Three derived order lemmas -- each SHORTER than its `Eq`-flavored
// counterpart because `leCongr`/`addCongr` are first-class fields.
// ---------------------------------------------------------------------------

/// `AlgS.add_le_add_right : forall (R:OrderedRing)(a b c:R.carrier), R.le a
/// b -> R.le (R.add a c)(R.add b c)` — from `add_le_add_left` + `addComm`,
/// rewriting both sides of `add_le_add_left(c,a,b,h)` across `add c x = add
/// x c` via `leCongr` directly.
fn build_add_le_add_right_s(k: &mut Kernel, ordered_ring: &RecordNames) -> (ExprId, ExprId) {
    use crate::nat_prelude::structures::{app2, arrow, lam_over, pi_over};
    use structures_s::idx::ordered_ring::{
        ADD, ADD_COMM, ADD_LE_ADD_LEFT, CARRIER, EQUIV_REFL, LE, LE_CONGR,
    };
    const R_FV: u64 = 25_500;
    const A_FV: u64 = 25_501;
    const B_FV: u64 = 25_502;
    const C_FV: u64 = 25_503;
    const H_FV: u64 = 25_504;

    let ind_ty = k.const_(ordered_ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = s(k, ordered_ring, CARRIER, r);
    let equiv_refl = s(k, ordered_ring, EQUIV_REFL, r);
    let add = s(k, ordered_ring, ADD, r);
    let le = s(k, ordered_ring, LE, r);
    let le_congr = s(k, ordered_ring, LE_CONGR, r);
    let add_comm = s(k, ordered_ring, ADD_COMM, r);
    let add_le_add_left = s(k, ordered_ring, ADD_LE_ADD_LEFT, r);

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let c = k.fvar(C_FV);
    let hab_ty = app2(k, le, a, b);
    let h = k.fvar(H_FV);

    let h0 = t_app(k, add_le_add_left, &[a, b, c, h]); // : le (add c a)(add c b)
    let ca = t_app(k, add, &[c, a]);
    let ac = t_app(k, add, &[a, c]);
    let cb = t_app(k, add, &[c, b]);
    let bc = t_app(k, add, &[b, c]);

    let e1 = t_app(k, add_comm, &[c, a]); // : equiv ca ac
    let refl_cb = k.app(equiv_refl, cb);
    let h1 = t_app(k, le_congr, &[ca, ac, cb, cb, e1, refl_cb, h0]); // : le ac cb
    let e2 = t_app(k, add_comm, &[c, b]); // : equiv cb bc
    let refl_ac = k.app(equiv_refl, ac);
    let h2 = t_app(k, le_congr, &[ac, ac, cb, bc, refl_ac, e2, h1]); // : le ac bc

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

/// `equiv (add (neg y)(add x y)) x` — the cancellation `linarith::int` and
/// `ordered_ring_ext`'s own `cancel_neg_add_left` each build once per
/// backend; here from `addAssoc`+`addComm`+`negAdd`+`addZero` via
/// `equivTrans`/`equivSymm`/`addCongr`.
#[allow(clippy::too_many_arguments)]
fn cancel_neg_add_left_s(
    k: &mut Kernel,
    add: ExprId,
    add_congr: ExprId,
    neg: ExprId,
    zero: ExprId,
    add_assoc: ExprId,
    add_comm: ExprId,
    add_zero: ExprId,
    neg_add: ExprId,
    equiv_refl: ExprId,
    equiv_symm: ExprId,
    equiv_trans: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let neg_y = k.app(neg, y);
    let inner = t_app(k, add, &[x, y]);
    let target = t_app(k, add, &[neg_y, inner]);

    let grouped = t_app(k, add, &[neg_y, x]);
    let regrouped = t_app(k, add, &[grouped, y]);
    let assoc1 = t_app(k, add_assoc, &[neg_y, x, y]); // : equiv regrouped target
    let back1 = t_app(k, equiv_symm, &[regrouped, target, assoc1]); // : equiv target regrouped

    let flipped_grouped = t_app(k, add, &[x, neg_y]);
    let comm1 = t_app(k, add_comm, &[neg_y, x]); // : equiv grouped flipped_grouped
    let refl_y = k.app(equiv_refl, y);
    let step2 = t_app(
        k,
        add_congr,
        &[grouped, flipped_grouped, y, y, comm1, refl_y],
    );
    let flipped_regrouped = t_app(k, add, &[flipped_grouped, y]);
    let mid = t_app(
        k,
        equiv_trans,
        &[target, regrouped, flipped_regrouped, back1, step2],
    );

    let assoc2 = t_app(k, add_assoc, &[x, neg_y, y]); // : equiv flipped_regrouped (add x (add neg_y y))
    let neg_y_y = t_app(k, add, &[neg_y, y]);
    let x_plus_negyy = t_app(k, add, &[x, neg_y_y]);
    let mid2 = t_app(
        k,
        equiv_trans,
        &[target, flipped_regrouped, x_plus_negyy, mid, assoc2],
    );

    let comm2 = t_app(k, add_comm, &[neg_y, y]); // : equiv neg_y_y (add y neg_y)
    let y_negy = t_app(k, add, &[y, neg_y]);
    let na = k.app(neg_add, y); // : equiv (add y neg_y) zero
    let neg_y_y_zero = t_app(k, equiv_trans, &[neg_y_y, y_negy, zero, comm2, na]);
    let refl_x = k.app(equiv_refl, x);
    let step4 = t_app(k, add_congr, &[x, x, neg_y_y, zero, refl_x, neg_y_y_zero]);
    let x_zero = t_app(k, add, &[x, zero]);
    let mid3 = t_app(k, equiv_trans, &[target, x_plus_negyy, x_zero, mid2, step4]);

    let az = k.app(add_zero, x); // : equiv (add x zero) x
    t_app(k, equiv_trans, &[target, x_zero, x, mid3, az])
}

/// `AlgS.le_of_add_le_add_right : forall (R:OrderedRing)(a b c:R.carrier),
/// R.le (R.add a c)(R.add b c) -> R.le a b` — cancel `c` by adding `neg c`
/// on the left of `add_le_add_left`, then rewrite both sides via
/// [`cancel_neg_add_left_s`] and `leCongr`.
#[allow(clippy::too_many_lines)]
fn build_le_of_add_le_add_right_s(k: &mut Kernel, ordered_ring: &RecordNames) -> (ExprId, ExprId) {
    use crate::nat_prelude::structures::{app2, arrow, lam_over, pi_over};
    use structures_s::idx::ordered_ring::{
        ADD, ADD_ASSOC, ADD_COMM, ADD_CONGR, ADD_LE_ADD_LEFT, ADD_ZERO, CARRIER, EQUIV_REFL,
        EQUIV_SYMM, EQUIV_TRANS, LE, LE_CONGR, NEG, NEG_ADD, ZERO,
    };
    const R_FV: u64 = 25_700;
    const A_FV: u64 = 25_701;
    const B_FV: u64 = 25_702;
    const C_FV: u64 = 25_703;
    const H_FV: u64 = 25_704;

    let ind_ty = k.const_(ordered_ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = s(k, ordered_ring, CARRIER, r);
    let equiv_refl = s(k, ordered_ring, EQUIV_REFL, r);
    let equiv_symm = s(k, ordered_ring, EQUIV_SYMM, r);
    let equiv_trans = s(k, ordered_ring, EQUIV_TRANS, r);
    let add = s(k, ordered_ring, ADD, r);
    let add_congr = s(k, ordered_ring, ADD_CONGR, r);
    let neg = s(k, ordered_ring, NEG, r);
    let zero = s(k, ordered_ring, ZERO, r);
    let le = s(k, ordered_ring, LE, r);
    let le_congr = s(k, ordered_ring, LE_CONGR, r);
    let add_assoc = s(k, ordered_ring, ADD_ASSOC, r);
    let add_comm = s(k, ordered_ring, ADD_COMM, r);
    let add_zero = s(k, ordered_ring, ADD_ZERO, r);
    let neg_add = s(k, ordered_ring, NEG_ADD, r);
    let add_le_add_left = s(k, ordered_ring, ADD_LE_ADD_LEFT, r);

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let c = k.fvar(C_FV);
    let ac = t_app(k, add, &[a, c]);
    let bc = t_app(k, add, &[b, c]);
    let hyp_ty = app2(k, le, ac, bc);
    let h = k.fvar(H_FV);

    let neg_c = k.app(neg, c);
    let h2 = t_app(k, add_le_add_left, &[ac, bc, neg_c, h]); // : le (add neg_c ac)(add neg_c bc)

    let eq_a = cancel_neg_add_left_s(
        k,
        add,
        add_congr,
        neg,
        zero,
        add_assoc,
        add_comm,
        add_zero,
        neg_add,
        equiv_refl,
        equiv_symm,
        equiv_trans,
        a,
        c,
    ); // : equiv (add neg_c ac) a
    let eq_b = cancel_neg_add_left_s(
        k,
        add,
        add_congr,
        neg,
        zero,
        add_assoc,
        add_comm,
        add_zero,
        neg_add,
        equiv_refl,
        equiv_symm,
        equiv_trans,
        b,
        c,
    ); // : equiv (add neg_c bc) b

    let neg_c_ac = t_app(k, add, &[neg_c, ac]);
    let neg_c_bc = t_app(k, add, &[neg_c, bc]);
    let refl_neg_c_bc = k.app(equiv_refl, neg_c_bc);
    let h3 = t_app(
        k,
        le_congr,
        &[neg_c_ac, a, neg_c_bc, neg_c_bc, eq_a, refl_neg_c_bc, h2],
    ); // : le a neg_c_bc
    let refl_a = k.app(equiv_refl, a);
    let h4 = t_app(k, le_congr, &[a, a, neg_c_bc, b, refl_a, eq_b, h3]); // : le a b

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

/// `AlgS.add_le_add : forall (R:OrderedRing)(a b c d:R.carrier), R.le a b ->
/// R.le c d -> R.le (R.add a c)(R.add b d)` — cites the already-declared
/// `add_le_add_right` by name, plus `add_le_add_left` + `le_trans`.
fn build_add_le_add_s(
    k: &mut Kernel,
    ordered_ring: &RecordNames,
    add_le_add_right_name: NameId,
) -> (ExprId, ExprId) {
    use crate::nat_prelude::structures::{app2, arrow, lam_over, pi_over};
    use structures_s::idx::ordered_ring::{ADD, ADD_LE_ADD_LEFT, CARRIER, LE, LE_TRANS};
    const R_FV: u64 = 25_900;
    const A_FV: u64 = 25_901;
    const B_FV: u64 = 25_902;
    const C_FV: u64 = 25_903;
    const D_FV: u64 = 25_904;
    const H1_FV: u64 = 25_905;
    const H2_FV: u64 = 25_906;

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
    let h1p = t_app(k, add_le_add_right, &[r, a, b, c, h1]);
    // h2' : le (add b c)(add b d)
    let h2p = t_app(k, add_le_add_left, &[c, d, b, h2]);
    let ac = t_app(k, add, &[a, c]);
    let bc = t_app(k, add, &[b, c]);
    let bd = t_app(k, add, &[b, d]);
    let result = t_app(k, le_trans, &[ac, bc, bd, h1p, h2p]);

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
pub struct OrderedRingExtSNames {
    pub ofnat: NameId,
    pub ofnat_add: NameId,
    pub ofnat_le_ofnat_of_le: NameId,
    pub add_le_add_right: NameId,
    pub le_of_add_le_add_right: NameId,
    pub add_le_add: NameId,
    /// `AlgS.OrderedRing.ofAlg(Int.orderedRing)`.
    pub int_ordered_ring_s: NameId,
    /// `AlgS.OrderedRing.ofAlg(Rat.orderedRing)`.
    pub rat_ordered_ring_s: NameId,
}

fn algs_root(k: &mut Kernel) -> NameId {
    let anon = k.anon();
    k.name_str(anon, "AlgS")
}

pub(crate) fn intern_ordered_ring_ext_s(k: &mut Kernel) -> OrderedRingExtSNames {
    let algs = algs_root(k);
    let ordered_ring = k.name_str(algs, "OrderedRing");
    OrderedRingExtSNames {
        ofnat: k.name_str(ordered_ring, "ofNat"),
        ofnat_add: k.name_str(ordered_ring, "ofNat_add"),
        ofnat_le_ofnat_of_le: k.name_str(ordered_ring, "ofNat_le_ofNat_of_le"),
        add_le_add_right: k.name_str(ordered_ring, "add_le_add_right"),
        le_of_add_le_add_right: k.name_str(ordered_ring, "le_of_add_le_add_right"),
        add_le_add: k.name_str(ordered_ring, "add_le_add"),
        int_ordered_ring_s: {
            let root = k.name_str(algs, "Int");
            k.name_str(root, "orderedRingS")
        },
        rat_ordered_ring_s: {
            let root = k.name_str(algs, "Rat");
            k.name_str(root, "orderedRingS")
        },
    }
}

pub(crate) fn declare_ordered_ring_ext_s_all(
    k: &mut Kernel,
    p: &RatPrelude,
    ordered_ring: &RecordNames,
    names: &OrderedRingExtSNames,
) -> Result<(), KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let nat = p.int.nat;
    let nat_ty = k.const_(nat.nat, vec![]);

    {
        let (ty, value) = build_ofnat_s(k, l1, ordered_ring, nat.rec, nat_ty);
        k.add_declaration(Declaration::Definition {
            name: names.ofnat,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    {
        let (ty, value) = build_ofnat_add_s(k, ordered_ring, nat, names.ofnat);
        k.add_declaration(Declaration::Theorem {
            name: names.ofnat_add,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    {
        let (ty, value) = build_ofnat_le_ofnat_of_le_s(k, ordered_ring, nat, names.ofnat);
        k.add_declaration(Declaration::Theorem {
            name: names.ofnat_le_ofnat_of_le,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    {
        let (ty, value) = build_add_le_add_right_s(k, ordered_ring);
        k.add_declaration(Declaration::Theorem {
            name: names.add_le_add_right,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    {
        let (ty, value) = build_le_of_add_le_add_right_s(k, ordered_ring);
        k.add_declaration(Declaration::Theorem {
            name: names.le_of_add_le_add_right,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    {
        let (ty, value) = build_add_le_add_s(k, ordered_ring, names.add_le_add_right);
        k.add_declaration(Declaration::Theorem {
            name: names.add_le_add,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    {
        // `AlgS.Int.orderedRingS := AlgS.OrderedRing.ofAlg(Int.orderedRing)`.
        let extra = &p.int.nat.structures_s_extra;
        let ofalg_c = k.const_(extra.ordered_ring_ofalg, vec![]);
        let int_or = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let value = k.app(ofalg_c, int_or);
        let ty = k.const_(ordered_ring.ind, vec![]);
        k.add_declaration(Declaration::Definition {
            name: names.int_ordered_ring_s,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    {
        let extra = &p.int.nat.structures_s_extra;
        let ofalg_c = k.const_(extra.ordered_ring_ofalg, vec![]);
        let rat_or = k.const_(p.algebra_ext.rat_ordered_ring, vec![]);
        let value = k.app(ofalg_c, rat_or);
        let ty = k.const_(ordered_ring.ind, vec![]);
        k.add_declaration(Declaration::Definition {
            name: names.rat_ordered_ring_s,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    Ok(())
}

#[cfg(test)]
mod ordered_ring_ext_s_tests {
    use super::*;
    use crate::Kernel;
    use crate::build_rat_prelude;
    use crate::nat_prelude::structures::{app2, lam_over};
    use structures_s::idx::ordered_ring::{ADD, LE};

    fn le_of(k: &mut Kernel, rn: &RecordNames, ring: ExprId, x: ExprId, y: ExprId) -> ExprId {
        let le = sel(k, rn, LE, ring);
        app2(k, le, x, y)
    }

    /// `AlgS.ofNat(AlgS.Int.orderedRingS, 3)` reduces to `Int.ofNat 3` --
    /// the same reduction the `Eq`-flavored `ofnat_evaluation_at_int_
    /// discriminates` test measures, negative control against `4`.
    #[test]
    fn ofnat_s_evaluation_at_int_discriminates() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let r = k.const_(p.ordered_ring_ext_s.int_ordered_ring_s, vec![]);
        let nat = p.int.nat;
        let n3 = {
            let mut e = k.const_(nat.zero, vec![]);
            for _ in 0..3 {
                let s = k.const_(nat.succ, vec![]);
                e = k.app(s, e);
            }
            e
        };
        let n4 = {
            let mut e = k.const_(nat.zero, vec![]);
            for _ in 0..4 {
                let s = k.const_(nat.succ, vec![]);
                e = k.app(s, e);
            }
            e
        };
        let got = ofnat_of(&mut k, p.ordered_ring_ext_s.ofnat, r, n3);
        let of_nat_c = k.const_(p.int.of_nat, vec![]);
        let want3 = k.app(of_nat_c, n3);
        let of_nat_c2 = k.const_(p.int.of_nat, vec![]);
        let want4 = k.app(of_nat_c2, n4);
        assert!(
            k.def_eq(got, want3),
            "AlgS.ofNat(AlgS.Int.orderedRingS, 3) must reduce to Int.ofNat 3"
        );
        assert!(
            !k.def_eq(got, want4),
            "AlgS.ofNat(AlgS.Int.orderedRingS, 3) must NOT reduce to Int.ofNat 4"
        );
    }

    /// `AlgS.ofNat_add`, symbolic, at `AlgS.Int.orderedRingS` and `AlgS.Rat.
    /// orderedRingS`.
    #[test]
    fn ofnat_add_s_symbolic_at_int_and_rat() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let nat_ty = k.const_(p.int.nat.nat, vec![]);
        for r_name in [
            p.ordered_ring_ext_s.int_ordered_ring_s,
            p.ordered_ring_ext_s.rat_ordered_ring_s,
        ] {
            const M_FV: u64 = 41_100;
            const N_FV: u64 = 41_101;
            let r = k.const_(r_name, vec![]);
            let thm = k.const_(p.ordered_ring_ext_s.ofnat_add, vec![]);
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
                .unwrap_or_else(|e| panic!("ofNat_add (setoid) must type-check: {e:?}"));
        }
    }

    /// `AlgS.ofNat_le_ofNat_of_le`, symbolic, at both carriers, `h01` built
    /// from each carrier's own `zero_lt_one`/`le_of_lt` -- the same source
    /// theorems the `Eq`-flavored test uses (`AlgS.Int.orderedRingS`'s `le`/
    /// `zero`/`one` selectors are Int's own, unchanged by `ofAlg`).
    #[test]
    fn ofnat_le_ofnat_of_le_s_symbolic_at_int_and_rat() {
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
            (p.ordered_ring_ext_s.int_ordered_ring_s, int_h01),
            (p.ordered_ring_ext_s.rat_ordered_ring_s, rat_h01),
        ] {
            const M_FV: u64 = 41_200;
            const N_FV: u64 = 41_201;
            const H_FV: u64 = 41_202;
            let r = k.const_(r_name, vec![]);
            let thm = k.const_(p.ordered_ring_ext_s.ofnat_le_ofnat_of_le, vec![]);
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
                .unwrap_or_else(|e| panic!("ofNat_le_ofNat_of_le (setoid) must type-check: {e:?}"));
        }
    }

    /// `AlgS.add_le_add_right(AlgS.Int.orderedRingS)` closed over `(a,b,c)`
    /// has the SAME TYPE as `Int.add_le_add_right` -- the setoid path
    /// reaches the same retirement target ADR-1585 named for the `Eq`
    /// spine.
    #[test]
    fn add_le_add_right_s_matches_int_add_le_add_right_by_type() {
        const A_FV: u64 = 41_300;
        const B_FV: u64 = 41_301;
        const C_FV: u64 = 41_302;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let r = k.const_(p.ordered_ring_ext_s.int_ordered_ring_s, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let thm = k.const_(p.ordered_ring_ext_s.add_le_add_right, vec![]);
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
        let generic_ty = k
            .infer(generic_closed)
            .expect("generic (setoid) must type-check");

        let hand = k.const_(p.int.add_le_add_right, vec![]);
        let hand_ty = k.infer(hand).expect("Int.add_le_add_right must exist");
        assert!(
            k.def_eq(generic_ty, hand_ty),
            "AlgS.add_le_add_right(AlgS.Int.orderedRingS) closed over (a,b,c) must \
             have the SAME TYPE as Int.add_le_add_right"
        );
    }

    /// `AlgS.add_le_add(AlgS.Int.orderedRingS)` closed over `(a,b,c,d)` has
    /// the SAME TYPE as `Int.add_le_add`.
    #[test]
    fn add_le_add_s_matches_int_add_le_add_by_type() {
        const A_FV: u64 = 41_310;
        const B_FV: u64 = 41_311;
        const C_FV: u64 = 41_312;
        const D_FV: u64 = 41_313;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let r = k.const_(p.ordered_ring_ext_s.int_ordered_ring_s, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let thm = k.const_(p.ordered_ring_ext_s.add_le_add, vec![]);
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
        let generic_ty = k
            .infer(generic_closed)
            .expect("generic (setoid) must type-check");

        let hand = k.const_(p.int.add_le_add, vec![]);
        let hand_ty = k.infer(hand).expect("Int.add_le_add must exist");
        assert!(
            k.def_eq(generic_ty, hand_ty),
            "AlgS.add_le_add(AlgS.Int.orderedRingS) closed over (a,b,c,d) must \
             have the SAME TYPE as Int.add_le_add"
        );
    }

    /// `AlgS.le_of_add_le_add_right`, symbolic, at both carriers.
    #[test]
    fn le_of_add_le_add_right_s_symbolic_at_int_and_rat() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        for (r_name, carrier_const) in [
            (p.ordered_ring_ext_s.int_ordered_ring_s, p.int.z),
            (p.ordered_ring_ext_s.rat_ordered_ring_s, p.int.rat),
        ] {
            const A_FV: u64 = 41_320;
            const B_FV: u64 = 41_321;
            const C_FV: u64 = 41_322;
            const H_FV: u64 = 41_323;
            let r = k.const_(r_name, vec![]);
            let carrier = k.const_(carrier_const, vec![]);
            let thm = k.const_(p.ordered_ring_ext_s.le_of_add_le_add_right, vec![]);
            let a = k.fvar(A_FV);
            let b = k.fvar(B_FV);
            let c = k.fvar(C_FV);
            let add_sel = sel(&mut k, &p.int.nat.structures_s.ordered_ring, ADD, r);
            let ac = app2(&mut k, add_sel, a, c);
            let bc = app2(&mut k, add_sel, b, c);
            let h_ty = le_of(&mut k, &p.int.nat.structures_s.ordered_ring, r, ac, bc);
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
            k.infer(closed).unwrap_or_else(|e| {
                panic!("le_of_add_le_add_right (setoid) must type-check: {e:?}")
            });
        }
    }

    /// Every `ordered_ring_ext_s` declaration must have an empty axiom
    /// footprint.
    #[test]
    fn ordered_ring_ext_s_declarations_are_axiom_free() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        for name in [
            p.ordered_ring_ext_s.ofnat,
            p.ordered_ring_ext_s.ofnat_add,
            p.ordered_ring_ext_s.ofnat_le_ofnat_of_le,
            p.ordered_ring_ext_s.add_le_add_right,
            p.ordered_ring_ext_s.le_of_add_le_add_right,
            p.ordered_ring_ext_s.add_le_add,
            p.ordered_ring_ext_s.int_ordered_ring_s,
            p.ordered_ring_ext_s.rat_ordered_ring_s,
        ] {
            assert!(
                k.axiom_footprint(name).is_empty(),
                "declaration must have an empty axiom footprint"
            );
        }
    }
}
