//! `Rat.det_matMul : ∀ n A B, det (matMul A B n) n = det A n * det B n` —
//! **determinant multiplicativity at a symbolic dimension**, the last of the
//! four laws ADR-1120 named over `Rat.det`, and ADR-1440's obligation 1 that
//! carries it.
//!
//! # Where this starts
//!
//! [ADR-1541](../../../../docs/research/09-decisions/adr-1541-both-blockers-on-the-selection-lemma-were-stale.md)
//! closed obligation 2 — the SELECTION lemma
//! `Rat.det_row_selection : MapsInto g n → det (B∘g) n = det (matId∘g) n *
//! det B n` — and measured obligation 1 as the whole remainder: expand
//! `det (A·B) n` in the rows of `A·B`, each of which is a `Rat.sumRange` of
//! rows of `B`, by `Rat.det_row_multilinear` once per row. The result is a sum
//! indexed by the function space `[0,n) -> [0,n)`; `rat_prelude/sum_maps.rs`
//! supplies that aggregate (`Rat.sumMaps`) and the coefficient's product
//! (`Rat.prodRange`).
//!
//! # The cursor, and why it needs two new matrix operations
//!
//! The expansion is an induction on **how many rows have already been
//! replaced**, and every step needs the partially-replaced matrix as an actual
//! term — `Rat.det_row_smul` and `Rat.det_row_replaced` take the reference
//! matrix as an ARGUMENT, not as a hypothesis, so there is no
//! hypothesis-only formulation. Two definitions:
//!
//! - [`RatPrelude::mat_set_row`] — `matSetRow t h M`, `M` with row `t`
//!   replaced by `h`. Built with `Rat.matId`'s own `bool_select_rat` on
//!   `Nat.beq r t` rather than by recursion on `t`, so both of its equations
//!   are ONE rewrite (`Nat.beq_refl` / the hypothesis) and neither is an
//!   induction.
//! - [`RatPrelude::mat_subst_rows`] — `matSubstRows B m s g M`, the rows
//!   `[s, s+m)` of `M` replaced by row `g i` of `B` at relative index `i`.
//!   Structural recursion on `m` with the higher-order motive
//!   `fun _ : Nat => Nat -> (Nat -> Nat) -> Mat -> Mat`, peeling the
//!   OUTERMOST row first:
//!
//!   ```text
//!   matSubstRows B 0       s g M = M
//!   matSubstRows B (m + 1) s g M =
//!     matSubstRows B m (s + 1) (fun i => g (succ i)) (matSetRow s (B (g 0)) M)
//!   ```
//!
//!   That order is forced and it is the whole reason the induction closes:
//!   `Rat.sumMaps`'s `cons` extends a map at the FRONT, so
//!   `matSubstRows B (succ j) s (cons k g) M` and
//!   `matSubstRows B j (succ s) g (matSetRow s (B k) M)` are the SAME TERM up
//!   to ι and η — no commutation lemma between "set row `s`" and "substitute
//!   rows above `s`" is ever needed. Peeling the innermost row first would
//!   have needed exactly that lemma.
//!
//! The cursor carries an OFFSET `s`, because after peeling row `s` the
//! induction hypothesis has to expand rows `s+1 …` of the same matrix and
//! `Rat.det` does not shift. Row `s + i` is written `Nat.add s i`, so that
//! `add s 0` ι-reduces to `s` (`Nat.add` recurses on its RIGHT argument) and
//! the peeled row is literally `s`; the price is one `Nat.succ_add` when the
//! induction hypothesis re-indexes, and one `Nat.zero_add` at the top where
//! `s := 0`.
//!
//! # Why the selection lemma needs a bounded congruence for `sumMaps`
//!
//! `Rat.det_row_selection`'s `MapsInto g n` hypothesis is load-bearing, and
//! the sum is over *every* `g : Nat -> Nat` as far as the type is concerned.
//! It is not, in fact: every map `Rat.sumMaps` enumerates is a `cons` tower
//! over the constant-zero map, so all of them map `[0,n)` into `[0,n)`. But
//! that has to be CARRIED, which is what
//! [`RatPrelude::sum_maps_congr_maps_into`] does — `Rat.sumMaps_congr` with
//! its pointwise hypothesis weakened to maps into the range, proved by
//! `Rat.sumRange_congr_lt` (whose index bound is what supplies `Lt k n` for
//! the head of the `cons`).

use super::RatPrelude;
use super::matrix_det::{ble_true_ty, mat_ty, one_mul_pf, ralt_sign, rdet, rmat_id, rmat_minor_of};
use super::matrix_det_selection::row_compose;
use super::ops::{
    nat_eq_to_rat, nat_rewrite_prop, rat_ty, rchain, rcongr, req, rmul, rone, rrefl, rsum_range,
    rsymm, rtrans,
};
use super::probability::{bool_select_rat, select_rat_false, select_rat_true};
use super::sum_maps::{cons_fn, fam_ty, junk_map, map_ty, rprod_range, rsum_maps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.matSetRow`: above every constant it unfolds to
/// (`Nat.beq`, `Bool.rec`) and above every other height this prelude
/// declares, so it unfolds before the matrix operations it is applied to.
const MAT_SET_ROW_HEIGHT: u16 = 53;

/// Delta height for `Rat.matSubstRows`: one above [`MAT_SET_ROW_HEIGHT`],
/// which its successor row calls.
const MAT_SUBST_ROWS_HEIGHT: u16 = 54;

/// Declare everything this file proves.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_det_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_mat_set_row(d, p)?;
    declare_mat_set_row_at(d, p)?;
    declare_mat_set_row_off(d, p)?;
    declare_mat_subst_rows(d, p)?;
    declare_mat_subst_rows_below(d, p)?;
    declare_mat_subst_rows_at(d, p)?;
    declare_sum_maps_congr_maps_into(d, p)?;
    declare_det_mat_mul_expand(d, p)?;
    declare_det_mat_mul(d, p)?;
    Ok(())
}

// --- small shapes ----------------------------------------------------------

/// `Nat -> Rat`, the type of one matrix row.
fn row_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    d.arrow(nat, carrier)
}

/// `Rat.matSetRow t h M`.
pub(super) fn rmat_set_row(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    t: ExprId,
    h: ExprId,
    m: ExprId,
) -> ExprId {
    d.const_app(p.mat_set_row, &[t, h, m])
}

/// `Rat.matSubstRows B m s g M`.
pub(super) fn rmat_subst_rows(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    b: ExprId,
    m: ExprId,
    s: ExprId,
    g: ExprId,
    mat: ExprId,
) -> ExprId {
    d.const_app(p.mat_subst_rows, &[b, m, s, g, mat])
}

/// `Eq Bool (Nat.beq r t) Bool.false`.
fn beq_false_ty(d: &mut IntDev<'_>, r: ExprId, t: ExprId) -> ExprId {
    let lhs = NatOps::beq(d, r, t);
    let false_v = d.bool_false();
    d.bool_eq(lhs, false_v)
}

/// `False.rec (fun _ => goal) contradiction : goal`.
fn ex_falso(d: &mut IntDev<'_>, goal: ExprId, contradiction: ExprId) -> ExprId {
    let anon = d.anon_name();
    let logic = d.prelude().logic;
    let false_ty = d.kernel().const_(logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(logic.false_rec, vec![zero]);
    d.apply(rec, &[motive, contradiction])
}

/// From `hlt : Lt a b`, derive `Not (Eq Nat a b)`.
fn ne_of_lt(d: &mut IntDev<'_>, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let eq_ty = d.eq(a, b);
    let he_fv = d.fresh_fvar();
    let he = d.kernel().fvar(he_fv);
    // `hlt : Lt a b` rewritten along `he : a = b` is `Lt b b`.
    let bad = nat_rewrite_prop(d, a, b, he, hlt, &|d, x| d.lt(x, b));
    let np = d.prelude();
    let irrefl = d.lemma(np.lt_irrefl, &[b]);
    let body = d.apply(irrefl, &[bad]);
    d.lam_fv(he_fv, eq_ty, body)
}

/// From `hlt : Lt a b`, derive `Eq Bool (Nat.beq a b) Bool.false` — the
/// direction `Rat.matSetRow_off` asks for when the row is BELOW the cursor.
fn beq_false_of_lt(d: &mut IntDev<'_>, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let hne = ne_of_lt(d, a, b, hlt);
    let np = d.prelude();
    d.lemma(np.beq_eq_false_of_ne, &[a, b, hne])
}

/// From `hlt : Lt a b`, derive `Not (Eq Nat b a)` — the direction a
/// `Nat.beq r t = false` side condition asks for when the KNOWN fact is that
/// the row index is ABOVE the cursor.
fn ne_of_gt(d: &mut IntDev<'_>, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let eq_ty = d.eq(b, a);
    let he_fv = d.fresh_fvar();
    let he = d.kernel().fvar(he_fv);
    // `hlt : Lt a b` rewritten along `he : b = a` is `Lt a a`.
    let bad = nat_rewrite_prop(d, b, a, he, hlt, &|d, x| d.lt(a, x));
    let np = d.prelude();
    let irrefl = d.lemma(np.lt_irrefl, &[a]);
    let body = d.apply(irrefl, &[bad]);
    d.lam_fv(he_fv, eq_ty, body)
}

/// From `hlt : Lt a b`, derive `Eq Bool (Nat.beq b a) Bool.false`.
fn beq_false_of_gt(d: &mut IntDev<'_>, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let hne = ne_of_gt(d, a, b, hlt);
    let np = d.prelude();
    d.lemma(np.beq_eq_false_of_ne, &[b, a, hne])
}

/// `Lt a b -> Lt a (succ b)`.
fn lt_succ_of_lt(d: &mut IntDev<'_>, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let np = d.prelude();
    let sa = d.succ(a);
    let sb = d.succ(b);
    let step = d.lemma(np.le_succ, &[b]);
    d.lemma(np.le_trans, &[sa, b, sb, hlt, step])
}

/// `fun i => g (succ i)` — the map the cursor hands to its induction
/// hypothesis, and the same shape `Rat.sumMaps`'s `cons` reduces to.
fn tail_map(d: &mut IntDev<'_>, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let si = d.succ(i);
    let body = d.apply(g, &[si]);
    d.lam_fv(i_fv, nat, body)
}

// --- Rat.matSetRow ---------------------------------------------------------

/// Admit `Rat.matSetRow : Nat -> (Nat -> Rat) -> (Nat -> Nat -> Rat) ->
/// (Nat -> Nat -> Rat)`, `matSetRow t h M := fun r c =>
/// if Nat.beq r t then h c else M r c`.
///
/// The `bool_select_rat` encoding is `Rat.matId`'s own, and it is chosen over
/// a structural recursion on `t` because both defining equations then cost one
/// rewrite instead of an induction.
fn declare_mat_set_row(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let rty = row_ty(d);

    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let cond = NatOps::beq(d, r, t);
    let hc = d.apply(h, &[c]);
    let mrc = d.apply(m, &[r, c]);
    let body = bool_select_rat(d, cond, hc, mrc);

    let value = {
        let over_c = d.lam_fv(c_fv, nat, body);
        let over_r = d.lam_fv(r_fv, nat, over_c);
        let over_m = d.lam_fv(m_fv, mty, over_r);
        let over_h = d.lam_fv(h_fv, rty, over_m);
        d.lam_fv(t_fv, nat, over_h)
    };
    let ty = {
        let over_m = d.arrow(mty, mty);
        let over_h = d.arrow(rty, over_m);
        d.arrow(nat, over_h)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mat_set_row,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAT_SET_ROW_HEIGHT),
    })
}

/// `Rat.matSetRow_at : ∀ t h M c, matSetRow t h M t c = h c`.
fn declare_mat_set_row_at(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let rty = row_ty(d);

    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let set = rmat_set_row(d, p, t, h, m);
    let lhs = d.apply(set, &[t, c]);
    let hc = d.apply(h, &[c]);
    let stmt = req(d, lhs, hc);

    let cond = NatOps::beq(d, t, t);
    let mtc = d.apply(m, &[t, c]);
    let np = d.prelude();
    let hrefl = d.lemma(np.beq_refl, &[t]);
    let proof = select_rat_true(d, cond, hc, mtc, hrefl);

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, mty, over_c);
        let over_h = d.pi_fv(h_fv, rty, over_m);
        d.pi_fv(t_fv, nat, over_h)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, mty, over_c);
        let over_h = d.lam_fv(h_fv, rty, over_m);
        d.lam_fv(t_fv, nat, over_h)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_set_row_at,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.matSetRow_off : ∀ t h M r, Nat.beq r t = false → ∀ c,
/// matSetRow t h M r c = M r c`.
fn declare_mat_set_row_off(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let rty = row_ty(d);

    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let hyp_ty = beq_false_ty(d, r, t);
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let set = rmat_set_row(d, p, t, h, m);
    let lhs = d.apply(set, &[r, c]);
    let mrc = d.apply(m, &[r, c]);
    let stmt = req(d, lhs, mrc);

    let cond = NatOps::beq(d, r, t);
    let hc = d.apply(h, &[c]);
    let proof = select_rat_false(d, cond, hc, mrc, hyp);

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let with_h = d.arrow(hyp_ty, over_c);
        let over_r = d.pi_fv(r_fv, nat, with_h);
        let over_m = d.pi_fv(m_fv, mty, over_r);
        let over_h = d.pi_fv(h_fv, rty, over_m);
        d.pi_fv(t_fv, nat, over_h)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let with_h = d.lam_fv(hyp_fv, hyp_ty, over_c);
        let over_r = d.lam_fv(r_fv, nat, with_h);
        let over_m = d.lam_fv(m_fv, mty, over_r);
        let over_h = d.lam_fv(h_fv, rty, over_m);
        d.lam_fv(t_fv, nat, over_h)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_set_row_off,
        uparams: vec![],
        ty,
        value,
    })
}

// --- Rat.matSubstRows ------------------------------------------------------

/// Admit `Rat.matSubstRows : (Nat -> Nat -> Rat) -> Nat -> Nat ->
/// (Nat -> Nat) -> (Nat -> Nat -> Rat) -> (Nat -> Nat -> Rat)`.
///
/// See the module doc for the recursion and for why it peels the OUTERMOST
/// row first.
fn declare_mat_subst_rows(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let map_t = map_ty(d);
    let anon = d.anon_name();
    let one_level = d.level_one();

    // `Nat -> (Nat -> Nat) -> Mat -> Mat`, the recursion's value type.
    let inner_ty = {
        let over_m = d.arrow(mty, mty);
        let over_g = d.arrow(map_t, over_m);
        d.arrow(nat, over_g)
    };

    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let motive = d.kernel().lam(anon, nat, inner_ty, BinderInfo::Default);

    let minor_zero = {
        let s_fv = d.fresh_fvar();
        let g_fv = d.fresh_fvar();
        let mat_fv = d.fresh_fvar();
        let mat = d.kernel().fvar(mat_fv);
        let over_m = d.lam_fv(mat_fv, mty, mat);
        let over_g = d.lam_fv(g_fv, map_t, over_m);
        d.lam_fv(s_fv, nat, over_g)
    };

    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let mat_fv = d.fresh_fvar();
        let mat = d.kernel().fvar(mat_fv);

        let ss = d.succ(s);
        let tail_g = tail_map(d, g);
        let zero_n = d.zero();
        let g0 = d.apply(g, &[zero_n]);
        let row = d.apply(b, &[g0]);
        let set = rmat_set_row(d, p, s, row, mat);
        let body = d.apply(ih, &[ss, tail_g, set]);

        let over_m = d.lam_fv(mat_fv, mty, body);
        let over_g = d.lam_fv(g_fv, map_t, over_m);
        let over_s = d.lam_fv(s_fv, nat, over_g);
        let over_ih = d.lam_fv(ih_fv, inner_ty, over_s);
        d.lam_fv(j_fv, nat, over_ih)
    };

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let rec_app = d.apply(rec, &[motive, minor_zero, minor_succ, m]);

    let s_outer_fv = d.fresh_fvar();
    let s_outer = d.kernel().fvar(s_outer_fv);
    let g_outer_fv = d.fresh_fvar();
    let g_outer = d.kernel().fvar(g_outer_fv);
    let mat_outer_fv = d.fresh_fvar();
    let mat_outer = d.kernel().fvar(mat_outer_fv);
    let applied = d.apply(rec_app, &[s_outer, g_outer, mat_outer]);

    let value = {
        let over_mat = d.lam_fv(mat_outer_fv, mty, applied);
        let over_g = d.lam_fv(g_outer_fv, map_t, over_mat);
        let over_s = d.lam_fv(s_outer_fv, nat, over_g);
        let over_m = d.lam_fv(m_fv, nat, over_s);
        d.lam_fv(b_fv, mty, over_m)
    };
    let ty = {
        let over_m = d.arrow(nat, inner_ty);
        d.arrow(mty, over_m)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mat_subst_rows,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAT_SUBST_ROWS_HEIGHT),
    })
}

/// `Rat.matSubstRows_below : ∀ B m s g M r, Lt r s → ∀ c,
/// matSubstRows B m s g M r c = M r c` — rows BELOW the window are untouched.
///
/// Induction on `m` with `s`, `g` and `M` inside the motive (the successor
/// step applies the induction hypothesis at a different triple) and the row
/// `r` outside it (the same row throughout).
fn declare_mat_subst_rows_below(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let map_t = map_ty(d);

    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let mat_fv = d.fresh_fvar();
        let mat = d.kernel().fvar(mat_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let hyp = d.lt(r, s);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let subst = rmat_subst_rows(d, p, b, x, s, g, mat);
        let lhs = d.apply(subst, &[r, c]);
        let rhs = d.apply(mat, &[r, c]);
        let eq = req(d, lhs, rhs);
        let over_c = d.pi_fv(c_fv, nat, eq);
        let with_h = d.arrow(hyp, over_c);
        let over_r = d.pi_fv(r_fv, nat, with_h);
        let over_mat = d.pi_fv(mat_fv, mty, over_r);
        let over_g = d.pi_fv(g_fv, map_t, over_mat);
        d.pi_fv(s_fv, nat, over_g)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            // `matSubstRows B 0 s g M ≡ M`, so every instance is `Eq.refl`.
            let s_fv = d.fresh_fvar();
            let s = d.kernel().fvar(s_fv);
            let g_fv = d.fresh_fvar();
            let mat_fv = d.fresh_fvar();
            let mat = d.kernel().fvar(mat_fv);
            let r_fv = d.fresh_fvar();
            let r = d.kernel().fvar(r_fv);
            let hyp = d.lt(r, s);
            let h_fv = d.fresh_fvar();
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let rhs = d.apply(mat, &[r, c]);
            let refl = rrefl(d, rhs);
            let over_c = d.lam_fv(c_fv, nat, refl);
            let with_h = d.lam_fv(h_fv, hyp, over_c);
            let over_r = d.lam_fv(r_fv, nat, with_h);
            let over_mat = d.lam_fv(mat_fv, mty, over_r);
            let over_g = d.lam_fv(g_fv, map_t, over_mat);
            d.lam_fv(s_fv, nat, over_g)
        },
        &|d, j, ih| {
            let s_fv = d.fresh_fvar();
            let s = d.kernel().fvar(s_fv);
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let mat_fv = d.fresh_fvar();
            let mat = d.kernel().fvar(mat_fv);
            let r_fv = d.fresh_fvar();
            let r = d.kernel().fvar(r_fv);
            let hyp_ty = d.lt(r, s);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);

            let ss = d.succ(s);
            let sj = d.succ(j);
            let tail_g = tail_map(d, g);
            let zero_n = d.zero();
            let g0 = d.apply(g, &[zero_n]);
            let row = d.apply(b, &[g0]);
            let set = rmat_set_row(d, p, s, row, mat);

            // step 1: the substitution above `s` does not see row `r < s`.
            let hlt_succ = lt_succ_of_lt(d, r, s, h);
            let inner = d.apply(ih, &[ss, tail_g, set, r, hlt_succ, c]);
            // step 2: `matSetRow s _ M` does not see row `r ≠ s` either.
            let hne = beq_false_of_lt(d, r, s, h);
            let off = d.lemma(p.mat_set_row_off, &[s, row, mat, r, hne, c]);

            let start = {
                let full = rmat_subst_rows(d, p, b, sj, s, g, mat);
                d.apply(full, &[r, c])
            };
            let mid = d.apply(set, &[r, c]);
            let end_ = d.apply(mat, &[r, c]);
            let (_, chained) = rchain(d, start, &[(mid, inner), (end_, off)]);

            let over_c = d.lam_fv(c_fv, nat, chained);
            let with_h = d.lam_fv(h_fv, hyp_ty, over_c);
            let over_r = d.lam_fv(r_fv, nat, with_h);
            let over_mat = d.lam_fv(mat_fv, mty, over_r);
            let over_g = d.lam_fv(g_fv, map_t, over_mat);
            d.lam_fv(s_fv, nat, over_g)
        },
        m,
    );

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, stmt);
        d.pi_fv(b_fv, mty, over_m)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        d.lam_fv(b_fv, mty, over_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_subst_rows_below,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.matSubstRows_at : ∀ B m s g M i, Lt i m → ∀ c,
/// matSubstRows B m s g M (add s i) c = B (g i) c` — inside the window the
/// row is the one `g` selects.
///
/// Induction on `m` with `s`, `g`, `M` and the relative index `i` all inside
/// the motive, plus a `Nat.rec` case split on `i` in the successor step whose
/// own induction hypothesis is DISCARDED: the two legs are structurally
/// different arguments, not a recursion in `i`.
///
/// - `i = 0`. `add s 0` ι-reduces to `s`, and the rest of the substitution
///   starts at `succ s`, so [`RatPrelude::mat_subst_rows_below`] carries the
///   row through it and [`RatPrelude::mat_set_row_at`] reads it off.
/// - `i = succ i'`. `add s (succ i')` ι-reduces to `succ (add s i')`, which is
///   `add (succ s) i'` by `Nat.succ_add` — the one arithmetic rewrite the
///   whole cursor costs.
fn declare_mat_subst_rows_at(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let map_t = map_ty(d);

    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let mat_fv = d.fresh_fvar();
        let mat = d.kernel().fvar(mat_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hyp = d.lt(i, x);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let subst = rmat_subst_rows(d, p, b, x, s, g, mat);
        let row = d.add(s, i);
        let lhs = d.apply(subst, &[row, c]);
        let gi = d.apply(g, &[i]);
        let rhs = d.apply(b, &[gi, c]);
        let eq = req(d, lhs, rhs);
        let over_c = d.pi_fv(c_fv, nat, eq);
        let with_h = d.arrow(hyp, over_c);
        let over_i = d.pi_fv(i_fv, nat, with_h);
        let over_mat = d.pi_fv(mat_fv, mty, over_i);
        let over_g = d.pi_fv(g_fv, map_t, over_mat);
        d.pi_fv(s_fv, nat, over_g)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            // `Lt i 0` is absurd.
            let s_fv = d.fresh_fvar();
            let s = d.kernel().fvar(s_fv);
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let mat_fv = d.fresh_fvar();
            let mat = d.kernel().fvar(mat_fv);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let zero_n = d.zero();
            let hyp_ty = d.lt(i, zero_n);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);

            let np = d.prelude();
            let not_lt = d.lemma(np.not_lt_zero, &[i]);
            let absurd = d.apply(not_lt, &[h]);
            let target = {
                let subst = rmat_subst_rows(d, p, b, zero_n, s, g, mat);
                let row = d.add(s, i);
                let lhs = d.apply(subst, &[row, c]);
                let gi = d.apply(g, &[i]);
                let rhs = d.apply(b, &[gi, c]);
                req(d, lhs, rhs)
            };
            let elim = ex_falso(d, target, absurd);

            let over_c = d.lam_fv(c_fv, nat, elim);
            let with_h = d.lam_fv(h_fv, hyp_ty, over_c);
            let over_i = d.lam_fv(i_fv, nat, with_h);
            let over_mat = d.lam_fv(mat_fv, mty, over_i);
            let over_g = d.lam_fv(g_fv, map_t, over_mat);
            d.lam_fv(s_fv, nat, over_g)
        },
        &|d, j, ih| {
            let s_fv = d.fresh_fvar();
            let s = d.kernel().fvar(s_fv);
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let mat_fv = d.fresh_fvar();
            let mat = d.kernel().fvar(mat_fv);

            let sj = d.succ(j);
            let ss = d.succ(s);
            let tail_g = tail_map(d, g);
            let zero_n = d.zero();
            let g0 = d.apply(g, &[zero_n]);
            let row0 = d.apply(b, &[g0]);
            let set = rmat_set_row(d, p, s, row0, mat);

            let index_motive = |d: &mut IntDev<'_>, i: ExprId| -> ExprId {
                let hyp = d.lt(i, sj);
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let subst = rmat_subst_rows(d, p, b, sj, s, g, mat);
                let row = d.add(s, i);
                let lhs = d.apply(subst, &[row, c]);
                let gi = d.apply(g, &[i]);
                let rhs = d.apply(b, &[gi, c]);
                let eq = req(d, lhs, rhs);
                let over_c = d.pi_fv(c_fv, nat, eq);
                d.arrow(hyp, over_c)
            };

            let i_outer_fv = d.fresh_fvar();
            let i_outer = d.kernel().fvar(i_outer_fv);
            let index_proof = d.induct(
                &index_motive,
                &|d| {
                    let zero_i = d.zero();
                    let hyp_ty = d.lt(zero_i, sj);
                    let h_fv = d.fresh_fvar();
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);

                    let np = d.prelude();
                    let hlt = d.lemma(np.lt_succ_self, &[s]);
                    let below =
                        d.lemma(p.mat_subst_rows_below, &[b, j, ss, tail_g, set, s, hlt, c]);
                    let at_ = d.lemma(p.mat_set_row_at, &[s, row0, mat, c]);

                    let start = {
                        let full = rmat_subst_rows(d, p, b, sj, s, g, mat);
                        let row = d.add(s, zero_i);
                        d.apply(full, &[row, c])
                    };
                    let mid = d.apply(set, &[s, c]);
                    let end_ = d.apply(row0, &[c]);
                    let (_, chained) = rchain(d, start, &[(mid, below), (end_, at_)]);
                    let over_c = d.lam_fv(c_fv, nat, chained);
                    d.lam_fv(h_fv, hyp_ty, over_c)
                },
                &|d, i2, _ih2| {
                    let si2 = d.succ(i2);
                    let hyp_ty = d.lt(si2, sj);
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);

                    let np = d.prelude();
                    // `Lt (succ i2) (succ j)` gives `Le (succ i2) j`, which IS
                    // `Lt i2 j`.
                    let hlt_i2 = d.lemma(np.le_of_lt_succ, &[si2, j, h]);
                    let ih_eq = d.apply(ih, &[ss, tail_g, set, i2, hlt_i2, c]);

                    let subst_j = rmat_subst_rows(d, p, b, j, ss, tail_g, set);
                    let row_ih = d.add(ss, i2);
                    let row_target = d.add(s, si2);
                    let hidx = d.lemma(np.succ_add, &[s, i2]);
                    let hcong = nat_eq_to_rat(d, row_ih, row_target, hidx, &|d, x| {
                        d.apply(subst_j, &[x, c])
                    });

                    let start = {
                        let full = rmat_subst_rows(d, p, b, sj, s, g, mat);
                        d.apply(full, &[row_target, c])
                    };
                    let mid = d.apply(subst_j, &[row_ih, c]);
                    let end_ = {
                        let gi = d.apply(g, &[si2]);
                        d.apply(b, &[gi, c])
                    };
                    let back = rsymm(d, mid, start, hcong);
                    let (_, chained) = rchain(d, start, &[(mid, back), (end_, ih_eq)]);
                    let over_c = d.lam_fv(c_fv, nat, chained);
                    d.lam_fv(h_fv, hyp_ty, over_c)
                },
                i_outer,
            );

            let over_i = d.lam_fv(i_outer_fv, nat, index_proof);
            let over_mat = d.lam_fv(mat_fv, mty, over_i);
            let over_g = d.lam_fv(g_fv, map_t, over_mat);
            d.lam_fv(s_fv, nat, over_g)
        },
        m,
    );

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, stmt);
        d.pi_fv(b_fv, mty, over_m)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        d.lam_fv(b_fv, mty, over_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_subst_rows_at,
        uparams: vec![],
        ty,
        value,
    })
}

/// `fun q => altSign (q + t) * (h q * det (matMinor A t q) m)` — the cofactor
/// summand with the row entries taken from `h` and the minors from `A`. A
/// local copy of `matrix_det`'s private `row_replaced_fn`, which is the shape
/// `Rat.det_row_replaced` and `Rat.det_row_multilinear` both conclude with.
pub(super) fn row_replaced_fn(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    h: ExprId,
    t: ExprId,
    m: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let index = d.add(q, t);
    let sign = ralt_sign(d, p, index);
    let entry = d.apply(h, &[q]);
    let minor = rmat_minor_of(d, p, a, t, q);
    let sub = rdet(d, p, minor, m);
    let product = rmul(d, entry, sub);
    let body = rmul(d, sign, product);
    d.lam_fv(q_fv, nat, body)
}

// --- the bounded congruence for a function-space sum -----------------------

/// `Rat.sumMaps_congr_mapsInto : ∀ n m F G,
/// (∀ g, MapsInto g n → F g = G g) → sumMaps m n F = sumMaps m n G`.
///
/// `Rat.sumMaps_congr`'s pointwise hypothesis weakened to the maps that
/// actually occur. Every map `Rat.sumMaps` enumerates IS a self-map of
/// `[0,n)` — the base case is the constant zero and every step `cons`es an
/// index the outer `Rat.sumRange` bounds — but nothing carries that until
/// this lemma does, and `Rat.det_row_selection`'s `MapsInto` hypothesis
/// cannot be discharged without it.
///
/// `Rat.sumRange_congr_lt`, not `Rat.sumRange_congr`, is what makes the
/// successor step work: its `Lt k n` is exactly the bound the `cons`'s head
/// needs. Note the base case needs no `0 < n` side condition — `MapsInto`
/// only constrains indices below `n`, and having one at all gives `0 < n`.
fn declare_sum_maps_congr_maps_into(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let fam = fam_ty(d);
    let map_t = map_ty(d);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    // `∀ g, MapsInto g n → F g = G g`.
    let restricted = |d: &mut IntDev<'_>, f: ExprId, gg: ExprId| -> ExprId {
        let map_t = map_ty(d);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let np = d.prelude();
        let mi = d.const_app(np.maps_into, &[a, n]);
        let fa = d.apply(f, &[a]);
        let ga = d.apply(gg, &[a]);
        let eq = req(d, fa, ga);
        let with_mi = d.arrow(mi, eq);
        d.pi_fv(a_fv, map_t, with_mi)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let gg = d.kernel().fvar(g_fv);
        let hyp = restricted(d, f, gg);
        let lhs = rsum_maps(d, p, x, n, f);
        let rhs = rsum_maps(d, p, x, n, gg);
        let concl = req(d, lhs, rhs);
        let with_h = d.arrow(hyp, concl);
        let over_g = d.pi_fv(g_fv, fam, with_h);
        d.pi_fv(f_fv, fam, over_g)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let g_fv = d.fresh_fvar();
            let gg = d.kernel().fvar(g_fv);
            let hyp_ty = restricted(d, f, gg);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let junk = junk_map(d);
            let mi_proof = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, n);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let np = d.prelude();
                let zero_n = d.zero();
                let zle = d.lemma(np.zero_le, &[i]);
                let s_zero = d.succ(zero_n);
                let si = d.succ(i);
                let step = d.lemma(np.succ_le_succ, &[zero_n, i, zle]);
                let body = d.lemma(np.le_trans, &[s_zero, si, n, step, hi]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, body);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let applied = d.apply(h, &[junk, mi_proof]);
            let with_h = d.lam_fv(h_fv, hyp_ty, applied);
            let over_g = d.lam_fv(g_fv, fam, with_h);
            d.lam_fv(f_fv, fam, over_g)
        },
        &|d, j, ih| {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let g_fv = d.fresh_fvar();
            let gg = d.kernel().fvar(g_fv);
            let hyp_ty = restricted(d, f, gg);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let shift = |d: &mut IntDev<'_>, target: ExprId, k: ExprId| -> ExprId {
                let map_t = map_ty(d);
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let c = cons_fn(d, k, a);
                let body = d.apply(target, &[c]);
                d.lam_fv(a_fv, map_t, body)
            };

            let summand_lhs = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sf = shift(d, f, k);
                let body = rsum_maps(d, p, j, n, sf);
                d.lam_fv(k_fv, nat, body)
            };
            let summand_rhs = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sg = shift(d, gg, k);
                let body = rsum_maps(d, p, j, n, sg);
                d.lam_fv(k_fv, nat, body)
            };
            let per_k = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let hk_ty = d.lt(k, n);
                let hk_fv = d.fresh_fvar();
                let hk = d.kernel().fvar(hk_fv);

                let sf = shift(d, f, k);
                let sg = shift(d, gg, k);
                let inner_h = {
                    let a_fv = d.fresh_fvar();
                    let a = d.kernel().fvar(a_fv);
                    let np = d.prelude();
                    let mi_ty = d.const_app(np.maps_into, &[a, n]);
                    let hmi_fv = d.fresh_fvar();
                    let hmi = d.kernel().fvar(hmi_fv);
                    let c = cons_fn(d, k, a);
                    let cons_mi = {
                        let index_motive = |d: &mut IntDev<'_>, i: ExprId| -> ExprId {
                            let hi = d.lt(i, n);
                            let ci = d.apply(c, &[i]);
                            let concl = d.lt(ci, n);
                            d.arrow(hi, concl)
                        };
                        let i_fv = d.fresh_fvar();
                        let i = d.kernel().fvar(i_fv);
                        let body = d.induct(
                            &index_motive,
                            &|d| {
                                let zero_n = d.zero();
                                let hi_ty = d.lt(zero_n, n);
                                let hi_fv = d.fresh_fvar();
                                d.lam_fv(hi_fv, hi_ty, hk)
                            },
                            &|d, i2, _ih2| {
                                let si2 = d.succ(i2);
                                let hi_ty = d.lt(si2, n);
                                let hi_fv = d.fresh_fvar();
                                let hi = d.kernel().fvar(hi_fv);
                                let np = d.prelude();
                                let ssi2 = d.succ(si2);
                                let step = d.lemma(np.le_succ, &[si2]);
                                let lt_i2 = d.lemma(np.le_trans, &[si2, ssi2, n, step, hi]);
                                let body = d.apply(hmi, &[i2, lt_i2]);
                                d.lam_fv(hi_fv, hi_ty, body)
                            },
                            i,
                        );
                        d.lam_fv(i_fv, nat, body)
                    };
                    let applied = d.apply(h, &[c, cons_mi]);
                    let with_mi = d.lam_fv(hmi_fv, mi_ty, applied);
                    d.lam_fv(a_fv, map_t, with_mi)
                };
                let body = d.apply(ih, &[sf, sg, inner_h]);
                let with_hk = d.lam_fv(hk_fv, hk_ty, body);
                d.lam_fv(k_fv, nat, with_hk)
            };
            let congr = d.lemma(p.sum_range_congr_lt, &[summand_lhs, summand_rhs, n, per_k]);
            let with_h = d.lam_fv(h_fv, hyp_ty, congr);
            let over_g = d.lam_fv(g_fv, fam, with_h);
            d.lam_fv(f_fv, fam, over_g)
        },
        m,
    );

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, stmt);
        d.pi_fv(n_fv, nat, over_m)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        d.lam_fv(n_fv, nat, over_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_maps_congr_maps_into,
        uparams: vec![],
        ty,
        value,
    })
}

// --- obligation 1: the Cauchy-Binet expansion ------------------------------

/// `Rat.det_matMul_expand : ∀ m n A B, det (matMul A B n) (succ m) =
/// sumMaps (succ m) n (fun g => prodRange (fun i => A i (g i)) (succ m) *
/// det (fun r c => B (g r) c) (succ m))` — **ADR-1440's obligation 1**.
///
/// The induction is on a CURSOR `x`, the number of rows still to expand,
/// against an OFFSET `s`, the first of them, with the coefficient matrix and
/// the working matrix both inside the motive because the step hands the
/// induction hypothesis a shifted coefficient matrix and a substituted
/// working one:
///
/// ```text
/// ∀ s A M, (∀ i, i < x → ble (s+i) m = true)
///        → (∀ i, i < x → ∀ c, M (s+i) c = sumRange (fun k => A i k * B k c) n)
///        → det M (succ m)
///          = sumMaps x n (fun g => prodRange (fun i => A i (g i)) x
///                                * det (matSubstRows B x s g M) (succ m))
/// ```
///
/// One step is four lemmas and no arithmetic beyond `Nat.succ_add`:
///
/// 1. `Rat.det_row_multilinear` at row `s` turns `det M` into a sum over the
///    inner index `k` of the cofactor sum whose row entries are
///    `A 0 k * B k ·`.
/// 2. `Rat.det_row_replaced` at the SAME row, applied to
///    `matSetRow s (A 0 k * B k ·) M`, produces the identical inner sum — so
///    the two read backwards give `det M = Σ_k det (that matrix)`, with no
///    minor ever mentioned outside the two lemma statements.
/// 3. `Rat.det_row_smul` pulls `A 0 k` out, leaving `matSetRow s (B k) M`.
/// 4. The induction hypothesis at `(succ s, A ∘ succ, matSetRow s (B k) M)`
///    expands the rest, and `Rat.prodRange_shiftFront` + `Rat.mul_assoc` +
///    `Rat.sumMaps_mul_left` put the result in exactly the shape
///    `Rat.sumMaps_succ` unfolds the right-hand side to.
///
/// The whole reason step 4 lines up is `Rat.matSubstRows`'s recursion order:
/// `matSubstRows B (succ j) s (cons k g) M` IS
/// `matSubstRows B j (succ s) g (matSetRow s (B k) M)` up to ι and η.
fn declare_det_mat_mul_expand(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let map_t = map_ty(d);

    let m0_fv = d.fresh_fvar();
    let m0 = d.kernel().fvar(m0_fv);
    let nn_fv = d.fresh_fvar();
    let nn = d.kernel().fvar(nn_fv);
    let a_fv = d.fresh_fvar();
    let a_top = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let dim = d.succ(m0);

    // `∀ i, Lt i x → Nat.ble (add s i) m0 = true`.
    let h0_ty = |d: &mut IntDev<'_>, x: ExprId, s: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi = d.lt(i, x);
        let row = d.add(s, i);
        let concl = ble_true_ty(d, row, m0);
        let with_hi = d.arrow(hi, concl);
        d.pi_fv(i_fv, nat, with_hi)
    };

    // `∀ i, Lt i x → ∀ c, M (add s i) c = sumRange (fun k => A i k * B k c) n`.
    let h1_ty = |d: &mut IntDev<'_>, x: ExprId, s: ExprId, aa: ExprId, mm: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi = d.lt(i, x);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let row = d.add(s, i);
        let lhs = d.apply(mm, &[row, c]);
        let summand = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let aik = d.apply(aa, &[i, k]);
            let bkc = d.apply(b, &[k, c]);
            let body = rmul(d, aik, bkc);
            d.lam_fv(k_fv, nat, body)
        };
        let rhs = rsum_range(d, p, summand, nn);
        let eq = req(d, lhs, rhs);
        let over_c = d.pi_fv(c_fv, nat, eq);
        let with_hi = d.arrow(hi, over_c);
        d.pi_fv(i_fv, nat, with_hi)
    };

    // `fun g => prodRange (fun i => A i (g i)) x * det (matSubstRows B x s g M) dim`.
    let family = |d: &mut IntDev<'_>, x: ExprId, s: ExprId, aa: ExprId, mm: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let map_t = map_ty(d);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let factors = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let gi = d.apply(g, &[i]);
            let body = d.apply(aa, &[i, gi]);
            d.lam_fv(i_fv, nat, body)
        };
        let coefficient = rprod_range(d, p, factors, x);
        let subst = rmat_subst_rows(d, p, b, x, s, g, mm);
        let det_term = rdet(d, p, subst, dim);
        let body = rmul(d, coefficient, det_term);
        d.lam_fv(g_fv, map_t, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let mty = mat_ty(d);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let aa_fv = d.fresh_fvar();
        let aa = d.kernel().fvar(aa_fv);
        let mm_fv = d.fresh_fvar();
        let mm = d.kernel().fvar(mm_fv);
        let hyp0 = h0_ty(d, x, s);
        let hyp1 = h1_ty(d, x, s, aa, mm);
        let lhs = rdet(d, p, mm, dim);
        let fam_x = family(d, x, s, aa, mm);
        let rhs = rsum_maps(d, p, x, nn, fam_x);
        let eq = req(d, lhs, rhs);
        let with_h1 = d.arrow(hyp1, eq);
        let with_h0 = d.arrow(hyp0, with_h1);
        let over_mm = d.pi_fv(mm_fv, mty, with_h0);
        let over_aa = d.pi_fv(aa_fv, mty, over_mm);
        d.pi_fv(s_fv, nat, over_aa)
    };
    let cursor_stmt = motive(d, dim);

    let cursor_proof = d.induct(
        &motive,
        &|d| {
            let nat = d.nat_ty();
            let mty = mat_ty(d);
            let s_fv = d.fresh_fvar();
            let s = d.kernel().fvar(s_fv);
            let aa_fv = d.fresh_fvar();
            let aa = d.kernel().fvar(aa_fv);
            let mm_fv = d.fresh_fvar();
            let mm = d.kernel().fvar(mm_fv);
            let zero_n = d.zero();
            let hyp0 = h0_ty(d, zero_n, s);
            let hyp1 = h1_ty(d, zero_n, s, aa, mm);
            let h0_fv = d.fresh_fvar();
            let h1_fv = d.fresh_fvar();

            // `sumMaps 0 n F ≡ F junk ≡ prodRange _ 0 * det M dim ≡ 1 * det M dim`.
            let det_m = rdet(d, p, mm, dim);
            let one_mul = one_mul_pf(d, p, det_m);
            let one_r = rone(d, p);
            let scaled = rmul(d, one_r, det_m);
            let body = rsymm(d, scaled, det_m, one_mul);

            let with_h1 = d.lam_fv(h1_fv, hyp1, body);
            let with_h0 = d.lam_fv(h0_fv, hyp0, with_h1);
            let over_mm = d.lam_fv(mm_fv, mty, with_h0);
            let over_aa = d.lam_fv(aa_fv, mty, over_mm);
            d.lam_fv(s_fv, nat, over_aa)
        },
        &|d, j, ih| {
            let nat = d.nat_ty();
            let mty = mat_ty(d);
            let map_t = map_ty(d);
            let s_fv = d.fresh_fvar();
            let s = d.kernel().fvar(s_fv);
            let aa_fv = d.fresh_fvar();
            let aa = d.kernel().fvar(aa_fv);
            let mm_fv = d.fresh_fvar();
            let mm = d.kernel().fvar(mm_fv);
            let sj = d.succ(j);
            let hyp0 = h0_ty(d, sj, s);
            let hyp1 = h1_ty(d, sj, s, aa, mm);
            let h0_fv = d.fresh_fvar();
            let h0 = d.kernel().fvar(h0_fv);
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);

            let zero_n = d.zero();
            let ss = d.succ(s);
            let det_m = rdet(d, p, mm, dim);

            // The row-`s` facts, read off the two hypotheses at relative
            // index `0` (`add s 0` ι-reduces to `s`).
            let hlt0 = d.zero_lt_succ(j);
            let hble_s = d.apply(h0, &[zero_n, hlt0]);
            let hlt0b = d.zero_lt_succ(j);
            let hrow = d.apply(h1, &[zero_n, hlt0b]);

            // `coef := fun k c => A 0 k * B k c`.
            let coef = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let a0k = d.apply(aa, &[zero_n, k]);
                let bkc = d.apply(b, &[k, c]);
                let body = rmul(d, a0k, bkc);
                let over_c = d.lam_fv(c_fv, nat, body);
                d.lam_fv(k_fv, nat, over_c)
            };
            // `∀ r, beq r s = false → ∀ c, M r c = M r c`.
            let hoff_refl = {
                let r_fv = d.fresh_fvar();
                let r = d.kernel().fvar(r_fv);
                let hne_ty = beq_false_ty(d, r, s);
                let hne_fv = d.fresh_fvar();
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let mrc = d.apply(mm, &[r, c]);
                let refl = rrefl(d, mrc);
                let over_c = d.lam_fv(c_fv, nat, refl);
                let with_hne = d.lam_fv(hne_fv, hne_ty, over_c);
                d.lam_fv(r_fv, nat, with_hne)
            };
            let hmulti = d.lemma(
                p.det_row_multilinear,
                &[m0, mm, mm, coef, s, nn, hble_s, hrow, hoff_refl],
            );

            // `fun k => sumRange (cofactor summand at k) dim`, the shape both
            // `det_row_multilinear` and `det_row_replaced` conclude with.
            let outer_fn = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let coef_k = d.apply(coef, &[k]);
                let inner = row_replaced_fn(d, p, mm, coef_k, s, m0);
                let body = rsum_range(d, p, inner, dim);
                d.lam_fv(k_fv, nat, body)
            };
            let after_multi = rsum_range(d, p, outer_fn, nn);

            // `fun k => A 0 k * det (matSetRow s (B k) M) dim`.
            let scaled_fn = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let a0k = d.apply(aa, &[zero_n, k]);
                let b_row = d.apply(b, &[k]);
                let ak = rmat_set_row(d, p, s, b_row, mm);
                let det_ak = rdet(d, p, ak, dim);
                let body = rmul(d, a0k, det_ak);
                d.lam_fv(k_fv, nat, body)
            };
            let after_smul = rsum_range(d, p, scaled_fn, nn);

            let per_k_left = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let coef_k = d.apply(coef, &[k]);
                let b_row = d.apply(b, &[k]);
                let a0k = d.apply(aa, &[zero_n, k]);
                let mk = rmat_set_row(d, p, s, coef_k, mm);
                let ak = rmat_set_row(d, p, s, b_row, mm);

                let at_of = |d: &mut IntDev<'_>, row: ExprId, target: ExprId| -> ExprId {
                    let nat = d.nat_ty();
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);
                    let body = d.lemma(p.mat_set_row_at, &[s, row, mm, c]);
                    let _ = target;
                    d.lam_fv(c_fv, nat, body)
                };
                let off_of = |d: &mut IntDev<'_>, row: ExprId| -> ExprId {
                    let nat = d.nat_ty();
                    let r_fv = d.fresh_fvar();
                    let r = d.kernel().fvar(r_fv);
                    let hne_ty = beq_false_ty(d, r, s);
                    let hne_fv = d.fresh_fvar();
                    let hne = d.kernel().fvar(hne_fv);
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);
                    let body = d.lemma(p.mat_set_row_off, &[s, row, mm, r, hne, c]);
                    let over_c = d.lam_fv(c_fv, nat, body);
                    let with_hne = d.lam_fv(hne_fv, hne_ty, over_c);
                    d.lam_fv(r_fv, nat, with_hne)
                };

                let hmk_at = at_of(d, coef_k, mk);
                let hmk_off = off_of(d, coef_k);
                let hrepl = d.lemma(
                    p.det_row_replaced,
                    &[m0, mm, mk, coef_k, s, hble_s, hmk_at, hmk_off],
                );

                // `∀ c, Mk s c = A 0 k * (Ak s c)`.
                let hz = {
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);
                    let mk_at = d.lemma(p.mat_set_row_at, &[s, coef_k, mm, c]);
                    let ak_at = d.lemma(p.mat_set_row_at, &[s, b_row, mm, c]);
                    let bkc = d.apply(b, &[k, c]);
                    let ak_sc = d.apply(ak, &[s, c]);
                    let back = rsymm(d, ak_sc, bkc, ak_at);
                    let step = rcongr(d, bkc, ak_sc, back, &|d, t| rmul(d, a0k, t));
                    let mk_sc = d.apply(mk, &[s, c]);
                    let mid = rmul(d, a0k, bkc);
                    let end_ = rmul(d, a0k, ak_sc);
                    let body = rtrans(d, mk_sc, mid, end_, mk_at, step);
                    d.lam_fv(c_fv, nat, body)
                };
                // `∀ r, beq r s = false → ∀ c, Mk r c = Ak r c`.
                let hoff2 = {
                    let r_fv = d.fresh_fvar();
                    let r = d.kernel().fvar(r_fv);
                    let hne_ty = beq_false_ty(d, r, s);
                    let hne_fv = d.fresh_fvar();
                    let hne = d.kernel().fvar(hne_fv);
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);
                    let mk_off = d.lemma(p.mat_set_row_off, &[s, coef_k, mm, r, hne, c]);
                    let ak_off = d.lemma(p.mat_set_row_off, &[s, b_row, mm, r, hne, c]);
                    let mrc = d.apply(mm, &[r, c]);
                    let ak_rc = d.apply(ak, &[r, c]);
                    let back = rsymm(d, ak_rc, mrc, ak_off);
                    let mk_rc = d.apply(mk, &[r, c]);
                    let body = rtrans(d, mk_rc, mrc, ak_rc, mk_off, back);
                    let over_c = d.lam_fv(c_fv, nat, body);
                    let with_hne = d.lam_fv(hne_fv, hne_ty, over_c);
                    d.lam_fv(r_fv, nat, with_hne)
                };
                let hsmul = d.lemma(p.det_row_smul, &[m0, ak, mk, a0k, s, hble_s, hz, hoff2]);

                let inner = row_replaced_fn(d, p, mm, coef_k, s, m0);
                let inner_sum = rsum_range(d, p, inner, dim);
                let det_mk = rdet(d, p, mk, dim);
                let det_ak = rdet(d, p, ak, dim);
                let target = rmul(d, a0k, det_ak);
                let back = rsymm(d, det_mk, inner_sum, hrepl);
                let body = rtrans(d, inner_sum, det_mk, target, back, hsmul);
                d.lam_fv(k_fv, nat, body)
            };
            let left_step = d.lemma(p.sum_range_congr, &[outer_fn, scaled_fn, nn, per_k_left]);

            // The right-hand side, and the same per-`k` value reached from it.
            let fam_sj = family(d, sj, s, aa, mm);
            let rhs_full = rsum_maps(d, p, sj, nn, fam_sj);
            let h_succ = d.lemma(p.sum_maps_succ, &[j, nn, fam_sj]);

            let tail_aa = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let si = d.succ(i);
                let body = d.apply(aa, &[si]);
                d.lam_fv(i_fv, nat, body)
            };

            let shift_fam = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                let map_t = map_ty(d);
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let c = cons_fn(d, k, g);
                let body = d.apply(fam_sj, &[c]);
                d.lam_fv(g_fv, map_t, body)
            };
            let rhs_inner_fn = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sf = shift_fam(d, k);
                let body = rsum_maps(d, p, j, nn, sf);
                d.lam_fv(k_fv, nat, body)
            };
            let rhs_after_succ = rsum_range(d, p, rhs_inner_fn, nn);

            let per_k_right = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let a0k = d.apply(aa, &[zero_n, k]);
                let b_row = d.apply(b, &[k]);
                let ak = rmat_set_row(d, p, s, b_row, mm);
                let det_ak = rdet(d, p, ak, dim);

                // The induction hypothesis at the shifted cursor.
                let h0_next = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hi_ty = d.lt(i, j);
                    let hi_fv = d.fresh_fvar();
                    let hi = d.kernel().fvar(hi_fv);
                    let np = d.prelude();
                    let si = d.succ(i);
                    let hlt = d.lemma(np.succ_le_succ, &[si, j, hi]);
                    let base = d.apply(h0, &[si, hlt]);
                    let add_si = d.add(s, i);
                    let succ_add_si = d.succ(add_si);
                    let row_next = d.add(ss, i);
                    let np = d.prelude();
                    let fwd = d.lemma(np.succ_add, &[s, i]);
                    let back = d.symm(row_next, succ_add_si, fwd);
                    let body = nat_rewrite_prop(d, succ_add_si, row_next, back, base, &|d, x| {
                        ble_true_ty(d, x, m0)
                    });
                    let with_hi = d.lam_fv(hi_fv, hi_ty, body);
                    d.lam_fv(i_fv, nat, with_hi)
                };
                let h1_next = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hi_ty = d.lt(i, j);
                    let hi_fv = d.fresh_fvar();
                    let hi = d.kernel().fvar(hi_fv);
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);

                    let row_next = d.add(ss, i);
                    let np = d.prelude();
                    let hgt = d.lemma(np.le_add_right, &[ss, i]);
                    let hne = beq_false_of_gt(d, s, row_next, hgt);
                    let off = d.lemma(p.mat_set_row_off, &[s, b_row, mm, row_next, hne, c]);

                    let add_si = d.add(s, i);
                    let succ_add_si = d.succ(add_si);
                    let np = d.prelude();
                    let hidx = d.lemma(np.succ_add, &[s, i]);
                    let cong =
                        nat_eq_to_rat(d, row_next, succ_add_si, hidx, &|d, x| d.apply(mm, &[x, c]));

                    let np = d.prelude();
                    let si = d.succ(i);
                    let hlt = d.lemma(np.succ_le_succ, &[si, j, hi]);
                    let base = d.apply(h1, &[si, hlt, c]);

                    let start = d.apply(ak, &[row_next, c]);
                    let mid1 = d.apply(mm, &[row_next, c]);
                    let mid2 = d.apply(mm, &[succ_add_si, c]);
                    let target = {
                        let summand = {
                            let kk_fv = d.fresh_fvar();
                            let kk = d.kernel().fvar(kk_fv);
                            let aik = d.apply(tail_aa, &[i, kk]);
                            let bkc = d.apply(b, &[kk, c]);
                            let body = rmul(d, aik, bkc);
                            d.lam_fv(kk_fv, nat, body)
                        };
                        rsum_range(d, p, summand, nn)
                    };
                    let (_, chained) =
                        rchain(d, start, &[(mid1, off), (mid2, cong), (target, base)]);
                    let over_c = d.lam_fv(c_fv, nat, chained);
                    let with_hi = d.lam_fv(hi_fv, hi_ty, over_c);
                    d.lam_fv(i_fv, nat, with_hi)
                };
                let ih_app = d.apply(ih, &[ss, tail_aa, ak, h0_next, h1_next]);

                let ih_family = family(d, j, ss, tail_aa, ak);
                let ih_sum = rsum_maps(d, p, j, nn, ih_family);

                // `fun g => A 0 k * ih_family g`, the shape `sumMaps_mul_left`
                // builds on the left of its equation.
                let scaled_family = {
                    let g_fv = d.fresh_fvar();
                    let g = d.kernel().fvar(g_fv);
                    let inner = d.apply(ih_family, &[g]);
                    let body = rmul(d, a0k, inner);
                    d.lam_fv(g_fv, map_t, body)
                };
                let scaled_sum = rsum_maps(d, p, j, nn, scaled_family);

                let per_g = {
                    let g_fv = d.fresh_fvar();
                    let g = d.kernel().fvar(g_fv);
                    let cg = cons_fn(d, k, g);

                    let factors = {
                        let i_fv = d.fresh_fvar();
                        let i = d.kernel().fvar(i_fv);
                        let cgi = d.apply(cg, &[i]);
                        let body = d.apply(aa, &[i, cgi]);
                        d.lam_fv(i_fv, nat, body)
                    };
                    let head_prod = rprod_range(d, p, factors, sj);
                    let tail_factors = {
                        let i_fv = d.fresh_fvar();
                        let i = d.kernel().fvar(i_fv);
                        let gi = d.apply(g, &[i]);
                        let body = d.apply(tail_aa, &[i, gi]);
                        d.lam_fv(i_fv, nat, body)
                    };
                    let tail_prod = rprod_range(d, p, tail_factors, j);
                    let subst = rmat_subst_rows(d, p, b, j, ss, g, ak);
                    let det_term = rdet(d, p, subst, dim);

                    let shift = d.lemma(p.prod_range_shift_front, &[factors, j]);
                    let split = rmul(d, a0k, tail_prod);
                    let step1 = rcongr(d, head_prod, split, shift, &|d, t| rmul(d, t, det_term));

                    let assoc = d.lemma(p.mul_assoc, &[a0k, tail_prod, det_term]);

                    let start = rmul(d, head_prod, det_term);
                    let mid = rmul(d, split, det_term);
                    let inner_pair = rmul(d, tail_prod, det_term);
                    let end_ = rmul(d, a0k, inner_pair);
                    let (_, chained) = rchain(d, start, &[(mid, step1), (end_, assoc)]);
                    d.lam_fv(g_fv, map_t, chained)
                };

                let sf = shift_fam(d, k);
                let congr1 = d.lemma(p.sum_maps_congr, &[nn, j, sf, scaled_family, per_g]);
                let pull = d.lemma(p.sum_maps_mul_left, &[nn, a0k, j, ih_family]);
                let back = rsymm(d, det_ak, ih_sum, ih_app);
                let lift = rcongr(d, ih_sum, det_ak, back, &|d, t| rmul(d, a0k, t));

                let start = rsum_maps(d, p, j, nn, sf);
                let mid1 = scaled_sum;
                let mid2 = rmul(d, a0k, ih_sum);
                let end_ = rmul(d, a0k, det_ak);
                let (_, chained) = rchain(d, start, &[(mid1, congr1), (mid2, pull), (end_, lift)]);
                d.lam_fv(k_fv, nat, chained)
            };
            let right_step = d.lemma(
                p.sum_range_congr,
                &[rhs_inner_fn, scaled_fn, nn, per_k_right],
            );

            let back_right = rsymm(d, rhs_after_succ, after_smul, right_step);
            let back_succ = rsymm(d, rhs_full, rhs_after_succ, h_succ);
            let (_, body) = rchain(
                d,
                det_m,
                &[
                    (after_multi, hmulti),
                    (after_smul, left_step),
                    (rhs_after_succ, back_right),
                    (rhs_full, back_succ),
                ],
            );

            let with_h1 = d.lam_fv(h1_fv, hyp1, body);
            let with_h0 = d.lam_fv(h0_fv, hyp0, with_h1);
            let over_mm = d.lam_fv(mm_fv, mty, with_h0);
            let over_aa = d.lam_fv(aa_fv, mty, over_mm);
            d.lam_fv(s_fv, nat, over_aa)
        },
        dim,
    );
    let _ = cursor_stmt;

    // --- instantiate at the whole matrix -----------------------------------

    let zero_n = d.zero();
    let product = d.const_app(p.mat_mul, &[a_top, b, nn]);

    let h0_top = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = d.lt(i, dim);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let np = d.prelude();
        let hle = d.lemma(np.le_of_lt_succ, &[i, m0, hi]);
        let hble = d.lemma(np.ble_eq_true_of_le, &[i, m0, hle]);
        let row = d.add(zero_n, i);
        let np = d.prelude();
        let hzero = d.lemma(np.zero_add, &[i]);
        let back = d.symm(row, i, hzero);
        let body = nat_rewrite_prop(d, i, row, back, hble, &|d, x| ble_true_ty(d, x, m0));
        let with_hi = d.lam_fv(hi_fv, hi_ty, body);
        d.lam_fv(i_fv, nat, with_hi)
    };
    let h1_top = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = d.lt(i, dim);
        let hi_fv = d.fresh_fvar();
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let row = d.add(zero_n, i);
        let np = d.prelude();
        let hzero = d.lemma(np.zero_add, &[i]);
        let body = nat_eq_to_rat(d, row, i, hzero, &|d, x| d.apply(product, &[x, c]));
        let over_c = d.lam_fv(c_fv, nat, body);
        let with_hi = d.lam_fv(hi_fv, hi_ty, over_c);
        d.lam_fv(i_fv, nat, with_hi)
    };

    let instantiated = d.apply(cursor_proof, &[zero_n, a_top, product, h0_top, h1_top]);
    let subst_family = family(d, dim, zero_n, a_top, product);
    let subst_sum = rsum_maps(d, p, dim, nn, subst_family);

    // `fun g => prodRange (fun i => A i (g i)) dim * det (B ∘ g) dim`.
    let clean_family = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let factors = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let gi = d.apply(g, &[i]);
            let body = d.apply(a_top, &[i, gi]);
            d.lam_fv(i_fv, nat, body)
        };
        let coefficient = rprod_range(d, p, factors, dim);
        let composed = row_compose(d, b, g);
        let det_term = rdet(d, p, composed, dim);
        let body = rmul(d, coefficient, det_term);
        d.lam_fv(g_fv, map_t, body)
    };
    let clean_sum = rsum_maps(d, p, dim, nn, clean_family);

    let bridge = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let subst = rmat_subst_rows(d, p, b, dim, zero_n, g, product);
        let composed = row_compose(d, b, g);
        let pointwise = {
            let r_fv = d.fresh_fvar();
            let r = d.kernel().fvar(r_fv);
            let hr_ty = d.lt(r, dim);
            let hr_fv = d.fresh_fvar();
            let hr = d.kernel().fvar(hr_fv);
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let row = d.add(zero_n, r);
            let at_ = d.lemma(p.mat_subst_rows_at, &[b, dim, zero_n, g, product, r, hr, c]);
            let np = d.prelude();
            let hzero = d.lemma(np.zero_add, &[r]);
            let cong = nat_eq_to_rat(d, row, r, hzero, &|d, x| d.apply(subst, &[x, c]));
            let start = d.apply(subst, &[r, c]);
            let mid = d.apply(subst, &[row, c]);
            let gr = d.apply(g, &[r]);
            let end_ = d.apply(b, &[gr, c]);
            let back = rsymm(d, mid, start, cong);
            let (_, chained) = rchain(d, start, &[(mid, back), (end_, at_)]);
            let over_c = d.lam_fv(c_fv, nat, chained);
            let with_hr = d.lam_fv(hr_fv, hr_ty, over_c);
            d.lam_fv(r_fv, nat, with_hr)
        };
        let hdet = d.lemma(p.det_congr_lt, &[dim, subst, composed, pointwise]);
        let subst_det = rdet(d, p, subst, dim);
        let clean_det = rdet(d, p, composed, dim);
        let factors = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let gi = d.apply(g, &[i]);
            let body = d.apply(a_top, &[i, gi]);
            d.lam_fv(i_fv, nat, body)
        };
        let coefficient = rprod_range(d, p, factors, dim);
        let body = rcongr(d, subst_det, clean_det, hdet, &|d, t| {
            rmul(d, coefficient, t)
        });
        d.lam_fv(g_fv, map_t, body)
    };
    let congr = d.lemma(
        p.sum_maps_congr,
        &[nn, dim, subst_family, clean_family, bridge],
    );

    let det_product = rdet(d, p, product, dim);
    let (_, full) = rchain(
        d,
        det_product,
        &[(subst_sum, instantiated), (clean_sum, congr)],
    );
    let stmt = req(d, det_product, clean_sum);

    let ty = {
        let over_b = d.pi_fv(b_fv, mty, stmt);
        let over_a = d.pi_fv(a_fv, mty, over_b);
        let over_nn = d.pi_fv(nn_fv, nat, over_a);
        d.pi_fv(m0_fv, nat, over_nn)
    };
    let value = {
        let over_b = d.lam_fv(b_fv, mty, full);
        let over_a = d.lam_fv(a_fv, mty, over_b);
        let over_nn = d.lam_fv(nn_fv, nat, over_a);
        d.lam_fv(m0_fv, nat, over_nn)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.det_mat_mul_expand,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.det_matMul : ∀ n A B, det (matMul A B n) n = det A n * det B n`.
///
/// Assembled from [`declare_det_mat_mul_expand`] and
/// `Rat.det_row_selection`, and the assembly needs the expansion TWICE:
///
/// ```text
/// det (A·B) n = Σ_g  c(g) * det (B∘g) n                    -- expansion at B
///             = Σ_g  c(g) * (det (matId∘g) n * det B n)    -- selection
///             = (Σ_g c(g) * det (matId∘g) n) * det B n     -- sumMaps_mul_right
///             = det (A·matId) n * det B n                  -- expansion at matId
///             = det A n * det B n                          -- matMul_id_right
/// ```
///
/// The coefficient `c(g) = prodRange (fun i => A i (g i)) n` is never
/// evaluated: it is the same term in both instances of the expansion, which is
/// the whole reason `Rat.prodRange` needs no algebra beyond its own front
/// peel. The last step is `Rat.det_congr_entry_lt`, not `det_congr_lt`,
/// because `Rat.matMul_id_right`'s bound is on the COLUMN.
///
/// `n = 0` is a separate leg: `det _ 0 ≡ 1` on both sides and the goal is
/// `1 = 1 * 1`.
fn declare_det_mat_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let map_t = map_ty(d);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let product = d.const_app(p.mat_mul, &[a, b, x]);
        let lhs = rdet(d, p, product, x);
        let da = rdet(d, p, a, x);
        let db = rdet(d, p, b, x);
        let rhs = rmul(d, da, db);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            // Both sides reduce to `Rat.one`; the goal is `1 = 1 * 1`.
            let one_r = rone(d, p);
            let squared = rmul(d, one_r, one_r);
            let unit = d.lemma(p.mul_one, &[one_r]);
            rsymm(d, squared, one_r, unit)
        },
        &|d, m0, _ih| {
            let nat = d.nat_ty();
            let map_t = map_ty(d);
            let dim = d.succ(m0);
            let mat_id = rmat_id(d, p);

            let expand_b = d.lemma(p.det_mat_mul_expand, &[m0, dim, a, b]);
            let expand_id = d.lemma(p.det_mat_mul_expand, &[m0, dim, a, mat_id]);

            let coefficient_of = |d: &mut IntDev<'_>, g: ExprId| -> ExprId {
                let nat = d.nat_ty();
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let gi = d.apply(g, &[i]);
                let body = d.apply(a, &[i, gi]);
                let factors = d.lam_fv(i_fv, nat, body);
                rprod_range(d, p, factors, dim)
            };
            let family_over = |d: &mut IntDev<'_>, mat: ExprId| -> ExprId {
                let map_t = map_ty(d);
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let coefficient = coefficient_of(d, g);
                let composed = row_compose(d, mat, g);
                let det_term = rdet(d, p, composed, dim);
                let body = rmul(d, coefficient, det_term);
                d.lam_fv(g_fv, map_t, body)
            };

            let fam_b = family_over(d, b);
            let fam_id = family_over(d, mat_id);
            let det_b = rdet(d, p, b, dim);

            // `fun g => fam_id g * det B dim`, the shape `sumMaps_mul_right`
            // builds on the left of its equation.
            let scaled_family = {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let inner = d.apply(fam_id, &[g]);
                let body = rmul(d, inner, det_b);
                d.lam_fv(g_fv, map_t, body)
            };

            let per_g = {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let np = d.prelude();
                let mi_ty = d.const_app(np.maps_into, &[g, dim]);
                let hmi_fv = d.fresh_fvar();
                let hmi = d.kernel().fvar(hmi_fv);

                let selection = d.lemma(p.det_row_selection, &[m0, b, g, hmi]);
                let coefficient = coefficient_of(d, g);
                let composed_b = row_compose(d, b, g);
                let det_bg = rdet(d, p, composed_b, dim);
                let composed_id = row_compose(d, mat_id, g);
                let det_ig = rdet(d, p, composed_id, dim);
                let pair = rmul(d, det_ig, det_b);
                let step1 = rcongr(d, det_bg, pair, selection, &|d, t| rmul(d, coefficient, t));
                let assoc = d.lemma(p.mul_assoc, &[coefficient, det_ig, det_b]);
                let start = rmul(d, coefficient, det_bg);
                let mid = rmul(d, coefficient, pair);
                let grouped = rmul(d, coefficient, det_ig);
                let end_ = rmul(d, grouped, det_b);
                let back = rsymm(d, end_, mid, assoc);
                let (_, chained) = rchain(d, start, &[(mid, step1), (end_, back)]);
                let with_mi = d.lam_fv(hmi_fv, mi_ty, chained);
                d.lam_fv(g_fv, map_t, with_mi)
            };
            let congr = d.lemma(
                p.sum_maps_congr_maps_into,
                &[dim, dim, fam_b, scaled_family, per_g],
            );
            let pull = d.lemma(p.sum_maps_mul_right, &[dim, det_b, dim, fam_id]);

            // `det (A · matId) dim = det A dim`, bounded on both indices.
            let id_product = d.const_app(p.mat_mul, &[a, mat_id, dim]);
            let entrywise = {
                let r_fv = d.fresh_fvar();
                let r = d.kernel().fvar(r_fv);
                let hr_ty = d.lt(r, dim);
                let hr_fv = d.fresh_fvar();
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let hc_ty = d.lt(c, dim);
                let hc_fv = d.fresh_fvar();
                let hc = d.kernel().fvar(hc_fv);
                let body = d.lemma(p.mat_mul_id_right, &[a, dim, r, c, hc]);
                let with_hc = d.lam_fv(hc_fv, hc_ty, body);
                let over_c = d.pi_fv(c_fv, nat, with_hc);
                let _ = over_c;
                let inner = d.lam_fv(c_fv, nat, with_hc);
                let with_hr = d.lam_fv(hr_fv, hr_ty, inner);
                d.lam_fv(r_fv, nat, with_hr)
            };
            let collapse = d.lemma(p.det_congr_entry_lt, &[dim, id_product, a, entrywise]);

            let det_product = {
                let product = d.const_app(p.mat_mul, &[a, b, dim]);
                rdet(d, p, product, dim)
            };
            let sum_b = rsum_maps(d, p, dim, dim, fam_b);
            let sum_scaled = rsum_maps(d, p, dim, dim, scaled_family);
            let sum_id = rsum_maps(d, p, dim, dim, fam_id);
            let det_id_product = rdet(d, p, id_product, dim);
            let det_a = rdet(d, p, a, dim);

            let back_expand_id = rsymm(d, det_id_product, sum_id, expand_id);
            let lift_id = rcongr(d, sum_id, det_id_product, back_expand_id, &|d, t| {
                rmul(d, t, det_b)
            });
            let lift_a = rcongr(d, det_id_product, det_a, collapse, &|d, t| {
                rmul(d, t, det_b)
            });

            let scaled_pair = rmul(d, sum_id, det_b);
            let id_pair = rmul(d, det_id_product, det_b);
            let target = rmul(d, det_a, det_b);
            let (_, chained) = rchain(
                d,
                det_product,
                &[
                    (sum_b, expand_b),
                    (sum_scaled, congr),
                    (scaled_pair, pull),
                    (id_pair, lift_id),
                    (target, lift_a),
                ],
            );
            chained
        },
        n,
    );
    let _ = map_t;

    let ty = {
        let over_b = d.pi_fv(b_fv, mty, stmt);
        let over_a = d.pi_fv(a_fv, mty, over_b);
        d.pi_fv(n_fv, nat, over_a)
    };
    let value = {
        let over_b = d.lam_fv(b_fv, mty, proof);
        let over_a = d.lam_fv(a_fv, mty, over_b);
        d.lam_fv(n_fv, nat, over_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.det_mat_mul,
        uparams: vec![],
        ty,
        value,
    })
}
