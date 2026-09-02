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
use super::matrix_det::{mat_ty, rdet, rmat_minor_of};
use super::ops::{nat_eq_to_rat, nat_rewrite_prop, rat_ty, rchain, req, rrefl, rsymm};
use super::probability::{bool_select_rat, select_rat_false, select_rat_true};
use super::sum_maps::map_ty;
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
#[allow(dead_code)]
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
#[allow(dead_code)]
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
#[allow(dead_code)]
pub(super) fn row_replaced_fn(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    h: ExprId,
    t: ExprId,
    m: ExprId,
) -> ExprId {
    use super::matrix_det::ralt_sign;
    use super::ops::rmul;
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
