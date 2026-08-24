//! The diagonal reindexing over ℕ that a Cauchy product needs: relating a
//! sum over pairs `(i, j)` with `i + j = k` (grouped by antidiagonal `k`) to
//! the same sum grouped by row `i`.
//!
//! # Can the diagonal be enumerated without `Nat.sub`?
//!
//! No — not the *value* `j` given `i` and `k`, though the *proof* that
//! `i + j = k` never needs to unfold `Nat.sub`'s own recursion.
//!
//! `Nat.le_dest : ∀ a b, Le a b → Exists (fun d => add a d = b)` looks like an
//! additive route to the diagonal's second coordinate: `i ≤ k` gives a `d`
//! with `add i d = k`, obtained by *destructing* a proof rather than
//! *subtracting*. But `Exists` in this kernel does not support extracting
//! that `d` as a computable `Nat`. [`crate::inductive`]'s recursor generator
//! only allows a `Prop`-valued inductive to eliminate into a non-`Prop`
//! motive when its sole constructor `exposes_non_prop_fields` — every
//! non-`Prop` field of the constructor's result must appear literally among
//! that result's own indices (`inductive.rs`, `exposes_non_prop_fields`).
//! `Exists.intro`'s non-`Prop` field is the witness `w : α`, and it is not an
//! index of `Exists α p` (`Exists` has zero indices — the witness is
//! existentially bound away, not carried). So `allows_large_elimination` is
//! `false` for `Exists`, `Exists.rec`'s generated universe parameters retain
//! only the inductive's own `u` (`prelude/prelude_tests.rs`'s
//! `exists_rec_retains_only_its_own_u_param`-shaped check), and every use of
//! `exists_rec` in this codebase — `super::choose::sub_succ_of_lt` included —
//! eliminates into a `Prop` motive (an equation between two ALREADY-BUILT
//! `Nat` terms), never to manufacture a new `Nat` value. This mirrors real
//! Lean 4's own restriction on `Exists`, and for the same reason: an
//! existential's witness is not computationally accessible without a choice
//! principle, which this kernel does not admit.
//!
//! And no *other* computable function can supply the diagonal's second
//! coordinate either: `Nat.add_left_cancel` makes `d` with `add i d = k`
//! UNIQUE once `i` and `k` are fixed, so any total computable `Nat → Nat →
//! Nat` satisfying that equation on `i ≤ k` computes the same graph
//! `Nat.sub` does. Renaming the recursion does not remove it.
//!
//! So the diagonal pairing is `Nat.diagPair k i := (i, sub k i)` (spelled out
//! inline below, not packaged as a separate `Prod`-valued definition — no use
//! site here needs the pair as a first-class value), and the discipline that
//! avoids the three off-by-ones `Nat.sub` hid elsewhere today is proof
//! STYLE, not statement shape: every equation this module proves about `sub`
//! goes through `succ_sub_of_le` / `sub_self` / `sub_add_cancel` — the
//! additive round-trip lemmas — never through unfolding `Nat.sub`'s own
//! `Nat.rec`. [`declare_add_sub_cancel_of_le`] is the missing round-trip in
//! that toolkit: `sub_add_cancel` restores `k` as `(k−i)+i`, and every
//! diagonal use site wants it the other way round, `i+(k−i)`.
//!
//! # The headline: `Nat.sumRange_diagonal`
//!
//! [`declare_sum_range_diagonal`] relates the triangle sum
//! `Σ_{k<n} Σ_{i≤k} F i (k−i)` (grouped by antidiagonal) to
//! `Σ_{i<n} Σ_{j<n−i} F i j` (grouped by row), both over the same index set
//! `{(i,j) : i+j < n}`. By induction on `n`:
//!
//! - Base case `n = 0`: both sides reduce to `zero` by `sumRange`'s own
//!   `zero`-case ι-rule (`Eq.refl`, no lemma needed).
//! - Successor step, given `T(n) = R(n)`: peel the new antidiagonal `k = n`
//!   off `T`, and the new row `i = n` off `R`; the surviving `i < n` rows of
//!   `R(succ n)` grow by one term each (`succ_sub_of_le` gives `n+1-i =
//!   succ(n-i)` for `i ≤ n`, then `sumRange_succ` peels it) via
//!   `sumRange_congr_lt`, and `sumRange_add` splits that growth from the row
//!   sum itself. Matching the two sides' remaining pieces up is `add_assoc`.
//!
//! Both peeled boundary terms — `F n (sub n n)` on the diagonal side, `F n
//! (sub (succ n) n)`'s row on the other — collapse to `F n 0` via
//! `succ_sub_of_le`/`sub_self`, which is where the two sides' extra terms
//! turn out to be the SAME term rather than two terms needing a further
//! identity.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `add_sub_cancel_of_le : ∀ i k, Le i k → add i (sub k i) = k`.
pub(super) fn declare_add_sub_cancel_of_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_sub_cancel_of_le, 2, &|d, v| {
        let (i, k) = (v[0], v[1]);
        let hyp_ty = d.le(i, k);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let sub_ki = d.sub(k, i);
        let add_i_ki = d.add(i, sub_ki);
        let add_ki_i = d.add(sub_ki, i);

        // sub_add_cancel i k h : add (sub k i) i = k
        let h1 = d.lemma(p.sub_add_cancel, &[i, k, h]);
        // add_comm i (sub k i) : add i (sub k i) = add (sub k i) i
        let h2 = d.lemma(p.add_comm, &[i, sub_ki]);
        let body = d.trans(add_i_ki, add_ki_i, k, h2, h1);

        let stmt = d.eq(add_i_ki, k);
        let full_stmt = d.arrow(hyp_ty, stmt);
        let full_proof = d.lam_fv(h_fv, hyp_ty, body);
        (full_stmt, full_proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Term builders shared by the headline theorem and its step proof.
// ---------------------------------------------------------------------------

/// `fun j => F i j`, i.e. `F` partially applied at the fixed row index `i`.
pub(super) fn row_inner(d: &mut NatDev<'_>, ff: ExprId, i: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let fij = d.apply(ff, &[i, j]);
    d.lam_fv(j_fv, nat, fij)
}

/// `fun i => sumRange (fun j => F i j) (sub bound i)` — one row of the
/// row-major reindexing, out to `bound`.
pub(super) fn row_fn(d: &mut NatDev<'_>, ff: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let inner = row_inner(d, ff, i);
    let b = d.sub(bound, i);
    let sr = d.sum_range(inner, b);
    d.lam_fv(i_fv, nat, sr)
}

/// `fun i => F i (sub k i)` — the antidiagonal `k`'s per-position summand.
fn diag_inner(d: &mut NatDev<'_>, ff: ExprId, k: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ki = d.sub(k, i);
    let fiki = d.apply(ff, &[i, ki]);
    d.lam_fv(i_fv, nat, fiki)
}

/// `fun k => sumRange (diag_inner F k) (succ k)` — one antidiagonal's sum.
fn t_fn(d: &mut NatDev<'_>, ff: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let inner = diag_inner(d, ff, k);
    let sk = d.succ(k);
    let sr = d.sum_range(inner, sk);
    d.lam_fv(k_fv, nat, sr)
}

/// The triangle sum by ANTIDIAGONAL: `sumRange (t_fn F) n`.
pub(super) fn triangle_sum(d: &mut NatDev<'_>, ff: ExprId, n: ExprId) -> ExprId {
    let t = t_fn(d, ff);
    d.sum_range(t, n)
}

/// The triangle sum by ROW: `sumRange (row_fn F n) n`.
pub(super) fn row_sum(d: &mut NatDev<'_>, ff: ExprId, n: ExprId) -> ExprId {
    let r = row_fn(d, ff, n);
    d.sum_range(r, n)
}

/// `fun i => add (apply f i) (apply g i)` — matches `sumRange_add`'s own
/// internal combined function shape exactly, so a `sumRange_add` instance's
/// inferred type lines up (up to the kernel's defeq check) with a sum built
/// against THIS function.
pub(super) fn combined_fn(d: &mut NatDev<'_>, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let body = d.add(fi, gi);
    d.lam_fv(i_fv, nat, body)
}

// ---------------------------------------------------------------------------
// Successor-case pieces.
// ---------------------------------------------------------------------------

/// `∀ i, Lt i n → Eq (row_fn F (succ n) applied i) (add (row_fn F n applied i) (diag_inner F n applied i))`.
///
/// For `i < n` (hence `i ≤ n`), `succ_sub_of_le` gives `sub (succ n) i = succ
/// (sub n i)`, and `sum_range_succ` then peels the grown row's new last term.
fn diagonal_pointwise(d: &mut NatDev<'_>, p: &NatPrelude, ff: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let sn = d.succ(n);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp_ty = d.lt(i, n);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    // Le i n, from Lt i n (definitionally Le (succ i) n) via le_succ + le_trans.
    let si = d.succ(i);
    let le_succ_i = d.lemma(p.le_succ, &[i]);
    let le_i_n = d.lemma(p.le_trans, &[i, si, n, le_succ_i, hi]);

    // sub (succ n) i = succ (sub n i)
    let h_sub = d.lemma(p.succ_sub_of_le, &[n, i, le_i_n]);
    let sub_n_i = d.sub(n, i);
    let succ_sub_n_i = d.succ(sub_n_i);
    let sub_sn_i = d.sub(sn, i);

    let row_inner_i = row_inner(d, ff, i);
    let h_sub_lift = d.congr(sub_sn_i, succ_sub_n_i, h_sub, &|d, x| {
        d.sum_range(row_inner_i, x)
    });
    let next1 = d.sum_range(row_inner_i, succ_sub_n_i);

    // sumRange(row_inner_i, succ (sub n i)) = sumRange(row_inner_i, sub n i) + row_inner_i(sub n i)
    let h_succ = d.lemma(p.sum_range_succ, &[row_inner_i, sub_n_i]);
    let sum_row_inner_i_subni = d.sum_range(row_inner_i, sub_n_i);
    let row_inner_i_subni = d.apply(row_inner_i, &[sub_n_i]);
    let target_sum = d.add(sum_row_inner_i_subni, row_inner_i_subni);

    let start = d.sum_range(row_inner_i, sub_sn_i);
    let (_e, body_eq) = d.chain(start, &[(next1, h_sub_lift), (target_sum, h_succ)]);

    let with_hi = d.lam_fv(hi_fv, hyp_ty, body_eq);
    d.lam_fv(i_fv, nat, with_hi)
}

/// `Eq (row_fn F (succ n) applied n) (F n zero)` — the row-major side's new
/// `i = n` boundary term collapses to `F n 0`, via `succ_sub_of_le` (at
/// `i = m = n`) and `sub_self`, then `sumRange_succ` + `sumRange_zero` +
/// `zero_add` to unwind the resulting length-`1` sum.
fn boundary_peel(d: &mut NatDev<'_>, p: &NatPrelude, ff: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let sn = d.succ(n);
    let row_inner_n = row_inner(d, ff, n);

    let le_refl_n = d.const_app(p.le_refl, &[n]);
    let h_b1 = d.lemma(p.succ_sub_of_le, &[n, n, le_refl_n]);
    let sub_sn_n = d.sub(sn, n);
    let sub_nn = d.sub(n, n);
    let succ_sub_nn = d.succ(sub_nn);

    let h_b2 = d.lemma(p.sub_self, &[n]);
    let zero = d.zero();
    let h_b2_lift = d.congr(sub_nn, zero, h_b2, &|d, x| d.succ(x));
    let succ_zero = d.succ(zero);

    let (_e1, h_sub_chain) = d.chain(sub_sn_n, &[(succ_sub_nn, h_b1), (succ_zero, h_b2_lift)]);

    let h_lift = d.congr(sub_sn_n, succ_zero, h_sub_chain, &|d, x| {
        d.sum_range(row_inner_n, x)
    });
    let start = d.sum_range(row_inner_n, sub_sn_n);
    let next1 = d.sum_range(row_inner_n, succ_zero);

    let h_b3 = d.lemma(p.sum_range_succ, &[row_inner_n, zero]);
    let sum_row_inner_n_zero = d.sum_range(row_inner_n, zero);
    let row_inner_n_zero = d.apply(row_inner_n, &[zero]);
    let next2 = d.add(sum_row_inner_n_zero, row_inner_n_zero);

    let h_zero_sum = d.lemma(p.sum_range_zero, &[row_inner_n]);
    let h_zero_lift = d.congr(sum_row_inner_n_zero, zero, h_zero_sum, &|d, x| {
        d.add(x, row_inner_n_zero)
    });
    let next3 = d.add(zero, row_inner_n_zero);

    let h_za = d.lemma(p.zero_add, &[row_inner_n_zero]);

    let (_e2, proof) = d.chain(
        start,
        &[
            (next1, h_lift),
            (next2, h_b3),
            (next3, h_zero_lift),
            (row_inner_n_zero, h_za),
        ],
    );
    proof
}

/// The successor step: given `ih : T(n) = R(n)`, prove `T(succ n) = R(succ n)`.
fn diagonal_step(d: &mut NatDev<'_>, p: &NatPrelude, ff: ExprId, n: ExprId, ih: ExprId) -> ExprId {
    let p = *p;
    let sn = d.succ(n);
    let zero = d.zero();

    // ---- shared pieces ----
    let t_fn_ff = t_fn(d, ff);
    let t_n = d.sum_range(t_fn_ff, n);
    let t_sn = d.sum_range(t_fn_ff, sn);

    let row_fn_n = row_fn(d, ff, n);
    let r_n = d.sum_range(row_fn_n, n);

    let row_fn_sn = row_fn(d, ff, sn);
    let r_sn = d.sum_range(row_fn_sn, sn);

    let dinner_n = diag_inner(d, ff, n);
    let s_term = d.sum_range(dinner_n, n);

    let f_n_zero = d.apply(ff, &[n, zero]);

    // ================= LHS: T(succ n) = r_n + (s_term + f_n_zero) =================
    let h_l1 = d.lemma(p.sum_range_succ, &[t_fn_ff, n]);
    let t_fn_ff_n = d.apply(t_fn_ff, &[n]);
    let l_mid1 = d.add(t_n, t_fn_ff_n);

    let h_l2 = d.lemma(p.sum_range_succ, &[dinner_n, n]);
    let dinner_n_n = d.apply(dinner_n, &[n]);
    let s_plus_dinner_n_n = d.add(s_term, dinner_n_n);
    let h_l2_lift = d.congr(t_fn_ff_n, s_plus_dinner_n_n, h_l2, &|d, x| d.add(t_n, x));
    let l_mid2 = d.add(t_n, s_plus_dinner_n_n);

    let sub_nn = d.sub(n, n);
    let h_sub_self = d.lemma(p.sub_self, &[n]);
    let h_l3 = d.congr(sub_nn, zero, h_sub_self, &|d, x| d.apply(ff, &[n, x]));
    let h_l3_lift = d.congr(dinner_n_n, f_n_zero, h_l3, &|d, x| d.add(s_term, x));
    let s_plus_fn0 = d.add(s_term, f_n_zero);
    let h_l3_final = d.congr(s_plus_dinner_n_n, s_plus_fn0, h_l3_lift, &|d, x| {
        d.add(t_n, x)
    });
    let l_mid3 = d.add(t_n, s_plus_fn0);

    let r_plus_s_fn0 = d.add(r_n, s_plus_fn0);
    let h_ih_lift = d.congr(t_n, r_n, ih, &|d, x| d.add(x, s_plus_fn0));

    let (_e_l, lhs_proof) = d.chain(
        t_sn,
        &[
            (l_mid1, h_l1),
            (l_mid2, h_l2_lift),
            (l_mid3, h_l3_final),
            (r_plus_s_fn0, h_ih_lift),
        ],
    );
    // lhs_proof : Eq(t_sn, r_plus_s_fn0)

    // ================= RHS: R(succ n) = (r_n + s_term) + f_n_zero =================
    let h_r1 = d.lemma(p.sum_range_succ, &[row_fn_sn, n]);
    let sum_row_sn_n = d.sum_range(row_fn_sn, n);
    let row_fn_sn_n = d.apply(row_fn_sn, &[n]);
    let r_mid1 = d.add(sum_row_sn_n, row_fn_sn_n);

    let combined_g = combined_fn(d, row_fn_n, dinner_n);
    let pointwise = diagonal_pointwise(d, &p, ff, n);
    let h_r2 = d.lemma(p.sum_range_congr_lt, &[row_fn_sn, combined_g, n, pointwise]);
    let sum_combined_n = d.sum_range(combined_g, n);

    let h_r3 = d.lemma(p.sum_range_add, &[row_fn_n, dinner_n, n]);
    let r_plus_s = d.add(r_n, s_term);

    let (_e_r0, h_r_sum) = d.chain(sum_row_sn_n, &[(sum_combined_n, h_r2), (r_plus_s, h_r3)]);
    let h_r1_lift = d.congr(sum_row_sn_n, r_plus_s, h_r_sum, &|d, x| {
        d.add(x, row_fn_sn_n)
    });
    let r_mid2 = d.add(r_plus_s, row_fn_sn_n);

    let h_bnd = boundary_peel(d, &p, ff, n);
    let h_bnd_lift = d.congr(row_fn_sn_n, f_n_zero, h_bnd, &|d, x| d.add(r_plus_s, x));
    let r_mid3 = d.add(r_plus_s, f_n_zero);

    let (_e_r, rhs_proof) = d.chain(
        r_sn,
        &[(r_mid1, h_r1), (r_mid2, h_r1_lift), (r_mid3, h_bnd_lift)],
    );
    // rhs_proof : Eq(r_sn, r_mid3)

    // ================= assemble via add_assoc =================
    // add_assoc r_n s_term f_n_zero : Eq(add(add(r_n,s_term),f_n_zero), add(r_n,add(s_term,f_n_zero)))
    //                                = Eq(r_mid3, r_plus_s_fn0)
    let h_assoc = d.lemma(p.add_assoc, &[r_n, s_term, f_n_zero]);

    let r_sn_eq_r_plus_s_fn0 = d.trans(r_sn, r_mid3, r_plus_s_fn0, rhs_proof, h_assoc);
    let r_plus_s_fn0_eq_r_sn = d.symm(r_sn, r_plus_s_fn0, r_sn_eq_r_plus_s_fn0);

    d.trans(t_sn, r_plus_s_fn0, r_sn, lhs_proof, r_plus_s_fn0_eq_r_sn)
}

/// `sumRange_diagonal : ∀ F n,
///   sumRange (fun k => sumRange (fun i => F i (sub k i)) (succ k)) n
///     = sumRange (fun i => sumRange (fun j => F i j) (sub n i)) n`.
pub(super) fn declare_sum_range_diagonal(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn2_ty = {
        let inner = d.arrow(nat, nat);
        d.arrow(nat, inner)
    };
    let f_fv = d.fresh_fvar();
    let ff = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let lhs = triangle_sum(d, ff, x);
        let rhs = row_sum(d, ff, x);
        d.eq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            d.refl(zero)
        },
        &|d, j, ih| diagonal_step(d, &p, ff, j, ih),
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn2_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn2_ty, over_n)
    };
    d.declare_theorem(p.sum_range_diagonal, ty, value)
}

/// Declare this module's two results in order: the round-trip lemma the
/// headline theorem's neighbourhood wants (`add_sub_cancel_of_le`), then the
/// headline itself (`sum_range_diagonal`).
pub(super) fn declare_diagonal(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_add_sub_cancel_of_le(d, p)?;
    declare_sum_range_diagonal(d, p)?;
    Ok(())
}
