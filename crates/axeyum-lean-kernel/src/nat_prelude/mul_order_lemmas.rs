//! `Nat` ordering under multiplication and division -- five `ml430` mirrors:
//! `Nat.mul_lt_mul_left`, `Nat.mul_lt_mul_right`, `Nat.lt_of_mul_lt_mul_left`,
//! `Nat.lt_of_mul_lt_mul_right`, `Nat.div_lt_of_lt_mul`.
//!
//! **The two `lt_of_mul_lt_mul_*` cancellation lemmas need NO positivity
//! hypothesis**, unlike the `mul_lt_mul_*` `Iff`s. `a*b < a*c -> b < c` holds
//! even at `a = 0` (the hypothesis is then vacuous, since `0*b = 0*c = 0` can
//! never be `<` itself), so requiring `0 < a` would only be a WEAKER, still
//! true, statement -- exactly the failure mode this family's Mathlib source
//! guards against getting backwards. Both are proved by contradiction via
//! `Nat.lt_or_ge` (`p.lt_or_ge`): split `Or (Lt b c) (Le c b)` and refute the
//! second branch by chaining the (weak) monotone `mul_le_mul_left`/an
//! `mul_le_mul_right` core back through the strict hypothesis into
//! `Lt x x`, discharged by `lt_irrefl` -- no `Nat.rec` case split anywhere in
//! this file.
//!
//! `Nat.div_lt_of_lt_mul` is the one genuine case split (on the divisor `n`,
//! via [`cases_zero_succ`]): at `n = 0` the hypothesis `m < 0*k` is
//! immediately absurd via `zero_mul`/`not_lt_zero`; at `n = succ n'` this is
//! exactly the already-proved `Nat.div_mod_lt_mul_iff`'s forward direction,
//! fed the canonical `divMod` witness from `Nat.div_mod_exec`.
//!
//! `Nat.mul_le_mul_left : forall c a b, Le a b -> Le (c*a) (c*b)` exists; a
//! symmetric `mul_le_mul_right` does not, so this file builds one privately
//! (via `mul_comm`, not a new recursion) rather than adding a sixth public
//! name nothing else asked for.

use super::NatPrelude;
use super::finite::ex_falso;
use super::helpers::iff_forward;
use super::ops::{NatDev, NatOps, cases_zero_succ};
use crate::KernelError;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// Shared algebraic cores
// ---------------------------------------------------------------------------

/// `h : Le x y  ⊢  Le (mul x mult) (mul y mult)` -- the right-multiplication
/// monotonicity `Nat.mul_le_mul_left` doesn't state directly, built from it
/// plus `mul_comm` on both sides (two `transport`s, no new recursion).
fn mul_le_mul_right_core(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    mult: ExprId,
    x: ExprId,
    y: ExprId,
    h: ExprId,
) -> ExprId {
    let mx = d.mul(mult, x);
    let my = d.mul(mult, y);
    let raw = d.lemma(p.mul_le_mul_left, &[mult, x, y, h]); // Le mx my
    let xm = d.mul(x, mult);
    let ym = d.mul(y, mult);
    let comm_x = d.lemma(p.mul_comm, &[mult, x]); // Eq mx xm
    let comm_y = d.lemma(p.mul_comm, &[mult, y]); // Eq my ym
    let motive1 = d.eq_motive(mx, &|d, t| d.le(t, my));
    let step1 = d.transport(mx, motive1, raw, xm, comm_x); // Le xm my
    let motive2 = d.eq_motive(my, &|d, t| d.le(xm, t));
    d.transport(my, motive2, step1, ym, comm_y) // Le xm ym
}

/// `pos : Lt zero a`, `hlt : Lt b c  ⊢  Lt (mul a b) (mul a c)`.
///
/// `mul_le_mul_left` at `succ b` gives `Le (mul a (succ b)) (mul a c)`; since
/// `mul a (succ b)` is `add (mul a b) a` BY REFL (`mul_succ`), and
/// `succ (mul a b)` is `add (mul a b) one` BY REFL (`add_succ`+`add_zero`),
/// `add_le_add_left (mul a b) one a pos` bridges the two ends via `le_trans`
/// with no explicit rewrite -- the kernel's own `def_eq` does it at the final
/// check.
fn mul_lt_mul_pos_left_core(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    pos: ExprId,
    hlt: ExprId,
) -> ExprId {
    let succ_b = d.succ(b);
    let ac = d.mul(a, c);
    let raw = d.lemma(p.mul_le_mul_left, &[a, succ_b, c, hlt]); // Le (mul a succ_b) ac
    let mul_a_b = d.mul(a, b);
    let one = d.num(1);
    let step = d.lemma(p.add_le_add_left, &[mul_a_b, one, a, pos]); // Le (add mul_a_b one) (add mul_a_b a)
    let mul_a_succ_b = d.mul(a, succ_b); // =defeq= add mul_a_b a
    let succ_mul_a_b = d.succ(mul_a_b); // =defeq= add mul_a_b one
    d.lemma(p.le_trans, &[succ_mul_a_b, mul_a_succ_b, ac, step, raw])
    // : Le succ_mul_a_b ac == Lt mul_a_b ac == Lt (mul a b) (mul a c)
}

/// `pos : Lt zero a`, `hlt : Lt b c  ⊢  Lt (mul b a) (mul c a)` -- the mirror
/// of [`mul_lt_mul_pos_left_core`] using `mul_le_mul_right_core` in place of
/// `mul_le_mul_left`.
///
/// UNLIKE the left core, `mul (succ b) a = add (mul b a) a` is **not** a
/// refl-provable defining equation here -- `mul_succ` (`mul n (succ m) = add
/// (mul n m) n`) is, because `Nat.mul` recurses on its RIGHT argument, but
/// `succ_mul` (the left-successor form this core needs) is a real theorem
/// under "multiplicative theorems", proved by induction, not by
/// `Eq.refl`. So the bridge from `mul (succ b) a` to `add (mul b a) a` needs
/// an explicit `transport` along `succ_mul`, not a free defeq.
fn mul_lt_mul_pos_right_core(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    pos: ExprId,
    hlt: ExprId,
) -> ExprId {
    let succ_b = d.succ(b);
    let ca = d.mul(c, a);
    let mul_succ_b_a = d.mul(succ_b, a);
    let raw = mul_le_mul_right_core(d, p, a, succ_b, c, hlt); // Le mul_succ_b_a ca
    let mul_b_a = d.mul(b, a);
    let one = d.num(1);
    let step = d.lemma(p.add_le_add_left, &[mul_b_a, one, a, pos]); // Le (add mul_b_a one) (add mul_b_a a)
    let succ_mul_b_a = d.succ(mul_b_a); // =defeq= add mul_b_a one (add_succ+add_zero, BY REFL)

    let succ_mul_eq = d.lemma(p.succ_mul, &[b, a]); // Eq mul_succ_b_a (add mul_b_a a)
    let add_mul_b_a_a = d.add(mul_b_a, a);
    let motive = d.eq_motive(mul_succ_b_a, &|d, t| d.le(t, ca));
    let raw_rewritten = d.transport(mul_succ_b_a, motive, raw, add_mul_b_a_a, succ_mul_eq);
    // : Le add_mul_b_a_a ca

    d.lemma(
        p.le_trans,
        &[succ_mul_b_a, add_mul_b_a_a, ca, step, raw_rewritten],
    )
    // : Le succ_mul_b_a ca == Lt mul_b_a ca == Lt (mul b a) (mul c a)
}

// ---------------------------------------------------------------------------
// Declarations
// ---------------------------------------------------------------------------

/// `Nat.lt_of_mul_lt_mul_left : forall a b c, Lt (mul a b) (mul a c) -> Lt b c`
/// and `Nat.lt_of_mul_lt_mul_right : forall a b c, Lt (mul b a) (mul c a) ->
/// Lt b c` -- NO positivity hypothesis. Proved by contradiction: split
/// `lt_or_ge b c`; the `Lt b c` branch is the goal directly, and the
/// `Le c b` branch gives `Le (mul a c) (mul a b)` (resp. right), which chains
/// against the strict hypothesis via `le_trans` into `Lt x x`, refuted by
/// `lt_irrefl`.
pub(super) fn declare_lt_of_mul_lt_mul(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.lt_of_mul_lt_mul_left, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let ab = d.mul(a, b);
        let ac = d.mul(a, c);
        let hyp = d.lt(ab, ac);
        let concl = d.lt(b, c);
        let stmt = d.arrow(hyp, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let le_c_b = d.le(c, b);
        let tri = d.lemma(p.lt_or_ge, &[b, c]); // Or (Lt b c) (Le c b)
        let minor1 = {
            let hp_fv = d.fresh_fvar();
            let hp = d.kernel().fvar(hp_fv);
            d.lam_fv(hp_fv, concl, hp)
        };
        let minor2 = {
            let hq_fv = d.fresh_fvar();
            let hq = d.kernel().fvar(hq_fv);
            let mul_le = d.lemma(p.mul_le_mul_left, &[a, c, b, hq]); // Le ac ab
            let succ_ab = d.succ(ab);
            let combined = d.lemma(p.le_trans, &[succ_ab, ac, ab, h, mul_le]); // Le succ_ab ab == Lt ab ab
            let lt_irrefl_ab = d.lemma(p.lt_irrefl, &[ab]);
            let false_val = d.apply(lt_irrefl_ab, &[combined]);
            let absurd = ex_falso(d, &p, concl, false_val);
            d.lam_fv(hq_fv, le_c_b, absurd)
        };
        let elim = d.const_app(
            p.logic.or_elim,
            &[concl, le_c_b, concl, tri, minor1, minor2],
        );
        let proof = d.lam_fv(h_fv, hyp, elim);
        (stmt, proof)
    })?;

    d.theorem(p.lt_of_mul_lt_mul_right, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let ba = d.mul(b, a);
        let ca = d.mul(c, a);
        let hyp = d.lt(ba, ca);
        let concl = d.lt(b, c);
        let stmt = d.arrow(hyp, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let le_c_b = d.le(c, b);
        let tri = d.lemma(p.lt_or_ge, &[b, c]); // Or (Lt b c) (Le c b)
        let minor1 = {
            let hp_fv = d.fresh_fvar();
            let hp = d.kernel().fvar(hp_fv);
            d.lam_fv(hp_fv, concl, hp)
        };
        let minor2 = {
            let hq_fv = d.fresh_fvar();
            let hq = d.kernel().fvar(hq_fv);
            let mul_le = mul_le_mul_right_core(d, &p, a, c, b, hq); // Le ca ba
            let succ_ba = d.succ(ba);
            let combined = d.lemma(p.le_trans, &[succ_ba, ca, ba, h, mul_le]); // Le succ_ba ba == Lt ba ba
            let lt_irrefl_ba = d.lemma(p.lt_irrefl, &[ba]);
            let false_val = d.apply(lt_irrefl_ba, &[combined]);
            let absurd = ex_falso(d, &p, concl, false_val);
            d.lam_fv(hq_fv, le_c_b, absurd)
        };
        let elim = d.const_app(
            p.logic.or_elim,
            &[concl, le_c_b, concl, tri, minor1, minor2],
        );
        let proof = d.lam_fv(h_fv, hyp, elim);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Nat.mul_lt_mul_left : forall a b c, Lt zero a -> Iff (Lt (mul a b) (mul a
/// c)) (Lt b c)` and `Nat.mul_lt_mul_right : forall a b c, Lt zero a -> Iff
/// (Lt (mul b a) (mul c a)) (Lt b c)`. `mp` in each is
/// [`declare_lt_of_mul_lt_mul`]'s (positivity-free) cancellation lemma; `mpr`
/// is the matching positive-monotone core above.
pub(super) fn declare_mul_lt_mul_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let zero = d.zero();

    d.theorem(p.mul_lt_mul_left, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let pos_ty = d.lt(zero, a);
        let ab = d.mul(a, b);
        let ac = d.mul(a, c);
        let left_ty = d.lt(ab, ac);
        let right_ty = d.lt(b, c);
        let concl = d.const_app(p.logic.iff, &[left_ty, right_ty]);
        let stmt = d.arrow(pos_ty, concl);

        let pos_fv = d.fresh_fvar();
        let pos = d.kernel().fvar(pos_fv);
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = mul_lt_mul_pos_left_core(d, &p, a, b, c, pos, h);
            d.lam_fv(h_fv, right_ty, body)
        };
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = d.lemma(p.lt_of_mul_lt_mul_left, &[a, b, c, h]);
            d.lam_fv(h_fv, left_ty, body)
        };
        let proof_iff = d.const_app(p.logic.iff_intro, &[left_ty, right_ty, mp, mpr]);
        let proof = d.lam_fv(pos_fv, pos_ty, proof_iff);
        (stmt, proof)
    })?;

    d.theorem(p.mul_lt_mul_right, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let pos_ty = d.lt(zero, a);
        let ba = d.mul(b, a);
        let ca = d.mul(c, a);
        let left_ty = d.lt(ba, ca);
        let right_ty = d.lt(b, c);
        let concl = d.const_app(p.logic.iff, &[left_ty, right_ty]);
        let stmt = d.arrow(pos_ty, concl);

        let pos_fv = d.fresh_fvar();
        let pos = d.kernel().fvar(pos_fv);
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = mul_lt_mul_pos_right_core(d, &p, a, b, c, pos, h);
            d.lam_fv(h_fv, right_ty, body)
        };
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = d.lemma(p.lt_of_mul_lt_mul_right, &[a, b, c, h]);
            d.lam_fv(h_fv, left_ty, body)
        };
        let proof_iff = d.const_app(p.logic.iff_intro, &[left_ty, right_ty, mp, mpr]);
        let proof = d.lam_fv(pos_fv, pos_ty, proof_iff);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Nat.div_lt_of_lt_mul : forall m n k, Lt m (mul n k) -> Lt (div m n) k`.
///
/// Case split on `n` ([`cases_zero_succ`], not induction):
/// - `n = zero`: the hypothesis becomes `Lt m (mul zero k)`, which is
///   `Lt m zero` after rewriting `mul zero k` to `zero` (`zero_mul`) --
///   immediately absurd via `not_lt_zero`, so the (unreachable) conclusion
///   `Lt (div m zero) k` follows by `ex_falso`.
/// - `n = succ n'`: exactly `Nat.div_mod_lt_mul_iff`'s forward direction, fed
///   the canonical witness `Nat.div_mod_exec n' m : divMod (succ n') m (div m
///   (succ n')) (mod m (succ n'))`.
pub(super) fn declare_div_lt_of_lt_mul(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.div_lt_of_lt_mul, 3, &|d, v| {
        let (m, n, k) = (v[0], v[1], v[2]);
        let nk = d.mul(n, k);
        let hyp_ty = d.lt(m, nk);
        let div_mk = d.div(m, n);
        let concl = d.lt(div_mk, k);
        let stmt = d.arrow(hyp_ty, concl);

        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let nk_inner = d.mul(x, k);
            let hyp_inner = d.lt(m, nk_inner);
            let div_inner = d.div(m, x);
            let concl_inner = d.lt(div_inner, k);
            d.arrow(hyp_inner, concl_inner)
        };

        let proof = cases_zero_succ(
            d,
            n,
            &motive,
            &|d| {
                let zero = d.zero();
                let mul_zero_k = d.mul(zero, k);
                let hyp_z = d.lt(m, mul_zero_k);
                let hz_fv = d.fresh_fvar();
                let hz = d.kernel().fvar(hz_fv);

                let eqz = d.lemma(p.zero_mul, &[k]); // Eq mul_zero_k zero
                let motive_z = d.eq_motive(mul_zero_k, &|d, t| d.lt(m, t));
                let hz_at_zero = d.transport(mul_zero_k, motive_z, hz, zero, eqz); // Lt m zero

                let not_lt_zero_m = d.lemma(p.not_lt_zero, &[m]); // arrow(Lt m zero, False)
                let false_val = d.apply(not_lt_zero_m, &[hz_at_zero]);

                let div_m_zero = d.div(m, zero);
                let target_z = d.lt(div_m_zero, k);
                let absurd = ex_falso(d, &p, target_z, false_val);
                d.lam_fv(hz_fv, hyp_z, absurd)
            },
            &|d, np| {
                let succ_np = d.succ(np);
                let mul_s_k = d.mul(succ_np, k);
                let hyp_s = d.lt(m, mul_s_k);
                let hs_fv = d.fresh_fvar();
                let hs = d.kernel().fvar(hs_fv);

                let div_m_s = d.div(m, succ_np);
                let mod_m_s = d.modulo(m, succ_np);
                let h_exec = d.lemma(p.div_mod_exec, &[np, m]); // divMod succ_np m div_m_s mod_m_s
                let iff_fn = d.lemma(p.div_mod_lt_mul_iff, &[succ_np, m, div_m_s, mod_m_s, k]);
                let the_iff = d.apply(iff_fn, &[h_exec]); // Iff (Lt m (mul succ_np k)) (Lt div_m_s k)

                let target_s = d.lt(div_m_s, k);
                let forward = iff_forward(d, hyp_s, target_s, the_iff);
                let result = d.apply(forward, &[hs]);
                d.lam_fv(hs_fv, hyp_s, result)
            },
        );
        (stmt, proof)
    })?;
    Ok(())
}
