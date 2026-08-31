//! `Nat.Even`/`Nat.Odd`: an existential parity predicate family, plus the
//! basic bridges between it and [`super::powsq::declare_even_or_odd`]'s
//! already-proved computed-half split.
//!
//! ## Why `k + k` (and `succ (k + k)`), not `2 * k` (and `2 * k + 1`)
//!
//! `Nat.even_or_odd` (`powsq.rs`) already proves, for every `n`:
//!
//! ```text
//! Or (Eq n (add (div n 2) (div n 2))) (Eq n (succ (add (div n 2) (div n 2))))
//! ```
//!
//! — i.e. its own even/odd split is stated in exactly the `half + half` /
//! `succ (half + half)` shape, with `half := div n 2` substituted directly
//! in place of a bound witness. Defining `Even`/`Odd` with `add k k` and
//! `succ (add k k)` means [`declare_even_or_odd_exists`] can hand that
//! proof's two branch equations straight to `Exists.intro` at witness
//! `div n 2` with no conversion step at all. Defining them with `mul 2 k`
//! instead would need an extra rewrite by the `2 * k = k + k` identity
//! (`two_mul_eq_add_self`, `powsq.rs`, module-private) at every use site —
//! pure overhead bought for no benefit, since nothing downstream of this
//! module needs the `mul`-shaped shape.
//!
//! `Nat.add` recursing on its RIGHT argument is not actually the deciding
//! factor here (see the CLAUDE.md gotcha on operand order): every proof in
//! this module works with `k`/`j` as genuinely free variables throughout —
//! `add k k` is never asked to *reduce*, only to be related to other terms
//! by explicit congruence/`succ_add`/`add_succ` rewrites — so the choice
//! that matters is which shape the reusable upstream proof already produces,
//! not which shape happens to compute.
//!
//! ## Scope
//!
//! [`declare_even_or_odd_exists`] delivers item 3 of the brief directly from
//! item 2 (`Even`/`Odd` themselves) plus `even_or_odd`, with no new case
//! analysis. [`declare_even_iff_odd_succ`] is similarly cheap: both
//! directions are a single `congrArg succ` / `succ_injective` on the
//! existential witness. [`declare_even_not_odd`]/[`declare_odd_not_even`]
//! need real work — an existential witness for `Even n` and one for `Odd n`
//! give **different, unrelated** witnesses `k, j` with `n = k+k = succ(j+j)`,
//! and showing that is impossible needs the `parity_ne` induction below, not
//! just unfolding definitions.
//!
//! Predicate-construction helpers (`even_predicate`/`odd_predicate`) are kept
//! module-private rather than added to `ops.rs`'s shared `NatOps` trait
//! (unlike `dvd`/`dvd_predicate`, which several files consume): nothing
//! outside this module needs them yet, and `ops.rs` is a widely-shared file
//! other lanes edit concurrently.

use super::NatPrelude;
use super::helpers::and_left;
use super::helpers::and_right;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `fun k : Nat => Eq n (add k k)` — the witness predicate defining
/// [`NatPrelude::even`].
pub(super) fn even_predicate(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let kk = d.add(k, k);
    let body = d.eq(n, kk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `fun k : Nat => Eq n (succ (add k k))` — the witness predicate defining
/// [`NatPrelude::odd`].
pub(super) fn odd_predicate(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let kk = d.add(k, k);
    let skk = d.succ(kk);
    let body = d.eq(n, skk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `Nat.Even`, `Nat.Odd` — see the module doc for the `k+k`/`succ(k+k)`
/// choice.
fn declare_even_odd_defs(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let one = d.level_one();

    // Even n := Exists Nat (fun k => Eq n (add k k))
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let pred = even_predicate(d, n);
        let exists_ = d.kernel().const_(p.logic.exists_, vec![one]);
        let body = d.apply(exists_, &[nat, pred]);
        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, prop);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.even,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // Odd n := Exists Nat (fun k => Eq n (succ (add k k)))
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let pred = odd_predicate(d, n);
        let exists_ = d.kernel().const_(p.logic.exists_, vec![one]);
        let body = d.apply(exists_, &[nat, pred]);
        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, prop);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.odd,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }
    Ok(())
}

/// `Nat.even_or_odd_exists : ∀ n, Or (Even n) (Odd n)` — `even_or_odd`
/// restated existentially. Each branch of `even_or_odd`'s `Or` is handed
/// straight to `Exists.intro` at witness `div n 2`: the branch equation IS
/// the exact hypothesis `Exists.intro` needs, with no rewriting.
fn declare_even_or_odd_exists(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();

    d.theorem(p.even_or_odd_exists, 1, &|d, values| {
        let n = values[0];
        let two = d.num(2);
        let half = d.div(n, two);
        let half_half = d.add(half, half);
        let succ_half_half = d.succ(half_half);

        let h = d.lemma(p.even_or_odd, &[n]);

        let even_ty = d.lemma(p.even, &[n]);
        let odd_ty = d.lemma(p.odd, &[n]);
        let target = d.const_app(p.logic.or, &[even_ty, odd_ty]);

        let even_disjunct = d.eq(n, half_half);
        let odd_disjunct = d.eq(n, succ_half_half);

        let even_minor = {
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let even_pred = even_predicate(d, n);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            let ev_proof = d.apply(intro, &[nat, even_pred, half, heq]);
            let or_proof = d.const_app(p.logic.or_inl, &[even_ty, odd_ty, ev_proof]);
            d.lam_fv(heq_fv, even_disjunct, or_proof)
        };
        let odd_minor = {
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let odd_pred = odd_predicate(d, n);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            let od_proof = d.apply(intro, &[nat, odd_pred, half, heq]);
            let or_proof = d.const_app(p.logic.or_inr, &[even_ty, odd_ty, od_proof]);
            d.lam_fv(heq_fv, odd_disjunct, or_proof)
        };

        let motive = {
            let or_ty = d.const_app(p.logic.or, &[even_disjunct, odd_disjunct]);
            d.kernel().lam(anon, or_ty, target, BinderInfo::Default)
        };
        let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
        let proof = d.apply(
            or_rec,
            &[
                even_disjunct,
                odd_disjunct,
                motive,
                even_minor,
                odd_minor,
                h,
            ],
        );
        (target, proof)
    })?;
    Ok(())
}

/// `Eq (add (succ m) (succ m)) (succ (succ (add m m)))` — peel one `succ`
/// off each side of a doubled successor via `add_succ` then `succ_add`.
pub(super) fn succ_double_eq(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> ExprId {
    let p = *p;
    let succ_m = d.succ(m);
    let lhs = d.add(succ_m, succ_m);
    let inner = d.add(succ_m, m);
    let succ_inner = d.succ(inner);
    let add_succ_eq = d.lemma(p.add_succ, &[succ_m, m]);

    let mm = d.add(m, m);
    let succ_mm = d.succ(mm);
    let succ_add_eq = d.lemma(p.succ_add, &[m, m]);
    let congr_succ = d.congr(inner, succ_mm, succ_add_eq, &|d, x| d.succ(x));
    let succ_succ_mm = d.succ(succ_mm);

    let (_, result) = d.chain(
        lhs,
        &[(succ_inner, add_succ_eq), (succ_succ_mm, congr_succ)],
    );
    result
}

/// `Nat.add_self_ne_succ_add_self : ∀ k j, Not (Eq (add k k) (succ (add j
/// j)))` — no doubled number equals the successor of a doubled number.
/// Induction on `k` (the theorem's own first parameter); the successor case
/// needs `j`'s shape too, so it case-splits on a FRESH `j` (a second, nested
/// `d.induct`, ignoring its own induction hypothesis — a pure case split) to
/// reach a point where two rounds of `succ_injective` strip both sides down
/// to exactly the outer IH's statement at the inner predecessor. The nested
/// proof is built generically (fresh `j`, then `lam_fv`-wrapped), matching
/// `order.rs`'s `le_total`/`total_a`/`total_b` construction; the theorem's
/// own two parameters (`k`, `j`) are only plugged in via a final `d.apply`
/// at the very end, exactly as that construction does.
fn declare_add_self_ne_succ_add_self(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    d.theorem(p.add_self_ne_succ_add_self, 2, &|d, values| {
        let (k, j) = (values[0], values[1]);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);

        let target_for = move |d: &mut NatDev<'_>, kx: ExprId, jx: ExprId| -> ExprId {
            let kk = d.add(kx, kx);
            let jj = d.add(jx, jx);
            let succ_jj = d.succ(jj);
            let eq_ty = d.eq(kk, succ_jj);
            d.arrow(eq_ty, false_ty)
        };
        let motive = move |d: &mut NatDev<'_>, kx: ExprId| -> ExprId {
            let j_fv = d.fresh_fvar();
            let jv = d.kernel().fvar(j_fv);
            let body = target_for(d, kx, jv);
            d.pi_fv(j_fv, nat, body)
        };
        let base = move |d: &mut NatDev<'_>| -> ExprId {
            // k = 0: ∀ j, Not (Eq (add 0 0) (succ (add j j))).
            let zero = d.zero();
            let j_fv = d.fresh_fvar();
            let jv = d.kernel().fvar(j_fv);
            let kk = d.add(zero, zero);
            let jj = d.add(jv, jv);
            let succ_jj = d.succ(jj);
            let eq_ty = d.eq(kk, succ_jj);

            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let flipped = d.symm(kk, succ_jj, h);
            let sne = d.lemma(p.succ_ne_zero, &[jj]);
            let false_proof = d.apply(sne, &[flipped]);
            let inner = d.lam_fv(h_fv, eq_ty, false_proof);
            d.lam_fv(j_fv, nat, inner)
        };
        let step = move |d: &mut NatDev<'_>, m: ExprId, ih: ExprId| -> ExprId {
            // k = succ m, given ih : ∀ j, Not (Eq (add m m) (succ (add j j))).
            let succ_m = d.succ(m);
            let lhs = d.add(succ_m, succ_m);
            let mm = d.add(m, m);
            let succ_mm = d.succ(mm);
            let succ_succ_mm = d.succ(succ_mm);
            let lhs_eq = succ_double_eq(d, &p, m);

            let inner_target = move |d: &mut NatDev<'_>, jx: ExprId| -> ExprId {
                let jj = d.add(jx, jx);
                let succ_jj = d.succ(jj);
                let eq_ty = d.eq(lhs, succ_jj);
                d.arrow(eq_ty, false_ty)
            };
            let inner_base = move |d: &mut NatDev<'_>| -> ExprId {
                // j = 0: Not (Eq lhs (succ (add 0 0))).
                let zero = d.zero();
                let jj0 = d.add(zero, zero);
                let succ_jj0 = d.succ(jj0);
                let eq_ty = d.eq(lhs, succ_jj0);

                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let lhs_flip = d.symm(lhs, succ_succ_mm, lhs_eq);
                let combined = d.trans(succ_succ_mm, lhs, succ_jj0, lhs_flip, h);
                let stripped = d.lemma(p.succ_injective, &[succ_mm, zero, combined]);
                let sne = d.lemma(p.succ_ne_zero, &[mm]);
                let false_proof = d.apply(sne, &[stripped]);
                d.lam_fv(h_fv, eq_ty, false_proof)
            };
            let inner_step = move |d: &mut NatDev<'_>, pj: ExprId, _pj_ih: ExprId| -> ExprId {
                // j = succ pj: Not (Eq lhs (succ (add (succ pj) (succ pj)))).
                let succ_pj = d.succ(pj);
                let jj = d.add(succ_pj, succ_pj);
                let succ_jj = d.succ(jj);
                let eq_ty = d.eq(lhs, succ_jj);

                let pp = d.add(pj, pj);
                let succ_pp = d.succ(pp);
                let succ_succ_pp = d.succ(succ_pp);
                let succ_succ_succ_pp = d.succ(succ_succ_pp);
                let jj_eq = succ_double_eq(d, &p, pj);
                let succ_jj_eq = d.congr(jj, succ_succ_pp, jj_eq, &|d, x| d.succ(x));

                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let lhs_flip = d.symm(lhs, succ_succ_mm, lhs_eq);
                let step1 = d.trans(succ_succ_mm, lhs, succ_jj, lhs_flip, h);
                let combined = d.trans(succ_succ_mm, succ_jj, succ_succ_succ_pp, step1, succ_jj_eq);
                let stripped1 = d.lemma(p.succ_injective, &[succ_mm, succ_succ_pp, combined]);
                let stripped2 = d.lemma(p.succ_injective, &[mm, succ_pp, stripped1]);
                let ih_at_pj = d.apply(ih, &[pj]);
                let false_proof = d.apply(ih_at_pj, &[stripped2]);
                d.lam_fv(h_fv, eq_ty, false_proof)
            };

            let j_fv = d.fresh_fvar();
            let jv = d.kernel().fvar(j_fv);
            let nested = d.induct(&inner_target, &inner_base, &inner_step, jv);
            d.lam_fv(j_fv, nat, nested)
        };

        let all_j = d.induct(&motive, &base, &step, k);
        let proof = d.apply(all_j, &[j]);
        let stmt = target_for(d, k, j);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.even_not_odd : ∀ n, Even n → Not (Odd n)`. Both existentials are
/// eliminated with `Exists.rec` (`Prop`-valued, so this is legal even though
/// the witnesses are never returned as data) down to `Eq n (add k k)` and
/// `Eq n (succ (add j j))` for some `k, j`; `trans`/`symm` combine them into
/// `Eq (add k k) (succ (add j j))`, refuted by
/// [`declare_add_self_ne_succ_add_self`].
fn declare_even_not_odd(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();

    d.theorem(p.even_not_odd, 1, &|d, values| {
        let n = values[0];
        let even_ty = d.lemma(p.even, &[n]);
        let odd_ty = d.lemma(p.odd, &[n]);
        let not_odd_ty = d.const_app(p.logic.not, &[odd_ty]);
        let stmt = d.arrow(even_ty, not_odd_ty);

        let even_pred = even_predicate(d, n);
        let odd_pred = odd_predicate(d, n);

        let he_fv = d.fresh_fvar();
        let he = d.kernel().fvar(he_fv);
        let ho_fv = d.fresh_fvar();
        let ho = d.kernel().fvar(ho_fv);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);

        // Outer Exists.rec, eliminating `he : Even n` into `False`.
        let outer_minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let kk = d.add(k, k);
            let hk_ty = d.eq(n, kk);

            // Inner Exists.rec, eliminating `ho : Odd n` into `False`.
            let inner_minor = {
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let hj_fv = d.fresh_fvar();
                let hj = d.kernel().fvar(hj_fv);
                let kk = d.add(k, k);
                let jj = d.add(j, j);
                let succ_jj = d.succ(jj);
                let hj_ty = d.eq(n, succ_jj);

                let kk_eq_n = d.symm(n, kk, hk);
                let kk_eq_succ_jj = d.trans(kk, n, succ_jj, kk_eq_n, hj);
                let refuter = d.lemma(p.add_self_ne_succ_add_self, &[k, j]);
                let false_proof = d.apply(refuter, &[kk_eq_succ_jj]);
                let inner = d.lam_fv(hj_fv, hj_ty, false_proof);
                d.lam_fv(j_fv, nat, inner)
            };
            let inner_motive = d.kernel().lam(anon, odd_ty, false_ty, BinderInfo::Default);
            let inner_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let false_from_ho = d.apply(inner_rec, &[nat, odd_pred, inner_motive, inner_minor, ho]);
            let with_ho = d.lam_fv(ho_fv, odd_ty, false_from_ho);
            let inner = d.lam_fv(hk_fv, hk_ty, with_ho);
            d.lam_fv(k_fv, nat, inner)
        };
        let outer_motive = {
            let target = d.arrow(odd_ty, false_ty);
            d.kernel().lam(anon, even_ty, target, BinderInfo::Default)
        };
        let outer_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let not_odd_from_he = d.apply(outer_rec, &[nat, even_pred, outer_motive, outer_minor, he]);
        let proof = d.lam_fv(he_fv, even_ty, not_odd_from_he);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.odd_not_even : ∀ n, Odd n → Not (Even n)` — [`declare_even_not_odd`]
/// with its two hypotheses supplied in the opposite order; no new
/// construction.
fn declare_odd_not_even(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.odd_not_even, 1, &|d, values| {
        let n = values[0];
        let even_ty = d.lemma(p.even, &[n]);
        let odd_ty = d.lemma(p.odd, &[n]);
        let not_even_ty = d.const_app(p.logic.not, &[even_ty]);
        let stmt = d.arrow(odd_ty, not_even_ty);

        let ho_fv = d.fresh_fvar();
        let ho = d.kernel().fvar(ho_fv);
        let he_fv = d.fresh_fvar();
        let he = d.kernel().fvar(he_fv);
        let even_not_odd = d.lemma(p.even_not_odd, &[n]);
        let not_odd = d.apply(even_not_odd, &[he]);
        let false_proof = d.apply(not_odd, &[ho]);
        let inner = d.lam_fv(he_fv, even_ty, false_proof);
        let proof = d.lam_fv(ho_fv, odd_ty, inner);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.even_iff_odd_succ : ∀ n, Iff (Even n) (Odd (succ n))`. Both
/// directions are a direct `congrArg succ`/`succ_injective` on the
/// existential witness — `add_self_ne_succ_add_self` is not needed here.
fn declare_even_iff_odd_succ(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();

    d.theorem(p.even_iff_odd_succ, 1, &|d, values| {
        let n = values[0];
        let succ_n = d.succ(n);
        let even_n_ty = d.lemma(p.even, &[n]);
        let odd_succ_n_ty = d.lemma(p.odd, &[succ_n]);
        let stmt = d.const_app(p.logic.iff, &[even_n_ty, odd_succ_n_ty]);

        let even_n_pred = even_predicate(d, n);
        let odd_succ_n_pred = odd_predicate(d, succ_n);

        // mp : Even n -> Odd (succ n)
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let kk = d.add(k, k);
            let hk_ty = d.eq(n, kk);

            let succ_n_eq_succ_kk = d.congr(n, kk, hk, &|d, x| d.succ(x));
            let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            let ev_proof = d.apply(intro, &[nat, odd_succ_n_pred, k, succ_n_eq_succ_kk]);
            let minor = d.lam_fv(hk_fv, hk_ty, ev_proof);
            let minor = d.lam_fv(k_fv, nat, minor);
            let motive = {
                let anon = d.anon_name();
                d.kernel()
                    .lam(anon, even_n_ty, odd_succ_n_ty, BinderInfo::Default)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(rec, &[nat, even_n_pred, motive, minor, h]);
            d.lam_fv(h_fv, even_n_ty, body)
        };

        // mpr : Odd (succ n) -> Even n
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let kk = d.add(k, k);
            let succ_kk = d.succ(kk);
            let hk_ty = d.eq(succ_n, succ_kk);

            let n_eq_kk = d.lemma(p.succ_injective, &[n, kk, hk]);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            let ev_proof = d.apply(intro, &[nat, even_n_pred, k, n_eq_kk]);
            let minor = d.lam_fv(hk_fv, hk_ty, ev_proof);
            let minor = d.lam_fv(k_fv, nat, minor);
            let motive = {
                let anon = d.anon_name();
                d.kernel()
                    .lam(anon, odd_succ_n_ty, even_n_ty, BinderInfo::Default)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(rec, &[nat, odd_succ_n_pred, motive, minor, h]);
            d.lam_fv(h_fv, odd_succ_n_ty, body)
        };

        let proof = d.const_app(p.logic.iff_intro, &[even_n_ty, odd_succ_n_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Eq (mul (succ one) k) (add k k)` — the multiplicative form of a doubled
/// witness, via `succ_mul` then `one_mul` (the identical technique
/// `binary.rs`'s `n_lt_mul_two` already inlines for a `Lt` conclusion,
/// extracted here as a standalone equality). `succ one` and a literal `two`
/// are the same term by construction, so callers may freely use either —
/// see `n_lt_mul_two`'s own doc for why the kernel's final `def_eq` check
/// bridges any residual surface difference.
///
/// This is the bridge's one piece of new arithmetic: `Even`/`Odd` are
/// stated in `k+k`/`succ(k+k)` form (see the module doc for why), while
/// `Nat.divMod`'s reconstruction equation is stated in `mul divisor
/// quotient + remainder` form. Connecting the two needs exactly this
/// conversion, in both directions.
fn mul_two_eq_add_self(d: &mut NatDev<'_>, p: &NatPrelude, k: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let succ_one = d.succ(one);
    let mul_succ_one_k = d.mul(succ_one, k);
    let mul_one_k = d.mul(one, k);
    let add_mul_one_k_k = d.add(mul_one_k, k);
    let kk = d.add(k, k);

    let succ_mul_eq = d.lemma(p.succ_mul, &[one, k]);
    let one_mul_eq = d.lemma(p.one_mul, &[k]);
    let congr_step = d.congr(mul_one_k, k, one_mul_eq, &|d, x| d.add(x, k));

    let (_, result) = d.chain(
        mul_succ_one_k,
        &[(add_mul_one_k_k, succ_mul_eq), (kk, congr_step)],
    );
    result
}

/// `Eq (succ a) (add a one)` — via `add_succ` (`add a (succ zero) = succ
/// (add a zero)`) then `add_zero`, reversed. The `succ(k+k)` shape `Odd`
/// uses and the `add (mul two j) one` shape `Nat.divMod`'s reconstruction
/// needs otherwise never meet.
fn succ_eq_add_one(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let zero = d.zero();
    let add_a_one = d.add(a, one);
    let add_a_zero = d.add(a, zero);
    let succ_add_a_zero = d.succ(add_a_zero);
    let succ_a = d.succ(a);

    let add_succ_eq = d.lemma(p.add_succ, &[a, zero]);
    let add_zero_eq = d.lemma(p.add_zero, &[a]);
    let congr_step = d.congr(add_a_zero, a, add_zero_eq, &|d, x| d.succ(x));

    let (_, result) = d.chain(
        add_a_one,
        &[(succ_add_a_zero, add_succ_eq), (succ_a, congr_step)],
    );
    d.symm(add_a_one, succ_a, result)
}

/// `Eq (mod (add (mul two x) r) two) r`, given `Lt r two` — the "the
/// reconstructed dividend has the DECLARED remainder" half of `Nat.divMod`
/// uniqueness, specialized to divisor `2`. Built exactly like
/// [`super::binary::declare_mod_two_mul_split`]: a hand-built `divMod`
/// witness (here simply `refl`, since the dividend IS `add (mul two x) r`
/// verbatim — no reconstruction algebra needed, unlike that theorem's own
/// witness) compared against the executable `div_mod_exec` instance via
/// `div_mod_unique`.
pub(super) fn mod_two_mul_add_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    r: ExprId,
    r_lt_two: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let two = d.num(2);
    let mul_two_x = d.mul(two, x);
    let dividend = d.add(mul_two_x, r);

    let eq_ty = d.eq(dividend, dividend);
    let bound_ty = d.lt(r, two);
    let refl_eq = d.refl(dividend);
    let h_construct = d.const_app(p.logic.and_intro, &[eq_ty, bound_ty, refl_eq, r_lt_two]);

    let h_exec = d.lemma(p.div_mod_exec, &[one, dividend]);
    let q_exec = d.div(dividend, two);
    let r_exec = d.modulo(dividend, two);

    let unique = d.lemma(
        p.div_mod_unique,
        &[two, dividend, q_exec, r_exec, x, r, h_exec, h_construct],
    );
    let eq_q_ty = d.eq(q_exec, x);
    let eq_r_ty = d.eq(r_exec, r);
    and_right(d, eq_q_ty, eq_r_ty, unique)
}

/// `Nat.even_iff_mod_two_eq_zero : ∀ n, Iff (Even n) (Eq (mod n 2) 0)` —
/// the parity <-> low-bit bridge `xor.rs`'s module doc named as missing
/// ("no established connection to `Nat.mod _ 2` anywhere in this prelude").
///
/// `mp`: eliminate `Even n` (`Exists.rec`, exactly `declare_even_not_odd`'s
/// shape) to `k, hk : Eq n (add k k)`, rewrite `mod n 2` along `hk` and
/// [`mul_two_eq_add_self`] down to `mod (add (mul two k) 0) 2`, and close
/// with [`mod_two_mul_add_of_lt`] at `r := 0`.
///
/// `mpr`: `div_mod_exec` gives `n = add (mul two (div n 2)) (mod n 2)`;
/// substitute the hypothesis `mod n 2 = 0`, simplify the `+ 0` away, rewrite
/// `mul two (div n 2)` to `add (div n 2) (div n 2)` via
/// [`mul_two_eq_add_self`], and hand the result to `Exists.intro` at witness
/// `div n 2`.
fn declare_even_iff_mod_two_eq_zero(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    d.theorem(p.even_iff_mod_two_eq_zero, 1, &|d, values| {
        let n = values[0];
        let two = d.num(2);
        let zero = d.zero();
        let mod_n_two = d.modulo(n, two);
        let even_ty = d.lemma(p.even, &[n]);
        let mod_zero_ty = d.eq(mod_n_two, zero);
        let stmt = d.const_app(p.logic.iff, &[even_ty, mod_zero_ty]);

        let even_pred = even_predicate(d, n);

        // mp : Even n -> Eq (mod n 2) 0
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let kk = d.add(k, k);
            let hk_ty = d.eq(n, kk);

            let minor = {
                let mul_two_k = d.mul(two, k);
                let mul_eq_kk = mul_two_eq_add_self(d, &p, k);
                let kk_eq_mul = d.symm(mul_two_k, kk, mul_eq_kk);

                let one_tmp = d.num(1);
                let zero_lt_two = d.zero_lt_succ(one_tmp);
                let mul_two_k_plus_zero = d.add(mul_two_k, zero);

                let congr_n = d.congr(n, kk, hk, &|d, x| d.modulo(x, two));
                let congr_kk = d.congr(kk, mul_two_k, kk_eq_mul, &|d, x| d.modulo(x, two));
                let add_zero_eq = d.lemma(p.add_zero, &[mul_two_k]);
                let congr_mtk = d.congr(mul_two_k_plus_zero, mul_two_k, add_zero_eq, &|d, x| {
                    d.modulo(x, two)
                });
                let mod_mtk_plus_zero_pre = d.modulo(mul_two_k_plus_zero, two);
                let mod_mtk_pre = d.modulo(mul_two_k, two);
                let rev_congr_mtk = d.symm(mod_mtk_plus_zero_pre, mod_mtk_pre, congr_mtk);
                let final_step = mod_two_mul_add_of_lt(d, &p, k, zero, zero_lt_two);

                let mod_kk = d.modulo(kk, two);
                let mod_mul_two_k = d.modulo(mul_two_k, two);
                let mod_mul_two_k_plus_zero = d.modulo(mul_two_k_plus_zero, two);
                let (_, chained) = d.chain(
                    mod_n_two,
                    &[
                        (mod_kk, congr_n),
                        (mod_mul_two_k, congr_kk),
                        (mod_mul_two_k_plus_zero, rev_congr_mtk),
                        (zero, final_step),
                    ],
                );
                chained
            };

            let motive = {
                let anon = d.anon_name();
                d.kernel()
                    .lam(anon, even_ty, mod_zero_ty, BinderInfo::Default)
            };
            let minor_fn = {
                let inner = d.lam_fv(hk_fv, hk_ty, minor);
                d.lam_fv(k_fv, nat, inner)
            };
            let one_lvl = d.level_one();
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
            let body = d.apply(rec, &[nat, even_pred, motive, minor_fn, h]);
            d.lam_fv(h_fv, even_ty, body)
        };

        // mpr : Eq (mod n 2) 0 -> Even n
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let one_p = d.num(1);
            let h_exec = d.lemma(p.div_mod_exec, &[one_p, n]);
            let half = d.div(n, two);
            let mul_two_half = d.mul(two, half);
            let recon = d.add(mul_two_half, mod_n_two);
            let eq_ty = d.eq(n, recon);
            let bound_ty = d.lt(mod_n_two, two);
            let n_eq_recon = and_left(d, eq_ty, bound_ty, h_exec);

            let recon_zero = d.add(mul_two_half, zero);
            let congr_h = d.congr(mod_n_two, zero, h, &|d, x| d.add(mul_two_half, x));
            let add_zero_eq = d.lemma(p.add_zero, &[mul_two_half]);
            let half_half = d.add(half, half);
            let mul_eq_half_half = mul_two_eq_add_self(d, &p, half);

            let (_, n_eq_half_half) = d.chain(
                n,
                &[
                    (recon, n_eq_recon),
                    (recon_zero, congr_h),
                    (mul_two_half, add_zero_eq),
                    (half_half, mul_eq_half_half),
                ],
            );

            let one_lvl_intro = d.level_one();
            let intro = d.kernel().const_(p.logic.exists_intro, vec![one_lvl_intro]);
            let ev_proof = d.apply(intro, &[nat, even_pred, half, n_eq_half_half]);
            d.lam_fv(h_fv, mod_zero_ty, ev_proof)
        };

        let proof = d.const_app(p.logic.iff_intro, &[even_ty, mod_zero_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.odd_iff_mod_two_eq_one : ∀ n, Iff (Odd n) (Eq (mod n 2) 1)` —
/// [`declare_even_iff_mod_two_eq_zero`]'s `succ` twin, via
/// [`succ_eq_add_one`] to bridge `succ(k+k)` and `add (mul two k) 1`.
fn declare_odd_iff_mod_two_eq_one(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    d.theorem(p.odd_iff_mod_two_eq_one, 1, &|d, values| {
        let n = values[0];
        let two = d.num(2);
        let one = d.num(1);
        let mod_n_two = d.modulo(n, two);
        let odd_ty = d.lemma(p.odd, &[n]);
        let mod_one_ty = d.eq(mod_n_two, one);
        let stmt = d.const_app(p.logic.iff, &[odd_ty, mod_one_ty]);

        let odd_pred = odd_predicate(d, n);

        // mp : Odd n -> Eq (mod n 2) 1
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hj_fv = d.fresh_fvar();
            let hj = d.kernel().fvar(hj_fv);
            let jj = d.add(j, j);
            let succ_jj = d.succ(jj);
            let hj_ty = d.eq(n, succ_jj);

            let minor = {
                let mul_two_j = d.mul(two, j);
                let mul_eq_jj = mul_two_eq_add_self(d, &p, j);
                let jj_eq_mul = d.symm(mul_two_j, jj, mul_eq_jj);
                let succ_congr = d.congr(jj, mul_two_j, jj_eq_mul, &|d, x| d.succ(x));
                let succ_mul_two_j = d.succ(mul_two_j);
                let succ_eq_add = succ_eq_add_one(d, &p, mul_two_j);
                let add_mul_two_j_one = d.add(mul_two_j, one);

                let one_lt_two = d.lemma(p.le_refl, &[two]);
                let final_step = mod_two_mul_add_of_lt(d, &p, j, one, one_lt_two);

                let congr_n = d.congr(n, succ_jj, hj, &|d, x| d.modulo(x, two));
                let congr_succ = d.congr(succ_jj, succ_mul_two_j, succ_congr, &|d, x| {
                    d.modulo(x, two)
                });
                let congr_add = d.congr(succ_mul_two_j, add_mul_two_j_one, succ_eq_add, &|d, x| {
                    d.modulo(x, two)
                });

                let mod_succ_jj = d.modulo(succ_jj, two);
                let mod_succ_mul_two_j = d.modulo(succ_mul_two_j, two);
                let mod_add_mul_two_j_one = d.modulo(add_mul_two_j_one, two);
                let (_, chained) = d.chain(
                    mod_n_two,
                    &[
                        (mod_succ_jj, congr_n),
                        (mod_succ_mul_two_j, congr_succ),
                        (mod_add_mul_two_j_one, congr_add),
                        (one, final_step),
                    ],
                );
                chained
            };

            let motive = {
                let anon = d.anon_name();
                d.kernel()
                    .lam(anon, odd_ty, mod_one_ty, BinderInfo::Default)
            };
            let minor_fn = {
                let inner = d.lam_fv(hj_fv, hj_ty, minor);
                d.lam_fv(j_fv, nat, inner)
            };
            let one_lvl = d.level_one();
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
            let body = d.apply(rec, &[nat, odd_pred, motive, minor_fn, h]);
            d.lam_fv(h_fv, odd_ty, body)
        };

        // mpr : Eq (mod n 2) 1 -> Odd n
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let one_p = d.num(1);
            let h_exec = d.lemma(p.div_mod_exec, &[one_p, n]);
            let half = d.div(n, two);
            let mul_two_half = d.mul(two, half);
            let recon = d.add(mul_two_half, mod_n_two);
            let eq_ty = d.eq(n, recon);
            let bound_ty = d.lt(mod_n_two, two);
            let n_eq_recon = and_left(d, eq_ty, bound_ty, h_exec);

            let recon_one = d.add(mul_two_half, one);
            let congr_h = d.congr(mod_n_two, one, h, &|d, x| d.add(mul_two_half, x));

            let succ_mul_two_half = d.succ(mul_two_half);
            let succ_eq_add = succ_eq_add_one(d, &p, mul_two_half);
            let add_eq_succ = d.symm(recon_one, succ_mul_two_half, succ_eq_add);

            let half_half = d.add(half, half);
            let succ_half_half = d.succ(half_half);
            let mul_eq_half_half = mul_two_eq_add_self(d, &p, half);
            let succ_congr = d.congr(mul_two_half, half_half, mul_eq_half_half, &|d, x| d.succ(x));

            let (_, n_eq_succ_half_half) = d.chain(
                n,
                &[
                    (recon, n_eq_recon),
                    (recon_one, congr_h),
                    (succ_mul_two_half, add_eq_succ),
                    (succ_half_half, succ_congr),
                ],
            );

            let one_lvl_intro = d.level_one();
            let intro = d.kernel().const_(p.logic.exists_intro, vec![one_lvl_intro]);
            let od_proof = d.apply(intro, &[nat, odd_pred, half, n_eq_succ_half_half]);
            d.lam_fv(h_fv, mod_one_ty, od_proof)
        };

        let proof = d.const_app(p.logic.iff_intro, &[odd_ty, mod_one_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declaration order: `Even`/`Odd` first, then `even_or_odd_exists` (needs
/// both), then the disjointness theorem, then the two bridges that consume
/// it, then the cheap `succ` iff, then the parity <-> low-bit bridge (needs
/// only `Even`/`Odd` themselves plus `division.rs`'s `div_mod_exec`/
/// `div_mod_unique`, already available by this point in the prelude).
pub(super) fn declare_parity_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_even_odd_defs(d, p)?;
    declare_even_or_odd_exists(d, p)?;
    declare_add_self_ne_succ_add_self(d, p)?;
    declare_even_not_odd(d, p)?;
    declare_odd_not_even(d, p)?;
    declare_even_iff_odd_succ(d, p)?;
    declare_even_iff_mod_two_eq_zero(d, p)?;
    declare_odd_iff_mod_two_eq_one(d, p)?;
    Ok(())
}
