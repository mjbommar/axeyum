//! The parity / division-by-two mirror cluster (lane `nat-parity-div`,
//! 2026-08-30): `Nat.div_two_mul_two_of_even`, `Nat.div_two_mul_two_add_one_of_odd`,
//! `Nat.add_one_lt_of_even`, `Nat.odd_of_mul_left`, `Nat.odd_of_mul_right`, plus
//! the private helper `Nat.even_mul_of_even_left` the last two need.
//!
//! ## Why these are NOT transported from `Int`
//!
//! `int_prelude/parity.rs` already carries `Int.ediv_two_mul_two_of_even`,
//! `Int.ediv_two_mul_two_add_one_of_odd`, `Int.odd_of_mul_left`,
//! `Int.odd_of_mul_right` at exactly matching shapes, and building an
//! `ofNat`/`natAbs` carrier bridge (`Int.add (ofNat m) (ofNat n)` reduces to
//! `ofNat (m+n)` by the `Int.add` case split, so that half is free; but
//! `Even (ofNat k) <-> Nat.Even k` needs `Int.even_iff_nat_abs_even` plus a
//! genuine `Iff`-inside-`Iff` congruence lemma this prelude does not have)
//! turned out costlier than reproving each statement directly against this
//! prelude's own `Nat.Even`/`Nat.Odd`/`div_mod_exec` machinery
//! (`nat_prelude/parity.rs`, `nat_prelude/division.rs`). Every proof below
//! is a direct Nat-level construction, not a carrier transport.
//!
//! ## What each proof reuses
//!
//! - [`declare_div_two_mul_two_of_even`]/[`declare_div_two_mul_two_add_one_of_odd`]
//!   reuse `Nat.even_iff_mod_two_eq_zero`/`Nat.odd_iff_mod_two_eq_one` (the
//!   parity <-> low-bit bridge) to pin `n % 2`, then `Nat.div_mod_exec` (the
//!   `n = 2*(n/2) + n%2` reconstruction) plus `Nat.mul_comm`/`Nat.add_zero` to
//!   rearrange it into the mirrors' `n/2*2 [+ 1] = n` shape. Exactly the
//!   pattern `declare_odd_iff_mod_two_eq_one`'s own `mpr` half already uses.
//! - [`declare_add_one_lt_of_even`] uses `Nat.lt_or_eq_of_le` at `(n+1, m)`
//!   (legal because `Nat.lt n m := Nat.le (succ n) m` and `add n 1` reduces
//!   to `succ n` by `Nat.add`'s definition — `add`'s right argument here is
//!   the literal `succ zero`, so the recursion bottoms out regardless of
//!   `n`), then rules out the equality branch: `n+1 = m` together with
//!   `Nat.even_iff_odd_succ` (`Even n -> Odd (succ n)`) and
//!   `Nat.odd_not_even` would make `m` both `Even` (hypothesis) and not.
//! - [`declare_even_mul_of_even_left`] (private helper) is `Even m -> Even
//!   (mul m n)` via `Nat.right_distrib` on the `k+k` witness:
//!   `mul (add k k) n = add (mul k n) (mul k n)`.
//! - [`declare_odd_of_mul_left`] case-splits `m` via
//!   `Nat.even_or_odd_exists`: the `Even m` branch contradicts `Odd (mul m
//!   n)` through the helper above plus `Nat.odd_not_even`; the `Odd m`
//!   branch is the goal directly.
//! - [`declare_odd_of_mul_right`] transports [`declare_odd_of_mul_left`]'s
//!   conclusion along `Nat.mul_comm`.
//!
//! `or_elim`/`absurd` are private per-file copies of the same non-dependent
//! `Or.rec`/`False.rec` wrappers `nat_prelude/add_basics.rs` and several
//! other files each carry independently (see those modules' doc comments
//! for why: this prelude is edited by concurrent lanes and a shared
//! `ops.rs` helper is a contended file).

use super::NatPrelude;
use super::helpers::and_left;
use super::ops::{NatDev, NatOps};
use super::parity::even_predicate;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// Non-dependent `Or.rec` (private copy; see the module doc for why).
#[allow(clippy::too_many_arguments)]
fn or_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_case: ExprId,
    right_case: ExprId,
    or_proof: ExprId,
) -> ExprId {
    let p = *p;
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

/// `False.rec` into `goal` (private copy; see the module doc for why).
fn absurd(d: &mut NatDev<'_>, p: &NatPrelude, goal: ExprId, contradiction: ExprId) -> ExprId {
    let p = *p;
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![zero]);
    d.apply(rec, &[motive, contradiction])
}

/// `Nat.even_mul_of_even_left : ∀ m n, Even m → Even (mul m n)` — private
/// helper under [`declare_odd_of_mul_left`]/[`declare_odd_of_mul_right`].
/// `Even m` gives a witness `k` with `m = k+k`; `mul (k+k) n = mul k n + mul
/// k n` by `right_distrib`, so `mul k n` witnesses `Even (mul m n)`.
fn declare_even_mul_of_even_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();

    d.theorem(p.even_mul_of_even_left, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let even_m_ty = d.lemma(p.even, &[m]);
        let mul_mn = d.mul(m, n);
        let even_mul_ty = d.lemma(p.even, &[mul_mn]);
        let stmt = d.arrow(even_m_ty, even_mul_ty);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let kk = d.add(k, k);
        let hk_ty = d.eq(m, kk);

        let mul_kk_n = d.mul(kk, n);
        let congr1 = d.congr(m, kk, hk, &|d, x| d.mul(x, n));
        let rdist = d.lemma(p.right_distrib, &[k, k, n]);
        let mul_k_n = d.mul(k, n);
        let witness_sum = d.add(mul_k_n, mul_k_n);
        let (_, chained) = d.chain(mul_mn, &[(mul_kk_n, congr1), (witness_sum, rdist)]);

        let even_mul_pred = even_predicate(d, mul_mn);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let ev_proof = d.apply(intro, &[nat, even_mul_pred, mul_k_n, chained]);

        let minor = d.lam_fv(hk_fv, hk_ty, ev_proof);
        let minor = d.lam_fv(k_fv, nat, minor);

        let even_m_pred = even_predicate(d, m);
        let motive = {
            let anon = d.anon_name();
            d.kernel().lam(anon, even_m_ty, even_mul_ty, BinderInfo::Default)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(rec, &[nat, even_m_pred, motive, minor, h]);
        let proof = d.lam_fv(h_fv, even_m_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.odd_of_mul_left : ∀ m n, Odd (mul m n) → Odd m` —
/// `F:ml430-nat-odd-of-mul-left-2c6c2553`. Case-split `m` via
/// `even_or_odd_exists`: the `Even m` branch contradicts the hypothesis via
/// [`declare_even_mul_of_even_left`] + `odd_not_even`; the `Odd m` branch is
/// the goal already.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_odd_of_mul_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.odd_of_mul_left, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let mul_mn = d.mul(m, n);
        let odd_mul_ty = d.lemma(p.odd, &[mul_mn]);
        let odd_m_ty = d.lemma(p.odd, &[m]);
        let stmt = d.arrow(odd_mul_ty, odd_m_ty);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let even_m_ty = d.lemma(p.even, &[m]);
        let or_proof = d.lemma(p.even_or_odd_exists, &[m]);

        let left_case = {
            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            let even_mul_fn = d.lemma(p.even_mul_of_even_left, &[m, n]);
            let even_mul_proof = d.apply(even_mul_fn, &[hm]);
            let onem = d.lemma(p.odd_not_even, &[mul_mn]);
            let not_even_mul = d.apply(onem, &[h]);
            let false_proof = d.apply(not_even_mul, &[even_mul_proof]);
            let odd_m_from_false = absurd(d, &p, odd_m_ty, false_proof);
            d.lam_fv(hm_fv, even_m_ty, odd_m_from_false)
        };

        let right_case = {
            let ho_fv = d.fresh_fvar();
            let ho = d.kernel().fvar(ho_fv);
            d.lam_fv(ho_fv, odd_m_ty, ho)
        };

        let body = or_elim(
            d, &p, even_m_ty, odd_m_ty, odd_m_ty, left_case, right_case, or_proof,
        );
        let proof = d.lam_fv(h_fv, odd_mul_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.odd_of_mul_right : ∀ m n, Odd (mul m n) → Odd n` —
/// `F:ml430-nat-odd-of-mul-right-fe6d20ff`. Transport the hypothesis along
/// `mul_comm` to `Odd (mul n m)` and hand it to
/// [`declare_odd_of_mul_left`].
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_odd_of_mul_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.odd_of_mul_right, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let mul_mn = d.mul(m, n);
        let mul_nm = d.mul(n, m);
        let odd_mul_mn_ty = d.lemma(p.odd, &[mul_mn]);
        let odd_n_ty = d.lemma(p.odd, &[n]);
        let stmt = d.arrow(odd_mul_mn_ty, odd_n_ty);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let comm = d.lemma(p.mul_comm, &[m, n]);
        let motive = d.eq_motive(mul_mn, &|d, x| d.lemma(p.odd, &[x]));
        let odd_mul_nm = d.transport(mul_mn, motive, h, mul_nm, comm);

        let recurse = d.lemma(p.odd_of_mul_left, &[n, m]);
        let odd_n = d.apply(recurse, &[odd_mul_nm]);

        let proof = d.lam_fv(h_fv, odd_mul_mn_ty, odd_n);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.div_two_mul_two_of_even : ∀ n, Even n → Eq (mul (div n 2) 2) n` —
/// `F:ml430-nat-div-two-mul-two-of-even-9ccc5340`. `even_iff_mod_two_eq_zero`
/// pins `n % 2 = 0`; `div_mod_exec` reconstructs `n = 2*(n/2) + n%2`;
/// substitute, drop the `+0` via `add_zero`, commute via `mul_comm`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_div_two_mul_two_of_even(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.div_two_mul_two_of_even, 1, &|d, values| {
        let n = values[0];
        let one = d.num(1);
        let two = d.num(2);
        let zero = d.zero();
        let half = d.div(n, two);
        let rem = d.modulo(n, two);
        let mul_half_two = d.mul(half, two);
        let even_ty = d.lemma(p.even, &[n]);
        let concl_ty = d.eq(mul_half_two, n);
        let stmt = d.arrow(even_ty, concl_ty);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let mod_zero_ty = d.eq(rem, zero);
        let even_iff = d.lemma(p.even_iff_mod_two_eq_zero, &[n]);
        let mp = d.const_app(p.logic.iff_mp, &[even_ty, mod_zero_ty, even_iff]);
        let mod_eq_zero = d.apply(mp, &[h]);

        let h_exec = d.lemma(p.div_mod_exec, &[one, n]);
        let mul_two_half = d.mul(two, half);
        let recon = d.add(mul_two_half, rem);
        let recon_eq_ty = d.eq(n, recon);
        let bound_ty = d.lt(rem, two);
        let n_eq_recon = and_left(d, recon_eq_ty, bound_ty, h_exec);

        let add_mth_zero = d.add(mul_two_half, zero);
        let congr_step = d.congr(rem, zero, mod_eq_zero, &|d, x| {
            let m2h = d.mul(two, half);
            d.add(m2h, x)
        });
        let add_zero_step = d.lemma(p.add_zero, &[mul_two_half]);
        let mul_comm_step = d.lemma(p.mul_comm, &[two, half]);

        let (_, chained) = d.chain(
            n,
            &[
                (recon, n_eq_recon),
                (add_mth_zero, congr_step),
                (mul_two_half, add_zero_step),
                (mul_half_two, mul_comm_step),
            ],
        );
        let final_proof = d.symm(n, mul_half_two, chained);
        let proof = d.lam_fv(h_fv, even_ty, final_proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.div_two_mul_two_add_one_of_odd : ∀ n, Odd n → Eq (add (mul (div n 2)
/// 2) 1) n` — `F:ml430-nat-div-two-mul-two-add-one-of-odd-9e3e8b82`.
/// [`declare_div_two_mul_two_of_even`]'s twin via
/// `odd_iff_mod_two_eq_one`/`mul_comm` instead of `add_zero` (there is no
/// `+0` to drop; the reconstructed remainder `1` is already the mirror's
/// addend).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_div_two_mul_two_add_one_of_odd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.div_two_mul_two_add_one_of_odd, 1, &|d, values| {
        let n = values[0];
        let one = d.num(1);
        let two = d.num(2);
        let half = d.div(n, two);
        let rem = d.modulo(n, two);
        let mul_half_two = d.mul(half, two);
        let target = d.add(mul_half_two, one);
        let odd_ty = d.lemma(p.odd, &[n]);
        let concl_ty = d.eq(target, n);
        let stmt = d.arrow(odd_ty, concl_ty);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let mod_one_ty = d.eq(rem, one);
        let odd_iff = d.lemma(p.odd_iff_mod_two_eq_one, &[n]);
        let mp = d.const_app(p.logic.iff_mp, &[odd_ty, mod_one_ty, odd_iff]);
        let mod_eq_one = d.apply(mp, &[h]);

        let h_exec = d.lemma(p.div_mod_exec, &[one, n]);
        let mul_two_half = d.mul(two, half);
        let recon = d.add(mul_two_half, rem);
        let recon_eq_ty = d.eq(n, recon);
        let bound_ty = d.lt(rem, two);
        let n_eq_recon = and_left(d, recon_eq_ty, bound_ty, h_exec);

        let add_mth_one = d.add(mul_two_half, one);
        let congr_step = d.congr(rem, one, mod_eq_one, &|d, x| {
            let m2h = d.mul(two, half);
            d.add(m2h, x)
        });
        let mul_comm_step = d.lemma(p.mul_comm, &[two, half]);
        let congr2 = d.congr(mul_two_half, mul_half_two, mul_comm_step, &|d, x| {
            d.add(x, one)
        });

        let (_, chained) = d.chain(
            n,
            &[(recon, n_eq_recon), (add_mth_one, congr_step), (target, congr2)],
        );
        let final_proof = d.symm(n, target, chained);
        let proof = d.lam_fv(h_fv, odd_ty, final_proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.add_one_lt_of_even : ∀ n m, Even n → Even m → Lt n m → Lt (add n 1)
/// m` — `F:ml430-nat-add-one-lt-of-even-3464b374`. `Lt n m` is `Le (succ n)
/// m` by definition, and `add n 1` reduces to `succ n`, so the hypothesis
/// already gives `Le (n+1) m`; `lt_or_eq_of_le` splits that into `Lt (n+1)
/// m` (the goal, directly) or `Eq (n+1) m`, and the latter is refuted:
/// `Even n` gives `Odd (succ n)` (`even_iff_odd_succ`), transporting along
/// `n+1 = m` gives `Odd m`, contradicting the hypothesis `Even m` via
/// `odd_not_even`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_add_one_lt_of_even(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.add_one_lt_of_even, 2, &|d, values| {
        let (n, m) = (values[0], values[1]);
        let one = d.num(1);
        let n1 = d.add(n, one);
        let even_n_ty = d.lemma(p.even, &[n]);
        let even_m_ty = d.lemma(p.even, &[m]);
        let lt_nm_ty = d.lt(n, m);
        let lt_n1m_ty = d.lt(n1, m);
        let stmt = {
            let inner = d.arrow(lt_nm_ty, lt_n1m_ty);
            let mid = d.arrow(even_m_ty, inner);
            d.arrow(even_n_ty, mid)
        };

        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let hlt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(hlt_fv);

        let eq_n1m_ty = d.eq(n1, m);
        let or_proof = d.lemma(p.lt_or_eq_of_le, &[n1, m, hlt]);

        let left_case = {
            let hlt2_fv = d.fresh_fvar();
            let hlt2 = d.kernel().fvar(hlt2_fv);
            d.lam_fv(hlt2_fv, lt_n1m_ty, hlt2)
        };

        let right_case = {
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);

            let succ_n = d.succ(n);
            let odd_succ_n_ty = d.lemma(p.odd, &[succ_n]);
            let even_iff_odd = d.lemma(p.even_iff_odd_succ, &[n]);
            let mp = d.const_app(p.logic.iff_mp, &[even_n_ty, odd_succ_n_ty, even_iff_odd]);
            let odd_succ_n = d.apply(mp, &[hn]);

            let motive = d.eq_motive(n1, &|d, x| d.lemma(p.odd, &[x]));
            let odd_m = d.transport(n1, motive, odd_succ_n, m, heq);

            let onem = d.lemma(p.odd_not_even, &[m]);
            let not_even_m = d.apply(onem, &[odd_m]);
            let false_proof = d.apply(not_even_m, &[hm]);

            let lt_from_false = absurd(d, &p, lt_n1m_ty, false_proof);
            d.lam_fv(heq_fv, eq_n1m_ty, lt_from_false)
        };

        let body = or_elim(
            d, &p, lt_n1m_ty, eq_n1m_ty, lt_n1m_ty, left_case, right_case, or_proof,
        );
        let proof = d.lam_fv(hlt_fv, lt_nm_ty, body);
        let proof = d.lam_fv(hm_fv, even_m_ty, proof);
        let proof = d.lam_fv(hn_fv, even_n_ty, proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declaration order: the two division reconstructions first (need only
/// `Nat.Even`/`Nat.Odd`'s low-bit bridges and `div_mod_exec`, both already
/// available), then `add_one_lt_of_even` (needs `even_iff_odd_succ`,
/// `odd_not_even`, `lt_or_eq_of_le`, all already available), then the
/// multiplication/oddness helper and the two mirrors that consume it.
pub(super) fn declare_parity_div_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_div_two_mul_two_of_even(d, p)?;
    declare_div_two_mul_two_add_one_of_odd(d, p)?;
    declare_add_one_lt_of_even(d, p)?;
    declare_even_mul_of_even_left(d, p)?;
    declare_odd_of_mul_left(d, p)?;
    declare_odd_of_mul_right(d, p)?;
    Ok(())
}
