//! `ml430` mirrors for `Nat.log`/`Nat.clog` that compose out of
//! `log.rs`/`clog.rs`/`log_clog_order.rs`'s existing machinery, plus two
//! supporting lemmas (`log_pos`, `log_of_left_le_one`) neither of those
//! files needed on their own.
//!
//! Nine facts land here:
//!
//! - `Nat.log_anti_left`/`Nat.clog_anti_left` — Mathlib states these with
//!   only `1 < c` and `c ≤ b`; `log_antitone_left`/`clog_antitone_left`
//!   (`log_clog_order.rs`) additionally take `1 < b` as an explicit
//!   hypothesis, because that file's diagonal-`AntitoneOn` framing states it
//!   pointwise rather than deriving it. `1 < b` follows from `1 < c ≤ b` via
//!   `lt_of_lt_of_le`, so each mirror here is a one-line wrapper deriving
//!   that hypothesis and re-dispatching.
//! - `Nat.clog_mono` — composes `clog_antitone_left` (base antitonicity, at
//!   the shared value `m`) with `clog_mono_right` (value monotonicity, at
//!   the shared base `c`) through `le_trans`: `clog b m ≤ clog c m ≤ clog c
//!   n`.
//! - `Nat.clog_of_left_le_one`/(local) `Nat.log_of_left_le_one` — `b ≤ 1`
//!   means `b = 0 ∨ b = 1` (`le_succ_succ` lifts `Le b 1` to `Lt b 2`, then
//!   [`super::ops::cases_lt_bound`] splits), and each boundary case is
//!   already a whole-Pi-type theorem (`clog_zero_left`/`clog_one_left`,
//!   `log_zero_left`/`log_one_left`) that can be used AS the branch — no
//!   application needed, since `d.lemma(name, &[])` with an empty argument
//!   list returns the bare constant at its full quantified type.
//! - `Nat.clog_of_right_le_one` — the same split on `n` via
//!   `clog_zero_right`/`clog_one_right`.
//! - `Nat.log_pos` — `clog_pos`'s exact recipe (`log_clog_order.rs`) with
//!   the two guard cuts' ROLES swapped: `log`'s outer cut is `b ≤ n` (the
//!   hypothesis that varies with the case split), inner is `2 ≤ b` (fixed);
//!   `clog`'s is the other way around. The `n = 0` branch is now refuted by
//!   combining `Lt 1 b` with the SPECIALIZED `Le b 0` (rather than `clog
//!   ​_pos`'s own `Lt 1 n` specialized to `n = 0`) via `lt_of_lt_of_le`,
//!   landing on the same `Lt 1 0` absurdity closed by `not_succ_le_zero`.
//! - `Nat.log_eq_zero_iff` — `mpr` case-splits the disjunction: `n < b`
//!   closes by `log_of_lt`, `b ≤ 1` closes by `log_of_left_le_one`. `mp`
//!   case-splits on `Nat.lt_or_ge n b`; the `b ≤ n` side splits again on
//!   `Nat.lt_or_ge 1 b` and refutes the `1 < b` sub-case by transporting
//!   `log_pos`'s `Lt 0 (log b n)` along the hypothesis `Eq (log b n) 0` to
//!   `Lt 0 0`, absurd via `lt_irrefl`.
//!
//! - `Nat.clog_eq_one` — [`declare_clog_pos`](super::log_clog_order)'s
//!   unfolding recipe (`cases_zero_succ` on `n`, both guard cuts known true,
//!   two `bool_transport`s reduced→general), aimed at `Eq (_, 1)` instead of
//!   `Lt 0 _`. The recursive argument's numerator `(n + b) - 1` is, via
//!   `Nat.succ_add` and `sub x 1 ≡ pred x` (pure defeq), EQUAL to `n' + b`
//!   (`n = succ n'`); `Nat.add_div_right` rewrites `(n' + b) / b` to
//!   `n' / b + 1`, and `n' / b = 0` because `n' < b` is exactly the
//!   hypothesis `Le n b` restated at `n = succ n'` (`Lt n' b ≡ Le (succ n')
//!   b` by `Nat.lt`'s own definition — no derivation needed). So the
//!   quotient is `1`, and [`clog_aux_at_one_eq_zero`] (a fuel-agnostic `Eq
//!   (clogAux base fuel 1) 0`, via [`super::ops::bool_select_nat_same`] once
//!   the LITERAL inner cut `2 ≤ 1` iota-collapses) closes the rest.
//!
//! - `Nat.log_eq_one_iff'` — `mpr` (`Le b n → Lt n (mul b b) → Eq (log b n)
//!   1`) is [`log_eq_one_of_bounds`]; unlike the unprimed form below, `1 <
//!   b` is not given, so `mpr` derives it from the bounds
//!   ([`derive_one_lt_base_from_bounds`]: if `b ≤ 1` then `b*b ≤ b ≤ 1`, so
//!   `n < 1`, so `n = 0`, so (with `b ≤ n`) `b = 0`, contradicting `n <
//!   b*b = 0` via `not_lt_zero`). `mp` composes
//!   [`log_eq_one_derive_base_le_n`] (`Nat.lt_or_ge n b`, the `n < b` side
//!   refuted the same way `log_eq_zero_iff`'s `mp` refutes its own `1 < b`
//!   sub-case) with [`log_eq_one_derive_sq_bound`] — the genuinely new
//!   piece, "`log b n < 2 → n < b*b`" this file's module doc used to call
//!   missing: peel `Eq (log b n) 1` (general → specific, TWO
//!   `bool_transport`s using the FORWARD `ble_eq_true_of_le` evidence,
//!   peeling the OUTER cut `b ≤ n` first since it wraps the inner `2 ≤ b` —
//!   the reverse of how `log_pos` BUILDS the same unfold) down to `Eq
//!   (logAux b n' quotient) 0`, then [`log_aux_eq_zero_imp_lt`] (the
//!   CONVERSE of `log_aux_lt_eq_zero` below, fuel-generalized via
//!   `cases_zero_succ` alone — no induction — fed `Le quotient n'` from
//!   `div_lt_self` + `le_of_lt_succ`) gives `Lt quotient b`, and
//!   [`lt_mul_of_div_lt`] (the BACKWARD direction of `Nat.div_mod_lt_mul_iff`,
//!   needing `Lt 0 b` unlike the forward direction already in the prelude)
//!   finishes.
//! - `Nat.log_eq_one_iff` — [`declare_log_eq_one_iff_prime`]'s exact core,
//!   repackaged into Mathlib's stronger hypothesis set (`1 < b` explicit,
//!   via [`derive_one_lt_base_from_log_eq_one`]: if `b ≤ 1` then
//!   `log_of_left_le_one` gives `Eq (log b n) 0`, contradicting `Eq (log b
//!   n) 1` via `succ_ne_zero`) and different `And` nesting/order.
//!
//! `Nat.log_div_mul_self` now lands too. The fuel-generalized induction the
//! module doc used to call missing turned out to be [`log_aux_agree_of_fuel`]
//! — the SAME two-fuel technique `rec_agreement.rs`'s
//! `land_aux_agree_of_fuel` uses for `landAux`, transported from a
//! structural `m = 0` guard to `logAux`'s order-comparison guard `ble base
//! value`. It relates `logAux` at the SAME value (the shared quotient `n /
//! b`) across two DIFFERENT but each individually sufficient fuels — not,
//! as this note used to say, at two different values. [`log_succ_unfold`]
//! (one recursive step of `log`'s own equation, [`declare_log_pos`]'s
//! `at_n_succ` recipe retargeted from `Lt zero _` to an `Eq`) supplies one
//! unfold on each side; [`mul_div_cancel_left`] identifies the two
//! resulting quotients. See [`declare_log_div_mul_self_big`] for the full
//! route.

use super::NatPrelude;
use super::helpers::{and_left, and_right, iff_forward, iff_reverse};
use super::ops::{NatDev, NatOps};
use super::steps::or_cases;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `Nat.logAux base fuel value` (mirrors `log.rs`'s private helper of the
/// same name and shape; not exported from that file).
fn log_aux(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    fuel: ExprId,
    value: ExprId,
) -> ExprId {
    d.const_app(p.log_aux, &[base, fuel, value])
}

/// `Nat.clogAux base fuel value` (mirrors `clog.rs`'s/`log_clog_order.rs`'s
/// private helper of the same name and shape; not exported from either
/// file).
fn clog_aux(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    fuel: ExprId,
    value: ExprId,
) -> ExprId {
    d.const_app(p.clog_aux, &[base, fuel, value])
}

/// `Nat.log base value`.
fn log(d: &mut NatDev<'_>, p: &NatPrelude, base: ExprId, value: ExprId) -> ExprId {
    d.const_app(p.log, &[base, value])
}

/// `Nat.clog base value`.
fn clog(d: &mut NatDev<'_>, p: &NatPrelude, base: ExprId, value: ExprId) -> ExprId {
    d.const_app(p.clog, &[base, value])
}

/// `False.elim`-style: `absurd : False` closes any `target`, via
/// `False.rec`. Mirrors `log_clog_order.rs`'s private construction of the
/// same shape (not exported from that file).
fn false_elim(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, absurd: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let zero = d.kernel().level_zero();
    let false_rec = d.kernel().const_(p.logic.false_rec, vec![zero]);
    d.apply(false_rec, &[motive, absurd])
}

/// `Nat.log_anti_left : ∀ {b c n}, Lt 1 c → Le c b → Le (log b n) (log c n)`
/// (`Mathlib`: `Nat.log_anti_left`) — [`log_antitone_left`](super::log_clog_order)'s
/// diagonal at a DERIVED `Lt 1 b` (`lt_of_lt_of_le` from `Lt 1 c` and
/// `Le c b`), matching Mathlib's weaker hypothesis set.
pub(super) fn declare_log_anti_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.log_anti_left, 3, &|d, values| {
        let (n, c, b) = (values[0], values[1], values[2]);
        let one = d.num(1);
        let hc_ty = d.lt(one, c);
        let hcb_ty = d.le(c, b);
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let hcb_fv = d.fresh_fvar();
        let hcb = d.kernel().fvar(hcb_fv);

        let hb = d.lemma(p.lt_of_lt_of_le, &[one, c, b, hc, hcb]);
        let proof_body = d.lemma(p.log_antitone_left, &[n, c, b, hcb, hc, hb]);

        let log_b = log(d, &p, b, n);
        let log_c = log(d, &p, c, n);
        let concl = d.le(log_b, log_c);
        let with_hcb = d.arrow(hcb_ty, concl);
        let stmt = d.arrow(hc_ty, with_hcb);
        let inner = d.lam_fv(hcb_fv, hcb_ty, proof_body);
        let proof = d.lam_fv(hc_fv, hc_ty, inner);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.clog_anti_left : ∀ {b c n}, Lt 1 c → Le c b → Le (clog b n) (clog c
/// n)` (`Mathlib`: `Nat.clog_anti_left`) — [`declare_log_anti_left`]'s exact
/// counterpart over [`clog_antitone_left`](super::log_clog_order).
pub(super) fn declare_clog_anti_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.clog_anti_left, 3, &|d, values| {
        let (n, c, b) = (values[0], values[1], values[2]);
        let one = d.num(1);
        let hc_ty = d.lt(one, c);
        let hcb_ty = d.le(c, b);
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let hcb_fv = d.fresh_fvar();
        let hcb = d.kernel().fvar(hcb_fv);

        let hb = d.lemma(p.lt_of_lt_of_le, &[one, c, b, hc, hcb]);
        let proof_body = d.lemma(p.clog_antitone_left, &[n, c, b, hcb, hc, hb]);

        let clog_b = clog(d, &p, b, n);
        let clog_c = clog(d, &p, c, n);
        let concl = d.le(clog_b, clog_c);
        let with_hcb = d.arrow(hcb_ty, concl);
        let stmt = d.arrow(hc_ty, with_hcb);
        let inner = d.lam_fv(hcb_fv, hcb_ty, proof_body);
        let proof = d.lam_fv(hc_fv, hc_ty, inner);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.clog_mono : ∀ {b c m n}, Lt 1 c → Le c b → Le m n → Le (clog b m)
/// (clog c n)` (`Mathlib`: `Nat.clog_mono`) — `clog b m ≤ clog c m`
/// ([`clog_antitone_left`](super::log_clog_order) at the shared value `m`,
/// bases `c ≤ b`) chained through `clog c m ≤ clog c n`
/// ([`clog_mono_right`](super::log_clog_order) at the shared base `c`,
/// `m ≤ n`) via `le_trans`.
pub(super) fn declare_clog_mono(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.clog_mono, 4, &|d, values| {
        let (m, n, c, b) = (values[0], values[1], values[2], values[3]);
        let one = d.num(1);
        let hc_ty = d.lt(one, c);
        let hcb_ty = d.le(c, b);
        let hmn_ty = d.le(m, n);
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let hcb_fv = d.fresh_fvar();
        let hcb = d.kernel().fvar(hcb_fv);
        let hmn_fv = d.fresh_fvar();
        let hmn = d.kernel().fvar(hmn_fv);

        let hb = d.lemma(p.lt_of_lt_of_le, &[one, c, b, hc, hcb]);
        let step1 = d.lemma(p.clog_antitone_left, &[m, c, b, hcb, hc, hb]); // clog b m <= clog c m
        let step2 = d.lemma(p.clog_mono_right, &[c, m, n, hmn]); // clog c m <= clog c n

        let clog_b_m = clog(d, &p, b, m);
        let clog_c_m = clog(d, &p, c, m);
        let clog_c_n = clog(d, &p, c, n);
        let proof_body = d.lemma(p.le_trans, &[clog_b_m, clog_c_m, clog_c_n, step1, step2]);

        let concl = d.le(clog_b_m, clog_c_n);
        let with_hmn = d.arrow(hmn_ty, concl);
        let with_hcb = d.arrow(hcb_ty, with_hmn);
        let stmt = d.arrow(hc_ty, with_hcb);
        let inner1 = d.lam_fv(hmn_fv, hmn_ty, proof_body);
        let inner2 = d.lam_fv(hcb_fv, hcb_ty, inner1);
        let proof = d.lam_fv(hc_fv, hc_ty, inner2);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.clog_of_left_le_one : ∀ {b}, Le b 1 → ∀ n, Eq (clog b n) 0`
/// (`Mathlib`: `Nat.clog_of_left_le_one`) — `Le b 1` splits into `b = 0 ∨ b =
/// 1` via [`super::ops::cases_lt_bound`] (`le_succ_succ` lifts `Le b 1` to
/// `Lt b 2`), and each branch is `clog_zero_left`/`clog_one_left` used
/// directly at their full `∀ n, …` type — no application needed.
pub(super) fn declare_clog_of_left_le_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.clog_of_left_le_one, 1, &|d, values| {
        let b = values[0];
        let one = d.num(1);
        let h_ty = d.le(b, one);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let motive = move |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let lhs = clog(d, &p, candidate, n);
            let zero = d.zero();
            let body = d.eq(lhs, zero);
            d.pi_fv(n_fv, nat, body)
        };
        let branch0 = d.lemma(p.clog_zero_left, &[]);
        let branch1 = d.lemma(p.clog_one_left, &[]);
        let lt_b_2 = d.lemma(p.le_succ_succ, &[b, one, h]);
        let body = super::ops::cases_lt_bound(d, &p, b, 2, lt_b_2, &motive, &[branch0, branch1]);
        let concl = motive(d, b);
        let stmt = d.arrow(h_ty, concl);
        let proof = d.lam_fv(h_fv, h_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.clog_of_right_le_one : ∀ {n}, Le n 1 → ∀ b, Eq (clog b n) 0`
/// (`Mathlib`: `Nat.clog_of_right_le_one`) — the same split, on `n`, via
/// `clog_zero_right`/`clog_one_right`.
pub(super) fn declare_clog_of_right_le_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.clog_of_right_le_one, 1, &|d, values| {
        let n = values[0];
        let one = d.num(1);
        let h_ty = d.le(n, one);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let motive = move |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let lhs = clog(d, &p, b, candidate);
            let zero = d.zero();
            let body = d.eq(lhs, zero);
            d.pi_fv(b_fv, nat, body)
        };
        let branch0 = d.lemma(p.clog_zero_right, &[]);
        let branch1 = d.lemma(p.clog_one_right, &[]);
        let lt_n_2 = d.lemma(p.le_succ_succ, &[n, one, h]);
        let body = super::ops::cases_lt_bound(d, &p, n, 2, lt_n_2, &motive, &[branch0, branch1]);
        let concl = motive(d, n);
        let stmt = d.arrow(h_ty, concl);
        let proof = d.lam_fv(h_fv, h_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.log_of_left_le_one : ∀ {b}, Le b 1 → ∀ n, Eq (log b n) 0` — not an
/// `ml430` mirror target on its own (Mathlib states the `b = 0`/`b = 1`
/// cases separately as `log_of_left_eq_zero`/`log_of_left_eq_one`-style
/// facts, and this repo does not preregister either), but the `b ≤ 1`
/// disjunct of [`declare_log_eq_zero_iff`]'s `mpr` needs exactly this, and
/// no existing lemma states it. [`declare_clog_of_left_le_one`]'s exact
/// recipe over `log_zero_left`/`log_one_left`.
pub(super) fn declare_log_of_left_le_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.log_of_left_le_one, 1, &|d, values| {
        let b = values[0];
        let one = d.num(1);
        let h_ty = d.le(b, one);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let motive = move |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let lhs = log(d, &p, candidate, n);
            let zero = d.zero();
            let body = d.eq(lhs, zero);
            d.pi_fv(n_fv, nat, body)
        };
        let branch0 = d.lemma(p.log_zero_left, &[]);
        let branch1 = d.lemma(p.log_one_left, &[]);
        let lt_b_2 = d.lemma(p.le_succ_succ, &[b, one, h]);
        let body = super::ops::cases_lt_bound(d, &p, b, 2, lt_b_2, &motive, &[branch0, branch1]);
        let concl = motive(d, b);
        let stmt = d.arrow(h_ty, concl);
        let proof = d.lam_fv(h_fv, h_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.log_pos : ∀ b n, Lt 1 b → Le b n → Lt 0 (log b n)` (`Mathlib`:
/// `Nat.log_pos`) — [`declare_clog_pos`](super::log_clog_order)'s exact
/// recipe with the two guard cuts' ROLES SWAPPED: `log`'s outer cut is `b ≤
/// n` (the hypothesis that varies with the `cases_zero_succ` split on `n`),
/// inner is `2 ≤ b` (fixed by `h1` alone, same at every `n`) — the reverse
/// of `clogAux`'s nesting, per `log.rs`'s/`clog.rs`'s module docs. The `n =
/// 0` branch is refuted by combining `h1 : Lt 1 b` with the SPECIALIZED `h2
/// : Le b 0` via `lt_of_lt_of_le`, landing on the same `Lt 1 0` absurdity
/// `clog_pos`'s own `n = 0` branch closes with `not_succ_le_zero`.
pub(super) fn declare_log_pos(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.log_pos, 2, &|d, values| {
        let (base, n) = (values[0], values[1]);
        let one = d.num(1);
        let h1_ty = d.lt(one, base);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);

        let motive_at = move |d: &mut NatDev<'_>, nc: ExprId| -> ExprId {
            let h2_ty = d.le(base, nc);
            let zero = d.zero();
            let lg = log(d, &p, base, nc);
            let concl = d.lt(zero, lg);
            d.arrow(h2_ty, concl)
        };

        let at_n_zero = move |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let h2_ty = d.le(base, zero);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let one_lt_zero = d.lemma(p.lt_of_lt_of_le, &[one, base, zero, h1, h2]);
            let absurd = d.lemma(p.not_succ_le_zero, &[one, one_lt_zero]);
            let lg = log(d, &p, base, zero);
            let target = d.lt(zero, lg);
            let elim = false_elim(d, &p, target, absurd);
            d.lam_fv(h2_fv, h2_ty, elim)
        };

        let at_n_succ = move |d: &mut NatDev<'_>, n_prime: ExprId| -> ExprId {
            let succ_n_prime = d.succ(n_prime);
            let h2_ty = d.le(base, succ_n_prime);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);

            let two = d.num(2);
            let base_exceeds_one = d.ble(two, base);
            let base_fits = d.ble(base, succ_n_prime);
            let proof_b_true = d.lemma(p.ble_eq_true_of_le, &[two, base, h1]);
            let proof_n_true = d.lemma(p.ble_eq_true_of_le, &[base, succ_n_prime, h2]);

            let quotient = d.div(succ_n_prime, base);
            let recursive = log_aux(d, &p, base, n_prime, quotient);
            let stepped = d.succ(recursive);
            let zero = d.zero();

            let true_ = d.bool_true();
            let pos = d.lemma(p.zero_lt_succ, &[recursive]);

            // Inner cut first (`2 <= base`, fixed): transport `stepped`'s
            // positivity to the inner `bool_select_nat`.
            let inner_term = d.bool_select_nat(base_exceeds_one, stepped, zero);
            let motive_inner = d.bool_eq_motive(true_, &|d, x| {
                let zero = d.zero();
                let selected = d.bool_select_nat(x, stepped, zero);
                d.lt(zero, selected)
            });
            let reversed_b = d.bool_symm(base_exceeds_one, true_, proof_b_true);
            let pos_inner =
                d.bool_transport(true_, motive_inner, pos, base_exceeds_one, reversed_b);

            // Outer cut second (`base <= succ n_prime`, varies with `n`).
            let motive_outer = d.bool_eq_motive(true_, &move |d, x| {
                let zero = d.zero();
                let selected = d.bool_select_nat(x, inner_term, zero);
                d.lt(zero, selected)
            });
            let reversed_n = d.bool_symm(base_fits, true_, proof_n_true);
            let pos_outer = d.bool_transport(true_, motive_outer, pos_inner, base_fits, reversed_n);
            d.lam_fv(h2_fv, h2_ty, pos_outer)
        };

        let body = super::ops::cases_zero_succ(d, n, &motive_at, &at_n_zero, &at_n_succ);
        let h2_ty = d.le(base, n);
        let zero = d.zero();
        let lg = log(d, &p, base, n);
        let final_concl = d.lt(zero, lg);
        let inner_arrow = d.arrow(h2_ty, final_concl);
        let stmt = d.arrow(h1_ty, inner_arrow);
        let proof = d.lam_fv(h1_fv, h1_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.log_eq_zero_iff : ∀ {b n}, Iff (Eq (log b n) 0) (Or (Lt n b) (Le b
/// 1))` (`Mathlib`: `Nat.log_eq_zero_iff`).
///
/// `mpr`: case-split the disjunction. `Lt n b` closes by `log_of_lt`; `Le b
/// 1` closes by [`declare_log_of_left_le_one`] applied at `n`.
///
/// `mp`: case-split `Nat.lt_or_ge n b` (`Or (Lt n b) (Le b n)`). The `Lt n
/// b` side is `Or.inl` directly. The `Le b n` side splits AGAIN on
/// `Nat.lt_or_ge 1 b` (`Or (Lt 1 b) (Le b 1)`): `Le b 1` is `Or.inr`
/// directly; `Lt 1 b` is refuted — [`declare_log_pos`] gives `Lt 0 (log b
/// n)`, transported along the hypothesis `Eq (log b n) 0` to `Lt 0 0`,
/// absurd via `lt_irrefl`, closing the goal by `False.elim`.
pub(super) fn declare_log_eq_zero_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.log_eq_zero_iff, 2, &|d, values| {
        let (base, n) = (values[0], values[1]);
        let zero = d.zero();
        let one = d.num(1);
        let lg = log(d, &p, base, n);
        let lhs_ty = d.eq(lg, zero);
        let n_lt_base = d.lt(n, base);
        let base_le_one = d.le(base, one);
        let rhs_ty = d.const_app(p.logic.or, &[n_lt_base, base_le_one]);
        let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);

        // mp : Eq (log base n) 0 -> Or (Lt n base) (Le base one)
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let dichotomy = d.lemma(p.lt_or_ge, &[n, base]); // Or (Lt n base) (Le base n)
            let lt_ty = d.lt(n, base);
            let ge_ty = d.le(base, n);

            let left_branch = {
                let hlt_fv = d.fresh_fvar();
                let hlt = d.kernel().fvar(hlt_fv);
                let inl = d.const_app(p.logic.or_inl, &[n_lt_base, base_le_one, hlt]);
                d.lam_fv(hlt_fv, lt_ty, inl)
            };
            let right_branch = {
                let hge_fv = d.fresh_fvar();
                let hge = d.kernel().fvar(hge_fv); // Le base n

                let inner_dichotomy = d.lemma(p.lt_or_ge, &[one, base]); // Or (Lt one base) (Le base one)
                let lt1_ty = d.lt(one, base);
                let le1_ty = d.le(base, one);

                let sub_left = {
                    let h1_fv = d.fresh_fvar();
                    let h1 = d.kernel().fvar(h1_fv); // Lt one base
                    let pos = d.lemma(p.log_pos, &[base, n, h1, hge]); // Lt zero lg
                    let motive = d.eq_motive(lg, &|d, x| {
                        let zero = d.zero();
                        d.lt(zero, x)
                    });
                    let pos_at_zero = d.transport(lg, motive, pos, zero, h); // Lt zero zero
                    let irrefl = d.lemma(p.lt_irrefl, &[zero]);
                    let absurd = d.apply(irrefl, &[pos_at_zero]);
                    let elim = false_elim(d, &p, rhs_ty, absurd);
                    d.lam_fv(h1_fv, lt1_ty, elim)
                };
                let sub_right = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv); // Le base one
                    let inr = d.const_app(p.logic.or_inr, &[n_lt_base, base_le_one, h2]);
                    d.lam_fv(h2_fv, le1_ty, inr)
                };
                let split_result = or_cases(
                    d,
                    lt1_ty,
                    le1_ty,
                    rhs_ty,
                    sub_left,
                    sub_right,
                    inner_dichotomy,
                );
                d.lam_fv(hge_fv, ge_ty, split_result)
            };
            let case_result = or_cases(
                d,
                lt_ty,
                ge_ty,
                rhs_ty,
                left_branch,
                right_branch,
                dichotomy,
            );
            d.lam_fv(h_fv, lhs_ty, case_result)
        };

        // mpr : Or (Lt n base) (Le base one) -> Eq (log base n) 0
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let left_branch = {
                let hlt_fv = d.fresh_fvar();
                let hlt = d.kernel().fvar(hlt_fv);
                let body = d.lemma(p.log_of_lt, &[base, n, hlt]);
                d.lam_fv(hlt_fv, n_lt_base, body)
            };
            let right_branch = {
                let hle_fv = d.fresh_fvar();
                let hle = d.kernel().fvar(hle_fv); // Le base one
                let all_n = d.lemma(p.log_of_left_le_one, &[base, hle]); // Pi n, Eq (log base n) 0
                let body = d.apply(all_n, &[n]);
                d.lam_fv(hle_fv, base_le_one, body)
            };
            let result = or_cases(
                d,
                n_lt_base,
                base_le_one,
                lhs_ty,
                left_branch,
                right_branch,
                h,
            );
            d.lam_fv(h_fv, rhs_ty, result)
        };

        let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Eq (clogAux base fuel 1) 0`, for ANY `fuel`, `base` — the fuel-exhaustion
/// row is the constant `0` (so `fuel = 0` is `d.refl`), and at `fuel = succ
/// f'` the INNER cut `2 ≤ 1` is a comparison between two LITERALS (`1 =
/// d.num(1)`), so it iota-reduces to `false` with no lemma, collapsing the
/// inner `bool_select_nat` to `0` regardless of what the taken branch would
/// have been. What remains, `bool_select_nat (ble 2 base) 0 0`, is stuck on
/// the OUTER (symbolic-`base`) test but has the SAME value (`0`) on both
/// branches, which is exactly [`super::ops::bool_select_nat_same`]'s shape.
fn clog_aux_at_one_eq_zero(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    fuel: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let motive = move |d: &mut NatDev<'_>, f: ExprId| -> ExprId {
        let zero = d.zero();
        let ca = clog_aux(d, &p, base, f, one);
        d.eq(ca, zero)
    };
    super::ops::cases_zero_succ(
        d,
        fuel,
        &motive,
        &|d| {
            let zero = d.zero();
            d.refl(zero)
        },
        &move |d, _f_prime| {
            let zero = d.zero();
            let two = d.num(2);
            let base_exceeds_one = d.ble(two, base);
            super::ops::bool_select_nat_same(d, &p, base_exceeds_one, zero)
        },
    )
}

/// `Nat.clog_eq_one : ∀ {b n}, Le 2 n → Le n b → Eq (clog b n) 1` (`Mathlib`:
/// `Nat.clog_eq_one`) — [`declare_clog_pos`](super::log_clog_order)'s exact
/// unfolding recipe (`cases_zero_succ` on `n`, both guard cuts known true,
/// two `bool_transport`s reduced→general), aimed at `Eq (_, 1)` instead of
/// `Lt 0 _`, plus the arithmetic that pins the recursive argument at `1`:
///
/// at `n = succ n'`, the recursive call's numerator `(n + b) - 1` is,
/// via [`super::NatPrelude::succ_add`] and `sub x 1 ≡ pred x` (pure
/// defeq, `clog.rs`'s own module doc), EQUAL to `n' + b`; `Nat.add_div_right`
/// then rewrites `(n' + b) / b` to `n' / b + 1`, and `n' / b = 0` because
/// `n' < b` is exactly the hypothesis `Le n b` restated at `n = succ n'`
/// (`Lt n' b ≡ Le (succ n') b` by `Nat.lt`'s own definition — no derivation
/// needed). So the quotient is `1`, and
/// [`clog_aux_at_one_eq_zero`] closes the rest.
pub(super) fn declare_clog_eq_one(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.clog_eq_one, 2, &|d, values| {
        let (base, n) = (values[0], values[1]);
        let two = d.num(2);

        let motive_at = move |d: &mut NatDev<'_>, nc: ExprId| -> ExprId {
            let h1_ty = d.le(two, nc);
            let h2_ty = d.le(nc, base);
            let cl = clog(d, &p, base, nc);
            let one = d.num(1);
            let concl = d.eq(cl, one);
            let inner = d.arrow(h2_ty, concl);
            d.arrow(h1_ty, inner)
        };

        let at_n_zero = move |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let h1_ty = d.le(two, zero);
            let h2_ty = d.le(zero, base);
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let one = d.num(1);
            let absurd = d.lemma(p.not_succ_le_zero, &[one, h1]);
            let cl = clog(d, &p, base, zero);
            let target = d.eq(cl, one);
            let elim = false_elim(d, &p, target, absurd);
            let h2_fv = d.fresh_fvar();
            let inner = d.lam_fv(h2_fv, h2_ty, elim);
            d.lam_fv(h1_fv, h1_ty, inner)
        };

        let at_n_succ = move |d: &mut NatDev<'_>, n_prime: ExprId| -> ExprId {
            let succ_np = d.succ(n_prime);
            let h1_ty = d.le(two, succ_np);
            let h2_ty = d.le(succ_np, base);
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);

            let h_two_le_base = d.lemma(p.le_trans, &[two, succ_np, base, h1, h2]);
            let base_exceeds_one = d.ble(two, base);
            let value_exceeds_one = d.ble(two, succ_np);
            let proof_b_true = d.lemma(p.ble_eq_true_of_le, &[two, base, h_two_le_base]);
            let proof_n_true = d.lemma(p.ble_eq_true_of_le, &[two, succ_np, h1]);

            // numerator := sub (add succ_np base) 1 ≡[via succ_add] add n_prime base
            let succ_add_h = d.lemma(p.succ_add, &[n_prime, base]); // Eq (add succ_np base) (succ (add n_prime base))
            let sum_arg = d.add(succ_np, base);
            let one_c = d.num(1);
            let np_plus_base = d.add(n_prime, base);
            let succ_np_plus_base = d.succ(np_plus_base);
            let numerator_eq = d.congr(sum_arg, succ_np_plus_base, succ_add_h, &|d, x| {
                d.sub(x, one_c)
            });
            let numerator = d.sub(sum_arg, one_c);
            let quotient = d.div(numerator, base);
            let quotient_eq = d.congr(numerator, np_plus_base, numerator_eq, &|d, x| {
                d.div(x, base)
            });

            // Lt n_prime base ≡ h2 (Le (succ n_prime) base) directly.
            let mul_one_h = d.lemma(p.mul_one, &[base]);
            let base_mul_one = d.mul(base, one_c);
            let mul_one_symm = d.symm(base_mul_one, base, mul_one_h);
            let motive_x = d.eq_motive(base, &move |d, x| d.lt(n_prime, x));
            let h_lt_mul = d.transport(base, motive_x, h2, base_mul_one, mul_one_symm);
            let div_lt_1 = d.lemma(p.div_lt_of_lt_mul, &[n_prime, base, one_c, h_lt_mul]);
            let zero = d.zero();
            let div_n_prime_base = d.div(n_prime, base);
            let div_le_0 = d.lemma(p.le_of_lt_succ, &[div_n_prime_base, zero, div_lt_1]);
            let zero_le_div = d.lemma(p.zero_le, &[div_n_prime_base]);
            let div_eq_0 = d.lemma(
                p.le_antisymm,
                &[div_n_prime_base, zero, div_le_0, zero_le_div],
            );

            let h_base_pos = {
                let le_succ_1 = d.lemma(p.le_succ, &[one_c]); // Le 1 (succ 1) = Le 1 2
                d.lemma(p.le_trans, &[one_c, two, base, le_succ_1, h_two_le_base])
            };
            let add_div_right_h = d.lemma(p.add_div_right, &[n_prime, base, h_base_pos]);
            // Eq (div np_plus_base base) (add (div n_prime base) 1)
            let add_div_right_at_zero = d.congr(div_n_prime_base, zero, div_eq_0, &move |d, x| {
                let one_c = d.num(1);
                d.add(x, one_c)
            });
            // Eq (add (div n_prime base) 1) 1  (RHS `add zero one_c` defeq `one_c`)

            let quot_div_base = d.div(np_plus_base, base);
            let div_n_prime_base_plus_one = d.add(div_n_prime_base, one_c);
            let step1 = d.trans(
                quotient,
                quot_div_base,
                div_n_prime_base_plus_one,
                quotient_eq,
                add_div_right_h,
            );
            let quotient_eq_one = d.trans(
                quotient,
                div_n_prime_base_plus_one,
                one_c,
                step1,
                add_div_right_at_zero,
            );

            let helper_at_one = clog_aux_at_one_eq_zero(d, &p, base, n_prime);
            let motive_r = d.eq_motive(one_c, &move |d, x| {
                let zero = d.zero();
                let ca = clog_aux(d, &p, base, n_prime, x);
                d.eq(ca, zero)
            });
            let quotient_eq_one_symm = d.symm(quotient, one_c, quotient_eq_one);
            let recursive = clog_aux(d, &p, base, n_prime, quotient);
            let recursive_eq_zero = d.transport(
                one_c,
                motive_r,
                helper_at_one,
                quotient,
                quotient_eq_one_symm,
            );

            let stepped = d.succ(recursive);
            let stepped_eq_one = d.congr(recursive, zero, recursive_eq_zero, &|d, x| d.succ(x));

            let inner_term = d.bool_select_nat(value_exceeds_one, stepped, zero);
            let true_ = d.bool_true();
            let motive_inner = d.bool_eq_motive(true_, &move |d, x| {
                let zero = d.zero();
                let one_c = d.num(1);
                let selected = d.bool_select_nat(x, stepped, zero);
                d.eq(selected, one_c)
            });
            let reversed_n = d.bool_symm(value_exceeds_one, true_, proof_n_true);
            let stepped_eq_one_inner = d.bool_transport(
                true_,
                motive_inner,
                stepped_eq_one,
                value_exceeds_one,
                reversed_n,
            );

            let motive_outer = d.bool_eq_motive(true_, &move |d, x| {
                let zero = d.zero();
                let one_c = d.num(1);
                let selected = d.bool_select_nat(x, inner_term, zero);
                d.eq(selected, one_c)
            });
            let reversed_b = d.bool_symm(base_exceeds_one, true_, proof_b_true);
            let final_eq = d.bool_transport(
                true_,
                motive_outer,
                stepped_eq_one_inner,
                base_exceeds_one,
                reversed_b,
            );

            let inner = d.lam_fv(h2_fv, h2_ty, final_eq);
            d.lam_fv(h1_fv, h1_ty, inner)
        };

        let body = super::ops::cases_zero_succ(d, n, &motive_at, &at_n_zero, &at_n_succ);
        let final_concl = motive_at(d, n);
        let stmt = final_concl;
        let proof = body;
        (stmt, proof)
    })?;
    Ok(())
}

/// `Lt 0 n → Lt (div m n) k → Lt m (mul n k)` — the BACKWARD direction of
/// `Nat.div_mod_lt_mul_iff`, [`super::mul_order_lemmas::declare_div_lt_of_lt_mul`]'s
/// mirror image (that file has the forward direction, which holds
/// unconditionally). `Lt 0 n` is needed here and not there: at `n = 0` the
/// hypothesis `Lt (div m 0) k` says nothing about `m`, so `Lt m 0` would be
/// false in general.
fn lt_mul_of_div_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    k: ExprId,
    h_pos_n: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    // `h_pos_n : Lt 0 n` is typed for the OUTER, fixed `n` -- it cannot be
    // used directly inside `at_zero`/`at_succ`, whose terms must be well
    // typed as `motive(candidate)` for an ARBITRARY candidate (that is what
    // `Nat.rec`'s base/step arguments are), independent of what `n` actually
    // is. So positivity is abstracted into the motive too, exactly like the
    // div-bound and mul-bound hypotheses, and `h_pos_n` is applied only at
    // the very end, against the fully-general result.
    let motive = move |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let pos_ty = {
            let zero = d.zero();
            d.lt(zero, x)
        };
        let hyp_ty = {
            let div_mx = d.div(m, x);
            d.lt(div_mx, k)
        };
        let concl = {
            let mx = d.mul(x, k);
            d.lt(m, mx)
        };
        let inner = d.arrow(hyp_ty, concl);
        d.arrow(pos_ty, inner)
    };
    let split = super::ops::cases_zero_succ(
        d,
        n,
        &motive,
        &move |d| {
            let zero = d.zero();
            let pos_ty = d.lt(zero, zero);
            let pos_fv = d.fresh_fvar();
            let pos = d.kernel().fvar(pos_fv);
            let irrefl = d.lemma(p.lt_irrefl, &[zero]);
            let absurd = d.apply(irrefl, &[pos]);
            let div_m0 = d.div(m, zero);
            let hyp_ty = d.lt(div_m0, k);
            let h_fv = d.fresh_fvar();
            let m0 = d.mul(zero, k);
            let target = d.lt(m, m0);
            let elim = false_elim(d, &p, target, absurd);
            let inner = d.lam_fv(h_fv, hyp_ty, elim);
            d.lam_fv(pos_fv, pos_ty, inner)
        },
        &move |d, np| {
            let succ_np = d.succ(np);
            let pos_ty = {
                let zero = d.zero();
                d.lt(zero, succ_np)
            };
            let pos_fv = d.fresh_fvar();
            let div_ms = d.div(m, succ_np);
            let hyp_ty = d.lt(div_ms, k);
            let h_fv = d.fresh_fvar();
            let hs = d.kernel().fvar(h_fv);
            let mod_ms = d.modulo(m, succ_np);
            let h_exec = d.lemma(p.div_mod_exec, &[np, m]);
            let iff_fn = d.lemma(p.div_mod_lt_mul_iff, &[succ_np, m, div_ms, mod_ms, k]);
            let the_iff = d.apply(iff_fn, &[h_exec]);
            let succ_np_k = d.mul(succ_np, k);
            let lt_mk = d.lt(m, succ_np_k);
            let backward = iff_reverse(d, lt_mk, hyp_ty, the_iff);
            let result = d.apply(backward, &[hs]);
            let inner = d.lam_fv(h_fv, hyp_ty, result);
            d.lam_fv(pos_fv, pos_ty, inner)
        },
    );
    let step1 = d.apply(split, &[h_pos_n]);
    d.apply(step1, &[h])
}

/// `Lt 1 base → Le value fuel → Eq (logAux base fuel value) 0 → Lt value
/// base` — the CONVERSE of [`log_aux_lt_eq_zero`]: fuel-generalized (`Le
/// value fuel` is "enough fuel"), induction-free (`cases_zero_succ` on
/// `fuel` alone). At `fuel = 0`: `Le value 0` forces `value = 0`
/// (`le_antisymm` + `zero_le`), and `Lt 0 base` follows from `Lt 1 base`
/// (`Le 2 base` chained through `le_succ 1 : Le 1 2` via `le_trans`). At
/// `fuel = succ f'`: split `Nat.lt_or_ge value base` — the `Lt value base`
/// side is immediate; the `Le base value` side derives a contradiction with
/// the `Eq (…) 0` hypothesis DIRECTLY (both guard cuts known true via
/// `ble_eq_true_of_le`, two `bool_transport`s peel the STUCK selector down
/// to `Eq (succ …) 0`, refuted by `succ_ne_zero`) — `Le value fuel` is not
/// needed in this branch, since the guard tests do not depend on `fuel`'s
/// shape once it is known `succ`-shaped.
fn log_aux_eq_zero_imp_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    value: ExprId,
    fuel: ExprId,
    h1: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let motive = move |d: &mut NatDev<'_>, fc: ExprId| -> ExprId {
        let h2_ty = d.le(value, fc);
        let h3_ty = {
            let la = log_aux(d, &p, base, fc, value);
            let zero = d.zero();
            d.eq(la, zero)
        };
        let concl = d.lt(value, base);
        let inner = d.arrow(h3_ty, concl);
        d.arrow(h2_ty, inner)
    };
    let at_zero = move |d: &mut NatDev<'_>| -> ExprId {
        let zero = d.zero();
        let h2_ty = d.le(value, zero);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let h3_ty = {
            let la = log_aux(d, &p, base, zero, value);
            d.eq(la, zero)
        };
        let h3_fv = d.fresh_fvar();

        let zero_le_value = d.lemma(p.zero_le, &[value]);
        let value_eq_zero = d.lemma(p.le_antisymm, &[value, zero, h2, zero_le_value]);

        let one = d.num(1);
        let le_succ_1 = d.lemma(p.le_succ, &[one]); // Le 1 2
        let le_1_base = d.lemma(p.le_trans, &[one, two, base, le_succ_1, h1]); // Le 1 base = Lt 0 base
        let value_eq_zero_symm = d.symm(value, zero, value_eq_zero);
        let motive_v = d.eq_motive(zero, &move |d, x| d.lt(x, base));
        let target = d.transport(zero, motive_v, le_1_base, value, value_eq_zero_symm);

        let inner = d.lam_fv(h3_fv, h3_ty, target);
        d.lam_fv(h2_fv, h2_ty, inner)
    };
    let at_succ = move |d: &mut NatDev<'_>, f_prime: ExprId| -> ExprId {
        let succ_fp = d.succ(f_prime);
        let h2_ty = d.le(value, succ_fp);
        let h2_fv = d.fresh_fvar();
        let h3_ty = {
            let la = log_aux(d, &p, base, succ_fp, value);
            let zero = d.zero();
            d.eq(la, zero)
        };
        let h3_fv = d.fresh_fvar();
        let h3 = d.kernel().fvar(h3_fv);

        let concl = d.lt(value, base);
        let dichotomy = d.lemma(p.lt_or_ge, &[value, base]); // Or (Lt value base) (Le base value)
        let lt_ty = d.lt(value, base);
        let ge_ty = d.le(base, value);

        let left_branch = {
            let hlt_fv = d.fresh_fvar();
            let hlt = d.kernel().fvar(hlt_fv);
            d.lam_fv(hlt_fv, lt_ty, hlt)
        };
        let right_branch = move |d: &mut NatDev<'_>| -> ExprId {
            let hge_fv = d.fresh_fvar();
            let hge = d.kernel().fvar(hge_fv);

            let proof_base_true = d.lemma(p.ble_eq_true_of_le, &[two, base, h1]);
            let proof_ge_true = d.lemma(p.ble_eq_true_of_le, &[base, value, hge]);
            let base_exceeds_one = d.ble(two, base);
            let base_le_value = d.ble(base, value);
            let true_ = d.bool_true();

            // Peel OUTER (base_le_value) first, then INNER (base_exceeds_one).
            let zero = d.zero();
            let quotient = d.div(value, base);
            let recursive = log_aux(d, &p, base, f_prime, quotient);
            let stepped = d.succ(recursive);
            let inner_term = d.bool_select_nat(base_exceeds_one, stepped, zero);

            let motive_outer = d.bool_eq_motive(base_le_value, &move |d, x| {
                let zero = d.zero();
                let selected = d.bool_select_nat(x, inner_term, zero);
                d.eq(selected, zero)
            });
            let step1 = d.bool_transport(base_le_value, motive_outer, h3, true_, proof_ge_true);
            // step1 : Eq inner_term 0

            let motive_inner = d.bool_eq_motive(base_exceeds_one, &move |d, x| {
                let zero = d.zero();
                let selected = d.bool_select_nat(x, stepped, zero);
                d.eq(selected, zero)
            });
            let step2 = d.bool_transport(
                base_exceeds_one,
                motive_inner,
                step1,
                true_,
                proof_base_true,
            );
            // step2 : Eq stepped 0 = Eq (succ recursive) 0

            let contradiction = d.lemma(p.succ_ne_zero, &[recursive, step2]); // False
            let elim = false_elim(d, &p, concl, contradiction);
            d.lam_fv(hge_fv, ge_ty, elim)
        };
        let right_branch_term = right_branch(d);
        let case_result = or_cases(
            d,
            lt_ty,
            ge_ty,
            concl,
            left_branch,
            right_branch_term,
            dichotomy,
        );

        let inner = d.lam_fv(h3_fv, h3_ty, case_result);
        d.lam_fv(h2_fv, h2_ty, inner)
    };
    super::ops::cases_zero_succ(d, fuel, &motive, &at_zero, &at_succ)
}

/// `Lt value base → Eq (logAux base fuel value) 0`, for ANY `fuel` —
/// [`super::log::NatPrelude::log_of_lt`]'s step-case technique
/// (`ble_eq_false_of_lt` + `bool_transport` collapses the OUTER guard,
/// `logAux`'s only cut that depends on `value` vs `base`), generalized from
/// the diagonal `fuel = value` to an arbitrary `fuel`: the mechanism never
/// looks at `fuel`'s shape past knowing it is `succ`-shaped, so nothing here
/// is specific to the diagonal instance.
fn log_aux_lt_eq_zero(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    fuel: ExprId,
    value: ExprId,
    h_lt: ExprId,
) -> ExprId {
    let p = *p;
    let motive = move |d: &mut NatDev<'_>, fc: ExprId| -> ExprId {
        let la = log_aux(d, &p, base, fc, value);
        let zero = d.zero();
        d.eq(la, zero)
    };
    super::ops::cases_zero_succ(
        d,
        fuel,
        &motive,
        &|d| {
            let zero = d.zero();
            d.refl(zero)
        },
        &move |d, f_prime| {
            let false_ = d.bool_false();
            let refuted = d.lemma(p.ble_eq_false_of_lt, &[base, value, h_lt]);
            let test = d.ble(base, value);
            let reversed = d.bool_symm(test, false_, refuted);
            let two = d.num(2);
            let quotient = d.div(value, base);
            let recursive = log_aux(d, &p, base, f_prime, quotient);
            let stepped = d.succ(recursive);
            let zero = d.zero();
            let base_exceeds_one = d.ble(two, base);
            let step_taken = d.bool_select_nat(base_exceeds_one, stepped, zero);
            let motive_false = d.bool_eq_motive(false_, &move |d, selector| {
                let zero = d.zero();
                let selected = d.bool_select_nat(selector, step_taken, zero);
                d.eq(selected, zero)
            });
            let refl_case = d.refl(zero);
            d.bool_transport(false_, motive_false, refl_case, test, reversed)
        },
    )
}

/// `Eq (log base n) 1 → Lt 1 base` — if `base ≤ 1`, `log_of_left_le_one`
/// gives `Eq (log base n) 0` at THIS `n`, contradicting the hypothesis (`Eq
/// 1 0` via `trans`/`symm`, refuted by `succ_ne_zero`).
fn derive_one_lt_base_from_log_eq_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    n: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let target = d.lt(one, base);
    let dichotomy = d.lemma(p.lt_or_ge, &[one, base]); // Or (Lt 1 base) (Le base 1)
    let lt_ty = d.lt(one, base);
    let le_ty = d.le(base, one);

    let left_branch = {
        let hlt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(hlt_fv);
        d.lam_fv(hlt_fv, lt_ty, hlt)
    };
    let right_branch = {
        let hle_fv = d.fresh_fvar();
        let hle = d.kernel().fvar(hle_fv);
        let zero = d.zero();
        let all_n = d.lemma(p.log_of_left_le_one, &[base, hle]); // Pi n, Eq (log base n) 0
        let log_eq_0 = d.apply(all_n, &[n]);
        let log_n = log(d, &p, base, n);
        let h_symm = d.symm(log_n, one, h); // Eq 1 (log base n)
        let one_eq_0 = d.trans(one, log_n, zero, h_symm, log_eq_0); // Eq 1 0
        let contradiction = d.lemma(p.succ_ne_zero, &[zero, one_eq_0]);
        let elim = false_elim(d, &p, target, contradiction);
        d.lam_fv(hle_fv, le_ty, elim)
    };
    or_cases(
        d,
        lt_ty,
        le_ty,
        target,
        left_branch,
        right_branch,
        dichotomy,
    )
}

/// `Le base n → Lt n (mul base base) → Lt 1 base` — used by
/// `Nat.log_eq_one_iff'`'s `mpr`, which is not GIVEN `1 < base` directly
/// (unlike `Nat.log_eq_one_iff`). If `base ≤ 1`: `base*base ≤ base*1 = base
/// ≤ 1` (`mul_le_mul_left` + `mul_one` + `le_trans`), so `n < base*base ≤ 1`
/// gives `n = 0`; combined with `base ≤ n` that forces `base = 0`, and
/// substituting `base = 0` into `Lt n (mul base base)` gives `Lt n 0`,
/// refuted by `not_lt_zero`.
fn derive_one_lt_base_from_bounds(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    n: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let target = d.lt(one, base);
    let dichotomy = d.lemma(p.lt_or_ge, &[one, base]);
    let lt_ty = d.lt(one, base);
    let le_ty = d.le(base, one);

    let left_branch = {
        let hlt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(hlt_fv);
        d.lam_fv(hlt_fv, lt_ty, hlt)
    };
    let right_branch = {
        let hle_fv = d.fresh_fvar();
        let hle = d.kernel().fvar(hle_fv);

        let base_sq = d.mul(base, base);
        let base_one = d.mul(base, one);
        let chain1 = d.lemma(p.mul_le_mul_left, &[base, base, one, hle]); // Le base_sq base_one
        let mul_one_h = d.lemma(p.mul_one, &[base]); // Eq base_one base
        let motive1 = d.eq_motive(base_one, &move |d, x| {
            let base_sq = d.mul(base, base);
            d.le(base_sq, x)
        });
        let chain1_fixed = d.transport(base_one, motive1, chain1, base, mul_one_h); // Le base_sq base
        let chain2 = d.lemma(p.le_trans, &[base_sq, base, one, chain1_fixed, hle]); // Le base_sq 1

        let n_lt_1 = d.lemma(p.lt_of_lt_of_le, &[n, base_sq, one, h2, chain2]); // Lt n 1
        let zero = d.zero();
        let n_le_0 = d.lemma(p.le_of_lt_succ, &[n, zero, n_lt_1]);
        let zero_le_n = d.lemma(p.zero_le, &[n]);
        let n_eq_0 = d.lemma(p.le_antisymm, &[n, zero, n_le_0, zero_le_n]); // Eq n 0

        let motive_n = d.eq_motive(n, &move |d, x| d.le(base, x));
        let h1_at_zero = d.transport(n, motive_n, h1, zero, n_eq_0); // Le base 0
        let zero_le_base = d.lemma(p.zero_le, &[base]);
        let base_eq_0 = d.lemma(p.le_antisymm, &[base, zero, h1_at_zero, zero_le_base]); // Eq base 0

        let motive_base = d.eq_motive(base, &move |d, x| {
            let mxx = d.mul(x, x);
            d.lt(n, mxx)
        });
        let h2_at_zero = d.transport(base, motive_base, h2, zero, base_eq_0); // Lt n (mul 0 0), defeq Lt n 0
        let not_lt = d.lemma(p.not_lt_zero, &[n]);
        let contradiction = d.apply(not_lt, &[h2_at_zero]);
        let elim = false_elim(d, &p, target, contradiction);
        d.lam_fv(hle_fv, le_ty, elim)
    };
    or_cases(
        d,
        lt_ty,
        le_ty,
        target,
        left_branch,
        right_branch,
        dichotomy,
    )
}

/// `Eq (log base n) 1 → Le base n` — case-split `Nat.lt_or_ge n base`; the
/// `Lt n base` side is refuted by `log_of_lt` (`Eq (log base n) 0`,
/// contradicting `h` the same way [`derive_one_lt_base_from_log_eq_one`]
/// does), the `Le base n` side is the identity.
fn log_eq_one_derive_base_le_n(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    n: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let target = d.le(base, n);
    let dichotomy = d.lemma(p.lt_or_ge, &[n, base]); // Or (Lt n base) (Le base n)
    let lt_ty = d.lt(n, base);
    let ge_ty = d.le(base, n);

    let left_branch = {
        let hlt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(hlt_fv);
        let zero = d.zero();
        let log_eq_0 = d.lemma(p.log_of_lt, &[base, n, hlt]);
        let log_n = log(d, &p, base, n);
        let h_symm = d.symm(log_n, one, h);
        let one_eq_0 = d.trans(one, log_n, zero, h_symm, log_eq_0);
        let contradiction = d.lemma(p.succ_ne_zero, &[zero, one_eq_0]);
        let elim = false_elim(d, &p, target, contradiction);
        d.lam_fv(hlt_fv, lt_ty, elim)
    };
    let right_branch = {
        let hge_fv = d.fresh_fvar();
        let hge = d.kernel().fvar(hge_fv);
        d.lam_fv(hge_fv, ge_ty, hge)
    };
    or_cases(
        d,
        lt_ty,
        ge_ty,
        target,
        left_branch,
        right_branch,
        dichotomy,
    )
}

/// `Lt 1 base → Le base n → Eq (log base n) 1 → Lt n (mul base base)` — the
/// hard direction. `cases_zero_succ` on `n` (the `n = 0` branch is refuted
/// by `Le base 0` contradicting `Lt 1 base`); at `n = succ n'`, peel `h`
/// (general → specific, the OPPOSITE direction from building — two
/// `d.transport`s using the FORWARD `ble_eq_true_of_le` evidence, peeling
/// the OUTER cut `Le base n` first since it wraps the inner one) down to
/// `Eq (succ (logAux base n' quotient)) 1`, `succ_injective` to `Eq
/// (logAux base n' quotient) 0`, [`log_aux_eq_zero_imp_lt`] (fed
/// `Le quotient n'` from `div_lt_self` + `le_of_lt_succ`) to `Lt quotient
/// base`, then [`lt_mul_of_div_lt`] to the goal.
fn log_eq_one_derive_sq_bound(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    n: ExprId,
    h1: ExprId,
    h_base_le_n: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let motive = move |d: &mut NatDev<'_>, nc: ExprId| -> ExprId {
        let h2_ty = d.le(base, nc);
        let h3_ty = {
            let lg = log(d, &p, base, nc);
            let one = d.num(1);
            d.eq(lg, one)
        };
        let concl = {
            let bb = d.mul(base, base);
            d.lt(nc, bb)
        };
        let inner = d.arrow(h3_ty, concl);
        d.arrow(h2_ty, inner)
    };
    let at_zero = move |d: &mut NatDev<'_>| -> ExprId {
        let zero = d.zero();
        let h2_ty = d.le(base, zero);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let h3_ty = {
            let lg = log(d, &p, base, zero);
            let one = d.num(1);
            d.eq(lg, one)
        };
        let h3_fv = d.fresh_fvar();

        let le_2_base = h1; // Lt 1 base = Le 2 base
        let le_2_zero = d.lemma(p.le_trans, &[two, base, zero, le_2_base, h2]);
        let one = d.num(1);
        let contradiction = d.lemma(p.not_succ_le_zero, &[one, le_2_zero]);
        let concl = {
            let bb = d.mul(base, base);
            d.lt(zero, bb)
        };
        let elim = false_elim(d, &p, concl, contradiction);
        let inner = d.lam_fv(h3_fv, h3_ty, elim);
        d.lam_fv(h2_fv, h2_ty, inner)
    };
    let at_succ = move |d: &mut NatDev<'_>, n_prime: ExprId| -> ExprId {
        let succ_np = d.succ(n_prime);
        let h2_ty = d.le(base, succ_np);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let one = d.num(1);
        let h3_ty = {
            let lg = log(d, &p, base, succ_np);
            d.eq(lg, one)
        };
        let h3_fv = d.fresh_fvar();
        let h3 = d.kernel().fvar(h3_fv);

        let base_exceeds_one = d.ble(two, base);
        let base_fits = d.ble(base, succ_np);
        let proof_inner_true = d.lemma(p.ble_eq_true_of_le, &[two, base, h1]);
        let proof_outer_true = d.lemma(p.ble_eq_true_of_le, &[base, succ_np, h2]);
        let true_ = d.bool_true();

        let quotient = d.div(succ_np, base);
        let recursive = log_aux(d, &p, base, n_prime, quotient);
        let stepped = d.succ(recursive);
        let zero_ = d.zero();
        let inner_term = d.bool_select_nat(base_exceeds_one, stepped, zero_);

        // Peel OUTER (base_fits) first.
        let motive_outer = d.bool_eq_motive(base_fits, &move |d, x| {
            let zero = d.zero();
            let one = d.num(1);
            let selected = d.bool_select_nat(x, inner_term, zero);
            d.eq(selected, one)
        });
        let step1 = d.bool_transport(base_fits, motive_outer, h3, true_, proof_outer_true);
        // step1 : Eq inner_term 1

        let motive_inner = d.bool_eq_motive(base_exceeds_one, &move |d, x| {
            let zero = d.zero();
            let one = d.num(1);
            let selected = d.bool_select_nat(x, stepped, zero);
            d.eq(selected, one)
        });
        let step2 = d.bool_transport(
            base_exceeds_one,
            motive_inner,
            step1,
            true_,
            proof_inner_true,
        );
        // step2 : Eq stepped 1 = Eq (succ recursive) 1

        let zero = d.zero();
        let recursive_eq_zero = d.lemma(p.succ_injective, &[recursive, zero, step2]);

        let pos_succ_np = d.lemma(p.zero_lt_succ, &[n_prime]);
        let div_lt_succ_np = d.lemma(p.div_lt_self, &[succ_np, base, pos_succ_np, h1]);
        let quotient_le_np = d.lemma(p.le_of_lt_succ, &[quotient, n_prime, div_lt_succ_np]);

        let quotient_lt_base = log_aux_eq_zero_imp_lt_apply(
            d,
            &p,
            base,
            quotient,
            n_prime,
            h1,
            quotient_le_np,
            recursive_eq_zero,
        );

        let base_pos = {
            let le_succ_1 = d.lemma(p.le_succ, &[one]);
            d.lemma(p.le_trans, &[one, two, base, le_succ_1, h1])
        };
        let final_bound = lt_mul_of_div_lt(d, &p, succ_np, base, base, base_pos, quotient_lt_base);

        let inner = d.lam_fv(h3_fv, h3_ty, final_bound);
        d.lam_fv(h2_fv, h2_ty, inner)
    };
    let body = super::ops::cases_zero_succ(d, n, &motive, &at_zero, &at_succ);
    let step1 = d.apply(body, &[h_base_le_n]);
    d.apply(step1, &[h])
}

/// [`log_aux_eq_zero_imp_lt`] applied to its three hypotheses, spelled as a
/// function to keep call sites (which already have all five arguments in
/// hand) from re-deriving the intermediate arrow terms.
#[allow(clippy::too_many_arguments)]
fn log_aux_eq_zero_imp_lt_apply(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    value: ExprId,
    fuel: ExprId,
    h1: ExprId,
    h_le_fuel: ExprId,
    h_eq_zero: ExprId,
) -> ExprId {
    let body = log_aux_eq_zero_imp_lt(d, p, base, value, fuel, h1);
    let step1 = d.apply(body, &[h_le_fuel]);
    d.apply(step1, &[h_eq_zero])
}

/// `Lt 1 base → Le base n → Lt n (mul base base) → Eq (log base n) 1` — the
/// `mpr` core, shared by both `log_eq_one_iff` mirrors.
/// [`declare_log_pos`]'s exact unfolding recipe (`cases_zero_succ` on `n`,
/// both guard cuts known true, two `bool_transport`s reduced→general,
/// INNER first then OUTER — `log`'s nesting, the opposite of `clog`'s),
/// aimed at `Eq (_, 1)`. The recursive quotient's `logAux … = 0` comes from
/// `div_lt_of_lt_mul` (forward direction, already in the prelude) plus
/// [`log_aux_lt_eq_zero`].
fn log_eq_one_of_bounds(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    n: ExprId,
    h1: ExprId,
    h_base_le_n: ExprId,
    h_sq: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let motive = move |d: &mut NatDev<'_>, nc: ExprId| -> ExprId {
        let h2_ty = d.le(base, nc);
        let h3_ty = {
            let bb = d.mul(base, base);
            d.lt(nc, bb)
        };
        let concl = {
            let lg = log(d, &p, base, nc);
            let one = d.num(1);
            d.eq(lg, one)
        };
        let inner = d.arrow(h3_ty, concl);
        d.arrow(h2_ty, inner)
    };
    let at_zero = move |d: &mut NatDev<'_>| -> ExprId {
        let zero = d.zero();
        let h2_ty = d.le(base, zero);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let h3_ty = {
            let bb = d.mul(base, base);
            d.lt(zero, bb)
        };
        let h3_fv = d.fresh_fvar();

        let le_2_zero = d.lemma(p.le_trans, &[two, base, zero, h1, h2]);
        let one = d.num(1);
        let contradiction = d.lemma(p.not_succ_le_zero, &[one, le_2_zero]);
        let concl = {
            let lg = log(d, &p, base, zero);
            d.eq(lg, one)
        };
        let elim = false_elim(d, &p, concl, contradiction);
        let inner = d.lam_fv(h3_fv, h3_ty, elim);
        d.lam_fv(h2_fv, h2_ty, inner)
    };
    let at_succ = move |d: &mut NatDev<'_>, n_prime: ExprId| -> ExprId {
        let succ_np = d.succ(n_prime);
        let h2_ty = d.le(base, succ_np);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let h3_ty = {
            let bb = d.mul(base, base);
            d.lt(succ_np, bb)
        };
        let h3_fv = d.fresh_fvar();
        let h3 = d.kernel().fvar(h3_fv);

        let quotient = d.div(succ_np, base);
        let quotient_lt_base = d.lemma(p.div_lt_of_lt_mul, &[succ_np, base, base, h3]);
        let recursive_eq_zero =
            log_aux_lt_eq_zero(d, &p, base, n_prime, quotient, quotient_lt_base);
        let recursive = log_aux(d, &p, base, n_prime, quotient);
        let zero = d.zero();
        let stepped_eq_one = d.congr(recursive, zero, recursive_eq_zero, &|d, x| d.succ(x));
        let stepped = d.succ(recursive);

        let base_exceeds_one = d.ble(two, base);
        let base_fits = d.ble(base, succ_np);
        let proof_inner_true = d.lemma(p.ble_eq_true_of_le, &[two, base, h1]);
        let proof_outer_true = d.lemma(p.ble_eq_true_of_le, &[base, succ_np, h2]);
        let true_ = d.bool_true();

        // Inner cut first (2 <= base, fixed), then outer (base <= n, varies).
        let inner_term = d.bool_select_nat(base_exceeds_one, stepped, zero);
        let motive_inner = d.bool_eq_motive(true_, &move |d, x| {
            let zero = d.zero();
            let one = d.num(1);
            let selected = d.bool_select_nat(x, stepped, zero);
            d.eq(selected, one)
        });
        let reversed_inner = d.bool_symm(base_exceeds_one, true_, proof_inner_true);
        let step_inner = d.bool_transport(
            true_,
            motive_inner,
            stepped_eq_one,
            base_exceeds_one,
            reversed_inner,
        );

        let motive_outer = d.bool_eq_motive(true_, &move |d, x| {
            let zero = d.zero();
            let one = d.num(1);
            let selected = d.bool_select_nat(x, inner_term, zero);
            d.eq(selected, one)
        });
        let reversed_outer = d.bool_symm(base_fits, true_, proof_outer_true);
        let final_eq = d.bool_transport(true_, motive_outer, step_inner, base_fits, reversed_outer);

        let inner = d.lam_fv(h3_fv, h3_ty, final_eq);
        d.lam_fv(h2_fv, h2_ty, inner)
    };
    let body = super::ops::cases_zero_succ(d, n, &motive, &at_zero, &at_succ);
    let step1 = d.apply(body, &[h_base_le_n]);
    d.apply(step1, &[h_sq])
}

/// `Nat.log_eq_one_iff' : ∀ {b n}, Eq (log b n) 1 ↔ (Le b n ∧ Lt n (mul b
/// b))` (`Mathlib`: `Nat.log_eq_one_iff'`) — unlike the unprimed form,
/// `1 < b` is not given; `mpr` derives it from the bounds
/// ([`derive_one_lt_base_from_bounds`]), `mp` derives it from `h` itself
/// ([`derive_one_lt_base_from_log_eq_one`]) purely as a tool, since it is
/// not part of this statement's conclusion.
pub(super) fn declare_log_eq_one_iff_prime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.log_eq_one_iff_prime, 2, &|d, values| {
        let (base, n) = (values[0], values[1]);
        let one = d.num(1);
        let lg = log(d, &p, base, n);
        let lhs_ty = d.eq(lg, one);
        let base_le_n = d.le(base, n);
        let bb = d.mul(base, base);
        let n_lt_sq = d.lt(n, bb);
        let rhs_ty = d.const_app(p.logic.and, &[base_le_n, n_lt_sq]);
        let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let h_one_lt_base = derive_one_lt_base_from_log_eq_one(d, &p, base, n, h);
            let h_base_le_n = log_eq_one_derive_base_le_n(d, &p, base, n, h);
            let h_sq = log_eq_one_derive_sq_bound(d, &p, base, n, h_one_lt_base, h_base_le_n, h);
            let pair = d.const_app(p.logic.and_intro, &[base_le_n, n_lt_sq, h_base_le_n, h_sq]);
            d.lam_fv(h_fv, lhs_ty, pair)
        };
        let mpr = {
            let hp_fv = d.fresh_fvar();
            let hp = d.kernel().fvar(hp_fv);
            let h1 = and_left(d, base_le_n, n_lt_sq, hp);
            let h2 = and_right(d, base_le_n, n_lt_sq, hp);
            let h_one_lt_base = derive_one_lt_base_from_bounds(d, &p, base, n, h1, h2);
            let result = log_eq_one_of_bounds(d, &p, base, n, h_one_lt_base, h1, h2);
            d.lam_fv(hp_fv, rhs_ty, result)
        };
        let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.log_eq_one_iff : ∀ {b n}, Eq (log b n) 1 ↔ (Lt n (mul b b) ∧ (Lt 1 b
/// ∧ Le b n))` (`Mathlib`: `Nat.log_eq_one_iff`) —
/// [`declare_log_eq_one_iff_prime`]'s exact core
/// ([`log_eq_one_derive_base_le_n`], [`log_eq_one_derive_sq_bound`],
/// [`log_eq_one_of_bounds`]), repackaged into Mathlib's stronger hypothesis
/// set (`1 < b` explicit) and its different `And` nesting/order.
pub(super) fn declare_log_eq_one_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.log_eq_one_iff, 2, &|d, values| {
        let (base, n) = (values[0], values[1]);
        let one = d.num(1);
        let lg = log(d, &p, base, n);
        let lhs_ty = d.eq(lg, one);
        let bb = d.mul(base, base);
        let n_lt_sq = d.lt(n, bb);
        let one_lt_base = d.lt(one, base);
        let base_le_n = d.le(base, n);
        let inner_and = d.const_app(p.logic.and, &[one_lt_base, base_le_n]);
        let rhs_ty = d.const_app(p.logic.and, &[n_lt_sq, inner_and]);
        let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let h_one_lt_base = derive_one_lt_base_from_log_eq_one(d, &p, base, n, h);
            let h_base_le_n = log_eq_one_derive_base_le_n(d, &p, base, n, h);
            let h_sq = log_eq_one_derive_sq_bound(d, &p, base, n, h_one_lt_base, h_base_le_n, h);
            let inner_pair = d.const_app(
                p.logic.and_intro,
                &[one_lt_base, base_le_n, h_one_lt_base, h_base_le_n],
            );
            let pair = d.const_app(p.logic.and_intro, &[n_lt_sq, inner_and, h_sq, inner_pair]);
            d.lam_fv(h_fv, lhs_ty, pair)
        };
        let mpr = {
            let hp_fv = d.fresh_fvar();
            let hp = d.kernel().fvar(hp_fv);
            let h_sq = and_left(d, n_lt_sq, inner_and, hp);
            let inner = and_right(d, n_lt_sq, inner_and, hp);
            let h_one_lt_base = and_left(d, one_lt_base, base_le_n, inner);
            let h_base_le_n = and_right(d, one_lt_base, base_le_n, inner);
            let result = log_eq_one_of_bounds(d, &p, base, n, h_one_lt_base, h_base_le_n, h_sq);
            d.lam_fv(hp_fv, rhs_ty, result)
        };
        let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Eq (div (mul m base) base) m`, given `pos_base : Lt zero base`.
///
/// Via `Nat.add_mul_div_right` at `x := zero`: `(zero + mul m base) / base =
/// zero / base + m`. `zero_add`/`zero_div` clear the padding on each side,
/// leaving `div (mul m base) base = m`.
fn mul_div_cancel_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    pos_base: ExprId,
    m: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let scaled = d.mul(m, base);
    let padded = d.add(zero, scaled);
    let target = d.div(scaled, base);
    let div_padded = d.div(padded, base);

    let zero_add_scaled = d.lemma(p.zero_add, &[scaled]);
    let padded_to_scaled = d.congr(padded, scaled, zero_add_scaled, &move |d, x| d.div(x, base));
    let step_a = d.symm(div_padded, target, padded_to_scaled);

    let step_b = d.lemma(p.add_mul_div_right, &[zero, m, base, pos_base]);
    let div_zero_base = d.div(zero, base);
    let shifted_rhs = d.add(div_zero_base, m);

    let zero_div_base = d.lemma(p.zero_div, &[base]);
    let step_c = d.congr(div_zero_base, zero, zero_div_base, &move |d, x| d.add(x, m));
    let zero_plus_m = d.add(zero, m);

    let step_d = d.lemma(p.zero_add, &[m]);

    let (_, proof) = d.chain(
        target,
        &[
            (div_padded, step_a),
            (shifted_rhs, step_b),
            (zero_plus_m, step_c),
            (m, step_d),
        ],
    );
    proof
}

/// `Eq (log base (succ n_prime)) (succ (logAux base n_prime quotient))`,
/// `quotient := div (succ n_prime) base`, given `h1 : Lt one base`, `h2 : Le
/// base (succ n_prime)`.
///
/// [`declare_log_pos`]'s `at_n_succ` branch, unchanged in its guard-collapse
/// structure, retargeted from `Lt zero _` to an `Eq` against the raw
/// `succ`-row unfold. Returns `(quotient, recursive, eq_proof)`.
fn log_succ_unfold(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    n_prime: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let p = *p;
    let succ_n_prime = d.succ(n_prime);
    let two = d.num(2);
    let base_exceeds_one = d.ble(two, base);
    let base_fits = d.ble(base, succ_n_prime);
    let proof_b_true = d.lemma(p.ble_eq_true_of_le, &[two, base, h1]);
    let proof_n_true = d.lemma(p.ble_eq_true_of_le, &[base, succ_n_prime, h2]);

    let quotient = d.div(succ_n_prime, base);
    let recursive = log_aux(d, &p, base, n_prime, quotient);
    let stepped = d.succ(recursive);
    let zero = d.zero();
    let true_ = d.bool_true();

    let inner_term = d.bool_select_nat(base_exceeds_one, stepped, zero);
    let motive_inner = d.bool_eq_motive(true_, &move |d, x| {
        let zero = d.zero();
        let selected = d.bool_select_nat(x, stepped, zero);
        d.eq(selected, stepped)
    });
    let refl_stepped = d.refl(stepped);
    let reversed_b = d.bool_symm(base_exceeds_one, true_, proof_b_true);
    let inner_eq = d.bool_transport(
        true_,
        motive_inner,
        refl_stepped,
        base_exceeds_one,
        reversed_b,
    );

    let motive_outer = d.bool_eq_motive(true_, &move |d, x| {
        let zero = d.zero();
        let selected = d.bool_select_nat(x, inner_term, zero);
        d.eq(selected, stepped)
    });
    let reversed_n = d.bool_symm(base_fits, true_, proof_n_true);
    let outer_eq = d.bool_transport(true_, motive_outer, inner_eq, base_fits, reversed_n);

    (quotient, recursive, outer_eq)
}

/// `log_aux_agree_of_fuel base pos_base base_gt1 fuel1 : ∀ a b c, Le a fuel1
/// → Le a c → Eq (logAux base fuel1 a) (logAux base c a)`.
///
/// [`super::rec_agreement::declare_land_aux_agree_of_fuel`]'s
/// `agree_by_double_fuel_induction` instantiation, transported from
/// `landAux`'s structural `m = 0` guard to `logAux`'s order-comparison guard
/// `ble base value`. The base case (`fuel1 = 0`) and the STEP case's `a = 0`
/// sub-branch both close by [`super::log_clog_order::log_aux_zero_value`],
/// applied at whichever fuel is in play — that lemma already carries the
/// "any fuel" generality this induction needs there, so no local analogue of
/// `land_aux_zero_left_any_fuel` had to be built.
///
/// The STEP case's `a = succ predecessor` sub-branch does NOT need to decide
/// `ble base (succ predecessor)`'s truth value (unlike `landAux`'s `m = 0`
/// guard, which the case split on `m` decides for free): both fuels being
/// compared (`sk := succ k` and `c`, rewritten to `succ (pred c)` once
/// `div_lt_self` shows `c` positive) are literal successors once `c`'s
/// positivity is established, so `logAux`'s OWN `Nat.rec` reduces both sides
/// against the IDENTICAL guard term, and `d.congr` isolates the only
/// differing subterm — the recursive call — which the IH (applied at the
/// shared quotient, itself bounded below both fuels via `div_lt_self` +
/// `le_of_lt_succ`) closes directly.
fn log_aux_agree_of_fuel(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    pos_base: ExprId,
    base_gt1: ExprId,
    fuel1: ExprId,
) -> ExprId {
    let p = *p;

    let statement =
        move |d: &mut NatDev<'_>, fuel: ExprId, a: ExprId, _b: ExprId, c: ExprId| -> ExprId {
            let bound1 = d.le(a, fuel);
            let bound2 = d.le(a, c);
            let lhs = log_aux(d, &p, base, fuel, a);
            let rhs = log_aux(d, &p, base, c, a);
            let concl = d.eq(lhs, rhs);
            let inner = d.arrow(bound2, concl);
            d.arrow(bound1, inner)
        };

    let base_case = move |d: &mut NatDev<'_>, a: ExprId, _b: ExprId, c: ExprId| -> ExprId {
        let zero = d.zero();
        let bound1_ty = d.le(a, zero);
        let bound2_ty = d.le(a, c);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();

        let zero_le_a = d.lemma(p.zero_le, &[a]);
        let a_eq_zero = d.lemma(p.le_antisymm, &[a, zero, h1, zero_le_a]);

        let left_term = log_aux(d, &p, base, zero, a);
        let right_term = log_aux(d, &p, base, c, a);

        let left_at_zero = log_aux(d, &p, base, zero, zero);
        let left_congr = d.congr(a, zero, a_eq_zero, &move |d, x| {
            log_aux(d, &p, base, zero, x)
        });
        let left_refl = d.refl(zero);
        let (_, left_is_zero) =
            d.chain(left_term, &[(left_at_zero, left_congr), (zero, left_refl)]);

        let right_at_zero = log_aux(d, &p, base, c, zero);
        let right_congr = d.congr(a, zero, a_eq_zero, &move |d, x| log_aux(d, &p, base, c, x));
        let right_is_zero_at_zero =
            super::log_clog_order::log_aux_zero_value(d, &p, base, c, pos_base);
        let (_, right_is_zero) = d.chain(
            right_term,
            &[(right_at_zero, right_congr), (zero, right_is_zero_at_zero)],
        );

        let right_is_zero_rev = d.symm(right_term, zero, right_is_zero);
        let body = d.trans(left_term, zero, right_term, left_is_zero, right_is_zero_rev);

        let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
        d.lam_fv(h1_fv, bound1_ty, with_h2)
    };

    let step_case = move |d: &mut NatDev<'_>,
                          k: ExprId,
                          ih: ExprId,
                          a: ExprId,
                          _b: ExprId,
                          c: ExprId|
          -> ExprId {
        let sk = d.succ(k);
        let goal_at = move |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let bound1 = d.le(candidate, sk);
            let bound2 = d.le(candidate, c);
            let lhs = log_aux(d, &p, base, sk, candidate);
            let rhs = log_aux(d, &p, base, c, candidate);
            let concl = d.eq(lhs, rhs);
            let inner = d.arrow(bound2, concl);
            d.arrow(bound1, inner)
        };

        super::ops::cases_zero_succ(
            d,
            a,
            &goal_at,
            &|d| {
                let zero = d.zero();
                let bound1_ty = d.le(zero, sk);
                let bound2_ty = d.le(zero, c);
                let h1_fv = d.fresh_fvar();
                let h2_fv = d.fresh_fvar();
                let left_term = log_aux(d, &p, base, sk, zero);
                let right_term = log_aux(d, &p, base, c, zero);
                let left_is_zero =
                    super::log_clog_order::log_aux_zero_value(d, &p, base, sk, pos_base);
                let right_is_zero =
                    super::log_clog_order::log_aux_zero_value(d, &p, base, c, pos_base);
                let right_is_zero_rev = d.symm(right_term, zero, right_is_zero);
                let body = d.trans(left_term, zero, right_term, left_is_zero, right_is_zero_rev);
                let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
                d.lam_fv(h1_fv, bound1_ty, with_h2)
            },
            &move |d, predecessor| {
                let succ_pred = d.succ(predecessor);
                let bound1_ty = d.le(succ_pred, sk);
                let bound2_ty = d.le(succ_pred, c);
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);

                let quotient = d.div(succ_pred, base);

                let one = d.num(1);
                let one_le_succ_pred = d.zero_lt_succ(predecessor);
                let one_le_c = d.lemma(p.le_trans, &[one, succ_pred, c, one_le_succ_pred, h2]);
                let c_eq = d.lemma(p.succ_pred_of_pos, &[c, one_le_c]);
                let pc = d.pred(c);
                let succ_pc = d.succ(pc);

                let pos_succ_pred = d.zero_lt_succ(predecessor);
                let quotient_lt_succ_pred =
                    d.lemma(p.div_lt_self, &[succ_pred, base, pos_succ_pred, base_gt1]);

                let quotient_lt_sk = d.lemma(
                    p.lt_of_lt_of_le,
                    &[quotient, succ_pred, sk, quotient_lt_succ_pred, h1],
                );
                let quotient_le_k = d.lemma(p.le_of_lt_succ, &[quotient, k, quotient_lt_sk]);

                let quotient_lt_c = d.lemma(
                    p.lt_of_lt_of_le,
                    &[quotient, succ_pred, c, quotient_lt_succ_pred, h2],
                );
                let motive_c = d.eq_motive(c, &move |d, x| d.lt(quotient, x));
                let quotient_lt_succ_pc = d.transport(c, motive_c, quotient_lt_c, succ_pc, c_eq);
                let quotient_le_pc = d.lemma(p.le_of_lt_succ, &[quotient, pc, quotient_lt_succ_pc]);

                let ih_at = d.apply(ih, &[quotient, quotient, pc]);
                let ih_at = d.apply(ih_at, &[quotient_le_k, quotient_le_pc]);

                let recursive_k = log_aux(d, &p, base, k, quotient);
                let recursive_pc = log_aux(d, &p, base, pc, quotient);
                let stepped_k = d.succ(recursive_k);
                let stepped_pc = d.succ(recursive_pc);
                let stepped_congr =
                    d.congr(recursive_k, recursive_pc, ih_at, &|d, hole| d.succ(hole));

                let two = d.num(2);
                let base_exceeds_one = d.ble(two, base);
                let base_fits = d.ble(base, succ_pred);
                let zero = d.zero();
                let inner_k = d.bool_select_nat(base_exceeds_one, stepped_k, zero);
                let inner_pc = d.bool_select_nat(base_exceeds_one, stepped_pc, zero);
                let inner_congr = d.congr(stepped_k, stepped_pc, stepped_congr, &move |d, hole| {
                    let zero = d.zero();
                    d.bool_select_nat(base_exceeds_one, hole, zero)
                });

                let full_congr = d.congr(inner_k, inner_pc, inner_congr, &move |d, hole| {
                    let zero = d.zero();
                    d.bool_select_nat(base_fits, hole, zero)
                });

                let target_c = log_aux(d, &p, base, c, succ_pred);
                let target_succ_pc = log_aux(d, &p, base, succ_pc, succ_pred);
                let outer_c_congr = d.congr(c, succ_pc, c_eq, &move |d, x| {
                    log_aux(d, &p, base, x, succ_pred)
                });

                let target_sk = log_aux(d, &p, base, sk, succ_pred);
                let outer_c_congr_rev = d.symm(target_c, target_succ_pc, outer_c_congr);
                let body = d.trans(
                    target_sk,
                    target_succ_pc,
                    target_c,
                    full_congr,
                    outer_c_congr_rev,
                );

                let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
                d.lam_fv(h1_fv, bound1_ty, with_h2)
            },
        )
    };

    super::ops::agree_by_double_fuel_induction(d, &statement, &base_case, &step_case, fuel1)
}

/// `Nat.log_div_mul_self : ∀ b n, Eq (log b (mul (div n b) b)) (log b n)`
/// (`Mathlib`: `Nat.log_div_mul_self`). See [`NatPrelude::log_div_mul_self`]
/// for the route.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_log_div_mul_self(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.log_div_mul_self, 2, &|d, values| {
        let (base0, n0) = (values[0], values[1]);
        let quotient0 = d.div(n0, base0);
        let scaled0 = d.mul(quotient0, base0);
        let lhs0 = log(d, &p, base0, scaled0);
        let rhs0 = log(d, &p, base0, n0);
        let stmt = d.eq(lhs0, rhs0);

        let one = d.num(1);
        let dichotomy = d.lemma(p.lt_or_ge, &[one, base0]);
        let lt1_ty = d.lt(one, base0);
        let le1_ty = d.le(base0, one);

        let small_branch = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let lhs_zero = d.lemma(p.log_of_left_le_one, &[base0, h, scaled0]);
            let rhs_zero = d.lemma(p.log_of_left_le_one, &[base0, h, n0]);
            let zero = d.zero();
            let rhs_zero_rev = d.symm(rhs0, zero, rhs_zero);
            let body = d.trans(lhs0, zero, rhs0, lhs_zero, rhs_zero_rev);
            d.lam_fv(h_fv, le1_ty, body)
        };

        let big_branch = {
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let body = declare_log_div_mul_self_big(d, &p, base0, n0, h1);
            d.lam_fv(h1_fv, lt1_ty, body)
        };

        let proof = or_cases(d, lt1_ty, le1_ty, stmt, big_branch, small_branch, dichotomy);
        (stmt, proof)
    })?;
    Ok(())
}

/// The `1 < base0` branch of [`declare_log_div_mul_self`]. Splits `base0`
/// into `succ bp` (via `succ_pred_of_pos`, transported at the very end
/// rather than by `cases_zero_succ` — `base0 = 0`/`1` are already excluded
/// by `h1`, so there is no degenerate branch to refute), then `n0` into "`n0
/// < base` (both sides round to `0`)" and "`base ≤ n0`" (one unfold of
/// `log`'s recursive equation on each side, related through
/// [`log_aux_agree_of_fuel`]).
fn declare_log_div_mul_self_big(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base0: ExprId,
    n0: ExprId,
    h1: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let two = d.num(2);

    // pos_base0 : Lt zero base0, from `Lt one base0` via `Le 1 2 <= base0`.
    let zero_le_one = d.lemma(p.zero_le, &[one]);
    let le_one_two = d.lemma(p.le_succ_succ, &[zero, one, zero_le_one]);
    let pos_base0 = d.lemma(p.le_trans, &[one, two, base0, le_one_two, h1]);

    let base0_eq = d.lemma(p.succ_pred_of_pos, &[base0, pos_base0]);
    let bp = d.pred(base0);
    let base = d.succ(bp);

    let motive_h1 = d.eq_motive(base0, &move |d, x| d.lt(one, x));
    let h1_base = d.transport(base0, motive_h1, h1, base, base0_eq);

    let final_h = d.symm(base0, base, base0_eq);

    let quotient = d.div(n0, base);
    let scaled = d.mul(quotient, base);
    let lhs = log(d, &p, base, scaled);
    let rhs = log(d, &p, base, n0);
    let stmt_at_base = d.eq(lhs, rhs);

    let dichotomy_n = d.lemma(p.lt_or_ge, &[n0, base]);
    let n_lt_ty = d.lt(n0, base);
    let n_ge_ty = d.le(base, n0);

    let n_small = {
        let h_fv = d.fresh_fvar();
        let h_lt = d.kernel().fvar(h_fv);

        let relation = d.lemma(p.div_mod_exec, &[bp, n0]);
        let remainder0 = d.modulo(n0, base);
        let bounds = d.lemma(
            p.div_mod_bounds,
            &[base, n0, quotient, remainder0, relation],
        );
        let mul_base_q = d.mul(base, quotient);
        let lower_ty = d.le(mul_base_q, n0);
        let succ_q = d.succ(quotient);
        let mul_base_succ_q = d.mul(base, succ_q);
        let upper_ty = d.lt(n0, mul_base_succ_q);
        let mul_base_q_le_n = and_left(d, lower_ty, upper_ty, bounds);

        let mcomm = d.lemma(p.mul_comm, &[base, quotient]);
        let motive_sw = d.eq_motive(mul_base_q, &move |d, x| d.le(x, n0));
        let scaled_le_n = d.transport(mul_base_q, motive_sw, mul_base_q_le_n, scaled, mcomm);

        let scaled_lt_base = d.lemma(p.lt_of_le_of_lt, &[scaled, n0, base, scaled_le_n, h_lt]);
        let lhs_zero = d.lemma(p.log_of_lt, &[base, scaled, scaled_lt_base]);
        let rhs_zero = d.lemma(p.log_of_lt, &[base, n0, h_lt]);

        let zero = d.zero();
        let rhs_zero_rev = d.symm(rhs, zero, rhs_zero);
        let body = d.trans(lhs, zero, rhs, lhs_zero, rhs_zero_rev);
        d.lam_fv(h_fv, n_lt_ty, body)
    };

    let n_big = {
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let base_pos = d.zero_lt_succ(bp);
        let zero = d.zero();
        let n0_pos = d.lemma(p.lt_of_lt_of_le, &[zero, base, n0, base_pos, h2]);
        let n0_eq = d.lemma(p.succ_pred_of_pos, &[n0, n0_pos]);
        let n_prime = d.pred(n0);
        let succ_n_prime = d.succ(n_prime);

        let motive_h2 = d.eq_motive(n0, &move |d, x| d.le(base, x));
        let h2_at_nprime = d.transport(n0, motive_h2, h2, succ_n_prime, n0_eq);

        let (quotient_a, _recursive_a, eq_a) =
            log_succ_unfold(d, &p, base, n_prime, h1_base, h2_at_nprime);

        let relation = d.lemma(p.div_mod_exec, &[bp, succ_n_prime]);
        let remainder = d.modulo(succ_n_prime, base);
        let one = d.num(1);
        let iff_fn = d.lemma(
            p.div_mod_mul_le_iff,
            &[base, succ_n_prime, quotient_a, remainder, one, relation],
        );
        let mul_base_one = d.mul(base, one);
        let mbo_eq = d.lemma(p.mul_one, &[base]);
        let mbo_eq_rev = d.symm(mul_base_one, base, mbo_eq);
        let motive_mbo = d.eq_motive(base, &move |d, x| d.le(x, succ_n_prime));
        let h2_as_mul = d.transport(base, motive_mbo, h2_at_nprime, mul_base_one, mbo_eq_rev);

        let left_ty = d.le(mul_base_one, succ_n_prime);
        let right_ty = d.le(one, quotient_a);
        let forward = iff_forward(d, left_ty, right_ty, iff_fn);
        let m_pos = d.apply(forward, &[h2_as_mul]);

        let scaled_pos = d.lemma(p.one_le_mul, &[quotient_a, base, m_pos, base_pos]);
        let scaled_a = d.mul(quotient_a, base);
        let scaled_eq = d.lemma(p.succ_pred_of_pos, &[scaled_a, scaled_pos]);
        let scaled_prime = d.pred(scaled_a);
        let succ_scaled_prime = d.succ(scaled_prime);

        let mul_base_q = d.mul(base, quotient_a);
        let mul_le1 = d.lemma(p.mul_le_mul_left, &[base, one, quotient_a, m_pos]);
        let motive_bl = d.eq_motive(mul_base_one, &move |d, x| d.le(x, mul_base_q));
        let base_le_mulbaseq = d.transport(mul_base_one, motive_bl, mul_le1, base, mbo_eq);

        let mcomm_bq = d.lemma(p.mul_comm, &[base, quotient_a]);
        let motive_bs = d.eq_motive(mul_base_q, &move |d, x| d.le(base, x));
        let base_le_scaled =
            d.transport(mul_base_q, motive_bs, base_le_mulbaseq, scaled_a, mcomm_bq);

        let motive_h2s = d.eq_motive(scaled_a, &move |d, x| d.le(base, x));
        let h2_scaled = d.transport(
            scaled_a,
            motive_h2s,
            base_le_scaled,
            succ_scaled_prime,
            scaled_eq,
        );

        let (quotient_b, _recursive_b, eq_b_raw) =
            log_succ_unfold(d, &p, base, scaled_prime, h1_base, h2_scaled);

        let div_scaled = d.div(scaled_a, base);
        let div_scaled_eq_qb = d.congr(scaled_a, succ_scaled_prime, scaled_eq, &move |d, x| {
            d.div(x, base)
        });
        let mdcl = mul_div_cancel_left(d, &p, base, base_pos, quotient_a);
        let div_scaled_eq_qb_rev = d.symm(div_scaled, quotient_b, div_scaled_eq_qb);
        let qb_eq_qa = d.trans(
            quotient_b,
            div_scaled,
            quotient_a,
            div_scaled_eq_qb_rev,
            mdcl,
        );

        let motive_eqb = d.eq_motive(quotient_b, &move |d, x| {
            let lhs = log(d, &p, base, succ_scaled_prime);
            let inner = log_aux(d, &p, base, scaled_prime, x);
            let rhs = d.succ(inner);
            d.eq(lhs, rhs)
        });
        let eq_b_mid = d.transport(quotient_b, motive_eqb, eq_b_raw, quotient_a, qb_eq_qa);

        let motive_eqb2 = d.eq_motive(succ_scaled_prime, &move |d, x| {
            let lhs = log(d, &p, base, x);
            let inner = log_aux(d, &p, base, scaled_prime, quotient_a);
            let rhs = d.succ(inner);
            d.eq(lhs, rhs)
        });
        let scaled_eq_rev = d.symm(scaled_a, succ_scaled_prime, scaled_eq);
        let eq_b = d.transport(
            succ_scaled_prime,
            motive_eqb2,
            eq_b_mid,
            scaled_a,
            scaled_eq_rev,
        );

        let pos_succ_nprime = d.zero_lt_succ(n_prime);
        let quotient_lt_succ_nprime = d.lemma(
            p.div_lt_self,
            &[succ_n_prime, base, pos_succ_nprime, h1_base],
        );
        let quotient_le_nprime = d.lemma(
            p.le_of_lt_succ,
            &[quotient_a, n_prime, quotient_lt_succ_nprime],
        );

        let pos_succ_scaledprime = d.zero_lt_succ(scaled_prime);
        let qb_lt_succ_scaledprime = d.lemma(
            p.div_lt_self,
            &[succ_scaled_prime, base, pos_succ_scaledprime, h1_base],
        );
        let motive_qb = d.eq_motive(quotient_b, &move |d, x| d.lt(x, succ_scaled_prime));
        let quotient_lt_succ_scaledprime = d.transport(
            quotient_b,
            motive_qb,
            qb_lt_succ_scaledprime,
            quotient_a,
            qb_eq_qa,
        );
        let quotient_le_scaledprime = d.lemma(
            p.le_of_lt_succ,
            &[quotient_a, scaled_prime, quotient_lt_succ_scaledprime],
        );

        let proof_fn = log_aux_agree_of_fuel(d, &p, base, base_pos, h1_base, n_prime);
        let agreement_applied = d.apply(proof_fn, &[quotient_a, quotient_a, scaled_prime]);
        let agreement = d.apply(
            agreement_applied,
            &[quotient_le_nprime, quotient_le_scaledprime],
        );

        let recursive_n = log_aux(d, &p, base, n_prime, quotient_a);
        let recursive_scaled = log_aux(d, &p, base, scaled_prime, quotient_a);
        let succ_congr = d.congr(recursive_n, recursive_scaled, agreement, &|d, x| d.succ(x));

        let log_succ_nprime = log(d, &p, base, succ_n_prime);
        let mid1 = d.succ(recursive_n);
        let mid2 = d.succ(recursive_scaled);
        let step1 = d.trans(log_succ_nprime, mid1, mid2, eq_a, succ_congr);

        let log_scaled = log(d, &p, base, scaled_a);
        let eq_b_rev = d.symm(log_scaled, mid2, eq_b);
        let final_nprime = d.trans(log_succ_nprime, mid2, log_scaled, step1, eq_b_rev);
        let final_nprime_rev = d.symm(log_succ_nprime, log_scaled, final_nprime);

        let n0_eq_rev = d.symm(n0, succ_n_prime, n0_eq);
        let motive_final = d.eq_motive(succ_n_prime, &move |d, x| {
            let q = d.div(x, base);
            let s = d.mul(q, base);
            let lhs = log(d, &p, base, s);
            let rhs = log(d, &p, base, x);
            d.eq(lhs, rhs)
        });
        let result = d.transport(succ_n_prime, motive_final, final_nprime_rev, n0, n0_eq_rev);
        d.lam_fv(h2_fv, n_ge_ty, result)
    };

    let result_at_base = or_cases(
        d,
        n_lt_ty,
        n_ge_ty,
        stmt_at_base,
        n_small,
        n_big,
        dichotomy_n,
    );

    let motive_base = d.eq_motive(base, &move |d, candidate| {
        let q = d.div(n0, candidate);
        let s = d.mul(q, candidate);
        let lhs = log(d, &p, candidate, s);
        let rhs = log(d, &p, candidate, n0);
        d.eq(lhs, rhs)
    });
    d.transport(base, motive_base, result_at_base, base0, final_h)
}

/// Declare every mirror this file carries.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_log_clog_mirrors_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_log_anti_left(d, p)?;
    declare_clog_anti_left(d, p)?;
    declare_clog_mono(d, p)?;
    declare_clog_of_left_le_one(d, p)?;
    declare_clog_of_right_le_one(d, p)?;
    declare_log_of_left_le_one(d, p)?;
    declare_log_pos(d, p)?;
    declare_log_eq_zero_iff(d, p)?;
    declare_clog_eq_one(d, p)?;
    declare_log_eq_one_iff_prime(d, p)?;
    declare_log_eq_one_iff(d, p)?;
    declare_log_div_mul_self(d, p)?;
    Ok(())
}
