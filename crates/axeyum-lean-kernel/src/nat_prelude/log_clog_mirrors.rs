//! `ml430` mirrors for `Nat.log`/`Nat.clog` that compose out of
//! `log.rs`/`clog.rs`/`log_clog_order.rs`'s existing machinery, plus two
//! supporting lemmas (`log_pos`, `log_of_left_le_one`) neither of those
//! files needed on their own.
//!
//! Seven facts land here:
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
//! `Nat.log_eq_one_iff`/`Nat.log_eq_one_iff'` and `Nat.log_div_mul_self`
//! stay OPEN — each needs a genuinely new numeric fact this session did not
//! build (a "`log b n < 2 → n < b*b`" converse bound for both
//! `log_eq_one_iff` forms, which is the hard direction `log_eq_zero_iff` did
//! not need; and a fuel-generalized "exact division doesn't change the
//! quotient chain" induction for `log_div_mul_self`) — see each fact's notes
//! for the precise gap.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
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

/// `Or.rec`-based case split (mirrors `log.rs`'s/`log_clog_order.rs`'s
/// private `or_cases`, not exported from either file).
#[allow(clippy::too_many_arguments)]
fn or_cases(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_minor: ExprId,
    right_minor: ExprId,
    proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let split_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, split_ty, goal, BinderInfo::Default);
    let rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        rec,
        &[left_ty, right_ty, motive, left_minor, right_minor, proof],
    )
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
                    &p,
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
                &p,
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
                &p,
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
    Ok(())
}
