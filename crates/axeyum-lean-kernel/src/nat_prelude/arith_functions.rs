//! The divisor aggregate and its `d ↦ n/d` reindexing — the reusable
//! primitive under multiplicative arithmetic functions (roadmap W2-18,
//! ADR-1619).
//!
//! ## Why this file exists
//!
//! `Nat.sumDivisors` (`perfect.rs`) already sums the divisors of `n`, but it
//! is MONOMORPHIC: the summand is hard-wired to `fun d => d`. Every
//! multiplicative arithmetic function — `σ`, `d`/`τ`, a Dirichlet
//! convolution — is the same fold over the same index set with a different
//! summand, so the first thing missing was the aggregate that takes the
//! summand as an argument.
//!
//! The second thing missing was the reindexing. The primitive-roots lane
//! (ADR-1598) stopped at exactly this point: the counting route to
//! `∑_{d∣n} φ(d) = n` needs `d ↦ n/d` applied INSIDE a predicate-restricted
//! sum, and nothing in the prelude turned that map into a permutation.
//!
//! ## What the reindexing needs, and why the obvious route fails
//!
//! `Nat.sumRange_permute` (`sum_range_permute.rs`) is the engine: a sum over
//! `[0,n)` is invariant under any `InjectiveOn`/`MapsInto` self-map. But
//! `d ↦ n/d` is **not** injective on `[0, n]` — at `n = 6` it sends `4`, `5`
//! and `6` all to `1`. So the map that is actually a permutation is the one
//! that moves only the divisors:
//!
//! ```text
//! Nat.divisorFlip n d := if d ∣ n then n / d else d
//! ```
//!
//! On the divisors of a positive `n` this is the classical involution
//! `d ↦ n/d`; everything else is fixed. Being an involution it is injective
//! with no bound at all, which is why
//! [`declare_divisor_flip_injective_on`] states `injectiveOn` at an ARBITRARY
//! range and only `mapsInto` carries `succ n`.
//!
//! Both halves need `0 < n`: at `n = 0` every `d` divides, `0 / d = 0`, and
//! the map collapses onto `0`.
//!
//! ## The predicate is `Bool`-valued
//!
//! `Nat.dvdB d n := Nat.beq (n % d) 0` is the decidable divisibility test the
//! `sumRangeIf`/`countRange`/`prodRangeIf` family requires (a `Prop` cannot
//! drive `Bool.rec`). It is deliberately the SAME expression
//! `Nat.sumDivisors` already inlined, so
//! [`declare_sum_divisors_by_eq_sum_divisors`] is closed by `Eq.refl`. Note
//! `dvdB 0 n` is `beq n 0`, because `Nat.mod n 0 = n`: `0` counts as a
//! divisor of `0` alone, which is exactly `Nat.dvd`'s own convention, and is
//! why [`declare_dvd_of_dvd_b`] needs no positivity hypothesis.
//!
//! ## What's declared
//!
//! - `Nat.dvdB`, with both bridges to `Nat.dvd`.
//! - `Nat.sumDivisorsBy f n`, the aggregate, and `Nat.numDivisors` — the
//!   divisor-COUNTING function, `sumDivisorsBy (fun _ => 1)`.
//! - `Nat.sumDivisorsBy_eq_sumDivisors`, tying the new aggregate to the
//!   existing `σ`.
//! - `Nat.div_div_self_of_dvd`, `n / (n / d) = d` for a divisor of a positive
//!   `n` — useful on its own, and the heart of the involution.
//! - `Nat.divisorFlip` with its two value equations, its involution law, and
//!   the `injectiveOn`/`mapsInto` pair `Nat.sumRange_permute` consumes.
//! - **`Nat.sumDivisorsBy_reindex`**, the deliverable:
//!   `0 < n → sumDivisorsBy f n = sumDivisorsBy (fun d => f (n / d)) n`.

use super::NatPrelude;
use super::finite::{select_nat_false, select_nat_true};
use super::helpers::{iff_forward, iff_reverse, transport_dvd_right};
use super::ops::{NatDev, NatOps, bool_true_or_false};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::{BinderInfo, ExprId};

/// Delta height for `Nat.dvdB`: strictly above `Nat.mod` (3), the deepest
/// definition it calls.
const DVD_B_HEIGHT: u16 = 4;
/// Delta height for `Nat.sumDivisorsBy` and `Nat.divisorFlip`: strictly above
/// `Nat.sumRangeIf` (3), `Nat.div` (3) and `Nat.dvdB` (4).
const AGGREGATE_HEIGHT: u16 = 5;
/// Delta height for `Nat.numDivisors`, which calls `Nat.sumDivisorsBy` (5).
const NUM_DIVISORS_HEIGHT: u16 = 6;

// ---------------------------------------------------------------------------
// Shared local shapes.
//
// Per this prelude's per-file convention, `or_elim` is a private copy of the
// same `Or.rec` wrapper `subset_search.rs` keeps, and `div_eq_of_mul_eq` a
// private copy of the helper `add_choose_div.rs` and `asc_factorial_div.rs`
// each keep.
// ---------------------------------------------------------------------------

/// `Or.rec` at a `Prop` goal.
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
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

/// `k_pos : 1 ≤ k`, `mul_eq : k * a = b  ⊢  b / k = a`.
fn div_eq_of_mul_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    k: ExprId,
    a: ExprId,
    b: ExprId,
    k_pos: ExprId,
    mul_eq: ExprId,
) -> ExprId {
    let p = *p;
    let ka = d.mul(k, a);
    let dvd_k_ka = d.lemma(p.dvd_mul, &[k, a]);
    let dvd_k_b = transport_dvd_right(d, k, ka, b, mul_eq, dvd_k_ka);
    let cancel = d.lemma(p.div_mul_cancel_of_dvd, &[k, b, k_pos, dvd_k_b]);
    let mul_eq_rev = d.symm(ka, b, mul_eq);
    let div_b_k = d.div(b, k);
    let mul_k_divbk = d.mul(k, div_b_k);
    let (_, chained) = d.chain(mul_k_divbk, &[(b, cancel), (ka, mul_eq_rev)]);
    d.lemma(p.mul_left_cancel_of_pos, &[k, div_b_k, a, k_pos, chained])
}

/// Restate `h : Eq Nat mid rhs` with a definitionally equal left-hand side
/// `a` — one `Eq.refl` bridge, so the term's INFERRED type is the one the
/// caller wants to read rather than one the kernel must unfold to recognise.
fn restate_lhs(d: &mut NatDev<'_>, a: ExprId, mid: ExprId, rhs: ExprId, h: ExprId) -> ExprId {
    let refl_a = d.refl(a);
    d.trans(a, mid, rhs, refl_a, h)
}

/// Restate `h : Eq Nat lhs mid` with a definitionally equal right-hand side.
fn restate_rhs(d: &mut NatDev<'_>, lhs: ExprId, mid: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let refl_mid = d.refl(mid);
    d.trans(lhs, mid, b, h, refl_mid)
}

/// `Nat.dvdB divisor n`.
fn dvd_b(d: &mut NatDev<'_>, p: &NatPrelude, divisor: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.dvd_b, &[divisor, n])
}

/// `Nat.divisorFlip n k`.
fn divisor_flip(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.divisor_flip, &[n, k])
}

/// `Nat.sumDivisorsBy f n`.
fn sum_divisors_by(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.sum_divisors_by, &[f, n])
}

/// The cofactor facts of a divisor: from `0 < n` and `k ∣ n`, with
/// `e := n / k`, returns `(e, (e * k = n), e ∣ n, 1 ≤ e)`.
fn cofactor_facts(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    k: ExprId,
    n_pos: ExprId,
    k_dvd_n: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let p = *p;
    let k_pos = d.lemma(p.one_le_of_dvd_pos, &[k, n, n_pos, k_dvd_n]);
    // `k * (n / k) = n`.
    let cancel = d.lemma(p.div_mul_cancel_of_dvd, &[k, n, k_pos, k_dvd_n]);
    let e = d.div(n, k);
    let k_e = d.mul(k, e);
    let e_k = d.mul(e, k);
    let comm = d.lemma(p.mul_comm, &[k, e]);
    let comm_rev = d.symm(k_e, e_k, comm);
    // `e * k = n`.
    let mul_eq = d.trans(e_k, k_e, n, comm_rev, cancel);
    let dvd_e_ek = d.lemma(p.dvd_mul, &[e, k]);
    let dvd_e_n = transport_dvd_right(d, e, e_k, n, mul_eq, dvd_e_ek);
    let e_pos = d.lemma(p.one_le_of_dvd_pos, &[e, n, n_pos, dvd_e_n]);
    (e, mul_eq, dvd_e_n, e_pos)
}

// ============================================================================
// `Nat.dvdB` and its two bridges.
// ============================================================================

/// `Nat.dvdB d n := Nat.beq (Nat.mod n d) Nat.zero`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_dvd_b(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let divisor_fv = d.fresh_fvar();
    let divisor = d.kernel().fvar(divisor_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let remainder = d.modulo(n, divisor);
    let zero = d.zero();
    let body = d.beq(remainder, zero);
    let value = {
        let over_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(divisor_fv, nat, over_n)
    };
    let ty = {
        let over_n = d.arrow(nat, bool_ty);
        d.arrow(nat, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.dvd_b,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DVD_B_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.dvd_of_dvdB : ∀ a n, Eq Bool (dvdB a n) true → dvd a n`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_dvd_of_dvd_b(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dvd_of_dvd_b, 2, &|d, v| {
        let (a, n) = (v[0], v[1]);
        let flag = dvd_b(d, &p, a, n);
        let tv = d.bool_true();
        let hyp = d.bool_eq(flag, tv);
        let concl = d.dvd(a, n);
        let stmt = d.arrow(hyp, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let remainder = d.modulo(n, a);
        let zero = d.zero();
        let mod_zero = d.lemma(p.eq_of_beq_eq_true, &[remainder, zero, h]);
        let bridge = d.lemma(p.dvd_iff_mod_eq_zero, &[a, n]);
        let left = d.dvd(a, n);
        let right = d.eq(remainder, zero);
        let reverse = iff_reverse(d, left, right, bridge);
        let body = d.apply(reverse, &[mod_zero]);
        let proof = d.lam_fv(h_fv, hyp, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.dvdB_of_dvd : ∀ a n, dvd a n → Eq Bool (dvdB a n) true`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_dvd_b_of_dvd(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dvd_b_of_dvd, 2, &|d, v| {
        let (a, n) = (v[0], v[1]);
        let flag = dvd_b(d, &p, a, n);
        let tv = d.bool_true();
        let hyp = d.dvd(a, n);
        let concl = d.bool_eq(flag, tv);
        let stmt = d.arrow(hyp, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let remainder = d.modulo(n, a);
        let zero = d.zero();
        let bridge = d.lemma(p.dvd_iff_mod_eq_zero, &[a, n]);
        let left = d.dvd(a, n);
        let right = d.eq(remainder, zero);
        let forward = iff_forward(d, left, right, bridge);
        let mod_zero = d.apply(forward, &[h]);
        let body = d.lemma(p.beq_eq_true_of_eq, &[remainder, zero, mod_zero]);
        let proof = d.lam_fv(h_fv, hyp, body);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.sumDivisorsBy`, `Nat.numDivisors`.
// ============================================================================

/// `Nat.sumDivisorsBy f n := sumRangeIf (fun k => dvdB k n) f (succ n)`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_sum_divisors_by(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let pred = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = dvd_b(d, &p, k, n);
        d.lam_fv(k_fv, nat, body)
    };
    let bound = d.succ(n);
    let body = d.const_app(p.sum_range_if, &[pred, f, bound]);

    let value = {
        let over_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(f_fv, fn_ty, over_n)
    };
    let ty = {
        let over_n = d.arrow(nat, nat);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sum_divisors_by,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(AGGREGATE_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.numDivisors n := sumDivisorsBy (fun _ => 1) n` — the number of
/// divisors of `n` (`d(n)`, `τ(n)`).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_num_divisors(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let constant_one = {
        let k_fv = d.fresh_fvar();
        let one = d.num(1);
        d.lam_fv(k_fv, nat, one)
    };
    let body = sum_divisors_by(d, &p, constant_one, n);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.num_divisors,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(NUM_DIVISORS_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.sumDivisorsBy_eq_sumDivisors : ∀ n,
/// Eq (sumDivisorsBy (fun k => k) n) (sumDivisors n)` — `Eq.refl`: the new
/// aggregate at the identity summand IS the old monomorphic `σ`, delta for
/// delta.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_sum_divisors_by_eq_sum_divisors(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.sum_divisors_by_eq_sum_divisors, 1, &|d, v| {
        let n = v[0];
        let nat = d.nat_ty();
        let identity = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            d.lam_fv(k_fv, nat, k)
        };
        let lhs = sum_divisors_by(d, &p, identity, n);
        let rhs = d.const_app(p.sum_divisors, &[n]);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(lhs);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.div_div_self_of_dvd`.
// ============================================================================

/// `Nat.div_div_self_of_dvd : ∀ n k, Lt zero n → dvd k n →
/// Eq (div n (div n k)) k`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_div_div_self_of_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.div_div_self_of_dvd, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let zero = d.zero();
        let pos_ty = d.lt(zero, n);
        let dvd_ty = d.dvd(k, n);
        let e = d.div(n, k);
        let concl = {
            let outer = d.div(n, e);
            d.eq(outer, k)
        };
        let stmt = {
            let inner = d.arrow(dvd_ty, concl);
            d.arrow(pos_ty, inner)
        };

        let pos_fv = d.fresh_fvar();
        let n_pos = d.kernel().fvar(pos_fv);
        let dvd_fv = d.fresh_fvar();
        let k_dvd_n = d.kernel().fvar(dvd_fv);

        let (cofactor, mul_eq, _dvd_e_n, e_pos) = cofactor_facts(d, &p, n, k, n_pos, k_dvd_n);
        let body = div_eq_of_mul_eq(d, &p, cofactor, k, n, e_pos, mul_eq);

        let proof = {
            let with_dvd = d.lam_fv(dvd_fv, dvd_ty, body);
            d.lam_fv(pos_fv, pos_ty, with_dvd)
        };
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.divisorFlip`.
// ============================================================================

/// `Nat.divisorFlip n k := bool_select_nat (dvdB k n) (div n k) k`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_divisor_flip(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let flag = dvd_b(d, &p, k, n);
    let quotient = d.div(n, k);
    let body = d.bool_select_nat(flag, quotient, k);
    let value = {
        let over_k = d.lam_fv(k_fv, nat, body);
        d.lam_fv(n_fv, nat, over_k)
    };
    let ty = {
        let over_k = d.arrow(nat, nat);
        d.arrow(nat, over_k)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.divisor_flip,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(AGGREGATE_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.divisorFlip_at_divisor : ∀ n k, Eq Bool (dvdB k n) true →
/// Eq (divisorFlip n k) (div n k)`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_divisor_flip_at_divisor(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.divisor_flip_at_divisor, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let flag = dvd_b(d, &p, k, n);
        let tv = d.bool_true();
        let hyp = d.bool_eq(flag, tv);
        let quotient = d.div(n, k);
        let flip = divisor_flip(d, &p, n, k);
        let concl = d.eq(flip, quotient);
        let stmt = d.arrow(hyp, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let selector = d.bool_select_nat(flag, quotient, k);
        let selected = select_nat_true(d, flag, quotient, k, h);
        let body = restate_lhs(d, flip, selector, quotient, selected);
        let proof = d.lam_fv(h_fv, hyp, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.divisorFlip_at_nonDivisor : ∀ n k, Eq Bool (dvdB k n) false →
/// Eq (divisorFlip n k) k`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_divisor_flip_at_non_divisor(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.divisor_flip_at_non_divisor, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let flag = dvd_b(d, &p, k, n);
        let false_value = d.bool_false();
        let hyp = d.bool_eq(flag, false_value);
        let flip = divisor_flip(d, &p, n, k);
        let concl = d.eq(flip, k);
        let stmt = d.arrow(hyp, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let quotient = d.div(n, k);
        let selector = d.bool_select_nat(flag, quotient, k);
        let selected = select_nat_false(d, flag, quotient, k, h);
        let body = restate_lhs(d, flip, selector, k, selected);
        let proof = d.lam_fv(h_fv, hyp, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.divisorFlip_dvdB : ∀ n k, Lt zero n → Eq Bool (dvdB k n) true →
/// Eq Bool (dvdB (div n k) n) true` — the cofactor of a divisor is again a
/// divisor.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_divisor_flip_dvd_b(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.divisor_flip_dvd_b, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let zero = d.zero();
        let pos_ty = d.lt(zero, n);
        let flag = dvd_b(d, &p, k, n);
        let tv = d.bool_true();
        let hyp = d.bool_eq(flag, tv);
        let e = d.div(n, k);
        let concl = {
            let cofactor_flag = dvd_b(d, &p, e, n);
            d.bool_eq(cofactor_flag, tv)
        };
        let stmt = {
            let inner = d.arrow(hyp, concl);
            d.arrow(pos_ty, inner)
        };

        let pos_fv = d.fresh_fvar();
        let n_pos = d.kernel().fvar(pos_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let k_dvd_n = d.lemma(p.dvd_of_dvd_b, &[k, n, h]);
        let (cofactor, _mul_eq, dvd_e_n, _e_pos) = cofactor_facts(d, &p, n, k, n_pos, k_dvd_n);
        let body = d.lemma(p.dvd_b_of_dvd, &[cofactor, n, dvd_e_n]);

        let proof = {
            let with_h = d.lam_fv(h_fv, hyp, body);
            d.lam_fv(pos_fv, pos_ty, with_h)
        };
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.divisorFlip_involutive : ∀ n, Lt zero n → ∀ k,
/// Eq (divisorFlip n (divisorFlip n k)) k`.
///
/// The quantifier order is deliberate: the conclusion is `∀ k, t (t k) = k`
/// as a single term, which is exactly what the generic involution-to-
/// injectivity argument consumes.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_divisor_flip_involutive(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let zero = d.zero();
    let pos_ty = d.lt(zero, n);
    let pos_fv = d.fresh_fvar();
    let n_pos = d.kernel().fvar(pos_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let flip_k = divisor_flip(d, &p, n, k);
    let flip_flip_k = divisor_flip(d, &p, n, flip_k);
    let goal = d.eq(flip_flip_k, k);

    let flag = dvd_b(d, &p, k, n);
    let tv = d.bool_true();
    let false_value = d.bool_false();
    let is_true = d.bool_eq(flag, tv);
    let is_false = d.bool_eq(flag, false_value);
    let decided = bool_true_or_false(d, &p, flag);

    let on_true = {
        let ht_fv = d.fresh_fvar();
        let ht = d.kernel().fvar(ht_fv);
        let e = d.div(n, k);
        // `divisorFlip n k = n / k`.
        let step_flip = d.lemma(p.divisor_flip_at_divisor, &[n, k, ht]);
        // `divisorFlip n (divisorFlip n k) = divisorFlip n (n / k)`.
        let step_a = d.congr(flip_k, e, step_flip, &|d, x| divisor_flip(d, &p, n, x));
        // `divisorFlip n (n / k) = n / (n / k)`.
        let cofactor_flag = d.lemma(p.divisor_flip_dvd_b, &[n, k, n_pos, ht]);
        let step_b = d.lemma(p.divisor_flip_at_divisor, &[n, e, cofactor_flag]);
        // `n / (n / k) = k`.
        let k_dvd_n = d.lemma(p.dvd_of_dvd_b, &[k, n, ht]);
        let step_c = d.lemma(p.div_div_self_of_dvd, &[n, k, n_pos, k_dvd_n]);
        let flip_e = divisor_flip(d, &p, n, e);
        let outer = d.div(n, e);
        let (_, chained) = d.chain(
            flip_flip_k,
            &[(flip_e, step_a), (outer, step_b), (k, step_c)],
        );
        d.lam_fv(ht_fv, is_true, chained)
    };
    let on_false = {
        let hf_fv = d.fresh_fvar();
        let hf = d.kernel().fvar(hf_fv);
        let step_flip = d.lemma(p.divisor_flip_at_non_divisor, &[n, k, hf]);
        let step_a = d.congr(flip_k, k, step_flip, &|d, x| divisor_flip(d, &p, n, x));
        let (_, chained) = d.chain(flip_flip_k, &[(flip_k, step_a), (k, step_flip)]);
        d.lam_fv(hf_fv, is_false, chained)
    };
    let body = or_elim(d, &p, is_true, is_false, goal, on_true, on_false, decided);

    let value = {
        let over_k = d.lam_fv(k_fv, nat, body);
        let with_pos = d.lam_fv(pos_fv, pos_ty, over_k);
        d.lam_fv(n_fv, nat, with_pos)
    };
    let ty = {
        let over_k = d.pi_fv(k_fv, nat, goal);
        let with_pos = d.arrow(pos_ty, over_k);
        d.pi_fv(n_fv, nat, with_pos)
    };
    d.declare_theorem(p.divisor_flip_involutive, ty, value)
}

/// `Nat.divisorFlip_injectiveOn : ∀ n m, Lt zero n →
/// injectiveOn (fun k => divisorFlip n k) m`.
///
/// The range `m` is arbitrary: an involution is injective everywhere, so no
/// bound enters the argument.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_divisor_flip_injective_on(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let zero = d.zero();
    let pos_ty = d.lt(zero, n);
    let pos_fv = d.fresh_fvar();
    let n_pos = d.kernel().fvar(pos_fv);

    let sigma = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = divisor_flip(d, &p, n, k);
        d.lam_fv(k_fv, nat, body)
    };
    let concl = d.const_app(p.injective_on, &[sigma, m]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let ha_ty = d.lt(a, m);
    let ha_fv = d.fresh_fvar();
    let hb_ty = d.lt(b, m);
    let hb_fv = d.fresh_fvar();

    let flip_a = divisor_flip(d, &p, n, a);
    let flip_b = divisor_flip(d, &p, n, b);
    let heq_ty = d.eq(flip_a, flip_b);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    // The generic involution-to-injectivity argument, inlined:
    // `a = t (t a) = t (t b) = b`.
    let t = d.const_app(p.divisor_flip, &[n]);
    let t_inv = d.lemma(p.divisor_flip_involutive, &[n, n_pos]);
    let inv_a = d.apply(t_inv, &[a]);
    let inv_b = d.apply(t_inv, &[b]);
    let congr_step = d.congr(flip_a, flip_b, heq, &|d, z| d.apply(t, &[z]));
    let tta = d.apply(t, &[flip_a]);
    let ttb = d.apply(t, &[flip_b]);
    let symm_inv_a = d.symm(tta, a, inv_a);
    let step1 = d.trans(a, tta, ttb, symm_inv_a, congr_step);
    let result = d.trans(a, ttb, b, step1, inv_b);

    let value = {
        let with_heq = d.lam_fv(heq_fv, heq_ty, result);
        let with_hb = d.lam_fv(hb_fv, hb_ty, with_heq);
        let with_ha = d.lam_fv(ha_fv, ha_ty, with_hb);
        let with_b = d.lam_fv(b_fv, nat, with_ha);
        let with_a = d.lam_fv(a_fv, nat, with_b);
        let with_pos = d.lam_fv(pos_fv, pos_ty, with_a);
        let over_m = d.lam_fv(m_fv, nat, with_pos);
        d.lam_fv(n_fv, nat, over_m)
    };
    let ty = {
        let with_pos = d.arrow(pos_ty, concl);
        let over_m = d.pi_fv(m_fv, nat, with_pos);
        d.pi_fv(n_fv, nat, over_m)
    };
    d.declare_theorem(p.divisor_flip_injective_on, ty, value)
}

/// `Nat.divisorFlip_mapsInto : ∀ n, Lt zero n →
/// mapsInto (fun k => divisorFlip n k) (succ n)`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_divisor_flip_maps_into(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let zero = d.zero();
    let pos_ty = d.lt(zero, n);
    let pos_fv = d.fresh_fvar();
    let n_pos = d.kernel().fvar(pos_fv);
    let bound = d.succ(n);

    let sigma = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = divisor_flip(d, &p, n, k);
        d.lam_fv(k_fv, nat, body)
    };
    let concl = d.const_app(p.maps_into, &[sigma, bound]);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hi_ty = d.lt(i, bound);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let flip_i = divisor_flip(d, &p, n, i);
    let goal = d.lt(flip_i, bound);

    let flag = dvd_b(d, &p, i, n);
    let tv = d.bool_true();
    let false_value = d.bool_false();
    let is_true = d.bool_eq(flag, tv);
    let is_false = d.bool_eq(flag, false_value);
    let decided = bool_true_or_false(d, &p, flag);

    let on_true = {
        let ht_fv = d.fresh_fvar();
        let ht = d.kernel().fvar(ht_fv);
        let e = d.div(n, i);
        let step_flip = d.lemma(p.divisor_flip_at_divisor, &[n, i, ht]);
        let i_dvd_n = d.lemma(p.dvd_of_dvd_b, &[i, n, ht]);
        let (cofactor, _mul_eq, dvd_e_n, _e_pos) = cofactor_facts(d, &p, n, i, n_pos, i_dvd_n);
        let e_le_n = d.lemma(p.le_of_dvd, &[cofactor, n, n_pos, dvd_e_n]);
        let e_lt_bound = d.lemma(p.lt_succ_of_le, &[cofactor, n, e_le_n]);
        // Move `n/i < succ n` back along `divisorFlip n i = n / i`.
        let symm_flip = d.symm(flip_i, e, step_flip);
        let motive = d.eq_motive(e, &|d, x| d.lt(x, bound));
        let moved = d.transport(e, motive, e_lt_bound, flip_i, symm_flip);
        d.lam_fv(ht_fv, is_true, moved)
    };
    let on_false = {
        let hf_fv = d.fresh_fvar();
        let hf = d.kernel().fvar(hf_fv);
        let step_flip = d.lemma(p.divisor_flip_at_non_divisor, &[n, i, hf]);
        let symm_flip = d.symm(flip_i, i, step_flip);
        let motive = d.eq_motive(i, &|d, x| d.lt(x, bound));
        let moved = d.transport(i, motive, hi, flip_i, symm_flip);
        d.lam_fv(hf_fv, is_false, moved)
    };
    let body = or_elim(d, &p, is_true, is_false, goal, on_true, on_false, decided);

    let value = {
        let with_hi = d.lam_fv(hi_fv, hi_ty, body);
        let over_i = d.lam_fv(i_fv, nat, with_hi);
        let with_pos = d.lam_fv(pos_fv, pos_ty, over_i);
        d.lam_fv(n_fv, nat, with_pos)
    };
    let ty = {
        let with_pos = d.arrow(pos_ty, concl);
        d.pi_fv(n_fv, nat, with_pos)
    };
    d.declare_theorem(p.divisor_flip_maps_into, ty, value)
}

// ============================================================================
// `Nat.sumDivisorsBy_reindex` — the deliverable.
// ============================================================================

/// `Nat.sumDivisorsBy_reindex : ∀ (f : Nat → Nat) (n : Nat), Lt zero n →
/// Eq (sumDivisorsBy f n) (sumDivisorsBy (fun k => f (div n k)) n)`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_sum_divisors_by_reindex(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let zero = d.zero();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pos_ty = d.lt(zero, n);
    let pos_fv = d.fresh_fvar();
    let n_pos = d.kernel().fvar(pos_fv);

    let bound = d.succ(n);

    // `g k := if dvdB k n then f k else 0` — `sumDivisorsBy f n`'s summand.
    let g = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let flag = dvd_b(d, &p, k, n);
        let value = d.apply(f, &[k]);
        let body = d.bool_select_nat(flag, value, zero);
        d.lam_fv(k_fv, nat, body)
    };
    // `f_flip k := f (n / k)` — the reindexed summand.
    let f_flip = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let quotient = d.div(n, k);
        let body = d.apply(f, &[quotient]);
        d.lam_fv(k_fv, nat, body)
    };
    // `g2 k := if dvdB k n then f (n / k) else 0`.
    let g2 = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let flag = dvd_b(d, &p, k, n);
        let quotient = d.div(n, k);
        let value = d.apply(f, &[quotient]);
        let body = d.bool_select_nat(flag, value, zero);
        d.lam_fv(k_fv, nat, body)
    };
    let sigma = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = divisor_flip(d, &p, n, k);
        d.lam_fv(k_fv, nat, body)
    };
    // `g ∘ σ`, in beta-reduced form.
    let g_sigma = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let flipped = divisor_flip(d, &p, n, k);
        let flag = dvd_b(d, &p, flipped, n);
        let value = d.apply(f, &[flipped]);
        let body = d.bool_select_nat(flag, value, zero);
        d.lam_fv(k_fv, nat, body)
    };

    let inj = d.lemma(p.divisor_flip_injective_on, &[n, bound, n_pos]);
    let maps = d.lemma(p.divisor_flip_maps_into, &[n, n_pos]);
    let permuted = d.lemma(p.sum_range_permute, &[g, sigma, bound, inj, maps]);

    // Pointwise: `g (σ k) = g2 k`, by the same `dvdB k n` dichotomy.
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let flipped = divisor_flip(d, &p, n, k);
        let flipped_flag = dvd_b(d, &p, flipped, n);
        let flipped_value = d.apply(f, &[flipped]);
        let lhs = d.bool_select_nat(flipped_flag, flipped_value, zero);
        let quotient = d.div(n, k);
        let flag = dvd_b(d, &p, k, n);
        let quotient_value = d.apply(f, &[quotient]);
        let rhs = d.bool_select_nat(flag, quotient_value, zero);
        let goal = d.eq(lhs, rhs);

        let tv = d.bool_true();
        let false_value = d.bool_false();
        let is_true = d.bool_eq(flag, tv);
        let is_false = d.bool_eq(flag, false_value);
        let decided = bool_true_or_false(d, &p, flag);

        let on_true = {
            let ht_fv = d.fresh_fvar();
            let ht = d.kernel().fvar(ht_fv);
            let step_flip = d.lemma(p.divisor_flip_at_divisor, &[n, k, ht]);
            let step_a = d.congr(flipped, quotient, step_flip, &|d, x| {
                let flag_x = dvd_b(d, &p, x, n);
                let value_x = d.apply(f, &[x]);
                d.bool_select_nat(flag_x, value_x, zero)
            });
            let cofactor_flag = d.lemma(p.divisor_flip_dvd_b, &[n, k, n_pos, ht]);
            let quotient_flag = dvd_b(d, &p, quotient, n);
            let mid = d.bool_select_nat(quotient_flag, quotient_value, zero);
            let step_b = select_nat_true(d, quotient_flag, quotient_value, zero, cofactor_flag);
            let rhs_value = select_nat_true(d, flag, quotient_value, zero, ht);
            let step_c = d.symm(rhs, quotient_value, rhs_value);
            let (_, chained) = d.chain(
                lhs,
                &[(mid, step_a), (quotient_value, step_b), (rhs, step_c)],
            );
            d.lam_fv(ht_fv, is_true, chained)
        };
        let on_false = {
            let hf_fv = d.fresh_fvar();
            let hf = d.kernel().fvar(hf_fv);
            let step_flip = d.lemma(p.divisor_flip_at_non_divisor, &[n, k, hf]);
            let step_a = d.congr(flipped, k, step_flip, &|d, x| {
                let flag_x = dvd_b(d, &p, x, n);
                let value_x = d.apply(f, &[x]);
                d.bool_select_nat(flag_x, value_x, zero)
            });
            let plain_value = d.apply(f, &[k]);
            let mid = d.bool_select_nat(flag, plain_value, zero);
            let step_b = select_nat_false(d, flag, plain_value, zero, hf);
            let rhs_zero = select_nat_false(d, flag, quotient_value, zero, hf);
            let step_c = d.symm(rhs, zero, rhs_zero);
            let (_, chained) = d.chain(lhs, &[(mid, step_a), (zero, step_b), (rhs, step_c)]);
            d.lam_fv(hf_fv, is_false, chained)
        };
        let body = or_elim(d, &p, is_true, is_false, goal, on_true, on_false, decided);
        d.lam_fv(k_fv, nat, body)
    };

    let congr_step = d.lemma(p.sum_range_congr, &[g_sigma, g2, bound, pointwise]);

    let lhs = sum_divisors_by(d, &p, f, n);
    let rhs = sum_divisors_by(d, &p, f_flip, n);
    let sum_g = d.sum_range(g, bound);
    let sum_g_sigma = d.sum_range(g_sigma, bound);
    let sum_g2 = d.sum_range(g2, bound);
    let head = restate_lhs(d, lhs, sum_g, sum_g_sigma, permuted);
    let tail = restate_rhs(d, sum_g_sigma, sum_g2, rhs, congr_step);
    let body = d.trans(lhs, sum_g_sigma, rhs, head, tail);

    let goal = d.eq(lhs, rhs);
    let value = {
        let with_pos = d.lam_fv(pos_fv, pos_ty, body);
        let over_n = d.lam_fv(n_fv, nat, with_pos);
        d.lam_fv(f_fv, fn_ty, over_n)
    };
    let ty = {
        let with_pos = d.arrow(pos_ty, goal);
        let over_n = d.pi_fv(n_fv, nat, with_pos);
        d.pi_fv(f_fv, fn_ty, over_n)
    };
    d.declare_theorem(p.sum_divisors_by_reindex, ty, value)
}

/// Declare every `arith_functions.rs` result, in dependency order.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_arith_functions_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_dvd_b(d, p)?;
    declare_dvd_of_dvd_b(d, p)?;
    declare_dvd_b_of_dvd(d, p)?;
    declare_sum_divisors_by(d, p)?;
    declare_num_divisors(d, p)?;
    declare_sum_divisors_by_eq_sum_divisors(d, p)?;
    declare_div_div_self_of_dvd(d, p)?;
    declare_divisor_flip(d, p)?;
    declare_divisor_flip_at_divisor(d, p)?;
    declare_divisor_flip_at_non_divisor(d, p)?;
    declare_divisor_flip_dvd_b(d, p)?;
    declare_divisor_flip_involutive(d, p)?;
    declare_divisor_flip_injective_on(d, p)?;
    declare_divisor_flip_maps_into(d, p)?;
    declare_sum_divisors_by_reindex(d, p)?;
    Ok(())
}
