//! Multiplicative arithmetic functions AS A FAMILY: the multiplicativity
//! predicate, the Dirichlet convolution, and the Möbius function as a graded
//! `Nat`-valued pair (roadmap W2-18, ADR-1619).
//!
//! Builds on `arith_functions.rs`, which supplies the divisor aggregate
//! `Nat.sumDivisorsBy` and its `d ↦ n/d` reindexing.
//!
//! ## The predicate is stated once, not per function
//!
//! `Nat.IsMultiplicative f := ∀ a b, gcd a b = 1 → f (a*b) = f a * f b`. The
//! coprimality spelling is `Eq (gcd a b) 1` because that is what the existing
//! [`totient_mul_of_coprime`](super::NatPrelude::totient_mul_of_coprime)
//! already uses; there is no `Nat.Coprime` constant in this prelude
//! (`shape_search --name Nat.Coprime` returns `ABSENT`).
//!
//! `Nat.isMultiplicative_totient` is what makes the interface worth having:
//! Euler's totient was already proved multiplicative in the general form, and
//! this repackages that theorem as a member of the family rather than as a
//! one-off.
//!
//! ## The convolution's commutativity IS the reindexing
//!
//! `Nat.dirichlet f g n := Σ_{d ∣ n} f d · g (n/d)`. Its commutativity is not
//! a new argument: reindex by `d ↦ n/d` (`sumDivisorsBy_reindex`), use
//! `n/(n/d) = d` at every divisor (`div_div_self_of_dvd`), commute the
//! product. That is the whole proof, and it is why the reindexing had to be
//! built first.
//!
//! `Nat.sumDivisorsBy_congr` is the piece that lets the middle step happen:
//! `n/(n/d) = d` holds only AT DIVISORS, so a pointwise congruence for the
//! aggregate must carry `dvdB d n = true` as a hypothesis. The unconditional
//! `Nat.sumRange_congr` cannot state it.
//!
//! ## Möbius is a GRADED PAIR, not a signed number
//!
//! `μ` takes values in `{-1, 0, 1}` and this carrier has no negatives, so `μ`
//! lands as two `Nat`-valued functions in the ADR-0603 style:
//! `Nat.moebiusPos n` is `1` exactly when `μ(n) = +1` and `Nat.moebiusNeg n`
//! is `1` exactly when `μ(n) = -1`. Two theorems tie them together and are
//! what a consumer needs in order to treat the pair as one signed quantity:
//! they sum to `|μ(n)|` (`Nat.moebiusAbs`) and their product is `0`, so at
//! most one is nonzero.
//!
//! Both are built from constants that already existed: `Squarefree`
//! (`squarefree.rs`, at the BARE root namespace, not `Nat.squarefree`) and
//! `Nat.omegaCount n := Multiset.card (factorization n)`, the number of prime
//! factors with multiplicity.
//!
//! ## The driver names the step it failed at
//!
//! [`declare_arith_functions_family_all`] reports the rejected step by name
//! and renders the mismatch, rather than propagating an opaque
//! `TypeMismatch { expected: ExprId(..), got: ExprId(..) }` out of a
//! fourteen-step build. One bad declaration poisons the whole shared prelude,
//! so the failure otherwise says nothing about WHICH declaration is broken —
//! this saved one bisect while the file was being written.
//!
//! **Möbius INVERSION did not land here.** It needs `Σ_{d ∣ n} μ(d) = [n = 1]`,
//! which over a graded pair is `Σ_{d∣n} moebiusPos d = Σ_{d∣n} moebiusNeg d`
//! for `n > 1`, and that identity's proof needs the divisor set of a
//! squarefree number put in bijection with the subsets of its prime factors —
//! machinery that does not exist and is not a corollary of anything here.

use super::NatPrelude;
use super::finite::{select_nat_false, select_nat_true};
use super::ops::{NatDev, NatOps, bool_true_or_false};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::{BinderInfo, ExprId};

/// Delta height for `Nat.dirichlet`: strictly above `Nat.sumDivisorsBy` (5).
const DIRICHLET_HEIGHT: u16 = 6;
/// Delta height for `Nat.omegaCount`, above `Nat.factorization` and
/// `Nat.Multiset.card`.
const OMEGA_HEIGHT: u16 = 8;
/// Delta height for the three Möbius definitions, above `Nat.omegaCount`.
const MOEBIUS_HEIGHT: u16 = 9;

/// `Or.rec` at a `Prop` goal — a private copy of the wrapper
/// `arith_functions.rs` and `subset_search.rs` each keep.
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
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

/// Restate `h : Eq Nat mid rhs` at a definitionally equal left-hand side.
fn restate_lhs(d: &mut NatDev<'_>, a: ExprId, mid: ExprId, rhs: ExprId, h: ExprId) -> ExprId {
    let refl_a = d.refl(a);
    d.trans(a, mid, rhs, refl_a, h)
}

/// Restate `h : Eq Nat lhs mid` at a definitionally equal right-hand side.
fn restate_rhs(d: &mut NatDev<'_>, lhs: ExprId, mid: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let refl_mid = d.refl(mid);
    d.trans(lhs, mid, b, h, refl_mid)
}

/// `Nat.dvdB divisor n`.
fn dvd_b(d: &mut NatDev<'_>, p: &NatPrelude, divisor: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.dvd_b, &[divisor, n])
}

/// `Nat.sumDivisorsBy f n`.
fn sum_divisors_by(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.sum_divisors_by, &[f, n])
}

/// `Nat.dirichlet f g n`.
fn dirichlet(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, g: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.dirichlet, &[f, g, n])
}

/// `Squarefree n` — the BARE-root constant, not `Nat.squarefree`.
fn squarefree(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    d.const_app(p.squarefree, &[n])
}

/// `Nat.beq (Nat.mod (omegaCount n) 2) 0` — "`n` has an even number of prime
/// factors", the sign bit of `μ` on a squarefree argument.
fn omega_even(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let omega = d.const_app(p.omega_count, &[n]);
    let two = d.num(2);
    let remainder = d.modulo(omega, two);
    let zero = d.zero();
    d.beq(remainder, zero)
}

// ============================================================================
// `Nat.sumDivisorsBy_congr`.
// ============================================================================

/// `Nat.sumDivisorsBy_congr : ∀ (f g : Nat → Nat) (n : Nat),
/// (∀ d, Eq Bool (dvdB d n) true → Eq (f d) (g d)) →
/// Eq (sumDivisorsBy f n) (sumDivisorsBy g n)`.
///
/// Bounded BY DIVISIBILITY, not by an index bound: the facts that make two
/// summands agree (`n / (n / d) = d`, say) hold only at divisors, and the
/// unconditional `Nat.sumRange_congr` cannot express that.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_sum_divisors_by_congr(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let zero = d.zero();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // `∀ d, dvdB d n = true → f d = g d`.
    let hyp_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let flag = dvd_b(d, &p, k, n);
        let tv = d.bool_true();
        let is_true = d.bool_eq(flag, tv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let concl = d.eq(fk, gk);
        let inner = d.arrow(is_true, concl);
        d.pi_fv(k_fv, nat, inner)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let bound = d.succ(n);
    let summand = |d: &mut NatDev<'_>, h: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let flag = dvd_b(d, &p, k, n);
        let value = d.apply(h, &[k]);
        let body = d.bool_select_nat(flag, value, zero);
        let nat = d.nat_ty();
        d.lam_fv(k_fv, nat, body)
    };
    let sf = summand(d, f);
    let sg = summand(d, g);

    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let flag = dvd_b(d, &p, k, n);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let lhs = d.bool_select_nat(flag, fk, zero);
        let rhs = d.bool_select_nat(flag, gk, zero);
        let goal = d.eq(lhs, rhs);

        let tv = d.bool_true();
        let false_value = d.bool_false();
        let is_true = d.bool_eq(flag, tv);
        let is_false = d.bool_eq(flag, false_value);
        let decided = bool_true_or_false(d, &p, flag);

        let on_true = {
            let ht_fv = d.fresh_fvar();
            let ht = d.kernel().fvar(ht_fv);
            let lhs_value = select_nat_true(d, flag, fk, zero, ht);
            let rhs_value = select_nat_true(d, flag, gk, zero, ht);
            let rhs_back = d.symm(rhs, gk, rhs_value);
            let agree = d.apply(hyp, &[k, ht]);
            let (_, chained) = d.chain(lhs, &[(fk, lhs_value), (gk, agree), (rhs, rhs_back)]);
            d.lam_fv(ht_fv, is_true, chained)
        };
        let on_false = {
            let hf_fv = d.fresh_fvar();
            let hf = d.kernel().fvar(hf_fv);
            let lhs_zero = select_nat_false(d, flag, fk, zero, hf);
            let rhs_zero = select_nat_false(d, flag, gk, zero, hf);
            let rhs_back = d.symm(rhs, zero, rhs_zero);
            let (_, chained) = d.chain(lhs, &[(zero, lhs_zero), (rhs, rhs_back)]);
            d.lam_fv(hf_fv, is_false, chained)
        };
        let body = or_elim(d, &p, is_true, is_false, goal, on_true, on_false, decided);
        d.lam_fv(k_fv, nat, body)
    };

    let congr_step = d.lemma(p.sum_range_congr, &[sf, sg, bound, pointwise]);
    let lhs = sum_divisors_by(d, &p, f, n);
    let rhs = sum_divisors_by(d, &p, g, n);
    let sum_sf = d.sum_range(sf, bound);
    let sum_sg = d.sum_range(sg, bound);
    let head = restate_lhs(d, lhs, sum_sf, sum_sg, congr_step);
    let body = restate_rhs(d, lhs, sum_sg, rhs, head);

    let goal = d.eq(lhs, rhs);
    let value = {
        let with_hyp = d.lam_fv(hyp_fv, hyp_ty, body);
        let over_n = d.lam_fv(n_fv, nat, with_hyp);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    let ty = {
        let with_hyp = d.arrow(hyp_ty, goal);
        let over_n = d.pi_fv(n_fv, nat, with_hyp);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.sum_divisors_by_congr, ty, value)
}

// ============================================================================
// `Nat.IsMultiplicative`.
// ============================================================================

/// `Nat.IsMultiplicative f := ∀ a b, Eq (gcd a b) 1 →
/// Eq (f (mul a b)) (mul (f a) (f b))`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_is_multiplicative(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let prop = d.kernel().sort_zero();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let g = d.gcd(a, b);
    let one = d.num(1);
    let coprime = d.eq(g, one);
    let product = d.mul(a, b);
    let fab = d.apply(f, &[product]);
    let fa = d.apply(f, &[a]);
    let fb = d.apply(f, &[b]);
    let split = d.mul(fa, fb);
    let concl = d.eq(fab, split);
    let body = {
        let with_coprime = d.arrow(coprime, concl);
        let over_b = d.pi_fv(b_fv, nat, with_coprime);
        d.pi_fv(a_fv, nat, over_b)
    };
    let value = d.lam_fv(f_fv, fn_ty, body);
    let ty = d.arrow(fn_ty, prop);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_multiplicative,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(3),
    })?;
    Ok(())
}

/// `Nat.isMultiplicative_totient : IsMultiplicative totient` — Euler's
/// totient, repackaged into the family interface from the already-proved
/// [`totient_mul_of_coprime`](super::NatPrelude::totient_mul_of_coprime).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_is_multiplicative_totient(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let totient = d.kernel().const_(p.totient, vec![]);
    let ty = d.const_app(p.is_multiplicative, &[totient]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let g = d.gcd(a, b);
    let one = d.num(1);
    let coprime = d.eq(g, one);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let body = d.lemma(p.totient_mul_of_coprime, &[a, b, h]);
    let value = {
        let with_h = d.lam_fv(h_fv, coprime, body);
        let over_b = d.lam_fv(b_fv, nat, with_h);
        d.lam_fv(a_fv, nat, over_b)
    };
    d.declare_theorem(p.is_multiplicative_totient, ty, value)
}

/// `Nat.isMultiplicative_one : IsMultiplicative (fun _ => 1)` — the Dirichlet
/// unit of the convolution monoid's underlying constant function, and the
/// second member of the family, so `IsMultiplicative` is inhabited by more
/// than one thing.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_is_multiplicative_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let constant_one = {
        let k_fv = d.fresh_fvar();
        let one = d.num(1);
        d.lam_fv(k_fv, nat, one)
    };
    let ty = d.const_app(p.is_multiplicative, &[constant_one]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let g = d.gcd(a, b);
    let one = d.num(1);
    let coprime = d.eq(g, one);
    let h_fv = d.fresh_fvar();
    let one_again = d.num(1);
    let body = d.refl(one_again);
    let value = {
        let with_h = d.lam_fv(h_fv, coprime, body);
        let over_b = d.lam_fv(b_fv, nat, with_h);
        d.lam_fv(a_fv, nat, over_b)
    };
    d.declare_theorem(p.is_multiplicative_one, ty, value)
}

// ============================================================================
// `Nat.dirichlet`.
// ============================================================================

/// `Nat.dirichlet f g n := sumDivisorsBy (fun k => mul (f k) (g (div n k))) n`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_dirichlet(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let summand = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let quotient = d.div(n, k);
        let gq = d.apply(g, &[quotient]);
        let body = d.mul(fk, gq);
        d.lam_fv(k_fv, nat, body)
    };
    let body = sum_divisors_by(d, &p, summand, n);

    let value = {
        let over_n = d.lam_fv(n_fv, nat, body);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    let ty = {
        let over_n = d.arrow(nat, nat);
        let over_g = d.arrow(fn_ty, over_n);
        d.arrow(fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.dirichlet,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DIRICHLET_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.dirichlet_comm : ∀ (f g : Nat → Nat) (n : Nat), Lt zero n →
/// Eq (dirichlet f g n) (dirichlet g f n)`.
///
/// Three steps and no new argument: reindex by `d ↦ n/d`, replace
/// `n/(n/d)` by `d` at every divisor, commute the product.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_dirichlet_comm(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let zero = d.zero();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pos_ty = d.lt(zero, n);
    let pos_fv = d.fresh_fvar();
    let n_pos = d.kernel().fvar(pos_fv);

    // `h k := f k * g (n/k)` — the `dirichlet f g n` summand.
    let h = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let quotient = d.div(n, k);
        let gq = d.apply(g, &[quotient]);
        let body = d.mul(fk, gq);
        d.lam_fv(k_fv, nat, body)
    };
    // `h_flip k := f (n/k) * g (n/(n/k))` — `h` after reindexing.
    let h_flip = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let quotient = d.div(n, k);
        let fq = d.apply(f, &[quotient]);
        let inner = d.div(n, quotient);
        let gi = d.apply(g, &[inner]);
        let body = d.mul(fq, gi);
        d.lam_fv(k_fv, nat, body)
    };
    // `h_swap k := g k * f (n/k)` — the `dirichlet g f n` summand.
    let h_swap = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let gk = d.apply(g, &[k]);
        let quotient = d.div(n, k);
        let fq = d.apply(f, &[quotient]);
        let body = d.mul(gk, fq);
        d.lam_fv(k_fv, nat, body)
    };

    let reindex = d.lemma(p.sum_divisors_by_reindex, &[h, n, n_pos]);

    // `∀ k, dvdB k n = true → h_flip k = h_swap k`.
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let flag = dvd_b(d, &p, k, n);
        let tv = d.bool_true();
        let is_true = d.bool_eq(flag, tv);

        let quotient = d.div(n, k);
        let fq = d.apply(f, &[quotient]);
        let inner = d.div(n, quotient);
        let gi = d.apply(g, &[inner]);
        let lhs = d.mul(fq, gi);
        let gk = d.apply(g, &[k]);
        let rhs = d.mul(gk, fq);
        let concl = d.eq(lhs, rhs);

        let ht_fv = d.fresh_fvar();
        let ht = d.kernel().fvar(ht_fv);
        let k_dvd_n = d.lemma(p.dvd_of_dvd_b, &[k, n, ht]);
        // `n / (n / k) = k`.
        let inner_eq = d.lemma(p.div_div_self_of_dvd, &[n, k, n_pos, k_dvd_n]);
        let mid = d.mul(fq, gk);
        let step_a = d.congr(inner, k, inner_eq, &|d, x| {
            let gx = d.apply(g, &[x]);
            d.mul(fq, gx)
        });
        let step_b = d.lemma(p.mul_comm, &[fq, gk]);
        let (_, chained) = d.chain(lhs, &[(mid, step_a), (rhs, step_b)]);

        let body = d.lam_fv(ht_fv, is_true, chained);
        let inner_ty = d.arrow(is_true, concl);
        let _ = inner_ty;
        d.lam_fv(k_fv, nat, body)
    };
    let swap = d.lemma(p.sum_divisors_by_congr, &[h_flip, h_swap, n, pointwise]);

    let lhs = dirichlet(d, &p, f, g, n);
    let rhs = dirichlet(d, &p, g, f, n);
    let sum_h = sum_divisors_by(d, &p, h, n);
    let sum_flip = sum_divisors_by(d, &p, h_flip, n);
    let sum_swap = sum_divisors_by(d, &p, h_swap, n);
    let head = restate_lhs(d, lhs, sum_h, sum_flip, reindex);
    let tail = restate_rhs(d, sum_flip, sum_swap, rhs, swap);
    let body = d.trans(lhs, sum_flip, rhs, head, tail);

    let goal = d.eq(lhs, rhs);
    let value = {
        let with_pos = d.lam_fv(pos_fv, pos_ty, body);
        let over_n = d.lam_fv(n_fv, nat, with_pos);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    let ty = {
        let with_pos = d.arrow(pos_ty, goal);
        let over_n = d.pi_fv(n_fv, nat, with_pos);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.dirichlet_comm, ty, value)
}

/// `Nat.numDivisors_eq_dirichlet : ∀ n,
/// Eq (numDivisors n) (dirichlet (fun _ => 1) (fun _ => 1) n)` — `d = 1 * 1`,
/// closed by `Eq.refl` (`mul 1 1` is a closed numeral).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_num_divisors_eq_dirichlet(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.num_divisors_eq_dirichlet, 1, &|d, v| {
        let n = v[0];
        let nat = d.nat_ty();
        let constant_one = {
            let k_fv = d.fresh_fvar();
            let one = d.num(1);
            d.lam_fv(k_fv, nat, one)
        };
        let constant_one2 = {
            let k_fv = d.fresh_fvar();
            let one = d.num(1);
            d.lam_fv(k_fv, nat, one)
        };
        let lhs = d.const_app(p.num_divisors, &[n]);
        let rhs = dirichlet(d, &p, constant_one, constant_one2, n);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(lhs);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.sumDivisors_eq_dirichlet : ∀ n,
/// Eq (sumDivisors n) (dirichlet (fun k => k) (fun _ => 1) n)` — `σ = id * 1`.
///
/// NOT `Eq.refl`: the summand becomes `mul k 1`, and `Nat.mul k 1` reduces to
/// `add zero k`, which is STUCK because `Nat.add` recurses on its RIGHT
/// argument and `k` is a bound variable. So it goes through `Nat.mul_one`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_sum_divisors_eq_dirichlet(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.sum_divisors_eq_dirichlet, 1, &|d, v| {
        let n = v[0];
        let nat = d.nat_ty();
        let identity = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            d.lam_fv(k_fv, nat, k)
        };
        let constant_one = {
            let k_fv = d.fresh_fvar();
            let one = d.num(1);
            d.lam_fv(k_fv, nat, one)
        };
        // `fun k => mul k 1`, the `dirichlet id one n` summand.
        let scaled = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let one = d.num(1);
            let body = d.mul(k, one);
            d.lam_fv(k_fv, nat, body)
        };

        let pointwise = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let flag = dvd_b(d, &p, k, n);
            let tv = d.bool_true();
            let is_true = d.bool_eq(flag, tv);
            let ht_fv = d.fresh_fvar();
            let one = d.num(1);
            let scaled_k = d.mul(k, one);
            let mul_one = d.lemma(p.mul_one, &[k]);
            let back = d.symm(scaled_k, k, mul_one);
            let body = d.lam_fv(ht_fv, is_true, back);
            d.lam_fv(k_fv, nat, body)
        };
        let congr_step = d.lemma(p.sum_divisors_by_congr, &[identity, scaled, n, pointwise]);

        let lhs = d.const_app(p.sum_divisors, &[n]);
        let identity2 = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            d.lam_fv(k_fv, nat, k)
        };
        let sum_id = sum_divisors_by(d, &p, identity2, n);
        let sum_scaled = sum_divisors_by(d, &p, scaled, n);
        let rhs = dirichlet(d, &p, identity, constant_one, n);
        let head = restate_lhs(d, lhs, sum_id, sum_scaled, congr_step);
        let proof = restate_rhs(d, lhs, sum_scaled, rhs, head);
        let stmt = d.eq(lhs, rhs);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// Möbius, as a graded pair.
// ============================================================================

/// `Nat.omegaCount n := Nat.Multiset.card (Nat.factorization n)` — the number
/// of prime factors of `n` COUNTED WITH MULTIPLICITY (`Ω(n)`, not `ω(n)`).
/// The two agree exactly on the squarefree numbers, which is the only place
/// the Möbius definitions read this.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_omega_count(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let factors = d.const_app(p.factorization, &[n]);
    let body = d.const_app(p.multiset_card, &[factors]);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.omega_count,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(OMEGA_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.moebiusAbs n := bool_select_nat (Squarefree n) 1 0` — `|μ(n)|`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_moebius_abs(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let flag = squarefree(d, &p, n);
    let one = d.num(1);
    let zero = d.zero();
    let body = d.bool_select_nat(flag, one, zero);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.moebius_abs,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MOEBIUS_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.moebiusPos n := if Squarefree n then (if Ω(n) even then 1 else 0)
/// else 0` — `1` exactly when `μ(n) = +1`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_moebius_pos(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let one = d.num(1);
    let zero = d.zero();
    let even = omega_even(d, &p, n);
    let inner = d.bool_select_nat(even, one, zero);
    let flag = squarefree(d, &p, n);
    let body = d.bool_select_nat(flag, inner, zero);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.moebius_pos,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MOEBIUS_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.moebiusNeg n := if Squarefree n then (if Ω(n) even then 0 else 1)
/// else 0` — `1` exactly when `μ(n) = -1`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_moebius_neg(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let one = d.num(1);
    let zero = d.zero();
    let even = omega_even(d, &p, n);
    let inner = d.bool_select_nat(even, zero, one);
    let flag = squarefree(d, &p, n);
    let body = d.bool_select_nat(flag, inner, zero);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.moebius_neg,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MOEBIUS_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.moebius_pos_add_neg : ∀ n,
/// Eq (add (moebiusPos n) (moebiusNeg n)) (moebiusAbs n)` — the graded pair
/// carries exactly `|μ|` between its two halves.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_moebius_pos_add_neg(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.moebius_pos_add_neg, 1, &|d, v| {
        let n = v[0];
        let pos = d.const_app(p.moebius_pos, &[n]);
        let neg = d.const_app(p.moebius_neg, &[n]);
        let lhs = d.add(pos, neg);
        let rhs = d.const_app(p.moebius_abs, &[n]);
        let stmt = d.eq(lhs, rhs);

        let one = d.num(1);
        let zero = d.zero();
        let flag = squarefree(d, &p, n);
        let even = omega_even(d, &p, n);
        let tv = d.bool_true();
        let false_value = d.bool_false();

        // The squarefree dichotomy.
        let sf_true = d.bool_eq(flag, tv);
        let sf_false = d.bool_eq(flag, false_value);
        let sf_decided = bool_true_or_false(d, &p, flag);

        let on_square = {
            let hf_fv = d.fresh_fvar();
            let hf = d.kernel().fvar(hf_fv);
            // Every selector goes to the `0` branch, and `0 + 0 = 0`.
            let inner_pos = d.bool_select_nat(even, one, zero);
            let inner_neg = d.bool_select_nat(even, zero, one);
            let sel_pos = d.bool_select_nat(flag, inner_pos, zero);
            let sel_neg = d.bool_select_nat(flag, inner_neg, zero);
            let sel_abs = d.bool_select_nat(flag, one, zero);
            let pos_zero = select_nat_false(d, flag, inner_pos, zero, hf);
            let neg_zero = select_nat_false(d, flag, inner_neg, zero, hf);
            let abs_zero = select_nat_false(d, flag, one, zero, hf);
            let abs_zero = restate_lhs(d, rhs, sel_abs, zero, abs_zero);
            let abs_back = d.symm(rhs, zero, abs_zero);
            let pos_zero = restate_lhs(d, pos, sel_pos, zero, pos_zero);
            let neg_zero = restate_lhs(d, neg, sel_neg, zero, neg_zero);
            let step_pos = d.congr(pos, zero, pos_zero, &|d, x| {
                let neg = d.const_app(p.moebius_neg, &[n]);
                d.add(x, neg)
            });
            let mid = d.add(zero, neg);
            let step_neg = d.congr(neg, zero, neg_zero, &|d, x| {
                let zero = d.zero();
                d.add(zero, x)
            });
            let both = d.add(zero, zero);
            let (_, chained) = d.chain(lhs, &[(mid, step_pos), (both, step_neg), (rhs, abs_back)]);
            d.lam_fv(hf_fv, sf_false, chained)
        };
        let on_squarefree = {
            let hs_fv = d.fresh_fvar();
            let hs = d.kernel().fvar(hs_fv);
            let inner_pos = d.bool_select_nat(even, one, zero);
            let inner_neg = d.bool_select_nat(even, zero, one);
            let sel_pos = d.bool_select_nat(flag, inner_pos, zero);
            let sel_neg = d.bool_select_nat(flag, inner_neg, zero);
            let sel_abs = d.bool_select_nat(flag, one, zero);
            let pos_sel = select_nat_true(d, flag, inner_pos, zero, hs);
            let neg_sel = select_nat_true(d, flag, inner_neg, zero, hs);
            let abs_one = select_nat_true(d, flag, one, zero, hs);
            let abs_one = restate_lhs(d, rhs, sel_abs, one, abs_one);
            let abs_back = d.symm(rhs, one, abs_one);
            let pos_sel = restate_lhs(d, pos, sel_pos, inner_pos, pos_sel);
            let neg_sel = restate_lhs(d, neg, sel_neg, inner_neg, neg_sel);

            let even_true = d.bool_eq(even, tv);
            let even_false = d.bool_eq(even, false_value);
            let even_decided = bool_true_or_false(d, &p, even);
            let goal = d.eq(lhs, rhs);

            let on_even = {
                let he_fv = d.fresh_fvar();
                let he = d.kernel().fvar(he_fv);
                let pos_one = select_nat_true(d, even, one, zero, he);
                // `inner_neg` selects `zero` on TRUE, so at `even = true` it
                // is `zero` -- `select_nat_true` at `(zero, one)`.
                let neg_zero = select_nat_true(d, even, zero, one, he);
                let pos_eq = d.trans(pos, inner_pos, one, pos_sel, pos_one);
                let neg_eq = d.trans(neg, inner_neg, zero, neg_sel, neg_zero);
                let step_pos = d.congr(pos, one, pos_eq, &|d, x| {
                    let neg = d.const_app(p.moebius_neg, &[n]);
                    d.add(x, neg)
                });
                let mid = d.add(one, neg);
                let step_neg = d.congr(neg, zero, neg_eq, &|d, x| {
                    let one = d.num(1);
                    d.add(one, x)
                });
                let both = d.add(one, zero);
                let (_, chained) =
                    d.chain(lhs, &[(mid, step_pos), (both, step_neg), (rhs, abs_back)]);
                d.lam_fv(he_fv, even_true, chained)
            };
            let on_odd = {
                let ho_fv = d.fresh_fvar();
                let ho = d.kernel().fvar(ho_fv);
                let pos_zero = select_nat_false(d, even, one, zero, ho);
                let neg_one = select_nat_false(d, even, zero, one, ho);
                let pos_eq = d.trans(pos, inner_pos, zero, pos_sel, pos_zero);
                let neg_eq = d.trans(neg, inner_neg, one, neg_sel, neg_one);
                let step_pos = d.congr(pos, zero, pos_eq, &|d, x| {
                    let neg = d.const_app(p.moebius_neg, &[n]);
                    d.add(x, neg)
                });
                let mid = d.add(zero, neg);
                let step_neg = d.congr(neg, one, neg_eq, &|d, x| {
                    let zero = d.zero();
                    d.add(zero, x)
                });
                let both = d.add(zero, one);
                let (_, chained) =
                    d.chain(lhs, &[(mid, step_pos), (both, step_neg), (rhs, abs_back)]);
                d.lam_fv(ho_fv, even_false, chained)
            };
            let body = or_elim(
                d,
                &p,
                even_true,
                even_false,
                goal,
                on_even,
                on_odd,
                even_decided,
            );
            d.lam_fv(hs_fv, sf_true, body)
        };
        let proof = or_elim(
            d,
            &p,
            sf_true,
            sf_false,
            stmt,
            on_squarefree,
            on_square,
            sf_decided,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.moebius_pos_mul_neg : ∀ n, Eq (mul (moebiusPos n) (moebiusNeg n)) 0`
/// — at most one half of the graded pair is nonzero, so the pair really does
/// encode a single signed value.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_moebius_pos_mul_neg(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.moebius_pos_mul_neg, 1, &|d, v| {
        let n = v[0];
        let pos = d.const_app(p.moebius_pos, &[n]);
        let neg = d.const_app(p.moebius_neg, &[n]);
        let lhs = d.mul(pos, neg);
        let zero = d.zero();
        let stmt = d.eq(lhs, zero);

        let one = d.num(1);
        let flag = squarefree(d, &p, n);
        let even = omega_even(d, &p, n);
        let tv = d.bool_true();
        let false_value = d.bool_false();
        let inner_pos = d.bool_select_nat(even, one, zero);
        let inner_neg = d.bool_select_nat(even, zero, one);

        let sf_true = d.bool_eq(flag, tv);
        let sf_false = d.bool_eq(flag, false_value);
        let sf_decided = bool_true_or_false(d, &p, flag);

        // `mul x 0 = 0` closes every branch where the SECOND factor is `0`;
        // `mul 0 x` is stuck at a symbolic `x`, so the branches are arranged
        // to reduce the right-hand factor first.
        let on_square = {
            let hf_fv = d.fresh_fvar();
            let hf = d.kernel().fvar(hf_fv);
            let sel_neg = d.bool_select_nat(flag, inner_neg, zero);
            let neg_zero = select_nat_false(d, flag, inner_neg, zero, hf);
            let neg_zero = restate_lhs(d, neg, sel_neg, zero, neg_zero);
            let step = d.congr(neg, zero, neg_zero, &|d, x| {
                let pos = d.const_app(p.moebius_pos, &[n]);
                d.mul(pos, x)
            });
            let collapsed = d.mul(pos, zero);
            let mul_zero = d.lemma(p.mul_zero, &[pos]);
            let (_, chained) = d.chain(lhs, &[(collapsed, step), (zero, mul_zero)]);
            d.lam_fv(hf_fv, sf_false, chained)
        };
        let on_squarefree = {
            let hs_fv = d.fresh_fvar();
            let hs = d.kernel().fvar(hs_fv);
            let sel_pos = d.bool_select_nat(flag, inner_pos, zero);
            let sel_neg = d.bool_select_nat(flag, inner_neg, zero);
            let pos_sel = select_nat_true(d, flag, inner_pos, zero, hs);
            let neg_sel = select_nat_true(d, flag, inner_neg, zero, hs);
            let pos_sel = restate_lhs(d, pos, sel_pos, inner_pos, pos_sel);
            let neg_sel = restate_lhs(d, neg, sel_neg, inner_neg, neg_sel);

            let even_true = d.bool_eq(even, tv);
            let even_false = d.bool_eq(even, false_value);
            let even_decided = bool_true_or_false(d, &p, even);
            let goal = d.eq(lhs, zero);

            let on_even = {
                // `neg = 0`, so `pos * 0 = 0`.
                let he_fv = d.fresh_fvar();
                let he = d.kernel().fvar(he_fv);
                let neg_zero = select_nat_true(d, even, zero, one, he);
                let neg_eq = d.trans(neg, inner_neg, zero, neg_sel, neg_zero);
                let step = d.congr(neg, zero, neg_eq, &|d, x| {
                    let pos = d.const_app(p.moebius_pos, &[n]);
                    d.mul(pos, x)
                });
                let collapsed = d.mul(pos, zero);
                let mul_zero = d.lemma(p.mul_zero, &[pos]);
                let (_, chained) = d.chain(lhs, &[(collapsed, step), (zero, mul_zero)]);
                d.lam_fv(he_fv, even_true, chained)
            };
            let on_odd = {
                // `pos = 0`, so `0 * neg = 0` -- via `zero_mul`.
                let ho_fv = d.fresh_fvar();
                let ho = d.kernel().fvar(ho_fv);
                let pos_zero = select_nat_false(d, even, one, zero, ho);
                let pos_eq = d.trans(pos, inner_pos, zero, pos_sel, pos_zero);
                let step = d.congr(pos, zero, pos_eq, &|d, x| {
                    let neg = d.const_app(p.moebius_neg, &[n]);
                    d.mul(x, neg)
                });
                let collapsed = d.mul(zero, neg);
                let zero_mul = d.lemma(p.zero_mul, &[neg]);
                let (_, chained) = d.chain(lhs, &[(collapsed, step), (zero, zero_mul)]);
                d.lam_fv(ho_fv, even_false, chained)
            };
            let body = or_elim(
                d,
                &p,
                even_true,
                even_false,
                goal,
                on_even,
                on_odd,
                even_decided,
            );
            d.lam_fv(hs_fv, sf_true, body)
        };
        let proof = or_elim(
            d,
            &p,
            sf_true,
            sf_false,
            stmt,
            on_squarefree,
            on_square,
            sf_decided,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare every `arith_functions_family.rs` result, in dependency order.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_arith_functions_family_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    if let Err(e) = declare_sum_divisors_by_congr(d, p) {
        let msg = d.explain(&e);
        eprintln!("arith-family: declare_sum_divisors_by_congr rejected: {msg}");
        return Err(e);
    }
    if let Err(e) = declare_is_multiplicative(d, p) {
        let msg = d.explain(&e);
        eprintln!("arith-family: declare_is_multiplicative rejected: {msg}");
        return Err(e);
    }
    if let Err(e) = declare_is_multiplicative_totient(d, p) {
        let msg = d.explain(&e);
        eprintln!("arith-family: declare_is_multiplicative_totient rejected: {msg}");
        return Err(e);
    }
    if let Err(e) = declare_is_multiplicative_one(d, p) {
        let msg = d.explain(&e);
        eprintln!("arith-family: declare_is_multiplicative_one rejected: {msg}");
        return Err(e);
    }
    if let Err(e) = declare_dirichlet(d, p) {
        let msg = d.explain(&e);
        eprintln!("arith-family: declare_dirichlet rejected: {msg}");
        return Err(e);
    }
    if let Err(e) = declare_dirichlet_comm(d, p) {
        let msg = d.explain(&e);
        eprintln!("arith-family: declare_dirichlet_comm rejected: {msg}");
        return Err(e);
    }
    if let Err(e) = declare_num_divisors_eq_dirichlet(d, p) {
        let msg = d.explain(&e);
        eprintln!("arith-family: declare_num_divisors_eq_dirichlet rejected: {msg}");
        return Err(e);
    }
    if let Err(e) = declare_sum_divisors_eq_dirichlet(d, p) {
        let msg = d.explain(&e);
        eprintln!("arith-family: declare_sum_divisors_eq_dirichlet rejected: {msg}");
        return Err(e);
    }
    if let Err(e) = declare_omega_count(d, p) {
        let msg = d.explain(&e);
        eprintln!("arith-family: declare_omega_count rejected: {msg}");
        return Err(e);
    }
    if let Err(e) = declare_moebius_abs(d, p) {
        let msg = d.explain(&e);
        eprintln!("arith-family: declare_moebius_abs rejected: {msg}");
        return Err(e);
    }
    if let Err(e) = declare_moebius_pos(d, p) {
        let msg = d.explain(&e);
        eprintln!("arith-family: declare_moebius_pos rejected: {msg}");
        return Err(e);
    }
    if let Err(e) = declare_moebius_neg(d, p) {
        let msg = d.explain(&e);
        eprintln!("arith-family: declare_moebius_neg rejected: {msg}");
        return Err(e);
    }
    if let Err(e) = declare_moebius_pos_add_neg(d, p) {
        let msg = d.explain(&e);
        eprintln!("arith-family: declare_moebius_pos_add_neg rejected: {msg}");
        return Err(e);
    }
    if let Err(e) = declare_moebius_pos_mul_neg(d, p) {
        let msg = d.explain(&e);
        eprintln!("arith-family: declare_moebius_pos_mul_neg rejected: {msg}");
        return Err(e);
    }
    Ok(())
}
