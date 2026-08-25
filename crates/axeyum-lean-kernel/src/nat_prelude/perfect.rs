//! The divisor sum and perfect numbers.
//!
//! [`declare_sum_divisors`] is `Nat.sumDivisors n := sumRange (fun d =>
//! bool_select_nat (beq (mod n d) 0) d 0) (succ n)` — the sum of every `d` in
//! `[0,n]` (the range is `succ n` so `n` itself is included) that divides
//! `n`, weighted by `d` itself rather than counted. This reuses the existing
//! [`super::defs::declare_finite_ranges`]'s `sumRange` and
//! [`NatOps::bool_select_nat`]'s `if`, exactly `totient.rs`'s
//! `totient_predicate`/`declare_totient` pattern (`countRange` in place of
//! `sumRange`, a divisor-value in place of a `1`/`0` count).
//!
//! `d = 0` never contributes: `bool_select_nat (beq (mod n 0) 0) 0 0` is `0`
//! on EITHER branch (the `on_true` value is `0` too, since the witness `d`
//! itself is `0`), so no lemma about `0 ∣ n` is needed to discharge it — it
//! is `Eq.refl` by construction. This matters downstream: `sumRange_shiftFront`
//! (`binomial.rs`) peels the `d = 0` term off for free.
//!
//! [`declare_perfect`] is `Nat.Perfect n := Eq (sumDivisors n) (mul 2 n)` —
//! summing *all* divisors including `n` itself, so the classical "sum of
//! proper divisors equals n" phrasing is NOT what this states; that phrasing
//! needs `Nat.sub`, which is truncated here and would silently mask an
//! off-by-one. `sumDivisors n = 2n` is subtraction-free and equivalent.
//!
//! [`declare_sum_divisors_one`] is the first sanity theorem,
//! `sumDivisors (succ zero) = succ zero`, closed by a single `Eq.refl` —
//! `sumDivisors 1` is a closed numeral and the whole computation is
//! definitional.
//!
//! [`declare_sum_divisors_prime`] is `Prime p → sumDivisors p = succ p`: a
//! prime's only divisors in `[0,p]` are `1` and `p`. Built in terms of
//! `n := succ (pred p)` exactly `totient.rs`'s `totient_prime` convention, so
//! `sumRange_shiftFront` sees a literal successor and the divisor bound
//! `m := pred n` is a literal predecessor; transported back to `p` only at
//! the very end. The executable bridge `mod value (succ j) = 0 ↔ dvd
//! (succ j) value` is assembled from
//! [`super::division::declare_executable_division_spec`]'s `div_mod_exec`
//! (the executable `div`/`mod` satisfy the relational `divMod` spec, for a
//! `succ`-shaped divisor) composed with
//! [`super::divisibility::declare_divisibility`]'s
//! `div_mod_remainder_eq_zero_iff_dvd` — NOT `mod_eq_zero_iff_dvd`
//! (`modular.rs`), which is the unrelated *balanced-witness congruence*
//! `modEq`, not the executable `Nat.mod`.
//!
//! The core fact `sumRange (fun k => f (succ k)) m = 1` (only `k = 0`, i.e.
//! divisor `1`, contributes below `m = pred n`) is proved by induction on a
//! generalized bound with hypothesis `Lt _ n`, case-splitting each step on
//! `beq j 0` (the SAME split resolves both the inductive hypothesis and the
//! new top divisor `succ j`, since both depend on exactly the same
//! condition) — unlike `totient.rs`'s `countRange_eq_pred_of_only_zero_false`
//! (uniformly true on `(0,n)`), this predicate is true at exactly the ONE
//! point `1`, so there is no uniform hypothesis to restrict; the split is
//! unavoidable.

use super::NatPrelude;
use super::helpers::and_right;
use super::helpers::{and_left, iff_forward, iff_reverse, transport_dvd_left, transport_dvd_right};
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

// ============================================================================
// `Nat.sumDivisors`.
// ============================================================================

/// `fun d => bool_select_nat (beq (mod n d) 0) d 0` — the per-divisor term at
/// a fixed `n`, matching `totient.rs`'s `totient_predicate` shape.
fn sum_divisors_term(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let divisor_fv = d.fresh_fvar();
    let divisor = d.kernel().fvar(divisor_fv);
    let remainder = d.modulo(n, divisor);
    let zero = d.zero();
    let cond = d.beq(remainder, zero);
    let body = d.bool_select_nat(cond, divisor, zero);
    d.lam_fv(divisor_fv, nat, body)
}

/// `sumDivisors(d, p, n)`, i.e. `d.const_app(p.sum_divisors, &[n])`.
fn sum_divisors(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    d.const_app(p.sum_divisors, &[n])
}

/// `Nat.sumDivisors n := sumRange (fun d => bool_select_nat (beq (mod n d) 0)
/// d 0) (succ n)`.
pub(super) fn declare_sum_divisors(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let f = sum_divisors_term(d, n);
    let bound = d.succ(n);
    let body = d.sum_range(f, bound);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sum_divisors,
        uparams: vec![],
        ty,
        value,
        // Strictly greater than `sum_range` (2) and `mod_`/`div` (3), the two
        // definitions this calls.
        hint: ReducibilityHint::Regular(4),
    })?;
    Ok(())
}

/// `Nat.sumDivisors_one : Eq (sumDivisors (succ zero)) (succ zero)` — closed
/// by `Eq.refl`: `sumDivisors 1` is a numeral, so the whole `sumRange`
/// unrolls by pure `β`/`δ`/`ι` reduction.
pub(super) fn declare_sum_divisors_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let one = d.num(1);
    let lhs = sum_divisors(d, &p, one);
    let one2 = d.num(1);
    let proof = d.refl(lhs);
    let ty = d.eq(lhs, one2);
    d.declare_theorem(p.sum_divisors_one, ty, proof)
}

// ============================================================================
// `Nat.Perfect`.
// ============================================================================

/// `Nat.Perfect n := Eq (sumDivisors n) (mul 2 n)` — summing *all* divisors
/// including `n` itself (the "sum of proper divisors" phrasing needs
/// `Nat.sub`, truncated here, and this form avoids it entirely).
pub(super) fn declare_perfect(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let sum = sum_divisors(d, &p, n);
    let two = d.num(2);
    let twice = d.mul(two, n);
    let body = d.eq(sum, twice);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, prop);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.perfect,
        uparams: vec![],
        ty,
        value,
        // Strictly greater than `sum_divisors` (4) and `mul` (2).
        hint: ReducibilityHint::Regular(5),
    })?;
    Ok(())
}

// ============================================================================
// Shared local combinators for `Nat.sumDivisors_prime` (this prelude's
// per-file convention: local copies rather than a shared private module —
// see `totient.rs`'s and `fermat.rs`'s own doc comments).
// ============================================================================

/// `2 ≤ x`, `∀ c, c ∣ x → c = 1 ∨ c = x`.
fn prime_parts(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let two = d.num(2);
    let one = d.num(1);
    let two_le = d.le(two, x);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hyp = d.dvd(c, x);
    let is_one = d.eq(c, one);
    let is_x = d.eq(c, x);
    let disjunction = d.const_app(p.logic.or, &[is_one, is_x]);
    let inner = d.arrow(hyp, disjunction);
    let divisor_clause = d.pi_fv(c_fv, nat, inner);
    (two_le, divisor_clause)
}

/// `(2 ≤ x) ∧ (∀ c, c ∣ x → c = 1 ∨ c = x)`.
fn prime_ty(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let (two_le, divisor_clause) = prime_parts(d, p, x);
    d.const_app(p.logic.and, &[two_le, divisor_clause])
}

/// `prime x → Lt zero x`.
fn prime_pos(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, prime_proof: ExprId) -> ExprId {
    let (two_le_ty, divisor_clause_ty) = prime_parts(d, p, x);
    let two_le = super::helpers::and_left(d, two_le_ty, divisor_clause_ty, prime_proof);
    let one = d.num(1);
    let two = d.num(2);
    let one_le_two = d.lemma(p.le_succ, &[one]);
    d.lemma(p.le_trans, &[one, two, x, one_le_two, two_le])
}

/// `Lt zero n → Eq n (succ (pred n))`.
fn pos_implies_succ_pred(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let zero = d.zero();
        let hyp = d.lt(zero, x);
        let px = d.pred(x);
        let spx = d.succ(px);
        let concl = d.eq(x, spx);
        d.arrow(hyp, concl)
    };
    d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp_ty = d.lt(zero, zero);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let px = d.pred(zero);
            let spx = d.succ(px);
            let target = d.eq(zero, spx);
            let irrefl = d.lemma(p.lt_irrefl, &[zero]);
            let absurd = d.apply(irrefl, &[hyp]);
            let motive_false = {
                let anon = d.anon_name();
                d.kernel().lam(anon, false_ty, target, BinderInfo::Default)
            };
            let level_zero = d.kernel().level_zero();
            let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
            let body = d.apply(false_rec, &[motive_false, absurd]);
            d.lam_fv(hyp_fv, hyp_ty, body)
        },
        &|d, j, _ih| {
            let sj = d.succ(j);
            let hyp_ty = {
                let zero = d.zero();
                d.lt(zero, sj)
            };
            let hyp_fv = d.fresh_fvar();
            // `pred (succ j) ≡ j`, so `succ (pred (succ j)) ≡ succ j`: the
            // whole equation is `Eq.refl` and the hypothesis is unused.
            let proof = d.refl(sj);
            d.lam_fv(hyp_fv, hyp_ty, proof)
        },
        n,
    )
}

/// `h : Eq Bool a b ⊢ Eq Nat (f a) (f b)`, for `f : Bool → Nat` — local copy
/// of `totient.rs`'s own local `bool_congr_nat`.
fn bool_congr_nat(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.bool_eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.eq(fa, fx)
    });
    let refl_case = d.refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `h : Eq Nat a b ⊢ Eq Bool (f a) (f b)`, for `f : Nat → Bool` — the
/// Bool-codomain analogue of [`bool_congr_nat`] (hardcoded to a
/// `Nat`-domain `f`), local copy of `totient.rs`'s own local
/// `nat_congr_bool`.
fn nat_congr_bool(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.bool_eq(fa, fx)
    });
    let refl_case = d.bool_refl(fa);
    d.transport(a, motive, refl_case, b, h)
}

/// `Or (Eq Bool b true) (Eq Bool b false)`, for an arbitrary `b : Bool` —
/// local copy of `totient.rs`'s `bool_true_or_false`.
fn bool_true_or_false(d: &mut NatDev<'_>, p: &NatPrelude, b: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let true_inner = d.bool_true();
        let false_inner = d.bool_false();
        let is_true = d.bool_eq(x, true_inner);
        let is_false = d.bool_eq(x, false_inner);
        let body = d.const_app(p.logic.or, &[is_true, is_false]);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let case_true = {
        let is_true = d.bool_eq(true_, true_);
        let is_false = d.bool_eq(true_, false_);
        let refl_true = d.bool_refl(true_);
        d.const_app(p.logic.or_inl, &[is_true, is_false, refl_true])
    };
    let case_false = {
        let is_true = d.bool_eq(false_, true_);
        let is_false = d.bool_eq(false_, false_);
        let refl_false = d.bool_refl(false_);
        d.const_app(p.logic.or_inr, &[is_true, is_false, refl_false])
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false, case_true, b])
}

/// `fun k => f (succ k)` — local copy of `binomial.rs`'s private
/// `shifted_fn`, the function `sumRange_shiftFront` peels the front term
/// against.
fn shifted_fn(d: &mut NatDev<'_>, f: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let sk = d.succ(k);
    let body = d.apply(f, &[sk]);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `Iff (Eq Nat (mod value (succ j)) zero) (dvd (succ j) value)` — the
/// executable bridge, for a `succ`-shaped divisor. Composes `div_mod_exec`
/// (the executable `div`/`mod` satisfy the relational `divMod` spec) with
/// `div_mod_remainder_eq_zero_iff_dvd` (`divisibility.rs`).
fn mod_eq_zero_iff_dvd_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    j: ExprId,
    value: ExprId,
) -> ExprId {
    let divisor = d.succ(j);
    let quotient = d.div(value, divisor);
    let remainder = d.modulo(value, divisor);
    let relation = d.lemma(p.div_mod_exec, &[j, value]);
    d.lemma(
        p.div_mod_remainder_eq_zero_iff_dvd,
        &[divisor, value, quotient, remainder, relation],
    )
}

/// `bool_select_nat cond on_true on_false`, congruence-rewritten along
/// `h : Eq Bool cond target_cond`, giving `Eq Nat (select cond on_true
/// on_false) (select target_cond on_true on_false)` — the caller chains this
/// against `Eq.refl` at whichever literal branch `target_cond` selects.
fn select_congr(
    d: &mut NatDev<'_>,
    cond: ExprId,
    target_cond: ExprId,
    h: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    bool_congr_nat(d, cond, target_cond, h, &|d, x| {
        d.bool_select_nat(x, on_true, on_false)
    })
}

/// `Not (dvd c pp)`, from `c ≠ 1`, `c ≠ pp`, and `pp`'s primality (the
/// divisor clause forces `c = 1 ∨ c = pp`, and both disjuncts are refuted).
fn not_dvd_of_ne_one_ne_self(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    prime_proof_pp: ExprId,
    c: ExprId,
    c_ne_one: ExprId,
    c_ne_pp: ExprId,
) -> ExprId {
    let p = *p;
    let dvd_fv = d.fresh_fvar();
    let dvd_hyp = d.kernel().fvar(dvd_fv);
    let dvd_ty = d.dvd(c, pp);

    let (two_le_ty, divisor_clause_ty) = prime_parts(d, &p, pp);
    let divisor_fact = and_right(d, two_le_ty, divisor_clause_ty, prime_proof_pp);
    let or_proof = d.apply(divisor_fact, &[c, dvd_hyp]);

    let one = d.num(1);
    let is_one = d.eq(c, one);
    let is_pp = d.eq(c, pp);
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);

    let left_branch = {
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let absurd = d.apply(c_ne_one, &[h1]);
        d.lam_fv(h1_fv, is_one, absurd)
    };
    let right_branch = {
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let absurd = d.apply(c_ne_pp, &[h2]);
        d.lam_fv(h2_fv, is_pp, absurd)
    };
    let motive_or = {
        let or_ty = d.const_app(p.logic.or, &[is_one, is_pp]);
        let anon = d.anon_name();
        d.kernel().lam(anon, or_ty, false_ty, BinderInfo::Default)
    };
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    let body = d.apply(
        or_rec,
        &[
            is_one,
            is_pp,
            motive_or,
            left_branch,
            right_branch,
            or_proof,
        ],
    );
    d.lam_fv(dvd_fv, dvd_ty, body)
}

/// `Not (Eq c pp)`, from `Lt c pp` (`c = pp` would give `Lt pp pp`, refuted
/// by `lt_irrefl`).
fn ne_of_lt(d: &mut NatDev<'_>, p: &NatPrelude, c: ExprId, pp: ExprId, lt_c_pp: ExprId) -> ExprId {
    let eq_fv = d.fresh_fvar();
    let eq_hyp = d.kernel().fvar(eq_fv);
    let eq_ty = d.eq(c, pp);
    let motive = d.eq_motive(c, &|d, x| d.lt(x, pp));
    let lt_pp_pp = d.transport(c, motive, lt_c_pp, pp, eq_hyp);
    let irrefl = d.lemma(p.lt_irrefl, &[pp]);
    let absurd = d.apply(irrefl, &[lt_pp_pp]);
    d.lam_fv(eq_fv, eq_ty, absurd)
}

/// `Eq Nat (g j) w`'s justification for one boolean branch: `cond = lit` is
/// given by `h`, and `w` is whichever value `select(lit, on_true, on_false)`
/// reduces to (the caller supplies `w` and relies on it being the correct
/// defeq reduct).
#[allow(clippy::too_many_arguments)]
fn resolve_select(
    d: &mut NatDev<'_>,
    gj: ExprId,
    cond: ExprId,
    lit: ExprId,
    h: ExprId,
    on_true: ExprId,
    on_false: ExprId,
    w: ExprId,
) -> ExprId {
    let step1 = select_congr(d, cond, lit, h, on_true, on_false);
    let selected = d.bool_select_nat(lit, on_true, on_false);
    let step2 = d.refl(selected); // used at type `Eq selected w` via defeq
    let (_e, proof) = d.chain(gj, &[(selected, step1), (w, step2)]);
    proof
}

/// `Nat.sumDivisors_prime : Prime pp → Eq (sumDivisors pp) (succ pp)`.
///
/// Built in terms of `n := succ m` (`m := pred pp`), exactly `totient_prime`'s
/// convention. `sumDivisors n = f 0 + sumRange g n` (`sumRange_shiftFront`,
/// `g k := f (succ k)`) with `f 0 ≡ 0`, so `sumDivisors n = sumRange g n`. A
/// general induction (`sum_over_below`, below) gives `sumRange g m = 1`
/// (`m = pred n`, resolved to `1` — not `0` — using primality's `2 ≤ n`), and
/// `g m = n` directly (`n` divides itself). `sumRange g n ≡ sumRange g m + g
/// m = 1 + n = n + 1 = succ n` (`add_comm` for the last step, since `add`
/// recurses on its right argument and `1 + n` does not reduce for symbolic
/// `n`). The whole result is transported from `n` back to `pp` at the end.
pub(super) fn declare_sum_divisors_prime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.sum_divisors_prime, 1, &|d, v| {
        let pp = v[0];
        let prime_ty_pp = prime_ty(d, &p, pp);
        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);

        let zero_lt_pp = prime_pos(d, &p, pp, prime_proof);
        let eq_pp_n_fn = pos_implies_succ_pred(d, &p, pp);
        let eq_pp_n = d.apply(eq_pp_n_fn, &[zero_lt_pp]); // Eq pp n
        let m = d.pred(pp);
        let n = d.succ(m);
        let eq_n_pp = d.symm(pp, n, eq_pp_n); // Eq n pp

        let transport_motive = d.eq_motive(pp, &|d, x| prime_ty(d, &p, x));
        let prime_proof_n = d.transport(pp, transport_motive, prime_proof, n, eq_pp_n);

        let f = sum_divisors_term(d, n);
        let g = shifted_fn(d, f);

        // ---- the general fact: `Lt mm n -> sumRange g mm = [mm = 0] 0 1` --
        let sum_motive = |d: &mut NatDev<'_>, mm: ExprId| -> ExprId {
            let lt_ty = d.lt(mm, n);
            let sr = d.sum_range(g, mm);
            let zero = d.zero();
            let cond = d.beq(mm, zero);
            let one = d.num(1);
            let rhs = d.bool_select_nat(cond, zero, one);
            let eq_ty = d.eq(sr, rhs);
            d.arrow(lt_ty, eq_ty)
        };
        let sum_below_proof = d.induct(
            &sum_motive,
            &|d| {
                // `Lt 0 n -> sumRange g 0 = select(beq 0 0, 0, 1)`. Both
                // sides reduce to `0` by pure `ι`-reduction.
                let hyp_fv = d.fresh_fvar();
                let lt_ty = {
                    let zero = d.zero();
                    d.lt(zero, n)
                };
                let sr0 = {
                    let zero = d.zero();
                    d.sum_range(g, zero)
                };
                let proof = d.refl(sr0);
                d.lam_fv(hyp_fv, lt_ty, proof)
            },
            &|d, j, ih| {
                let sj = d.succ(j);
                let lt_fv = d.fresh_fvar();
                let lt_sj_n = d.kernel().fvar(lt_fv);
                let lt_ty = d.lt(sj, n);

                // `Lt j n`, from `Lt sj n` (`Le sj (succ sj)` + transitivity;
                // `Lt a b := Le (succ a) b`, so this is exactly `Lt j n`).
                let lt_j_n = {
                    let ssj = d.succ(sj);
                    let le_sj_ssj = d.lemma(p.le_succ, &[sj]);
                    d.lemma(p.le_trans, &[sj, ssj, n, le_sj_ssj, lt_sj_n])
                };
                let ih_val = d.apply(ih, &[lt_j_n]);

                let zero = d.zero();
                let one = d.num(1);
                let gj = {
                    let mm = d.modulo(n, sj);
                    let cond = d.beq(mm, zero);
                    d.bool_select_nat(cond, sj, zero)
                };
                let sum_g_j = d.sum_range(g, j);
                let bridge = mod_eq_zero_iff_dvd_succ(d, &p, j, n);
                let mod_eq_zero_ty = {
                    let mm = d.modulo(n, sj);
                    d.eq(mm, zero)
                };
                let dvd_ty = d.dvd(sj, n);

                let beq_j0 = d.beq(j, zero);
                let cases = bool_true_or_false(d, &p, beq_j0);
                let bool_true_lit = d.bool_true();
                let bool_false_lit = d.bool_false();
                let true_ty = d.bool_eq(beq_j0, bool_true_lit);
                let false_ty = d.bool_eq(beq_j0, bool_false_lit);

                let target = {
                    let lhs = d.add(sum_g_j, gj);
                    d.eq(lhs, one)
                };

                let true_branch = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);

                    let j_eq_0 = d.lemma(p.eq_of_beq_eq_true, &[j, zero, h]);
                    let sum_g_j_eq_0 = {
                        let sel = d.bool_select_nat(beq_j0, zero, one);
                        let bool_true_lit = d.bool_true();
                        let cong = bool_congr_nat(d, beq_j0, bool_true_lit, h, &|d, x| {
                            let zero_i = d.zero();
                            let one_i = d.num(1);
                            d.bool_select_nat(x, zero_i, one_i)
                        });
                        let bool_true_lit2 = d.bool_true();
                        let sel_true = d.bool_select_nat(bool_true_lit2, zero, one);
                        let step2 = d.refl(sel_true); // defeq to `0`
                        let (_e, proof) =
                            d.chain(sum_g_j, &[(sel, ih_val), (sel_true, cong), (zero, step2)]);
                        proof
                    };

                    // `succ j = 1`, from `j = 0`.
                    let sj_eq_1 = d.congr(j, zero, j_eq_0, &|d, x| d.succ(x));

                    // `dvd 1 n`, unconditionally (`n = 1 * n`).
                    let dvd_1_n = {
                        let one2 = d.num(1);
                        let mul_1_n = d.mul(one2, n);
                        let one_mul_n = d.lemma(p.one_mul, &[n]);
                        let n_eq_mul = d.symm(mul_1_n, n, one_mul_n);
                        let predicate = d.dvd_predicate(one2, n);
                        let intro = {
                            let one_lvl = d.level_one();
                            d.kernel().const_(p.logic.exists_intro, vec![one_lvl])
                        };
                        let nat = d.nat_ty();
                        d.apply(intro, &[nat, predicate, n, n_eq_mul])
                    };
                    // `dvd sj n`, transported along `sj = 1`.
                    let dvd_sj_n = {
                        let one2 = d.num(1);
                        let motive = d.eq_motive(one2, &|d, x| d.dvd(x, n));
                        let h_one_sj = d.symm(sj, one2, sj_eq_1);
                        d.transport(one2, motive, dvd_1_n, sj, h_one_sj)
                    };
                    let mod_zero = {
                        let rev = iff_reverse(d, mod_eq_zero_ty, dvd_ty, bridge);
                        d.apply(rev, &[dvd_sj_n])
                    };
                    let mm = d.modulo(n, sj);
                    let cond_eq_true = {
                        let beq_mm_0 = d.beq(mm, zero);
                        let congr_mm = nat_congr_bool(d, mm, zero, mod_zero, &|d, x| {
                            let zero_i = d.zero();
                            d.beq(x, zero_i)
                        });
                        let beq_0_0 = d.beq(zero, zero);
                        let bool_true_lit = d.bool_true();
                        let refl00 = d.bool_refl(bool_true_lit);
                        let true_ = d.bool_true();
                        d.bool_trans(beq_mm_0, beq_0_0, true_, congr_mm, refl00)
                    };
                    let cond = d.beq(mm, zero);
                    let true_ = d.bool_true();
                    let gj_eq_1 = resolve_select(d, gj, cond, true_, cond_eq_true, sj, zero, sj);
                    // `gj_eq_1 : gj = sj`; chain onward to `1` via `sj = 1`.
                    let gj_eq_1 = {
                        let (_e, p2) = d.chain(gj, &[(sj, gj_eq_1), (one, sj_eq_1)]);
                        p2
                    };

                    let start = d.add(sum_g_j, gj);
                    let step1 = d.congr(sum_g_j, zero, sum_g_j_eq_0, &|d, x| d.add(x, gj));
                    let after1 = d.add(zero, gj);
                    let step2 = d.congr(gj, one, gj_eq_1, &|d, x| d.add(zero, x));
                    let after2 = d.add(zero, one);
                    let step3 = d.refl(after2); // defeq to `1`
                    let (_e, proof) =
                        d.chain(start, &[(after1, step1), (after2, step2), (one, step3)]);
                    d.lam_fv(h_fv, true_ty, proof)
                };

                let false_branch = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);

                    let j_ne_0 = d.lemma(p.ne_of_beq_eq_false, &[j, zero, h]);
                    let sum_g_j_eq_1 = {
                        let sel = d.bool_select_nat(beq_j0, zero, one);
                        let false_lit = d.bool_false();
                        let cong = bool_congr_nat(d, beq_j0, false_lit, h, &|d, x| {
                            let zero_i = d.zero();
                            let one_i = d.num(1);
                            d.bool_select_nat(x, zero_i, one_i)
                        });
                        let false_lit2 = d.bool_false();
                        let sel_false = d.bool_select_nat(false_lit2, zero, one);
                        let step2 = d.refl(sel_false); // defeq to `1`
                        let (_e, proof) =
                            d.chain(sum_g_j, &[(sel, ih_val), (sel_false, cong), (one, step2)]);
                        proof
                    };

                    // `sj ≠ 1`: `sj = 1 = succ 0` would give (via
                    // `succ_injective`) `j = 0`, contradicting `j ≠ 0`.
                    let sj_ne_1 = {
                        let h2_fv = d.fresh_fvar();
                        let h2 = d.kernel().fvar(h2_fv);
                        let eq_ty = d.eq(sj, one);
                        let j_eq_0 = d.lemma(p.succ_injective, &[j, zero, h2]);
                        let absurd = d.apply(j_ne_0, &[j_eq_0]);
                        d.lam_fv(h2_fv, eq_ty, absurd)
                    };
                    let sj_ne_n = ne_of_lt(d, &p, sj, n, lt_sj_n);
                    let not_dvd_sj_n =
                        not_dvd_of_ne_one_ne_self(d, &p, n, prime_proof_n, sj, sj_ne_1, sj_ne_n);
                    let not_mod_zero = {
                        let h2_fv = d.fresh_fvar();
                        let h2 = d.kernel().fvar(h2_fv);
                        let fwd = iff_forward(d, mod_eq_zero_ty, dvd_ty, bridge);
                        let dvd_from_mod = d.apply(fwd, &[h2]);
                        let absurd = d.apply(not_dvd_sj_n, &[dvd_from_mod]);
                        d.lam_fv(h2_fv, mod_eq_zero_ty, absurd)
                    };
                    let mm = d.modulo(n, sj);
                    let cond_eq_false = d.lemma(p.beq_eq_false_of_ne, &[mm, zero, not_mod_zero]);
                    let cond = d.beq(mm, zero);
                    let false_ = d.bool_false();
                    let gj_eq_0 =
                        resolve_select(d, gj, cond, false_, cond_eq_false, sj, zero, zero);

                    let start = d.add(sum_g_j, gj);
                    let step1 = d.congr(sum_g_j, one, sum_g_j_eq_1, &|d, x| d.add(x, gj));
                    let after1 = d.add(one, gj);
                    let step2 = d.congr(gj, zero, gj_eq_0, &|d, x| d.add(one, x));
                    let after2 = d.add(one, zero);
                    let step3 = d.refl(after2); // defeq to `1`
                    let (_e, proof) =
                        d.chain(start, &[(after1, step1), (after2, step2), (one, step3)]);
                    d.lam_fv(h_fv, false_ty, proof)
                };

                let motive_or = {
                    let or_ty = d.const_app(p.logic.or, &[true_ty, false_ty]);
                    let anon = d.anon_name();
                    d.kernel().lam(anon, or_ty, target, BinderInfo::Default)
                };
                let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                let final_val = d.apply(
                    or_rec,
                    &[
                        true_ty,
                        false_ty,
                        motive_or,
                        true_branch,
                        false_branch,
                        cases,
                    ],
                );
                d.lam_fv(lt_fv, lt_ty, final_val)
            },
            m,
        );

        // Resolve `sum_below_proof` at `m`: need `Lt m n` (`= lt_succ_self
        // m`, since `n = succ m` literally) and `m ≠ 0` (from `2 ≤ n` and
        // `n = succ m`, via `le_of_succ_le_succ`).
        let lt_m_n = d.lemma(p.lt_succ_self, &[m]);
        let sum_g_m_select = d.apply(sum_below_proof, &[lt_m_n]);

        let m_ne_0 = {
            let (two_le_n, divisor_clause_n) = prime_parts(d, &p, n);
            let two_le_n_proof =
                super::helpers::and_left(d, two_le_n, divisor_clause_n, prime_proof_n);
            let one = d.num(1);
            // `Le 2 n = Le (succ 1) (succ m)`, literally.
            let le_1_m = d.lemma(p.le_of_succ_le_succ, &[one, m, two_le_n_proof]);
            // `Le 1 m = Lt 0 m`, literally.
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let eq_ty = {
                let zero = d.zero();
                d.eq(m, zero)
            };
            let zero = d.zero();
            let motive = d.eq_motive(m, &|d, x| {
                let zero_i = d.zero();
                d.lt(zero_i, x)
            });
            let lt_0_0 = d.transport(m, motive, le_1_m, zero, h);
            let irrefl = d.lemma(p.lt_irrefl, &[zero]);
            let absurd = d.apply(irrefl, &[lt_0_0]);
            d.lam_fv(h_fv, eq_ty, absurd)
        };
        let beq_m_0_false = {
            let zero = d.zero();
            d.lemma(p.beq_eq_false_of_ne, &[m, zero, m_ne_0])
        };
        let sum_g_m_eq_1 = {
            let zero = d.zero();
            let one = d.num(1);
            let cond = d.beq(m, zero);
            let sr = d.sum_range(g, m);
            let selected = d.bool_select_nat(cond, zero, one);
            let bool_false_lit = d.bool_false();
            let cong = select_congr(d, cond, bool_false_lit, beq_m_0_false, zero, one);
            let sel_false = d.bool_select_nat(bool_false_lit, zero, one);
            let step2 = d.refl(sel_false); // defeq to `1`
            let (_e, proof) = d.chain(
                sr,
                &[(selected, sum_g_m_select), (sel_false, cong), (one, step2)],
            );
            proof
        };

        // `g m = n`: `n` divides itself.
        let g_m_eq_n = {
            let zero = d.zero();
            let dvd_n_n = d.lemma(p.dvd_refl, &[n]);
            let bridge_m = mod_eq_zero_iff_dvd_succ(d, &p, m, n);
            let mod_eq_zero_ty_m = {
                let mm = d.modulo(n, n); // `succ m ≡ n`
                d.eq(mm, zero)
            };
            let dvd_ty_m = d.dvd(n, n);
            let mod_zero = {
                let rev = iff_reverse(d, mod_eq_zero_ty_m, dvd_ty_m, bridge_m);
                d.apply(rev, &[dvd_n_n])
            };
            let mm = d.modulo(n, n);
            let cond_eq_true = {
                let congr_mm = nat_congr_bool(d, mm, zero, mod_zero, &|d, x| {
                    let zero_i = d.zero();
                    d.beq(x, zero_i)
                });
                let beq_mm_0 = d.beq(mm, zero);
                let beq_0_0 = d.beq(zero, zero);
                let bool_true_lit = d.bool_true();
                let refl00 = d.bool_refl(bool_true_lit);
                let true_ = d.bool_true();
                d.bool_trans(beq_mm_0, beq_0_0, true_, congr_mm, refl00)
            };
            let cond = d.beq(mm, zero);
            let gm = d.bool_select_nat(cond, n, zero);
            let true_ = d.bool_true();
            resolve_select(d, gm, cond, true_, cond_eq_true, n, zero, n)
        };

        // `sumRange g n ≡ sumRange g m + g m = 1 + n = n + 1 = succ n`.
        let sr_g_m = d.sum_range(g, m);
        let gm = {
            let zero = d.zero();
            let mm = d.modulo(n, n);
            let cond = d.beq(mm, zero);
            d.bool_select_nat(cond, n, zero)
        };
        let sr_g_n_start = d.add(sr_g_m, gm);
        let one = d.num(1);
        let step1 = d.congr(sr_g_m, one, sum_g_m_eq_1, &|d, x| d.add(x, gm));
        let after1 = d.add(one, gm);
        let step2 = d.congr(gm, n, g_m_eq_n, &|d, x| d.add(one, x));
        let after2 = d.add(one, n);
        let comm = d.lemma(p.add_comm, &[one, n]);
        let after3 = d.add(n, one);
        let step4 = d.refl(after3); // defeq to `succ n`
        let succ_n = d.succ(n);
        let (_e, sr_g_n_eq_succ_n) = d.chain(
            sr_g_n_start,
            &[
                (after1, step1),
                (after2, step2),
                (after3, comm),
                (succ_n, step4),
            ],
        );

        // `sumDivisors n = f 0 + sumRange g n` (`sumRange_shiftFront`).
        let sd_n = sum_divisors(d, &p, n);
        let f0 = {
            let zero = d.zero();
            d.apply(f, &[zero])
        };
        let sr_g_n = d.sum_range(g, n);
        let shift_front = d.lemma(p.sum_range_shift_front, &[f, n]);
        let sum_plus = d.add(f0, sr_g_n);
        let zero_add_srgn = d.lemma(p.zero_add, &[sr_g_n]);

        let (_e2, sd_n_eq_succ_n) = d.chain(
            sd_n,
            &[
                (sum_plus, shift_front),
                (sr_g_n, zero_add_srgn),
                (succ_n, sr_g_n_eq_succ_n),
            ],
        );

        // Transport from `n` back to `pp`.
        let final_motive = d.eq_motive(n, &|d, x| {
            let sd_x = sum_divisors(d, &p, x);
            let succ_x = d.succ(x);
            d.eq(sd_x, succ_x)
        });
        let final_proof = d.transport(n, final_motive, sd_n_eq_succ_n, pp, eq_n_pp);

        let sd_pp = sum_divisors(d, &p, pp);
        let succ_pp = d.succ(pp);
        let target_ty = d.eq(sd_pp, succ_pp);
        let stmt = d.arrow(prime_ty_pp, target_ty);
        let proof = d.lam_fv(prime_fv, prime_ty_pp, final_proof);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.pow2_geom_sum` — the finite geometric sum over powers of two, in its
// subtraction-free form (`Nat.sub` is truncated; `sum_fib`, `fibonacci.rs`,
// carries the same convention for exactly the same reason).
// ============================================================================

/// `fun i => pow 2 i`.
fn pow2_term(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let two = d.num(2);
    let body = d.pow(two, i);
    d.lam_fv(i_fv, nat, body)
}

/// `Nat.pow2_geom_sum : ∀ n, Eq (add (sumRange (fun i => pow 2 i) n) one)
/// (pow 2 n)` — the finite geometric sum `Σ_{i<n} 2^i = 2^n − 1`, stated
/// subtraction-free as `Σ_{i<n} 2^i + 1 = 2^n`. This is the load-bearing
/// lemma Euclid IX.36 needs (`Σ_{i<p} 2^i = 2^p − 1`) and did not exist in
/// this kernel — `Nat.mul_sumRange_pow` (`algebra.rs`) is only the shift
/// identity `a * Σ (a^·) n = Σ (a^(·+1)) n`, not the closed form.
///
/// By induction on `n`. Base (`n = 0`): both sides reduce to `1` by pure
/// `ι`/`δ` reduction (`sumRange _ 0 ≡ 0`, `pow 2 0 ≡ 1`). Step: `Σ_{i<succ m}
/// 2^i + 1 ≡ (Σ_{i<m} 2^i + 2^m) + 1` (`sumRange`'s own defining equation)
/// `= (2^m + Σ_{i<m} 2^i) + 1` (`add_comm`) `= 2^m + (Σ_{i<m} 2^i + 1)`
/// (`add_assoc`) `= 2^m + 2^m` (the IH) `= 2^{succ m}` (`zero_add` plus
/// `pow`'s and `mul`'s own recursive equations: `2^{succ m} ≡ 2^m * 2 ≡
/// (2^m * 1) + 2^m ≡ (2^m * 0 + 2^m) + 2^m ≡ (0 + 2^m) + 2^m`).
pub(super) fn declare_pow2_geom_sum(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let f = pow2_term(d);
    d.theorem(p.pow2_geom_sum, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let sr = d.sum_range(f, x);
            let one = d.num(1);
            let lhs = d.add(sr, one);
            let two = d.num(2);
            let rhs = d.pow(two, x);
            d.eq(lhs, rhs)
        };
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let sr0 = d.sum_range(f, zero);
                let one = d.num(1);
                let lhs = d.add(sr0, one);
                d.refl(lhs) // both sides defeq `1`
            },
            &|d, m, ih| {
                let sm = d.succ(m);
                let sr_m = d.sum_range(f, m);
                let two = d.num(2);
                let pow_m = d.pow(two, m);
                let one = d.num(1);
                let zero = d.zero();

                // `start` is defeq `add (sumRange f (succ m)) one`, since
                // `sumRange f (succ m) ≡ add sr_m (f m) ≡ add sr_m pow_m`.
                let inner1 = d.add(sr_m, pow_m);
                let start = d.add(inner1, one);

                let comm1 = d.lemma(p.add_comm, &[sr_m, pow_m]);
                let inner2 = d.add(pow_m, sr_m);
                let step1 = d.congr(inner1, inner2, comm1, &|d, x| d.add(x, one));
                let mid1 = d.add(inner2, one);

                let assoc = d.lemma(p.add_assoc, &[pow_m, sr_m, one]);
                let inner3 = d.add(sr_m, one);
                let mid2 = d.add(pow_m, inner3);

                let step3 = d.congr(inner3, pow_m, ih, &|d, x| d.add(pow_m, x));
                let mid3 = d.add(pow_m, pow_m);

                let zero_add_pm = d.lemma(p.zero_add, &[pow_m]);
                let mul_intermediate = d.add(zero, pow_m);
                let step4_inner = d.congr(mul_intermediate, pow_m, zero_add_pm, &|d, x| {
                    d.add(x, pow_m)
                });
                let pow_succ_m = d.pow(two, sm);
                let mul_intermediate_plus_pow_m = d.add(mul_intermediate, pow_m);
                let step4 = d.symm(mul_intermediate_plus_pow_m, mid3, step4_inner);

                let (_e, proof) = d.chain(
                    start,
                    &[
                        (mid1, step1),
                        (mid2, assoc),
                        (mid3, step3),
                        (pow_succ_m, step4),
                    ],
                );
                proof
            },
            n,
        );
        (motive(d, n), proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.dvd_two_pow_mul_classify` — divisors of `2^k * q`, for `q` prime.
//
// The Euclid IX.36 blocker: classifying an arbitrary `d ∣ 2^k·q` as `d = 2^i`
// or `d = 2^i·q` (`i ≤ k`), via unique factorization on the single prime `2`.
// The proof is ONE induction on `k` (not two, as the task brief anticipated
// for a separate `dvd_pow2`): at each step, split on `gcd(dd, 2) ∈ {1, 2}`
// (proved inline by [`divisors_of_two`] — literally "`2` is prime", spelled
// out once for this single use rather than as a general `Nat.prime_two`).
// `gcd = 2` peels a factor of `2` off `dd` and recurses via the induction
// hypothesis (applied to the fresh quotient `dd/2`); `gcd = 1` is coprime to
// `2`, so `gauss_lemma` cancels the `2` directly from `dd ∣ 2·(2^m·q)` and the
// induction hypothesis applies to `dd` itself unchanged (only the bound needs
// widening from `m` to `succ m`, done by [`classify_widen`]).
//
// `¬(q ∣ 2)` is carried in the statement (matching the shape the task brief
// asked for) but never consumed by the proof below: the `gcd(dd,2)` split
// only inspects `dd`, never `q`, so nothing here needs `q` to be odd. This
// mirrors an existing convention in this very file — see
// [`pos_implies_succ_pred`]'s base case, whose hypothesis is likewise unused
// once the goal reduces to a bare `Eq.refl`.
// ============================================================================

/// Eliminate `dvd_hyp : dvd divisor dividend`, continuing with the witness
/// `q` and `eq_proof : Eq dividend (mul divisor q)` to build a proof of
/// `goal` (which must not mention `q`). Local copy of `lcm.rs`'s private
/// `dvd_elim` (this file's own per-file convention; see the module doc for
/// `sumDivisors_prime`'s local combinators).
fn dvd_elim(
    d: &mut NatDev<'_>,
    divisor: ExprId,
    dividend: ExprId,
    goal: ExprId,
    dvd_hyp: ExprId,
    continuation: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let predicate = d.dvd_predicate(divisor, dividend);
    let dvd_ty = d.dvd(divisor, dividend);
    let motive = d.kernel().lam(anon, dvd_ty, goal, BinderInfo::Default);
    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let divisor_q = d.mul(divisor, q);
        let eq_ty = d.eq(dividend, divisor_q);
        let eq_fv = d.fresh_fvar();
        let eq_proof = d.kernel().fvar(eq_fv);
        let body = continuation(d, q, eq_proof);
        let with_eq = d.lam_fv(eq_fv, eq_ty, body);
        d.lam_fv(q_fv, nat, with_eq)
    };
    let exists_rec_name = d.prelude().logic.exists_rec;
    let rec = d.kernel().const_(exists_rec_name, vec![one]);
    d.apply(rec, &[nat, predicate, motive, minor, dvd_hyp])
}

/// Local copy of `lcm.rs`'s private `dvd_intro`.
fn dvd_intro(
    d: &mut NatDev<'_>,
    a: ExprId,
    n: ExprId,
    witness: ExprId,
    eq_proof: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let predicate = d.dvd_predicate(a, n);
    let intro_name = d.prelude().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[nat, predicate, witness, eq_proof])
}

/// `∀ c, dvd c 2 → Or (Eq c 1) (Eq c 2)` — the only divisors of the literal
/// `2` are `1` and `2` (i.e. `2` is prime), spelled out inline for this one
/// use (classifying `gcd dd 2`) rather than as a general `Nat.prime_two`.
/// `1 ≤ c ≤ 2` from `le_of_dvd`/`one_le_of_dvd_pos`, `c = succ (pred c)`
/// from `succ_pred_of_pos`, then `two_le_succ_or_eq_one` on `pred c`
/// resolves the two cases (mirroring `two_le_succ_or_eq_one`'s own use in
/// `primes.rs`).
fn divisors_of_two(d: &mut NatDev<'_>, p: &NatPrelude, c: ExprId, dvd_c2: ExprId) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let one = d.num(1);
    let one_le_two = d.lemma(p.le_succ, &[one]);
    let one_le_c = d.lemma(p.one_le_of_dvd_pos, &[c, two, one_le_two, dvd_c2]);
    let c_le_two = d.lemma(p.le_of_dvd, &[c, two, one_le_two, dvd_c2]);

    let succ_pred = d.lemma(p.succ_pred_of_pos, &[c, one_le_c]);
    let e = d.pred(c);
    let se = d.succ(e);

    let se_le_two = {
        let motive = d.eq_motive(c, &|d, x| d.le(x, two));
        d.transport(c, motive, c_le_two, se, succ_pred)
    };

    let dichotomy = d.lemma(p.two_le_succ_or_eq_one, &[e]);
    let left_ty = d.le(two, se);
    let right_ty = d.eq(se, one);

    let goal_one = d.eq(c, one);
    let goal_two = d.eq(c, two);
    let logic = d.prelude().logic;
    let goal = d.const_app(logic.or, &[goal_one, goal_two]);

    let left_branch = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let se_eq_two = d.lemma(p.le_antisymm, &[se, two, se_le_two, h]);
        let (_e2, c_eq_two) = d.chain(c, &[(se, succ_pred), (two, se_eq_two)]);
        let proof = d.const_app(logic.or_inr, &[goal_one, goal_two, c_eq_two]);
        d.lam_fv(h_fv, left_ty, proof)
    };
    let right_branch = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let (_e2, c_eq_one) = d.chain(c, &[(se, succ_pred), (one, h)]);
        let proof = d.const_app(logic.or_inl, &[goal_one, goal_two, c_eq_one]);
        d.lam_fv(h_fv, right_ty, proof)
    };

    let anon = d.anon_name();
    let or_ty = d.const_app(logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[
            left_ty,
            right_ty,
            motive,
            left_branch,
            right_branch,
            dichotomy,
        ],
    )
}

/// `fun i => Le i bound ∧ Eq target (pow 2 i [* extra])` — shared by
/// [`pow_eq_exists`] and [`pow_eq_intro`]/[`pow_eq_elim`] so all three build
/// the identical predicate term.
fn pow_eq_predicate(
    d: &mut NatDev<'_>,
    bound: ExprId,
    target: ExprId,
    extra: Option<ExprId>,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let le_ty = d.le(i, bound);
    let two = d.num(2);
    let pow_i = d.pow(two, i);
    let rhs = match extra {
        Some(q) => d.mul(pow_i, q),
        None => pow_i,
    };
    let eq_ty = d.eq(target, rhs);
    let logic = d.prelude().logic;
    let body = d.const_app(logic.and, &[le_ty, eq_ty]);
    d.lam_fv(i_fv, nat, body)
}

/// `∃ i, Le i bound ∧ Eq target (pow 2 i [* extra])`.
fn pow_eq_exists(
    d: &mut NatDev<'_>,
    bound: ExprId,
    target: ExprId,
    extra: Option<ExprId>,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let predicate = pow_eq_predicate(d, bound, target, extra);
    let logic = d.prelude().logic;
    let exists_ = d.kernel().const_(logic.exists_, vec![one]);
    d.apply(exists_, &[nat, predicate])
}

/// Introduce a proof of [`pow_eq_exists`] at witness `witness_i`.
#[allow(clippy::too_many_arguments)]
fn pow_eq_intro(
    d: &mut NatDev<'_>,
    bound: ExprId,
    target: ExprId,
    extra: Option<ExprId>,
    witness_i: ExprId,
    le_proof: ExprId,
    eq_proof: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let predicate = pow_eq_predicate(d, bound, target, extra);
    let le_ty = d.le(witness_i, bound);
    let two = d.num(2);
    let pow_i = d.pow(two, witness_i);
    let rhs = match extra {
        Some(q) => d.mul(pow_i, q),
        None => pow_i,
    };
    let eq_ty = d.eq(target, rhs);
    let logic = d.prelude().logic;
    let and_proof = d.const_app(logic.and_intro, &[le_ty, eq_ty, le_proof, eq_proof]);
    let intro = d.kernel().const_(logic.exists_intro, vec![one]);
    d.apply(intro, &[nat, predicate, witness_i, and_proof])
}

/// Eliminate a proof of [`pow_eq_exists`] `bound target extra`, continuing
/// with the witness `i` and its `Le i bound`/`Eq target (2^i[*q])` halves
/// (via [`and_left`]/[`and_right`]) to build a proof of `goal` (which must
/// not mention `i`).
#[allow(clippy::too_many_arguments)]
fn pow_eq_elim(
    d: &mut NatDev<'_>,
    bound: ExprId,
    target: ExprId,
    extra: Option<ExprId>,
    goal: ExprId,
    proof: ExprId,
    continuation: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let src_predicate = pow_eq_predicate(d, bound, target, extra);
    let src_ty = pow_eq_exists(d, bound, target, extra);
    let motive = d.kernel().lam(anon, src_ty, goal, BinderInfo::Default);
    let minor = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let and_fv = d.fresh_fvar();
        let and_proof = d.kernel().fvar(and_fv);
        let le_ty = d.le(i, bound);
        let two = d.num(2);
        let pow_i = d.pow(two, i);
        let rhs = match extra {
            Some(q) => d.mul(pow_i, q),
            None => pow_i,
        };
        let eq_ty = d.eq(target, rhs);
        let le_i = and_left(d, le_ty, eq_ty, and_proof);
        let eq_i = and_right(d, le_ty, eq_ty, and_proof);
        let body = continuation(d, i, le_i, eq_i);
        let logic = d.prelude().logic;
        let and_ty = d.const_app(logic.and, &[le_ty, eq_ty]);
        let with_and = d.lam_fv(and_fv, and_ty, body);
        d.lam_fv(i_fv, nat, with_and)
    };
    let logic = d.prelude().logic;
    let rec = d.kernel().const_(logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, src_predicate, motive, minor, proof])
}

/// `Or (pow_eq_exists bound target None) (pow_eq_exists bound target (Some q))`.
fn classify_goal(d: &mut NatDev<'_>, bound: ExprId, target: ExprId, q: ExprId) -> ExprId {
    let left = pow_eq_exists(d, bound, target, None);
    let right = pow_eq_exists(d, bound, target, Some(q));
    let logic = d.prelude().logic;
    d.const_app(logic.or, &[left, right])
}

fn classify_inl(
    d: &mut NatDev<'_>,
    bound: ExprId,
    target: ExprId,
    q: ExprId,
    proof: ExprId,
) -> ExprId {
    let left = pow_eq_exists(d, bound, target, None);
    let right = pow_eq_exists(d, bound, target, Some(q));
    let logic = d.prelude().logic;
    d.const_app(logic.or_inl, &[left, right, proof])
}

fn classify_inr(
    d: &mut NatDev<'_>,
    bound: ExprId,
    target: ExprId,
    q: ExprId,
    proof: ExprId,
) -> ExprId {
    let left = pow_eq_exists(d, bound, target, None);
    let right = pow_eq_exists(d, bound, target, Some(q));
    let logic = d.prelude().logic;
    d.const_app(logic.or_inr, &[left, right, proof])
}

/// Widen a classification proof bounded by `m` to one bounded by `succ m`
/// (`le_trans` against `le_succ`) — used when the induction hypothesis is
/// applied to the SAME `dd` (the `gcd(dd,2)=1` branch), so only the bound,
/// not the witness's shape, needs adjusting.
fn classify_widen(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    target: ExprId,
    q: ExprId,
    proof_m: ExprId,
) -> ExprId {
    let p = *p;
    let sm = d.succ(m);
    let goal = classify_goal(d, sm, target, q);
    let left_m = pow_eq_exists(d, m, target, None);
    let right_m = pow_eq_exists(d, m, target, Some(q));

    let left_branch = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = pow_eq_elim(d, m, target, None, goal, h, &|d, i, le_i, eq_i| {
            let le_succ_m = d.lemma(p.le_succ, &[m]);
            let le_i_sm = d.lemma(p.le_trans, &[i, m, sm, le_i, le_succ_m]);
            let intro = pow_eq_intro(d, sm, target, None, i, le_i_sm, eq_i);
            classify_inl(d, sm, target, q, intro)
        });
        d.lam_fv(h_fv, left_m, body)
    };
    let right_branch = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = pow_eq_elim(d, m, target, Some(q), goal, h, &|d, i, le_i, eq_i| {
            let le_succ_m = d.lemma(p.le_succ, &[m]);
            let le_i_sm = d.lemma(p.le_trans, &[i, m, sm, le_i, le_succ_m]);
            let intro = pow_eq_intro(d, sm, target, Some(q), i, le_i_sm, eq_i);
            classify_inr(d, sm, target, q, intro)
        });
        d.lam_fv(h_fv, right_m, body)
    };

    let anon = d.anon_name();
    let logic = d.prelude().logic;
    let or_ty = d.const_app(logic.or, &[left_m, right_m]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_m, right_m, motive, left_branch, right_branch, proof_m],
    )
}

/// `∀ dd, dvd dd (mul (pow 2 kk) q) → classify_goal kk dd q`.
fn classify_motive(d: &mut NatDev<'_>, kk: ExprId, q: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let dd_fv = d.fresh_fvar();
    let dd = d.kernel().fvar(dd_fv);
    let two = d.num(2);
    let pow_kk = d.pow(two, kk);
    let target = d.mul(pow_kk, q);
    let hyp_ty = d.dvd(dd, target);
    let goal = classify_goal(d, kk, dd, q);
    let body = d.arrow(hyp_ty, goal);
    d.pi_fv(dd_fv, nat, body)
}

/// The even branch's `dprime = 2^i` case: from `dd_eq : Eq dd (mul two
/// dprime)` and `eq_i : Eq dprime (pow 2 i)` (`i ≤ m`), build `classify_goal
/// (succ m) dd q`'s LEFT disjunct at witness `succ i`.
#[allow(clippy::too_many_arguments)]
fn even_branch_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    dd: ExprId,
    dprime: ExprId,
    dd_eq: ExprId,
    m: ExprId,
    sm: ExprId,
    q: ExprId,
    i: ExprId,
    le_i: ExprId,
    eq_i: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let two_dprime = d.mul(two, dprime);
    let pow_i = d.pow(two, i);
    let congr_step = d.congr(dprime, pow_i, eq_i, &|d, t| d.mul(two, t));
    let two_pow_i = d.mul(two, pow_i);
    let comm = d.lemma(p.mul_comm, &[two, pow_i]);
    let pow_i_two = d.mul(pow_i, two);
    let (_e, dd_eq_final) = d.chain(
        dd,
        &[
            (two_dprime, dd_eq),
            (two_pow_i, congr_step),
            (pow_i_two, comm),
        ],
    );
    let succ_i = d.succ(i);
    let le_i_sm = d.lemma(p.le_succ_succ, &[i, m, le_i]);
    let intro = pow_eq_intro(d, sm, dd, None, succ_i, le_i_sm, dd_eq_final);
    classify_inl(d, sm, dd, q, intro)
}

/// The even branch's `dprime = 2^i * q` case: build `classify_goal (succ m)
/// dd q`'s RIGHT disjunct at witness `succ i`.
#[allow(clippy::too_many_arguments)]
fn even_branch_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    dd: ExprId,
    dprime: ExprId,
    dd_eq: ExprId,
    m: ExprId,
    sm: ExprId,
    q: ExprId,
    i: ExprId,
    le_i: ExprId,
    eq_i: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let two_dprime = d.mul(two, dprime);
    let pow_i = d.pow(two, i);
    let pow_i_q = d.mul(pow_i, q);
    let congr_step = d.congr(dprime, pow_i_q, eq_i, &|d, t| d.mul(two, t));
    let two_pow_i_q = d.mul(two, pow_i_q);
    let assoc_fwd = d.lemma(p.mul_assoc, &[two, pow_i, q]);
    let two_pow_i = d.mul(two, pow_i);
    let two_pow_i_mul_q = d.mul(two_pow_i, q);
    let assoc_back = d.symm(two_pow_i_mul_q, two_pow_i_q, assoc_fwd);
    let comm = d.lemma(p.mul_comm, &[two, pow_i]);
    let pow_i_two = d.mul(pow_i, two);
    let congr2 = d.congr(two_pow_i, pow_i_two, comm, &|d, t| d.mul(t, q));
    let pow_i_two_q = d.mul(pow_i_two, q);
    let (_e, dd_eq_final) = d.chain(
        dd,
        &[
            (two_dprime, dd_eq),
            (two_pow_i_q, congr_step),
            (two_pow_i_mul_q, assoc_back),
            (pow_i_two_q, congr2),
        ],
    );
    let succ_i = d.succ(i);
    let le_i_sm = d.lemma(p.le_succ_succ, &[i, m, le_i]);
    let intro = pow_eq_intro(d, sm, dd, Some(q), succ_i, le_i_sm, dd_eq_final);
    classify_inr(d, sm, dd, q, intro)
}

/// `Nat.dvd_two_pow_mul_classify : ∀ k q, (2 ≤ q ∧ ∀ c, dvd c q → Eq c 1 ∨ Eq
/// c q) → ¬(dvd q 2) → ∀ d, dvd d (mul (pow 2 k) q) → (∃ i, Le i k ∧ Eq d
/// (pow 2 i)) ∨ (∃ i, Le i k ∧ Eq d (mul (pow 2 i) q))` — the divisor
/// classification Euclid IX.36 needs. See the module doc above for the
/// single-induction route.
pub(super) fn declare_dvd_two_pow_mul_classify(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dvd_two_pow_mul_classify, 2, &|d, v| {
        let (k, q) = (v[0], v[1]);

        let prime_q_ty = prime_ty(d, &p, q);
        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);

        let two_lit = d.num(2);
        let dvd_q2_ty = d.dvd(q, two_lit);
        let logic = d.prelude().logic;
        let not_dvd_q2_ty = d.const_app(logic.not, &[dvd_q2_ty]);
        let not_fv = d.fresh_fvar();

        let (two_le_q_ty, divisor_clause_ty) = prime_parts(d, &p, q);
        let q_divisor_clause = and_right(d, two_le_q_ty, divisor_clause_ty, prime_proof);

        let motive = |d: &mut NatDev<'_>, kk: ExprId| -> ExprId { classify_motive(d, kk, q) };

        let base = |d: &mut NatDev<'_>| -> ExprId {
            let nat = d.nat_ty();
            let dd_fv = d.fresh_fvar();
            let dd = d.kernel().fvar(dd_fv);
            let zero = d.zero();
            let two = d.num(2);
            let pow0 = d.pow(two, zero);
            let target = d.mul(pow0, q);
            let hyp_ty = d.dvd(dd, target);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);

            let one = d.num(1);
            let mul_one_q = d.mul(one, q);
            let one_mul_q = d.lemma(p.one_mul, &[q]);
            let dvd_dd_q = transport_dvd_right(d, dd, mul_one_q, q, one_mul_q, hyp);

            let or_proof = d.apply(q_divisor_clause, &[dd, dvd_dd_q]);

            let goal = classify_goal(d, zero, dd, q);
            let left_ty = d.eq(dd, one);
            let right_ty = d.eq(dd, q);

            let left_branch = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let zero2 = d.zero();
                let le00 = d.lemma(p.le_refl, &[zero2]);
                let intro = pow_eq_intro(d, zero, dd, None, zero2, le00, h);
                let proof = classify_inl(d, zero, dd, q, intro);
                d.lam_fv(h_fv, left_ty, proof)
            };
            let right_branch = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let q_eq_mul_one_q = d.symm(mul_one_q, q, one_mul_q);
                let (_e, dd_eq_mul_one_q) = d.chain(dd, &[(q, h), (mul_one_q, q_eq_mul_one_q)]);
                let zero2 = d.zero();
                let le00 = d.lemma(p.le_refl, &[zero2]);
                let intro = pow_eq_intro(d, zero, dd, Some(q), zero2, le00, dd_eq_mul_one_q);
                let proof = classify_inr(d, zero, dd, q, intro);
                d.lam_fv(h_fv, right_ty, proof)
            };

            let anon = d.anon_name();
            let logic = d.prelude().logic;
            let or_ty = d.const_app(logic.or, &[left_ty, right_ty]);
            let motive_or = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
            let or_rec = d.kernel().const_(logic.or_rec, vec![]);
            let case_result = d.apply(
                or_rec,
                &[
                    left_ty,
                    right_ty,
                    motive_or,
                    left_branch,
                    right_branch,
                    or_proof,
                ],
            );
            let dd_body = d.lam_fv(hyp_fv, hyp_ty, case_result);
            d.lam_fv(dd_fv, nat, dd_body)
        };

        let step = |d: &mut NatDev<'_>, m: ExprId, ih: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let sm = d.succ(m);
            let dd_fv = d.fresh_fvar();
            let dd = d.kernel().fvar(dd_fv);
            let two = d.num(2);
            let one = d.num(1);
            let pow_sm = d.pow(two, sm);
            let pow_m = d.pow(two, m);
            let target_sm = d.mul(pow_sm, q);
            let hyp_ty = d.dvd(dd, target_sm);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);

            let goal = classify_goal(d, sm, dd, q);

            // Reassociate: (2^m*2)*q = 2*(2^m*q). `pm2 := mul(pow_m,two)` is
            // defeq to `pow_sm` (pow's own succ-equation), so `target_sm` is
            // defeq to `mul(pm2, q)` and the chain below is accepted at
            // `target_sm`'s type by the kernel's defeq check.
            let pm2 = d.mul(pow_m, two);
            let start2 = d.mul(pm2, q);
            let mul_comm_2 = d.lemma(p.mul_comm, &[pow_m, two]);
            let two_pm = d.mul(two, pow_m);
            let step_a = d.congr(pm2, two_pm, mul_comm_2, &|d, t| d.mul(t, q));
            let mid = d.mul(two_pm, q);
            let assoc = d.lemma(p.mul_assoc, &[two, pow_m, q]);
            let pow_m_q = d.mul(pow_m, q);
            let end_ = d.mul(two, pow_m_q);
            let (_e, reassoc) = d.chain(start2, &[(mid, step_a), (end_, assoc)]);

            let dvd_two_pmq = transport_dvd_right(d, dd, start2, end_, reassoc, hyp);

            let gcd_dd2 = d.gcd(dd, two);
            let gcd_dvd_2 = d.lemma(p.gcd_dvd_right, &[dd, two]);
            let two_cases = divisors_of_two(d, &p, gcd_dd2, gcd_dvd_2);

            let left_ty = d.eq(gcd_dd2, one);
            let right_ty = d.eq(gcd_dd2, two);

            let coprime_branch = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let dvd_dd_pow_m_q = d.lemma(p.gauss_lemma, &[dd, two, pow_m_q, h, dvd_two_pmq]);
                let ih_result = d.apply(ih, &[dd, dvd_dd_pow_m_q]);
                let widened = classify_widen(d, &p, m, dd, q, ih_result);
                d.lam_fv(h_fv, left_ty, widened)
            };

            let even_branch = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let gcd_dvd_dd = d.lemma(p.gcd_dvd_left, &[dd, two]);
                let dvd_2_dd = transport_dvd_left(d, gcd_dd2, two, h, dd, gcd_dvd_dd);

                let body = dvd_elim(d, two, dd, goal, dvd_2_dd, &|d, dprime, dd_eq| {
                    let two_dprime = d.mul(two, dprime);
                    let dvd_scaled =
                        transport_dvd_left(d, dd, two_dprime, dd_eq, end_, dvd_two_pmq);

                    dvd_elim(d, two_dprime, end_, goal, dvd_scaled, &|d, e, eq2| {
                        let two_dprime_e = d.mul(two_dprime, e);
                        let assoc2 = d.lemma(p.mul_assoc, &[two, dprime, e]);
                        let dprime_e = d.mul(dprime, e);
                        let two_dprime_e2 = d.mul(two, dprime_e);
                        let (_e3, eq3) =
                            d.chain(end_, &[(two_dprime_e, eq2), (two_dprime_e2, assoc2)]);
                        let one_le_two = d.lemma(p.le_succ, &[one]);
                        let cancelled = d.lemma(
                            p.mul_left_cancel_of_pos,
                            &[two, pow_m_q, dprime_e, one_le_two, eq3],
                        );
                        let dvd_dprime_pow_m_q = dvd_intro(d, dprime, pow_m_q, e, cancelled);
                        let ih_result = d.apply(ih, &[dprime, dvd_dprime_pow_m_q]);

                        let ih_left_ty = pow_eq_exists(d, m, dprime, None);
                        let ih_right_ty = pow_eq_exists(d, m, dprime, Some(q));

                        let left_of_ih = {
                            let hh_fv = d.fresh_fvar();
                            let hh = d.kernel().fvar(hh_fv);
                            let inner =
                                pow_eq_elim(d, m, dprime, None, goal, hh, &|d, i, le_i, eq_i| {
                                    even_branch_left(
                                        d, &p, dd, dprime, dd_eq, m, sm, q, i, le_i, eq_i,
                                    )
                                });
                            d.lam_fv(hh_fv, ih_left_ty, inner)
                        };
                        let right_of_ih = {
                            let hh_fv = d.fresh_fvar();
                            let hh = d.kernel().fvar(hh_fv);
                            let inner = pow_eq_elim(
                                d,
                                m,
                                dprime,
                                Some(q),
                                goal,
                                hh,
                                &|d, i, le_i, eq_i| {
                                    even_branch_right(
                                        d, &p, dd, dprime, dd_eq, m, sm, q, i, le_i, eq_i,
                                    )
                                },
                            );
                            d.lam_fv(hh_fv, ih_right_ty, inner)
                        };

                        let anon2 = d.anon_name();
                        let logic2 = d.prelude().logic;
                        let or_ty2 = d.const_app(logic2.or, &[ih_left_ty, ih_right_ty]);
                        let motive2 = d.kernel().lam(anon2, or_ty2, goal, BinderInfo::Default);
                        let or_rec2 = d.kernel().const_(logic2.or_rec, vec![]);
                        d.apply(
                            or_rec2,
                            &[
                                ih_left_ty,
                                ih_right_ty,
                                motive2,
                                left_of_ih,
                                right_of_ih,
                                ih_result,
                            ],
                        )
                    })
                });
                d.lam_fv(h_fv, right_ty, body)
            };

            let anon = d.anon_name();
            let logic = d.prelude().logic;
            let or_ty = d.const_app(logic.or, &[left_ty, right_ty]);
            let motive_or = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
            let or_rec = d.kernel().const_(logic.or_rec, vec![]);
            let case_result = d.apply(
                or_rec,
                &[
                    left_ty,
                    right_ty,
                    motive_or,
                    coprime_branch,
                    even_branch,
                    two_cases,
                ],
            );
            let dd_body = d.lam_fv(hyp_fv, hyp_ty, case_result);
            d.lam_fv(dd_fv, nat, dd_body)
        };

        let induction_proof = d.induct(&motive, &base, &step, k);
        let stmt_inner = motive(d, k);
        let stmt_with_not = d.arrow(not_dvd_q2_ty, stmt_inner);
        let stmt = d.arrow(prime_q_ty, stmt_with_not);

        let proof_with_not = d.lam_fv(not_fv, not_dvd_q2_ty, induction_proof);
        let proof = d.lam_fv(prime_fv, prime_q_ty, proof_with_not);

        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.dvd_two_pow_classify` — divisors of `2^k` alone (no coprime cofactor
// `q`): every `d ∣ 2^k` is `2^i` for some `i ≤ k`. This is the "divisors of
// `2^n` are exactly the powers of `2` up to `n`" classification
// `sumDivisors_two_pow`'s congruence step needs, and
// [`declare_dvd_two_pow_mul_classify`] does NOT supply it: that theorem's
// cofactor `q` carries a primality hypothesis (`2 ≤ q`) that blocks
// instantiating it at `q = 1`.
//
// The proof reuses [`pow_eq_predicate`]/[`pow_eq_exists`]/[`pow_eq_intro`]/
// [`pow_eq_elim`] verbatim with `extra = None` — those four are already
// generic in the optional cofactor — so this is the SAME single induction on
// `k`, splitting on `gcd(dd, 2) ∈ {1, 2}` via [`divisors_of_two`], with the
// `Or`-of-two-shapes machinery ([`classify_goal`]/[`classify_inl`]/
// [`classify_inr`]/[`classify_widen`]) dropped since there is only one shape
// to land in. [`widen_pow_eq`] and [`even_step_result`] below are the
// `q`-free analogues of [`classify_widen`]'s left branch and
// [`even_branch_left`], respectively; the odd/coprime branch closes directly
// through `gauss_lemma` exactly as the mul-classify theorem's coprime branch
// does, minus the cofactor.
// ============================================================================

/// `∀ dd, dvd dd (pow 2 kk) → pow_eq_exists kk dd None`.
fn dvd_two_pow_motive(d: &mut NatDev<'_>, kk: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let dd_fv = d.fresh_fvar();
    let dd = d.kernel().fvar(dd_fv);
    let two = d.num(2);
    let pow_kk = d.pow(two, kk);
    let hyp_ty = d.dvd(dd, pow_kk);
    let goal = pow_eq_exists(d, kk, dd, None);
    let body = d.arrow(hyp_ty, goal);
    d.pi_fv(dd_fv, nat, body)
}

/// Widen a `q`-free classification proof bounded by `m` to one bounded by
/// `succ m` — the `q`-free analogue of [`classify_widen`]'s left branch
/// (used when the induction hypothesis is applied to the SAME `dd`, so only
/// the bound needs adjusting, not the witness's shape).
fn widen_pow_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    target: ExprId,
    proof_m: ExprId,
) -> ExprId {
    let p = *p;
    let sm = d.succ(m);
    let goal = pow_eq_exists(d, sm, target, None);
    pow_eq_elim(d, m, target, None, goal, proof_m, &|d, i, le_i, eq_i| {
        let le_succ_m = d.lemma(p.le_succ, &[m]);
        let le_i_sm = d.lemma(p.le_trans, &[i, m, sm, le_i, le_succ_m]);
        pow_eq_intro(d, sm, target, None, i, le_i_sm, eq_i)
    })
}

/// The even branch's result: from `dd_eq : Eq dd (mul two dprime)` and
/// `eq_i : Eq dprime (pow 2 i)` (`i ≤ m`), build a proof of `pow_eq_exists
/// (succ m) dd None` at witness `succ i` — the `q`-free analogue of
/// [`even_branch_left`] (identical algebra, minus the `classify_inl` `Or`
/// wrap, since there is no second disjunct here).
#[allow(clippy::too_many_arguments)]
fn even_step_result(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    dd: ExprId,
    dprime: ExprId,
    dd_eq: ExprId,
    m: ExprId,
    sm: ExprId,
    i: ExprId,
    le_i: ExprId,
    eq_i: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let two_dprime = d.mul(two, dprime);
    let pow_i = d.pow(two, i);
    let congr_step = d.congr(dprime, pow_i, eq_i, &|d, t| d.mul(two, t));
    let two_pow_i = d.mul(two, pow_i);
    let comm = d.lemma(p.mul_comm, &[two, pow_i]);
    let pow_i_two = d.mul(pow_i, two);
    let (_e, dd_eq_final) = d.chain(
        dd,
        &[
            (two_dprime, dd_eq),
            (two_pow_i, congr_step),
            (pow_i_two, comm),
        ],
    );
    let succ_i = d.succ(i);
    let le_i_sm = d.lemma(p.le_succ_succ, &[i, m, le_i]);
    pow_eq_intro(d, sm, dd, None, succ_i, le_i_sm, dd_eq_final)
}

/// `Nat.dvd_two_pow_classify : ∀ k d, dvd d (pow 2 k) → ∃ i, Le i k ∧ Eq d
/// (pow 2 i)` — every divisor of `2^k` is a power of `2` up to `2^k`. See the
/// module doc above for the proof route (one induction on `k`, reusing
/// [`declare_dvd_two_pow_mul_classify`]'s `gcd(dd,2)` split machinery with
/// the cofactor `q` erased).
pub(super) fn declare_dvd_two_pow_classify(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dvd_two_pow_classify, 1, &|d, v| {
        let k = v[0];

        let motive = |d: &mut NatDev<'_>, kk: ExprId| -> ExprId { dvd_two_pow_motive(d, kk) };

        let base = |d: &mut NatDev<'_>| -> ExprId {
            let nat = d.nat_ty();
            let dd_fv = d.fresh_fvar();
            let dd = d.kernel().fvar(dd_fv);
            let zero = d.zero();
            let two = d.num(2);
            let pow0 = d.pow(two, zero);
            let hyp_ty = d.dvd(dd, pow0);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);

            // `pow0 ≡ one` by iota (`pow _ zero ≡ succ zero`), so `hyp` (typed
            // `dvd dd pow0`) serves directly where `dvd dd one` is expected —
            // exactly the convention [`declare_dvd_two_pow_mul_classify`]'s
            // own base case relies on.
            let dd_eq_one = d.lemma(p.eq_one_of_dvd_one, &[dd, hyp]);

            let zero2 = d.zero();
            let le00 = d.lemma(p.le_refl, &[zero2]);
            let intro = pow_eq_intro(d, zero, dd, None, zero2, le00, dd_eq_one);

            let dd_body = d.lam_fv(hyp_fv, hyp_ty, intro);
            d.lam_fv(dd_fv, nat, dd_body)
        };

        let step = |d: &mut NatDev<'_>, m: ExprId, ih: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let sm = d.succ(m);
            let dd_fv = d.fresh_fvar();
            let dd = d.kernel().fvar(dd_fv);
            let two = d.num(2);
            let one = d.num(1);
            let pow_m = d.pow(two, m);
            let pow_sm = d.pow(two, sm);
            let hyp_ty = d.dvd(dd, pow_sm);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);

            let goal = pow_eq_exists(d, sm, dd, None);

            // `pow_sm ≡ mul(pow_m, two)` by iota; reorder to `mul(two, pow_m)`.
            let pm2 = d.mul(pow_m, two);
            let mul_comm_2 = d.lemma(p.mul_comm, &[pow_m, two]);
            let two_pm = d.mul(two, pow_m);
            let dvd_two_pm = transport_dvd_right(d, dd, pm2, two_pm, mul_comm_2, hyp);

            let gcd_dd2 = d.gcd(dd, two);
            let gcd_dvd_2 = d.lemma(p.gcd_dvd_right, &[dd, two]);
            let two_cases = divisors_of_two(d, &p, gcd_dd2, gcd_dvd_2);

            let left_ty = d.eq(gcd_dd2, one);
            let right_ty = d.eq(gcd_dd2, two);

            let coprime_branch = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let dvd_dd_pow_m = d.lemma(p.gauss_lemma, &[dd, two, pow_m, h, dvd_two_pm]);
                let ih_result = d.apply(ih, &[dd, dvd_dd_pow_m]);
                let widened = widen_pow_eq(d, &p, m, dd, ih_result);
                d.lam_fv(h_fv, left_ty, widened)
            };

            let even_branch = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let gcd_dvd_dd = d.lemma(p.gcd_dvd_left, &[dd, two]);
                let dvd_2_dd = transport_dvd_left(d, gcd_dd2, two, h, dd, gcd_dvd_dd);

                let body = dvd_elim(d, two, dd, goal, dvd_2_dd, &|d, dprime, dd_eq| {
                    let two_dprime = d.mul(two, dprime);
                    let dvd_scaled =
                        transport_dvd_left(d, dd, two_dprime, dd_eq, two_pm, dvd_two_pm);

                    dvd_elim(d, two_dprime, two_pm, goal, dvd_scaled, &|d, e, eq2| {
                        let two_dprime_e = d.mul(two_dprime, e);
                        let assoc2 = d.lemma(p.mul_assoc, &[two, dprime, e]);
                        let dprime_e = d.mul(dprime, e);
                        let two_dprime_e2 = d.mul(two, dprime_e);
                        let (_e3, eq3) =
                            d.chain(two_pm, &[(two_dprime_e, eq2), (two_dprime_e2, assoc2)]);
                        let one_le_two = d.lemma(p.le_succ, &[one]);
                        let cancelled = d.lemma(
                            p.mul_left_cancel_of_pos,
                            &[two, pow_m, dprime_e, one_le_two, eq3],
                        );
                        let dvd_dprime_pow_m = dvd_intro(d, dprime, pow_m, e, cancelled);
                        let ih_result = d.apply(ih, &[dprime, dvd_dprime_pow_m]);

                        pow_eq_elim(d, m, dprime, None, goal, ih_result, &|d, i, le_i, eq_i| {
                            even_step_result(d, &p, dd, dprime, dd_eq, m, sm, i, le_i, eq_i)
                        })
                    })
                });
                d.lam_fv(h_fv, right_ty, body)
            };

            let anon = d.anon_name();
            let logic = d.prelude().logic;
            let or_ty = d.const_app(logic.or, &[left_ty, right_ty]);
            let motive_or = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
            let or_rec = d.kernel().const_(logic.or_rec, vec![]);
            let case_result = d.apply(
                or_rec,
                &[
                    left_ty,
                    right_ty,
                    motive_or,
                    coprime_branch,
                    even_branch,
                    two_cases,
                ],
            );
            let dd_body = d.lam_fv(hyp_fv, hyp_ty, case_result);
            d.lam_fv(dd_fv, nat, dd_body)
        };

        let proof = d.induct(&motive, &base, &step, k);
        (motive(d, k), proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.pow_pos` / `Nat.pow_lt_pow_succ` — strict monotonicity of `pow` in the
// exponent, for any base greater than `1`. Verified against the full
// `--include-constructed` theorem inventory that neither existed anywhere in
// this kernel: the only `pow`-adjacent order facts are `Nat.lt_pow_size` /
// `Nat.size_aux_lt_pow` (bounds tied to the `size` function, not general
// monotonicity) and `Nat.choose_le_two_pow` (binomial coefficients). This is
// the blocker the module doc above names for `sumDivisors_two_pow`'s tail
// sub-induction: the segment `(2^k, 2^(k+1))` argument needs `2^k <
// 2^(k+1)`, a direct instance of `pow_lt_pow_succ` at base `2`.
//
// Chose the SUCCESSOR form (`pow b k < pow b (succ k)`) over a general
// `pow_lt_pow_of_lt` (comparing two arbitrary exponents `i < j`): the tail
// sub-induction only ever steps one exponent at a time, and the successor
// form is what falls out directly from `pow`'s own recursive equation
// (`pow b (succ k) ≡ mul (pow b k) b`, by iota) without an extra induction
// on the exponent gap. A general form could be built later by induction on
// that gap using this lemma as its step case, if a future use needs it.
// ============================================================================

/// `eq : Eq from to`, `proof : Lt zero from` ⊢ `Lt zero to` — local copy of
/// `helpers.rs`'s `transport_dvd_left` pattern, specialized to `Lt zero ·`.
fn transport_lt_zero(
    d: &mut NatDev<'_>,
    from: ExprId,
    to: ExprId,
    eq: ExprId,
    proof: ExprId,
) -> ExprId {
    let motive = d.eq_motive(from, &|d, x| {
        let zero = d.zero();
        d.lt(zero, x)
    });
    d.transport(from, motive, proof, to, eq)
}

/// `ha : Lt zero a`, `hb : Lt zero b` ⊢ `Lt zero (mul a b)`.
///
/// Rewrites `b` to its succ-shape via [`pos_implies_succ_pred`], so `mul a
/// b` unfolds by iota to `add (mul a (pred b)) a`; that sum is `≥ a` (`a ≤
/// add a (mul a (pred b))` is [`super::NatPrelude::le_add_right`], commuted
/// into position by `add_comm`), and `a > 0` closes it through
/// `lt_of_lt_of_le`. No induction on `b` is needed — `pos_implies_succ_pred`
/// already supplies the one successor layer this needs.
fn positive_mul(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let succ_pred_fn = pos_implies_succ_pred(d, p, b);
    let eq_b = d.apply(succ_pred_fn, &[hb]); // Eq b (succ (pred b))
    let pred_b = d.pred(b);
    let succ_pred_b = d.succ(pred_b);

    let mul_a_predb = d.mul(a, pred_b);
    let lhs = d.add(mul_a_predb, a); // defeq `mul a succ_pred_b`
    let rhs = d.add(a, mul_a_predb);
    let comm = d.lemma(p.add_comm, &[mul_a_predb, a]); // Eq lhs rhs

    let zero = d.zero();
    let le_a_rhs = d.lemma(p.le_add_right, &[a, mul_a_predb]); // Le a rhs
    let q_rhs = d.lemma(p.lt_of_lt_of_le, &[zero, a, rhs, ha, le_a_rhs]); // Lt zero rhs

    let comm_rev = d.symm(lhs, rhs, comm); // Eq rhs lhs
    let q_lhs = transport_lt_zero(d, rhs, lhs, comm_rev, q_rhs); // Lt zero lhs

    // `q_lhs : Lt zero lhs`, and `lhs` is defeq `mul a succ_pred_b`, so it
    // serves directly as the motive's refl case at `succ_pred_b` below.
    let eq_b_rev = d.symm(b, succ_pred_b, eq_b); // Eq succ_pred_b b
    let motive = d.eq_motive(succ_pred_b, &|d, x| {
        let mx = d.mul(a, x);
        let zero = d.zero();
        d.lt(zero, mx)
    });
    d.transport(succ_pred_b, motive, q_lhs, b, eq_b_rev)
}

/// `Nat.pow_pos : ∀ b k, Lt zero b → Lt zero (pow b k)`, by induction on `k`.
///
/// Base (`k = 0`): `pow b zero ≡ succ zero` by iota, so `zero_lt_succ zero`
/// closes it directly (`hb` unused, matching this file's own convention for
/// an unused induction hypothesis — see [`pos_implies_succ_pred`]'s base
/// case). Step: `pow b (succ j) ≡ mul (pow b j) b` by iota; apply the IH to
/// `hb` for `Lt zero (pow b j)`, then [`positive_mul`] with `hb` again for
/// positivity of `b` itself.
pub(super) fn declare_pow_pos(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.pow_pos, 2, &|d, v| {
        let b = v[0];
        let k = v[1];
        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let zero = d.zero();
            let hb_ty = d.lt(zero, b);
            let px = d.pow(b, x);
            let concl = d.lt(zero, px);
            d.arrow(hb_ty, concl)
        };
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let hb_ty = d.lt(zero, b);
                let hb_fv = d.fresh_fvar();
                let body = d.zero_lt_succ(zero); // Lt zero (succ zero), defeq `Lt zero (pow b zero)`
                d.lam_fv(hb_fv, hb_ty, body)
            },
            &|d, j, ih| {
                let zero = d.zero();
                let hb_ty = d.lt(zero, b);
                let hb_fv = d.fresh_fvar();
                let hb = d.kernel().fvar(hb_fv);
                let ih_at_hb = d.apply(ih, &[hb]); // Lt zero (pow b j)
                let pow_b_j = d.pow(b, j);
                let body = positive_mul(d, &p, pow_b_j, b, ih_at_hb, hb);
                d.lam_fv(hb_fv, hb_ty, body)
            },
            k,
        );
        (motive(d, k), proof)
    })?;
    Ok(())
}

/// `Nat.pow_lt_pow_succ : ∀ b k, Lt (succ zero) b → Lt (pow b k) (pow b
/// (succ k))` — see the module note above for why this successor form was
/// chosen over a general two-exponent comparison.
///
/// `Lt (succ zero) b` is definitionally `Le 2 b`. The goal reduces (`pow b
/// (succ k) ≡ mul (pow b k) b` by iota) to `pow b k < mul (pow b k) b`. Let
/// `P := pow b k`: `P > 0` by `pow_pos` (needs `Lt 0 b`, derived from `Le 2
/// b` exactly as [`prime_pos`] derives `Le 1 x` from `Le 2 x`), and `P <
/// mul P 2 = add P P` is `add_lt_add_left` at `P + 0 < P + P` (`add P 0`
/// defeq `P`) transported along the `Eq (mul P 2) (add P P)` unfolding
/// (`mul P 2 ≡ add (add zero P) P` by iota; `zero_add` closes the inner
/// `add zero P = P`). Composing `P < mul P 2 ≤ mul P b` (the second step
/// `mul_le_mul_left` from `Le 2 b`) through `lt_of_lt_of_le` finishes it;
/// `mul P b` is defeq the goal's `pow b (succ k)`.
pub(super) fn declare_pow_lt_pow_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.pow_lt_pow_succ, 2, &|d, v| {
        let b = v[0];
        let k = v[1];
        let one = d.num(1);
        let two = d.num(2);
        let zero = d.zero();

        let pow_bk = d.pow(b, k);
        let sk = d.succ(k);
        let pow_bsk = d.pow(b, sk);
        let target = d.lt(pow_bk, pow_bsk);

        let hb_ty = d.lt(one, b); // defeq `Le 2 b`
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);

        // `Le 1 b` from `hb : Le 2 b` — the `prime_pos` pattern above.
        let le_1_2 = d.lemma(p.le_succ, &[one]); // Le 1 2
        let le_1_b = d.lemma(p.le_trans, &[one, two, b, le_1_2, hb]); // Le 1 b, defeq `Lt 0 b`

        // `Lt zero pow_bk` via `pow_pos`.
        let pow_pos_fn = d.lemma(p.pow_pos, &[b, k]);
        let hp = d.apply(pow_pos_fn, &[le_1_b]); // Lt zero pow_bk

        // `Eq (mul pow_bk 2) (add pow_bk pow_bk)`.
        let add_zero_p = d.add(zero, pow_bk);
        let za = d.lemma(p.zero_add, &[pow_bk]); // Eq (add zero pow_bk) pow_bk
        let add_add_zero_p_p = d.add(add_zero_p, pow_bk);
        let add_p_p = d.add(pow_bk, pow_bk);
        let step_eq = d.congr(add_zero_p, pow_bk, za, &|d, x| d.add(x, pow_bk));
        // step_eq : Eq add_add_zero_p_p add_p_p, and `mul pow_bk 2` is
        // defeq `add_add_zero_p_p` (unfold twice through `mul`'s recursion).

        // `Lt pow_bk add_p_p`, from `Lt zero pow_bk` via `add_lt_add_left`
        // (`add pow_bk zero` defeq `pow_bk`, `add`'s base case).
        let lt_add = d.lemma(p.add_lt_add_left, &[pow_bk, zero, pow_bk, hp]);

        // Transport along `step_eq` (reversed) from `add_p_p` back to
        // `add_add_zero_p_p` (i.e. `mul pow_bk 2`'s iota-shape).
        let step_eq_rev = d.symm(add_add_zero_p_p, add_p_p, step_eq); // Eq add_p_p add_add_zero_p_p
        let motive_mulp2 = d.eq_motive(add_p_p, &|d, x| d.lt(pow_bk, x));
        let lt_mul_p2 = d.transport(add_p_p, motive_mulp2, lt_add, add_add_zero_p_p, step_eq_rev);
        // lt_mul_p2 : Lt pow_bk add_add_zero_p_p, defeq `Lt pow_bk (mul pow_bk 2)`.

        // `mul pow_bk 2 ≤ mul pow_bk b`, from `hb : Le 2 b`.
        let mul_pow_bk_two = d.mul(pow_bk, two);
        let mul_pow_bk_b = d.mul(pow_bk, b);
        let mul_le = d.lemma(p.mul_le_mul_left, &[pow_bk, two, b, hb]);

        // Chain: `pow_bk < mul_pow_bk_two ≤ mul_pow_bk_b`, and `mul_pow_bk_b`
        // is defeq the goal's `pow b (succ k)`.
        let final_proof = d.lemma(
            p.lt_of_lt_of_le,
            &[pow_bk, mul_pow_bk_two, mul_pow_bk_b, lt_mul_p2, mul_le],
        );

        let proof = d.lam_fv(hb_fv, hb_ty, final_proof);
        let stmt = d.arrow(hb_ty, target);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.dvd_two_pow_succ_iff_of_le` — the congruence step
// `sumDivisors_two_pow`'s tail sub-induction consumes: for `dd ≤ 2^k`, `dd ∣
// 2^k ↔ dd ∣ 2^(succ k)`. Depends on both classification theorems above AND
// [`declare_pow_lt_pow_succ`] (called after it in [`declare_perfect_all`]).
//
// Forward (`dd ∣ 2^k → dd ∣ 2^(succ k)`) is immediate: `2^(succ k) ≡ mul (2^k)
// 2` by iota, and `dvd_mul_right_of_dvd` (`divisibility.rs`) lands directly.
//
// Backward needs the bound. [`declare_dvd_two_pow_classify`] applied to `dd ∣
// 2^(succ k)` gives `dd = 2^i` for some `i ≤ succ k`. Split via
// `lt_or_eq_of_le` on that bound: `i < succ k` gives `i ≤ k`
// (`le_of_succ_le_succ`) directly, and [`pow_dvd_pow_of_le`] plus transport
// along `dd = 2^i` closes it. `i = succ k` is IMPOSSIBLE given `dd ≤ 2^k`:
// it would force `dd = 2^(succ k)`, so `2^(succ k) ≤ 2^k`, contradicting
// `pow_lt_pow_succ`'s `2^k < 2^(succ k)` via `lt_irrefl`.
// ============================================================================

/// `∀ i k, Le i k → dvd (pow 2 i) (pow 2 k)` — built directly rather than
/// registered as its own kernel declaration, since it is only ever consumed
/// here. `le_dest` gives `k = i + j`; `pow_add` (`algebra.rs`) then gives
/// `pow 2 k = mul (pow 2 i) (pow 2 j)`, exactly the divisor witness.
fn pow_dvd_pow_of_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    k: ExprId,
    le_i_k: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let two = d.num(2);
    let pow_i = d.pow(two, i);
    let pow_k = d.pow(two, k);
    let goal = d.dvd(pow_i, pow_k);

    let dest = d.lemma(p.le_dest, &[i, k, le_i_k]); // ∃ j, Eq (add i j) k

    // Predicate `fun j => Eq (add i j) k`, matching `le_dest`'s own witness
    // shape exactly (`order.rs`'s `le_dest` declaration).
    let predicate = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sum = d.add(i, j);
        let body = d.eq(sum, k);
        d.lam_fv(j_fv, nat, body)
    };
    let logic = d.prelude().logic;
    let src_ty = {
        let one = d.level_one();
        let exists_ = d.kernel().const_(logic.exists_, vec![one]);
        d.apply(exists_, &[nat, predicate])
    };
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, src_ty, goal, BinderInfo::Default);
    let minor = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let eq_fv = d.fresh_fvar();
        let eq_proof = d.kernel().fvar(eq_fv);
        let sum = d.add(i, j);
        let eq_ty = d.eq(sum, k);

        let pow_add_eq = d.lemma(p.pow_add, &[two, i, j]); // Eq (pow 2 sum) (mul pow_i pow_j)
        let pow_sum = d.pow(two, sum);
        let pow_j = d.pow(two, j);
        let mul_ij = d.mul(pow_i, pow_j);

        let congr_pow = d.congr(sum, k, eq_proof, &|d, t| d.pow(two, t)); // Eq pow_sum pow_k
        let symm_congr = d.symm(pow_sum, pow_k, congr_pow); // Eq pow_k pow_sum
        let (_e, final_eq) = d.chain(pow_k, &[(pow_sum, symm_congr), (mul_ij, pow_add_eq)]);

        let intro = dvd_intro(d, pow_i, pow_k, pow_j, final_eq);
        let with_eq = d.lam_fv(eq_fv, eq_ty, intro);
        d.lam_fv(j_fv, nat, with_eq)
    };
    let one = d.level_one();
    let rec = d.kernel().const_(logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, predicate, motive, minor, dest])
}

/// `Nat.dvd_two_pow_succ_iff_of_le : ∀ k dd, Le dd (pow 2 k) → Iff (dvd dd
/// (pow 2 k)) (dvd dd (pow 2 (succ k)))` — see the module doc above for the
/// proof route.
pub(super) fn declare_dvd_two_pow_succ_iff_of_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dvd_two_pow_succ_iff_of_le, 2, &|d, v| {
        let (k, dd) = (v[0], v[1]);
        let two = d.num(2);
        let pow_k = d.pow(two, k);
        let sk = d.succ(k);
        let pow_sk = d.pow(two, sk);

        let bound_ty = d.le(dd, pow_k);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);

        let left_ty = d.dvd(dd, pow_k);
        let right_ty = d.dvd(dd, pow_sk);

        let forward = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            // `dvd dd (mul pow_k two)`, defeq `dvd dd pow_sk` (`pow`'s own
            // succ-equation).
            let step = d.lemma(p.dvd_mul_right_of_dvd, &[dd, pow_k, two, h]);
            d.lam_fv(h_fv, left_ty, step)
        };

        let backward = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let classify = d.lemma(p.dvd_two_pow_classify, &[sk, dd, h]);
            let goal = left_ty;

            let body = pow_eq_elim(d, sk, dd, None, goal, classify, &|d, i, le_i_sk, eq_i| {
                let dich = d.lemma(p.lt_or_eq_of_le, &[i, sk, le_i_sk]);
                let lt_ty = d.lt(i, sk);
                let eq_ty2 = d.eq(i, sk);

                let lt_branch = {
                    let hh_fv = d.fresh_fvar();
                    let hh = d.kernel().fvar(hh_fv); // Lt i sk, defeq Le (succ i) (succ k)
                    let le_i_k = d.lemma(p.le_of_succ_le_succ, &[i, k, hh]);
                    let dvd_pow_i_pow_k = pow_dvd_pow_of_le(d, &p, i, k, le_i_k);
                    let pow_i = d.pow(two, i);
                    let eq_i_rev = d.symm(dd, pow_i, eq_i); // Eq pow_i dd
                    let result = transport_dvd_left(d, pow_i, dd, eq_i_rev, pow_k, dvd_pow_i_pow_k);
                    d.lam_fv(hh_fv, lt_ty, result)
                };

                let eq_branch = {
                    let hh_fv = d.fresh_fvar();
                    let hh = d.kernel().fvar(hh_fv); // Eq i sk
                    let pow_i = d.pow(two, i);
                    let congr_i = d.congr(i, sk, hh, &|d, t| d.pow(two, t)); // Eq pow_i pow_sk
                    let (_e, dd_eq_pow_sk) = d.chain(dd, &[(pow_i, eq_i), (pow_sk, congr_i)]);

                    let motive_bound = d.eq_motive(dd, &|d, x| d.le(x, pow_k));
                    let le_powsk_powk = d.transport(dd, motive_bound, bound, pow_sk, dd_eq_pow_sk);

                    let two2 = d.num(2);
                    let le_two_two = d.lemma(p.le_refl, &[two2]); // Le 2 2, defeq Lt 1 2
                    let lt_powk_powsk = d.lemma(p.pow_lt_pow_succ, &[two2, k, le_two_two]);
                    let contra = d.lemma(
                        p.lt_of_lt_of_le,
                        &[pow_k, pow_sk, pow_k, lt_powk_powsk, le_powsk_powk],
                    );
                    let irrefl = d.lemma(p.lt_irrefl, &[pow_k]);
                    let absurd = d.apply(irrefl, &[contra]);

                    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                    let level = d.kernel().level_zero();
                    let false_rec = d.kernel().const_(p.logic.false_rec, vec![level]);
                    let anon2 = d.anon_name();
                    let motive_false = d.kernel().lam(anon2, false_ty, goal, BinderInfo::Default);
                    let result = d.apply(false_rec, &[motive_false, absurd]);
                    d.lam_fv(hh_fv, eq_ty2, result)
                };

                let anon = d.anon_name();
                let logic = d.prelude().logic;
                let or_ty = d.const_app(logic.or, &[lt_ty, eq_ty2]);
                let motive_or = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
                let or_rec = d.kernel().const_(logic.or_rec, vec![]);
                d.apply(
                    or_rec,
                    &[lt_ty, eq_ty2, motive_or, lt_branch, eq_branch, dich],
                )
            });
            d.lam_fv(h_fv, right_ty, body)
        };

        let logic = d.prelude().logic;
        let iff_ty = d.const_app(logic.iff, &[left_ty, right_ty]);
        let iff_proof = d.const_app(logic.iff_intro, &[left_ty, right_ty, forward, backward]);
        let proof = d.lam_fv(bound_fv, bound_ty, iff_proof);
        let stmt = d.arrow(bound_ty, iff_ty);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare `Nat.sumDivisors`, its computational and prime sanity theorems,
/// `Nat.Perfect`, the finite geometric sum over powers of two, the divisor
/// classifications `Nat.dvd_two_pow_mul_classify` and
/// `Nat.dvd_two_pow_classify`, the divisor congruence
/// `Nat.dvd_two_pow_succ_iff_of_le`, and `pow`'s strict monotonicity in the
/// exponent (`Nat.pow_pos`, `Nat.pow_lt_pow_succ`), in dependency order.
pub(super) fn declare_perfect_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_sum_divisors(d, p)?;
    declare_sum_divisors_one(d, p)?;
    declare_sum_divisors_prime(d, p)?;
    declare_perfect(d, p)?;
    declare_pow2_geom_sum(d, p)?;
    declare_dvd_two_pow_mul_classify(d, p)?;
    declare_dvd_two_pow_classify(d, p)?;
    declare_pow_pos(d, p)?;
    declare_pow_lt_pow_succ(d, p)?;
    declare_dvd_two_pow_succ_iff_of_le(d, p)?;
    Ok(())
}
