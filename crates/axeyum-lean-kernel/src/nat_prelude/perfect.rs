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
use super::helpers::{iff_forward, iff_reverse};
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

/// Declare `Nat.sumDivisors`, its computational and prime sanity theorems,
/// and `Nat.Perfect`, in dependency order.
pub(super) fn declare_perfect_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_sum_divisors(d, p)?;
    declare_sum_divisors_one(d, p)?;
    declare_sum_divisors_prime(d, p)?;
    declare_perfect(d, p)?;
    Ok(())
}
