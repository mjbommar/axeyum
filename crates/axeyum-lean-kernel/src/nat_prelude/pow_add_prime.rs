//! Toward `F:ml430-nat-pow-of-pow-add-prime-ab61d0d3` (the Fermat-prime
//! lemma: `Nat.Prime (a^n+1) -> exists m, n = 2^m`).
//!
//! The classical proof is a contrapositive: if `n` has an odd factor `d > 1`,
//! write `n = d*e`; then `a^e+1` divides `a^n+1` via the odd-power
//! factorization `x^d+1 = (x+1)*(x^{d-1} - x^{d-2} + ... + 1)`, exhibiting a
//! nontrivial divisor of the supposed prime.
//!
//! **That cofactor is an alternating sum, and this kernel has no signed sum
//! over ℕ.** Rather than build one (pairing terms, or transporting through
//! `Int`), this file avoids the closed-form cofactor entirely and proves the
//! divisibility by INDUCTION on the number of odd steps, using only the
//! `dvd` calculus (`dvd_add`, `dvd_mul_left`) plus one algebraic identity
//! with no subtraction:
//!
//! ```text
//! x^2 = x'*(x+1) + 1        (x = succ x', i.e. x' is the free predecessor)
//! ```
//!
//! which is `x^2 - 1 = (x-1)(x+1)` written additively by substituting the
//! genuinely free variable `x'` for `x-1` (so no `Nat.sub` ever appears).
//! Multiplying by `x^{2j+1}` and using `pow_add` gives, for every `j`:
//!
//! ```text
//! x^{2(j+1)+1} + 1 = x'*(x+1)*x^{2j+1} + (x^{2j+1} + 1)
//! ```
//!
//! — a multiple of `(x+1)` plus something already known (by the induction
//! hypothesis) to be a multiple of `(x+1)`, so `dvd_add` finishes the step.
//! No sum, no closed-form cofactor, no `Int` transport: just one identity and
//! the standard divisibility lemmas, at magnitudes that stay tiny in every
//! test (`2^3+1=9`, `2^5+1=33`, ...).
//!
//! **Scope landed here**: the fully general reusable lemma
//! `Nat.dvd_pow_add_one_of_odd_mul_exp : forall a e t, a^e+1 | a^(e*(2t+1))+1`
//! (odd exponents spelled `succ (mul 2 t)`, i.e. `2t+1`, rather than via
//! `Nat.Odd`'s own `succ (add t t)` witness shape — bridging the two needs
//! only `two_mul_eq_add_self`, `powsq.rs`, for a future lane). This is
//! exactly the "d odd, d > 1 ⟹ a^e+1 ∣ a^{d·e}+1" step named in the fact's
//! brief as a good outcome on its own. **Assembling it into the full Fermat
//! lemma is NOT done here**: that direction additionally needs "n is not a
//! power of two ⟹ n has an odd factor > 1" (a 2-adic-valuation argument, a
//! separate well-founded construction) plus the final primality contradiction
//! (showing the exhibited divisor is neither `1` nor `a^n+1`). Left open for
//! a follow-up lane; `F:ml430-nat-pow-of-pow-add-prime-ab61d0d3` stays `open`.
//!
//! Every numeral formed by the checked test instantiations stays under 40
//! (`2^5+1=33` is the largest), per the "keep formed magnitudes small" rule —
//! this is a proof about FREE variables, not a computation, so nothing here
//! forces a large unary tower.

use super::NatPrelude;
use super::finite::ex_falso;
use super::helpers::{and_left, and_right, iff_reverse};
use super::ops::{NatDev, NatOps, cases_zero_succ, two_mul_eq_add_self};
use super::primes::or_cases;
use crate::KernelError;
use crate::expr::ExprId;

/// `succ (mul 2 t)` — the `t`-th odd number, `2t+1`.
pub(super) fn exponent_of(d: &mut NatDev<'_>, t: ExprId) -> ExprId {
    let two = d.num(2);
    let e = d.mul(two, t);
    d.succ(e)
}

/// `dvd (add x 1) (add (pow x (exponent_of t)) 1)` — the statement shared by
/// the outer `x`-case-split and the inner `t`-induction (with whichever of
/// `x`/`t` is not yet fixed left as the argument).
fn core_stmt(d: &mut NatDev<'_>, x: ExprId, t: ExprId) -> ExprId {
    let one = d.num(1);
    let exp = exponent_of(d, t);
    let pw = d.pow(x, exp);
    let n = d.add(pw, one);
    let base = d.add(x, one);
    d.dvd(base, n)
}

/// Build a proof of `dvd a n` from a witness `q` and `eq_proof : Eq n (mul a
/// q)`. A local copy of `divisibility.rs`'s private `dvd_intro` — that one is
/// module-private and this module has no other need to touch that file.
fn intro_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    n: ExprId,
    witness: ExprId,
    eq_proof: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let predicate = d.dvd_predicate(a, n);
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
    d.apply(intro, &[nat, predicate, witness, eq_proof])
}

/// `x = 0` branch of the outer case split: `dvd 1 n` holds for every `n`
/// (witness `n`, since `n = 1*n`), and `add 0 1` is defeq `1`.
fn at_zero_branch(d: &mut NatDev<'_>, p: &NatPrelude, t: ExprId) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let exp = exponent_of(d, t);
    let pw = d.pow(zero, exp);
    let n = d.add(pw, one);
    let mul_one_n = d.mul(one, n);
    let h_om = d.lemma(p.one_mul, &[n]); // Eq(mul_one_n, n)
    let h_rev = d.symm(mul_one_n, n, h_om); // Eq(n, mul_one_n)
    intro_dvd(d, &p, one, n, n, h_rev)
}

/// `t = 0` base case of the inner induction, `x = succ xp` already fixed:
/// `dvd (x+1) (x^1+1)` is `dvd (x+1) (x+1)`, up to `pow_x_one = mul(1,x)`.
fn base_t_branch(d: &mut NatDev<'_>, p: &NatPrelude, xp: ExprId) -> ExprId {
    let p = *p;
    let x = d.succ(xp);
    let one = d.num(1);
    let p_fixed = d.add(x, one);
    let mul_one_x = d.mul(one, x);
    let q = d.add(mul_one_x, one);
    let h_om = d.lemma(p.one_mul, &[x]); // Eq(mul_one_x, x)
    let h_rev = d.symm(mul_one_x, x, h_om); // Eq(x, mul_one_x)
    let h_add = d.congr(x, mul_one_x, h_rev, &|d, t| d.add(t, one)); // Eq(p_fixed, q)
    let dvd_refl_p = d.lemma(p.dvd_refl, &[p_fixed]);
    let motive = d.eq_motive(p_fixed, &|d, xx| d.dvd(p_fixed, xx));
    d.transport(p_fixed, motive, dvd_refl_p, q, h_add)
}

/// `Eq (add (mul xp (add x 1)) 1) (mul x x)`, i.e. `x'*(x+1)+1 = x^2`, for
/// `x = succ xp` — `x^2 - 1 = (x-1)(x+1)` written with no subtraction, using
/// the free predecessor `xp` in place of `x-1`.
///
/// Derived in two hops: `K' : mul x x = add (mul xp x) x` (one
/// `right_distrib` + `one_mul`), then `add (mul xp (add x 1)) 1` is chased
/// down to `add (mul xp x) x` (one `left_distrib`, `mul_one`, `add_assoc`)
/// and identified with `K'`'s right side via `add xp 1` being defeq `x`.
fn square_eq_pred_mul_succ_add_one(d: &mut NatDev<'_>, p: &NatPrelude, xp: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let x = d.succ(xp);
    let p_fixed = d.add(x, one);

    // K' : Eq(mul(x,x), add(mul(xp,x), x))
    let mul_xp_x = d.mul(xp, x);
    let mul_one_x = d.mul(one, x);
    let xx = d.mul(x, x);
    let h_rd = d.lemma(p.right_distrib, &[xp, one, x]);
    let target1 = d.add(mul_xp_x, mul_one_x);
    let h_om = d.lemma(p.one_mul, &[x]);
    let target2 = d.add(mul_xp_x, x);
    let h2 = d.congr(mul_one_x, x, h_om, &|d, t| d.add(mul_xp_x, t));
    let (_, kprime_proof) = d.chain(xx, &[(target1, h_rd), (target2, h2)]);
    // kprime_proof : Eq(xx, target2)

    // Chase add(mul(xp,p_fixed),one) down to xx.
    let mul_xp_pfixed = d.mul(xp, p_fixed);
    let mul_xp_one = d.mul(xp, one);
    let start = d.add(mul_xp_pfixed, one);
    let h_ld = d.lemma(p.left_distrib, &[xp, x, one]);
    let inner1 = d.add(mul_xp_x, mul_xp_one);
    let t1 = d.add(inner1, one);
    let h1 = d.congr(mul_xp_pfixed, inner1, h_ld, &|d, t| d.add(t, one));
    let h_mo = d.lemma(p.mul_one, &[xp]);
    let inner2 = d.add(mul_xp_x, xp);
    let t2 = d.add(inner2, one);
    let h2b = d.congr(mul_xp_one, xp, h_mo, &|d, t| {
        let inner = d.add(mul_xp_x, t);
        d.add(inner, one)
    });
    let h_assoc = d.lemma(p.add_assoc, &[mul_xp_x, xp, one]);
    let xp_plus_one = d.add(xp, one);
    let t3 = d.add(mul_xp_x, xp_plus_one);
    let kprime_rev = d.symm(xx, target2, kprime_proof); // Eq(target2, xx), defeq-usable as Eq(t3, xx)
    let (_, proof) = d.chain(
        start,
        &[(t1, h1), (t2, h2b), (t3, h_assoc), (xx, kprime_rev)],
    );
    proof
}

/// The inductive step: from `dvd (x+1) (x^{2j+1}+1)` derive
/// `dvd (x+1) (x^{2(j+1)+1}+1)` via
/// `x^{2(j+1)+1}+1 = x'*(x+1)*x^{2j+1} + (x^{2j+1}+1)`.
fn step_t_branch(d: &mut NatDev<'_>, p: &NatPrelude, xp: ExprId, j: ExprId, ih: ExprId) -> ExprId {
    let p = *p;
    let x = d.succ(xp);
    let one = d.num(1);
    let two = d.num(2);
    let p_fixed = d.add(x, one);
    let ej = d.mul(two, j);
    let a_exp = d.succ(ej);
    let a_pow = d.pow(x, a_exp); // A = x^(2j+1)

    let k_factored = square_eq_pred_mul_succ_add_one(d, &p, xp);
    // k_factored : Eq(add(mul(xp,p_fixed),one), mul(x,x))

    let mul_one_x = d.mul(one, x);
    let h_om_x = d.lemma(p.one_mul, &[x]);
    let xx = d.mul(x, x);
    let h_pow2 = d.congr(mul_one_x, x, h_om_x, &|d, t| d.mul(t, x));
    // h_pow2 : Eq(mul(mul_one_x,x), xx) -- serves as Eq(pow(x,2), xx) by defeq

    let pow_x_two = d.pow(x, two);
    let sum_aexp_two = d.add(a_exp, two);
    let pow_x_sum = d.pow(x, sum_aexp_two); // defeq to x^{2(j+1)+1}, the goal's B
    let h_pow_add = d.lemma(p.pow_add, &[x, a_exp, two]);
    let target0 = d.mul(a_pow, pow_x_two);

    let h1 = d.congr(pow_x_two, xx, h_pow2, &|d, t| d.mul(a_pow, t));
    let target1 = d.mul(a_pow, xx);

    let mul_xp_pfixed = d.mul(xp, p_fixed);
    let kf_lhs = d.add(mul_xp_pfixed, one);
    let k_rev = d.symm(kf_lhs, xx, k_factored); // Eq(xx, kf_lhs)
    let h2 = d.congr(xx, kf_lhs, k_rev, &|d, t| d.mul(a_pow, t));
    let target2 = d.mul(a_pow, kf_lhs);

    let h3 = d.lemma(p.left_distrib, &[a_pow, mul_xp_pfixed, one]);
    let mul_apow_mulxppfixed = d.mul(a_pow, mul_xp_pfixed);
    let mul_apow_one = d.mul(a_pow, one);
    let target3 = d.add(mul_apow_mulxppfixed, mul_apow_one);

    let mul_apow_xp = d.mul(a_pow, xp);
    let m_target = d.mul(mul_apow_xp, p_fixed);
    let h_assoc = d.lemma(p.mul_assoc, &[a_pow, xp, p_fixed]);
    // h_assoc : Eq(m_target, mul_apow_mulxppfixed)
    let h_assoc_rev = d.symm(m_target, mul_apow_mulxppfixed, h_assoc);
    let h4 = d.congr(mul_apow_mulxppfixed, m_target, h_assoc_rev, &|d, t| {
        d.add(t, mul_apow_one)
    });
    let target4 = d.add(m_target, mul_apow_one);

    let h_mo = d.lemma(p.mul_one, &[a_pow]);
    let h5 = d.congr(mul_apow_one, a_pow, h_mo, &|d, t| d.add(m_target, t));
    let target5 = d.add(m_target, a_pow);

    let (_, eq_b_eq_m_plus_a) = d.chain(
        pow_x_sum,
        &[
            (target0, h_pow_add),
            (target1, h1),
            (target2, h2),
            (target3, h3),
            (target4, h4),
            (target5, h5),
        ],
    );
    // eq_b_eq_m_plus_a : Eq(pow_x_sum, target5 = add(m_target, a_pow))

    let b_plus_one = d.add(pow_x_sum, one);
    let h6 = d.congr(pow_x_sum, target5, eq_b_eq_m_plus_a, &|d, t| d.add(t, one));
    let target6 = d.add(target5, one);

    let h_assoc2 = d.lemma(p.add_assoc, &[m_target, a_pow, one]);
    let a_pow_plus_one = d.add(a_pow, one);
    let target7 = d.add(m_target, a_pow_plus_one);

    let (_, final_eq) = d.chain(b_plus_one, &[(target6, h6), (target7, h_assoc2)]);
    // final_eq : Eq(b_plus_one, target7)

    let dvd_m = d.lemma(p.dvd_mul_left, &[p_fixed, mul_apow_xp]);
    // dvd_m : Dvd(p_fixed, mul(mul_apow_xp,p_fixed)) = Dvd(p_fixed, m_target)

    let dvd_a_plus_one = ih; // Dvd(p_fixed, a_pow_plus_one), exactly motive_t(j)

    let dvd_sum = d.lemma(
        p.dvd_add,
        &[p_fixed, m_target, a_pow_plus_one, dvd_m, dvd_a_plus_one],
    );
    // dvd_sum : Dvd(p_fixed, target7)

    let final_eq_rev = d.symm(b_plus_one, target7, final_eq);
    let motive_final = d.eq_motive(target7, &|d, tt| d.dvd(p_fixed, tt));
    d.transport(target7, motive_final, dvd_sum, b_plus_one, final_eq_rev)
}

/// `Nat.pow_mul : ∀ a e k, Eq (pow a (mul e k)) (pow (pow a e) k)` —
/// induction on `k`. Both directions of the base case compute (`mul e 0` and
/// `pow _ 0` both hit `pow _ zero ≡ 1` definitionally, mirroring
/// `Int.pow_mul`'s own base case, `int_prelude/algebra.rs`); the step chains
/// `pow_add` then the induction hypothesis, with `mul e (succ j) ≡ add (mul e
/// j) e` and `pow (pow a e) (succ j) ≡ mul (pow (pow a e) j) (pow a e)` both
/// definitional (`Nat.mul`/`Nat.pow` both recurse on their SECOND argument).
pub(super) fn declare_pow_mul(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.pow_mul, 3, &|d, v| {
        let (a, e, k) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let prod = d.mul(e, x);
            let lhs = d.pow(a, prod);
            let pow_a_e = d.pow(a, e);
            let rhs = d.pow(pow_a_e, x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, k);
        let proof = d.induct(
            &motive,
            &|d| {
                let one = d.num(1);
                d.refl(one)
            },
            &|d, j, ih| {
                let ej = d.mul(e, j);
                let pow_a_ej = d.pow(a, ej);
                let sum = d.add(ej, e);
                let start = d.pow(a, sum);
                let pow_a_e = d.pow(a, e);
                let after_pow_add = d.mul(pow_a_ej, pow_a_e);
                let h_pow_add = d.lemma(p.pow_add, &[a, ej, e]);
                let pow_pae_j = d.pow(pow_a_e, j);
                let after_ih = d.mul(pow_pae_j, pow_a_e);
                let h_ih = d.congr(pow_a_ej, pow_pae_j, ih, &|d, t| d.mul(t, pow_a_e));
                let (_, proof) = d.chain(start, &[(after_pow_add, h_pow_add), (after_ih, h_ih)]);
                proof
            },
            k,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.dvd_pow_add_one_of_odd_exp : ∀ x t, dvd (add x 1) (add (pow x (succ
/// (mul 2 t))) 1)` — `x+1 ∣ x^{2t+1}+1` for every `x`. `x = 0` is trivial
/// (`dvd 1 _`); `x = succ xp` inducts on `t` via [`base_t_branch`] and
/// [`step_t_branch`].
pub(super) fn declare_dvd_pow_add_one_of_odd_exp(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dvd_pow_add_one_of_odd_exp, 2, &|d, v| {
        let (x, t) = (v[0], v[1]);
        let stmt = core_stmt(d, x, t);
        let motive_x = |d: &mut NatDev<'_>, xx: ExprId| -> ExprId { core_stmt(d, xx, t) };
        let proof = cases_zero_succ(d, x, &motive_x, &|d| at_zero_branch(d, &p, t), &|d, xp| {
            let motive_t = |d: &mut NatDev<'_>, tt: ExprId| -> ExprId {
                let xx = d.succ(xp);
                core_stmt(d, xx, tt)
            };
            d.induct(
                &motive_t,
                &|d| base_t_branch(d, &p, xp),
                &|d, j, ih| step_t_branch(d, &p, xp, j, ih),
                t,
            )
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.dvd_pow_add_one_of_odd_mul_exp : ∀ a e t, dvd (add (pow a e) 1) (add
/// (pow a (mul e (succ (mul 2 t)))) 1)` — `a^e+1 ∣ a^{e*(2t+1)}+1`, the
/// reusable "odd-factor divisibility" step named in the fact's brief
/// (`d := 2t+1` odd; `d = 1` at `t = 0` is the trivial case, `d > 1` for
/// `t ≥ 1`). Combines [`declare_pow_mul`] (to see `a^(e*d)` as `(a^e)^d`)
/// with [`declare_dvd_pow_add_one_of_odd_exp`] at `x := a^e`.
pub(super) fn declare_dvd_pow_add_one_of_odd_mul_exp(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dvd_pow_add_one_of_odd_mul_exp, 3, &|d, v| {
        let (a, e, t) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let x = d.pow(a, e);
        let d_exp = exponent_of(d, t);
        let ed = d.mul(e, d_exp);
        let pow_a_ed = d.pow(a, ed);
        let n_goal = d.add(pow_a_ed, one);
        let base_goal = d.add(x, one);
        let stmt = d.dvd(base_goal, n_goal);

        let h_pm = d.lemma(p.pow_mul, &[a, e, d_exp]);
        // h_pm : Eq(pow_a_ed, pow(x,d_exp))
        let pow_x_dexp = d.pow(x, d_exp);
        let core_proof = d.lemma(p.dvd_pow_add_one_of_odd_exp, &[x, t]);
        // core_proof : Dvd(base_goal, add(pow_x_dexp,one))

        let h_pm_rev = d.symm(pow_a_ed, pow_x_dexp, h_pm); // Eq(pow_x_dexp, pow_a_ed)
        let h_n = d.congr(pow_x_dexp, pow_a_ed, h_pm_rev, &|d, tt| d.add(tt, one));
        let n_mid = d.add(pow_x_dexp, one);
        let motive = d.eq_motive(n_mid, &|d, tt| d.dvd(base_goal, tt));
        let proof = d.transport(n_mid, motive, core_proof, n_goal, h_n);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// Closing the fact: `n` not a power of two has an odd factor > 1, and that
// factor's exhibited divisor of `a^n+1` is neither `1` nor `a^n+1`.
//
// The two remaining pieces named by the earlier handoff, both landed here:
//
// 1. `Nat.pow_two_or_has_odd_factor : ∀ n, Ne n 0 →
//    Or (∃ m, Eq n (pow 2 m)) (∃ e t, Eq n (mul e (exponent_of t)) ∧ Ne t 0)`
//    — by STRUCTURAL (not well-founded) induction on a FUEL bound `Le n
//    fuel`, instantiated at `fuel := n` via `le_refl`. The handoff sized
//    this as "a genuine well-founded-recursion undertaking" needing
//    `WellFounded.fix`; that sizing does not hold up. Ordinary `Nat.rec` on
//    a fuel bound gives the induction hypothesis for EVERY `n' ≤ fuel - 1`,
//    not just `fuel - 1` itself (the motive is `∀ n, Le n fuel → …`), which
//    is exactly the strong-induction shape this proof needs to recurse on
//    `half := div n 2` rather than on `n`'s predecessor. No `WellFounded`,
//    no `Acc`, no `lt_well_founded` anywhere in this file.
//
//    The recursion itself splits on `Nat.even_or_odd` (`powsq.rs`, already
//    proved: `n = half+half` or `n = succ(half+half)`), then on `half`
//    itself via `cases_zero_succ` (`half = 0` or `half = succ hp`) — never on
//    a `beq`/decidability dance, since parity is already decided by
//    `even_or_odd` and "is `half` zero" is just `Nat`'s own constructors.
//    Four leaves: even+half=0 is `n=0`, contradicting the hypothesis; odd+
//    half=0 is `n=1=2^0`; even+half=succ hp recurses on `half` (bounded via
//    `lt_two_mul_of_pos`+`lt_of_lt_of_le`+`le_of_succ_le_succ`, the same
//    three-lemma bound `bit_order.rs`'s `msb_exists_of_le_fuel` step uses for
//    an unrelated predicate) and re-assembles the answer at `n` by
//    `n = 2*half`; odd+half=succ hp answers directly with witness `e := 1`,
//    `t := half` (`half ≠ 0` for free, `half` being `succ hp`).
//
// 2. `Nat.pow_of_pow_add_prime` itself — the fact's statement. The odd
//    branch's witnesses `(e, t)` feed `dvd_pow_add_one_of_odd_mul_exp`,
//    exhibiting `a^e+1 ∣ a^n+1`; primality (spelled inline, matching
//    `primes.rs`/`factorization.rs`'s own convention: this prelude has no
//    `Prime`) forces that divisor to be `1` or `a^n+1`, and BOTH are
//    excluded (`a^e+1 ≥ 2` from `pow_pos`, since `a > 1`; `a^e+1 ≠ a^n+1`
//    from `e < n` — which needs `d := exponent_of(t) > 1` from `t ≠ 0`,
//    hence `e·1 < e·d = n` via `mul_lt_mul_left` — combined with
//    `pow_injective` and `lt_irrefl`).
// ============================================================================

/// `Ne x zero`, i.e. `Eq x zero → False`.
pub(super) fn ne_zero_ty(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let eq_ty = d.eq(x, zero);
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    d.arrow(eq_ty, false_ty)
}

/// `fun m => Eq n (pow 2 m)`.
fn pow2_pred(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let two = d.num(2);
    let pw = d.pow(two, m);
    let body = d.eq(n, pw);
    d.lam_fv(m_fv, nat, body)
}

/// `∃ m, Eq n (pow 2 m)`.
pub(super) fn pow2_disjunct(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let pred = pow2_pred(d, n);
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `fun t => Eq n (mul e (exponent_of t)) ∧ Ne t zero`.
fn odd_inner_pred(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, e: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let dexp = exponent_of(d, t);
    let prod = d.mul(e, dexp);
    let eqn = d.eq(n, prod);
    let net = ne_zero_ty(d, &p, t);
    let conj = d.const_app(p.logic.and, &[eqn, net]);
    d.lam_fv(t_fv, nat, conj)
}

/// `fun e => ∃ t, Eq n (mul e (exponent_of t)) ∧ Ne t zero`.
fn odd_pred(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let pred_t = odd_inner_pred(d, &p, n, e);
    let ex_t = d.kernel().const_(p.logic.exists_, vec![one]);
    let body = d.apply(ex_t, &[nat, pred_t]);
    d.lam_fv(e_fv, nat, body)
}

/// `∃ e t, Eq n (mul e (exponent_of t)) ∧ Ne t zero`.
pub(super) fn odd_disjunct(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let pred = odd_pred(d, &p, n);
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `Or (pow2_disjunct n) (odd_disjunct n)`.
pub(super) fn disj_stmt(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let a = pow2_disjunct(d, &p, n);
    let b = odd_disjunct(d, &p, n);
    d.const_app(p.logic.or, &[a, b])
}

/// `Exists.intro` at domain `Nat`.
fn intro_exists_nat(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
    d.apply(intro, &[nat, pred, witness, proof])
}

/// `Exists.rec` at domain `Nat`, non-dependent motive `goal`, given the
/// existential proof `proof_ex` directly. `build_minor(d, witness, h)` must
/// produce a proof of `goal` from an arbitrary witness and a proof of
/// `pred witness`.
fn elim_exists_nat(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred: ExprId,
    goal: ExprId,
    proof_ex: ExprId,
    build_minor: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pred_x = d.apply(pred, &[x]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let body = build_minor(d, x, h);
    let minor = {
        let inner = d.lam_fv(h_fv, pred_x, body);
        d.lam_fv(x_fv, nat, inner)
    };
    let hh_fv = d.fresh_fvar();
    let ex_ty = {
        let ex = d.kernel().const_(p.logic.exists_, vec![one]);
        d.apply(ex, &[nat, pred])
    };
    let motive = d.lam_fv(hh_fv, ex_ty, goal);
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, pred, motive, minor, proof_ex])
}

/// [`elim_exists_nat`], but returning the ARROW `(∃ x, pred x) → goal`
/// itself, rather than requiring the existential proof up front — the shape
/// `or_cases`'s minors need.
fn exists_elim_arrow_nat(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred: ExprId,
    goal: ExprId,
    build_minor: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let ex_ty = {
        let ex = d.kernel().const_(p.logic.exists_, vec![one]);
        d.apply(ex, &[nat, pred])
    };
    let hex_fv = d.fresh_fvar();
    let hex = d.kernel().fvar(hex_fv);
    let body = elim_exists_nat(d, &p, pred, goal, hex, build_minor);
    d.lam_fv(hex_fv, ex_ty, body)
}

/// `∀ n, Le n fuel → Ne n zero → disj_stmt n` — the fuel-quantified motive.
fn fuel_motive_body(d: &mut NatDev<'_>, p: &NatPrelude, fuel: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let le_ty = d.le(n, fuel);
    let ne_ty = ne_zero_ty(d, &p, n);
    let disj = disj_stmt(d, &p, n);
    let body = d.arrow(ne_ty, disj);
    let body2 = d.arrow(le_ty, body);
    d.pi_fv(n_fv, nat, body2)
}

/// Fuel base case (`fuel = 0`): `Le n 0` forces `Eq n 0`
/// (`le_antisymm`/`zero_le`), contradicting `Ne n 0`.
fn odd_factor_base(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let zero = d.zero();
    let le_ty = d.le(n, zero);
    let le_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(le_fv);
    let ne_ty = ne_zero_ty(d, &p, n);
    let ne_fv = d.fresh_fvar();
    let hne = d.kernel().fvar(ne_fv);

    let zero_le_n = d.lemma(p.zero_le, &[n]);
    let n_eq_zero = d.lemma(p.le_antisymm, &[n, zero, hle, zero_le_n]);
    let false_proof = d.apply(hne, &[n_eq_zero]);
    let goal = disj_stmt(d, &p, n);
    let absurd = ex_falso(d, &p, goal, false_proof);

    let with_ne = d.lam_fv(ne_fv, ne_ty, absurd);
    let with_le = d.lam_fv(le_fv, le_ty, with_ne);
    d.lam_fv(n_fv, nat, with_le)
}

/// EVEN case, `half = 0`: `n = half+half = 0`, contradicting `Ne n 0`.
fn even_base(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, hne: ExprId, goal: ExprId) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let zz = d.add(zero, zero);
    let heq_ty = d.eq(n, zz);
    let heq_fv = d.fresh_fvar();
    let heqv = d.kernel().fvar(heq_fv);

    let add_zero_zero = d.lemma(p.add_zero, &[zero]);
    let n_eq_zero = d.trans(n, zz, zero, heqv, add_zero_zero);
    let false_proof = d.apply(hne, &[n_eq_zero]);
    let body = ex_falso(d, &p, goal, false_proof);
    d.lam_fv(heq_fv, heq_ty, body)
}

/// EVEN case, `half = succ hp`: bound `half ≤ f` and recurse via `ih`, then
/// re-assemble the answer at `n` from the answer at `half` (`n = 2*half`).
#[allow(clippy::too_many_arguments)]
fn even_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    f: ExprId,
    hle: ExprId,
    ih: ExprId,
    goal: ExprId,
    hp: ExprId,
) -> ExprId {
    let p = *p;
    let half_s = d.succ(hp);
    let hh = d.add(half_s, half_s);
    let heq_ty = d.eq(n, hh);
    let heq_fv = d.fresh_fvar();
    let heqv = d.kernel().fvar(heq_fv);

    let two = d.num(2);
    let pos_half = d.lemma(p.zero_lt_succ, &[hp]); // Lt 0 half_s
    let e_lt_2e = d.lemma(p.lt_two_mul_of_pos, &[half_s, pos_half]); // Lt half_s (mul 2 half_s)
    let two_mul_eq = two_mul_eq_add_self(d, &p, half_s); // Eq(mul 2 half_s, hh)
    let mul_2_half_s = d.mul(two, half_s);
    let motive_a = d.eq_motive(mul_2_half_s, &|d, x| d.lt(half_s, x));
    let half_s_lt_hh = d.transport(mul_2_half_s, motive_a, e_lt_2e, hh, two_mul_eq);

    let eq_hh_n = d.symm(n, hh, heqv); // Eq(hh, n)
    let motive_b = d.eq_motive(hh, &|d, x| d.lt(half_s, x));
    let half_s_lt_n = d.transport(hh, motive_b, half_s_lt_hh, n, eq_hh_n);

    let sf = d.succ(f);
    let half_s_lt_sf = d.lemma(p.lt_of_lt_of_le, &[half_s, n, sf, half_s_lt_n, hle]);
    let le_half_s_f = d.lemma(p.le_of_succ_le_succ, &[half_s, f, half_s_lt_sf]);

    let ne_half_s = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.lemma(p.succ_ne_zero, &[hp, h]);
        let zero = d.zero();
        let eq_ty = d.eq(half_s, zero);
        d.lam_fv(h_fv, eq_ty, body)
    };

    let ih_result = d.apply(ih, &[half_s, le_half_s_f, ne_half_s]); // disj_stmt(half_s)

    let pow2_ty_half = pow2_disjunct(d, &p, half_s);
    let odd_ty_half = odd_disjunct(d, &p, half_s);

    let pow2_pred_half = pow2_pred(d, half_s);
    let pow2_minor = exists_elim_arrow_nat(d, &p, pow2_pred_half, goal, &|d, m, hm| {
        // hm : Eq half_s (pow 2 m)
        let two = d.num(2);
        let pow2m = d.pow(two, m);
        let mul_2_half_s = d.mul(two, half_s);
        let mul_2_pow2m = d.mul(two, pow2m);
        let mul_pow2m_2 = d.mul(pow2m, two);
        let succ_m = d.succ(m);
        let pow2_succm = d.pow(two, succ_m);

        let two_mul_eq2 = two_mul_eq_add_self(d, &p, half_s); // Eq(mul_2_half_s, hh)
        let eq_hh_mul2halfs = d.symm(mul_2_half_s, hh, two_mul_eq2); // Eq(hh, mul_2_half_s)
        let congr_step = d.congr(half_s, pow2m, hm, &|d, x| d.mul(two, x)); // Eq(mul_2_half_s, mul_2_pow2m)
        let mul_comm_step = d.lemma(p.mul_comm, &[two, pow2m]); // Eq(mul_2_pow2m, mul_pow2m_2)
        let pow_succ_step = d.lemma(p.pow_succ, &[two, m]); // Eq(pow2_succm, mul_pow2m_2)
        let symm_pow_succ = d.symm(pow2_succm, mul_pow2m_2, pow_succ_step); // Eq(mul_pow2m_2, pow2_succm)

        let (_, witness_eq) = d.chain(
            n,
            &[
                (hh, heqv),
                (mul_2_half_s, eq_hh_mul2halfs),
                (mul_2_pow2m, congr_step),
                (mul_pow2m_2, mul_comm_step),
                (pow2_succm, symm_pow_succ),
            ],
        );

        let pred_pow2_n = pow2_pred(d, n);
        let ex_proof = intro_exists_nat(d, &p, pred_pow2_n, succ_m, witness_eq);
        let pow2_ty_n = pow2_disjunct(d, &p, n);
        let odd_ty_n = odd_disjunct(d, &p, n);
        d.const_app(p.logic.or_inl, &[pow2_ty_n, odd_ty_n, ex_proof])
    });

    let odd_pred_half = odd_pred(d, &p, half_s);
    let odd_minor = exists_elim_arrow_nat(d, &p, odd_pred_half, goal, &|d, e2, he_outer| {
        let inner_pred = odd_inner_pred(d, &p, half_s, e2);
        elim_exists_nat(d, &p, inner_pred, goal, he_outer, &|d, t2, hand| {
            let dexp2 = exponent_of(d, t2);
            let prod2 = d.mul(e2, dexp2);
            let eqn_ty = d.eq(half_s, prod2);
            let net_ty = ne_zero_ty(d, &p, t2);
            let heq3 = and_left(d, eqn_ty, net_ty, hand); // Eq half_s prod2
            let hne_t2 = and_right(d, eqn_ty, net_ty, hand); // Ne t2 0

            let two = d.num(2);
            let mul_2_half_s = d.mul(two, half_s);
            let mul_2_prod2 = d.mul(two, prod2);
            let mul_2e2_dexp2 = {
                let m2e2 = d.mul(two, e2);
                d.mul(m2e2, dexp2)
            };

            let two_mul_eq3 = two_mul_eq_add_self(d, &p, half_s); // Eq(mul_2_half_s, hh)
            let eq_hh_mul2halfs = d.symm(mul_2_half_s, hh, two_mul_eq3); // Eq(hh, mul_2_half_s)
            let congr_step2 = d.congr(half_s, prod2, heq3, &|d, x| d.mul(two, x)); // Eq(mul_2_half_s, mul_2_prod2)
            let mul_2e2 = d.mul(two, e2);
            let mul_assoc_step = d.lemma(p.mul_assoc, &[two, e2, dexp2]); // Eq(mul_2e2_dexp2, mul_2_prod2)
            let symm_assoc = d.symm(mul_2e2_dexp2, mul_2_prod2, mul_assoc_step); // Eq(mul_2_prod2, mul_2e2_dexp2)

            let (_, witness_eq2) = d.chain(
                n,
                &[
                    (hh, heqv),
                    (mul_2_half_s, eq_hh_mul2halfs),
                    (mul_2_prod2, congr_step2),
                    (mul_2e2_dexp2, symm_assoc),
                ],
            );

            let net_ty2 = ne_zero_ty(d, &p, t2);
            let eqn_ty2 = d.eq(n, mul_2e2_dexp2);
            let and_proof =
                d.const_app(p.logic.and_intro, &[eqn_ty2, net_ty2, witness_eq2, hne_t2]);

            let pred_t_final = odd_inner_pred(d, &p, n, mul_2e2);
            let ex_t_final = intro_exists_nat(d, &p, pred_t_final, t2, and_proof);
            let pred_e_final = odd_pred(d, &p, n);
            let ex_e_final = intro_exists_nat(d, &p, pred_e_final, mul_2e2, ex_t_final);

            let pow2_ty_n = pow2_disjunct(d, &p, n);
            let odd_ty_n = odd_disjunct(d, &p, n);
            d.const_app(p.logic.or_inr, &[pow2_ty_n, odd_ty_n, ex_e_final])
        })
    });

    let result = or_cases(
        d,
        &p,
        pow2_ty_half,
        odd_ty_half,
        goal,
        pow2_minor,
        odd_minor,
        ih_result,
    );
    d.lam_fv(heq_fv, heq_ty, result)
}

/// ODD case, `half = 0`: `n = succ(half+half) = 1 = 2^0`.
fn odd_base(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, _goal: ExprId) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let zz = d.add(zero, zero);
    let szz = d.succ(zz);
    let heq_ty = d.eq(n, szz);
    let heq_fv = d.fresh_fvar();
    let heqv = d.kernel().fvar(heq_fv);

    let add_zero_zero = d.lemma(p.add_zero, &[zero]); // Eq(zz, zero)
    let sz = d.succ(zero); // = one, syntactically
    let congr_succ = d.congr(zz, zero, add_zero_zero, &|d, x| d.succ(x)); // Eq(szz, sz)

    let (_, n_eq_one) = d.chain(n, &[(szz, heqv), (sz, congr_succ)]);

    let two = d.num(2);
    let pow_two_zero = d.pow(two, zero);
    let pow_zero_eq = d.lemma(p.pow_zero, &[two]); // Eq(pow_two_zero, sz) [pow a 0 = 1 = sz]
    let symm_pow_zero = d.symm(pow_two_zero, sz, pow_zero_eq); // Eq(sz, pow_two_zero)

    let (_, witness_eq) = d.chain(n, &[(sz, n_eq_one), (pow_two_zero, symm_pow_zero)]);

    let pred_pow2_n = pow2_pred(d, n);
    let ex_proof = intro_exists_nat(d, &p, pred_pow2_n, zero, witness_eq);
    let pow2_ty_n = pow2_disjunct(d, &p, n);
    let odd_ty_n = odd_disjunct(d, &p, n);
    let result = d.const_app(p.logic.or_inl, &[pow2_ty_n, odd_ty_n, ex_proof]);
    d.lam_fv(heq_fv, heq_ty, result)
}

/// ODD case, `half = succ hp`: answer directly with `e := 1`, `t := half`
/// (`half ≠ 0` for free).
fn odd_succ(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, _goal: ExprId, hp: ExprId) -> ExprId {
    let p = *p;
    let half_s = d.succ(hp);
    let hh = d.add(half_s, half_s);
    let shh = d.succ(hh);
    let heq_ty = d.eq(n, shh);
    let heq_fv = d.fresh_fvar();
    let heqv = d.kernel().fvar(heq_fv);

    let two = d.num(2);
    let mul_2_half_s = d.mul(two, half_s);
    let dexp3 = exponent_of(d, half_s); // succ(mul 2 half_s)

    let two_mul_eq = two_mul_eq_add_self(d, &p, half_s); // Eq(mul_2_half_s, hh)
    let eq_hh_mul2halfs = d.symm(mul_2_half_s, hh, two_mul_eq); // Eq(hh, mul_2_half_s)
    let congr_succ = d.congr(hh, mul_2_half_s, eq_hh_mul2halfs, &|d, x| d.succ(x)); // Eq(shh, dexp3)

    let one = d.num(1);
    let mul_one_dexp3 = d.mul(one, dexp3);
    let one_mul_eq = d.lemma(p.one_mul, &[dexp3]); // Eq(mul_one_dexp3, dexp3)
    let symm_one_mul = d.symm(mul_one_dexp3, dexp3, one_mul_eq); // Eq(dexp3, mul_one_dexp3)

    let (_, final_eq) = d.chain(
        n,
        &[
            (shh, heqv),
            (dexp3, congr_succ),
            (mul_one_dexp3, symm_one_mul),
        ],
    );

    let ne_half_s = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.lemma(p.succ_ne_zero, &[hp, h]);
        let zero = d.zero();
        let eq_ty = d.eq(half_s, zero);
        d.lam_fv(h_fv, eq_ty, body)
    };

    let net_ty = ne_zero_ty(d, &p, half_s);
    let eqn_ty = d.eq(n, mul_one_dexp3);
    let and_proof = d.const_app(p.logic.and_intro, &[eqn_ty, net_ty, final_eq, ne_half_s]);

    let pred_t = odd_inner_pred(d, &p, n, one);
    let ex_t = intro_exists_nat(d, &p, pred_t, half_s, and_proof);
    let pred_e = odd_pred(d, &p, n);
    let ex_e = intro_exists_nat(d, &p, pred_e, one, ex_t);

    let pow2_ty_n = pow2_disjunct(d, &p, n);
    let odd_ty_n = odd_disjunct(d, &p, n);
    let result = d.const_app(p.logic.or_inr, &[pow2_ty_n, odd_ty_n, ex_e]);
    d.lam_fv(heq_fv, heq_ty, result)
}

/// EVEN branch wrapper: case-splits `half := div n 2` via `cases_zero_succ`.
fn even_branch(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    f: ExprId,
    hle: ExprId,
    hne: ExprId,
    ih: ExprId,
) -> ExprId {
    let p = *p;
    let goal = disj_stmt(d, &p, n);
    let two = d.num(2);
    let half = d.div(n, two);
    let motive_h = |d: &mut NatDev<'_>, hv: ExprId| -> ExprId {
        let hvhv = d.add(hv, hv);
        let heq_ty = d.eq(n, hvhv);
        d.arrow(heq_ty, goal)
    };
    let base_h = |d: &mut NatDev<'_>| -> ExprId { even_base(d, &p, n, hne, goal) };
    let succ_h =
        |d: &mut NatDev<'_>, hp: ExprId| -> ExprId { even_succ(d, &p, n, f, hle, ih, goal, hp) };
    cases_zero_succ(d, half, &motive_h, &base_h, &succ_h)
}

/// ODD branch wrapper: case-splits `half := div n 2` via `cases_zero_succ`.
fn odd_branch(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let goal = disj_stmt(d, &p, n);
    let two = d.num(2);
    let half = d.div(n, two);
    let motive_h2 = |d: &mut NatDev<'_>, hv: ExprId| -> ExprId {
        let hvhv = d.add(hv, hv);
        let shv = d.succ(hvhv);
        let heq_ty = d.eq(n, shv);
        d.arrow(heq_ty, goal)
    };
    let base_h2 = |d: &mut NatDev<'_>| -> ExprId { odd_base(d, &p, n, goal) };
    let succ_h2 = |d: &mut NatDev<'_>, hp: ExprId| -> ExprId { odd_succ(d, &p, n, goal, hp) };
    cases_zero_succ(d, half, &motive_h2, &base_h2, &succ_h2)
}

/// The fuel-induction step (`fuel = succ f`): split `n` by parity
/// ([`super::powsq`]'s `Nat.even_or_odd`) into [`even_branch`]/[`odd_branch`].
fn odd_factor_step(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, ih: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let sf = d.succ(f);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let le_ty = d.le(n, sf);
    let le_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(le_fv);
    let ne_ty = ne_zero_ty(d, &p, n);
    let ne_fv = d.fresh_fvar();
    let hne = d.kernel().fvar(ne_fv);

    let goal = disj_stmt(d, &p, n);
    let two = d.num(2);
    let half = d.div(n, two);
    let half_half = d.add(half, half);
    let even_ty = d.eq(n, half_half);
    let succ_half_half = d.succ(half_half);
    let odd_ty_eq = d.eq(n, succ_half_half);
    let eo = d.lemma(p.even_or_odd, &[n]);

    let even_minor = even_branch(d, &p, n, f, hle, hne, ih);
    let odd_minor = odd_branch(d, &p, n);

    let result = or_cases(d, &p, even_ty, odd_ty_eq, goal, even_minor, odd_minor, eo);

    let with_ne = d.lam_fv(ne_fv, ne_ty, result);
    let with_le = d.lam_fv(le_fv, le_ty, with_ne);
    d.lam_fv(n_fv, nat, with_le)
}

/// `Nat.pow_two_or_has_odd_factor : ∀ n, Ne n zero → Or (∃ m, Eq n (pow 2 m))
/// (∃ e t, Eq n (mul e (exponent_of t)) ∧ Ne t zero)` — by ordinary
/// structural induction on a fuel bound, instantiated at `fuel := n`. See
/// the module-level note above for why this is NOT a `WellFounded.fix`
/// construction.
pub(super) fn declare_pow_two_or_has_odd_factor(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.pow_two_or_has_odd_factor, 1, &|d, v| {
        let n = v[0];
        let ne_ty = ne_zero_ty(d, &p, n);
        let disj = disj_stmt(d, &p, n);
        let stmt = d.arrow(ne_ty, disj);

        let fuel_proof = d.induct(
            &|d, fuel| fuel_motive_body(d, &p, fuel),
            &|d| odd_factor_base(d, &p),
            &|d, f, ih| odd_factor_step(d, &p, f, ih),
            n,
        );
        let le_refl_n = d.lemma(p.le_refl, &[n]);

        let ne_fv = d.fresh_fvar();
        let hne = d.kernel().fvar(ne_fv);
        let final_proof = d.apply(fuel_proof, &[n, le_refl_n, hne]);
        let proof = d.lam_fv(ne_fv, ne_ty, final_proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// The two dead-end contradictions in [`pow_of_pow_add_prime_contradiction`]:
/// the exhibited divisor `a^e+1` is `1` (impossible, `a^e+1 ≥ 2` since
/// `a > 1`) or is `a^n+1` (impossible, `e < n` forces `a^e ≠ a^n`).
#[allow(clippy::too_many_arguments)]
fn derive_e_lt_n(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    e: ExprId,
    t: ExprId,
    n: ExprId,
    heq: ExprId,
    hn: ExprId,
    hne_t: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let two = d.num(2);
    let dexp = exponent_of(d, t);

    // ne_e0 : Ne e zero, from heq (n = e*dexp) and hn (Ne n zero).
    let ne_e0 = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let mul_e_dexp = d.mul(e, dexp);
        let mul_zero_dexp = d.mul(zero, dexp);
        let congr_e = d.congr(e, zero, h, &|d, x| d.mul(x, dexp));
        let zm = d.lemma(p.zero_mul, &[dexp]);
        let e_prod_eq_zero = d.trans(mul_e_dexp, mul_zero_dexp, zero, congr_e, zm);
        let n_eq_zero = d.trans(n, mul_e_dexp, zero, heq, e_prod_eq_zero);
        let false_proof = d.apply(hn, &[n_eq_zero]);
        let eq_ty = d.eq(e, zero);
        d.lam_fv(h_fv, eq_ty, false_proof)
    };
    let pos_e = d.lemma(p.zero_lt_of_ne_zero, &[e, ne_e0]); // Lt zero e

    // lt1_dexp : Lt one dexp, from hne_t (t ≠ 0, so dexp = succ(2t) ≥ 3).
    let pos_t = d.lemma(p.zero_lt_of_ne_zero, &[t, hne_t]); // Lt zero t
    let add_tt_pos = d.lemma(p.add_pos_right, &[t, t, pos_t]); // Lt zero (add t t)
    let mul_2t = d.mul(two, t);
    let add_tt = d.add(t, t);
    let two_mul_eq_t = two_mul_eq_add_self(d, &p, t); // Eq(mul_2t, add_tt)
    let eq_att_m2t = d.symm(mul_2t, add_tt, two_mul_eq_t); // Eq(add_tt, mul_2t)
    let motive1 = d.eq_motive(add_tt, &|d, x| {
        let z = d.zero();
        d.lt(z, x)
    });
    let lt0_mul2t = d.transport(add_tt, motive1, add_tt_pos, mul_2t, eq_att_m2t); // Lt zero mul_2t
    let lt1_dexp = d.lemma(p.succ_le_succ, &[one, mul_2t, lt0_mul2t]); // Le(succ one, succ mul_2t) = Lt one dexp

    // lt_e_n : Lt e n.
    let mul_e_one = d.mul(e, one);
    let mul_e_dexp = d.mul(e, dexp);
    let lt_mul_ty = d.lt(mul_e_one, mul_e_dexp);
    let lt_one_dexp_ty = d.lt(one, dexp);
    let iff_e = d.lemma(p.mul_lt_mul_left, &[e, one, dexp, pos_e]); // Iff(lt_mul_ty, lt_one_dexp_ty)
    let rev = iff_reverse(d, lt_mul_ty, lt_one_dexp_ty, iff_e);
    let lt_mul_e1_edexp = d.apply(rev, &[lt1_dexp]); // Lt(mul_e_one, mul_e_dexp)

    let mul_one_eq = d.lemma(p.mul_one, &[e]); // Eq(mul_e_one, e)
    let motive2 = d.eq_motive(mul_e_one, &|d, x| {
        let med = d.mul(e, dexp);
        d.lt(x, med)
    });
    let step1 = d.transport(mul_e_one, motive2, lt_mul_e1_edexp, e, mul_one_eq); // Lt(e, mul_e_dexp)

    let eq_medexp_n = d.symm(n, mul_e_dexp, heq); // Eq(mul_e_dexp, n)
    let motive3 = d.eq_motive(mul_e_dexp, &|d, x| d.lt(e, x));
    d.transport(mul_e_dexp, motive3, step1, n, eq_medexp_n) // Lt e n
}

/// `2 ≤ x ∧ ∀ c, dvd c x → Eq c 1 ∨ Eq c x` — primality, spelled inline,
/// matching `primes.rs`/`factorization.rs`'s own convention (this prelude
/// has no `Prime`). Returns the two conjuncts separately, so
/// `and_left`/`and_right` can project either side of a checked proof.
fn prime_parts_local(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> (ExprId, ExprId) {
    let p = *p;
    let nat = d.nat_ty();
    let two = d.num(2);
    let one = d.num(1);
    let lower = d.le(two, x);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hyp = d.dvd(c, x);
    let triv = d.eq(c, one);
    let whole = d.eq(c, x);
    let disj = d.const_app(p.logic.or, &[triv, whole]);
    let body = d.arrow(hyp, disj);
    let divisors = d.pi_fv(c_fv, nat, body);
    (lower, divisors)
}

/// Given the odd-factor witnesses `(e, t)` (`n = e * exponent_of(t)`,
/// `t ≠ 0`), derive `False` from primality of `a^n+1`, then `ex_falso` into
/// `goal`.
#[allow(clippy::too_many_arguments)]
fn pow_of_pow_add_prime_contradiction(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    n: ExprId,
    e: ExprId,
    t: ExprId,
    ha: ExprId,
    hn: ExprId,
    hp: ExprId,
    hand: ExprId,
    goal: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let zero = d.zero();
    let two = d.num(2);
    let dexp = exponent_of(d, t);
    let prod = d.mul(e, dexp);
    let eqn_ty = d.eq(n, prod);
    let net_ty = ne_zero_ty(d, &p, t);
    let heq = and_left(d, eqn_ty, net_ty, hand); // Eq n prod
    let hne_t = and_right(d, eqn_ty, net_ty, hand); // Ne t 0

    let core = d.lemma(p.dvd_pow_add_one_of_odd_mul_exp, &[a, e, t]);
    // core : Dvd(add(pow a e,1), add(pow a prod,1))

    let pow_a_e = d.pow(a, e);
    let base = d.add(pow_a_e, one);
    let pow_a_prod = d.pow(a, prod);
    let n_side = d.add(pow_a_prod, one);
    let pow_a_n = d.pow(a, n);
    let prime_arg = d.add(pow_a_n, one);

    let heq_rev = d.symm(n, prod, heq); // Eq(prod, n)
    let eq_pow = d.congr(prod, n, heq_rev, &|d, x| d.pow(a, x)); // Eq(pow_a_prod, pow_a_n)
    let eq_full = d.congr(pow_a_prod, pow_a_n, eq_pow, &|d, x| d.add(x, one)); // Eq(n_side, prime_arg)
    let motive_dvd = d.eq_motive(n_side, &|d, x| d.dvd(base, x));
    let dvd_prime_arg = d.transport(n_side, motive_dvd, core, prime_arg, eq_full);
    // dvd_prime_arg : Dvd(base, prime_arg)

    let (prime_lower, prime_divisors) = prime_parts_local(d, &p, prime_arg);
    let hdiv_all = and_right(d, prime_lower, prime_divisors, hp);
    let case_result = d.apply(hdiv_all, &[base, dvd_prime_arg]);
    // case_result : Or(Eq(base,one), Eq(base,prime_arg))

    let eq_base_one_ty = d.eq(base, one);
    let eq_base_prime_ty = d.eq(base, prime_arg);

    let minor_a = {
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let eq_pae_zero = d.lemma(p.succ_injective, &[pow_a_e, zero, h1]); // Eq(pow_a_e, zero)

        let le_succ_1 = d.lemma(p.le_succ, &[one]); // Le(one, succ one) = Le(1,2)
        let pos_a = d.lemma(p.le_trans, &[one, two, a, le_succ_1, ha]); // Le(one,a) = Lt(zero,a)
        let pow_a_e_pos = d.lemma(p.pow_pos, &[a, e, pos_a]); // Lt(zero, pow_a_e)
        let motive_g = d.eq_motive(pow_a_e, &|d, x| {
            let z = d.zero();
            d.lt(z, x)
        });
        let lt_0_0 = d.transport(pow_a_e, motive_g, pow_a_e_pos, zero, eq_pae_zero);
        let false_a = d.lemma(p.lt_irrefl, &[zero, lt_0_0]);
        let body = ex_falso(d, &p, goal, false_a);
        d.lam_fv(h1_fv, eq_base_one_ty, body)
    };

    let minor_b = {
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let pow_eq = d.lemma(p.succ_injective, &[pow_a_e, pow_a_n, h2]); // Eq(pow_a_e, pow_a_n)
        let e_eq_n = d.lemma(p.pow_injective, &[a, e, n, ha, pow_eq]); // Eq(e,n)

        let lt_e_n = derive_e_lt_n(d, &p, e, t, n, heq, hn, hne_t);
        let motive_f = d.eq_motive(e, &|d, x| d.lt(x, n));
        let lt_n_n = d.transport(e, motive_f, lt_e_n, n, e_eq_n);
        let false_b = d.lemma(p.lt_irrefl, &[n, lt_n_n]);
        let body = ex_falso(d, &p, goal, false_b);
        d.lam_fv(h2_fv, eq_base_prime_ty, body)
    };

    or_cases(
        d,
        &p,
        eq_base_one_ty,
        eq_base_prime_ty,
        goal,
        minor_a,
        minor_b,
        case_result,
    )
}

/// The proof body of `Nat.pow_of_pow_add_prime`, given `a`, `n` and the
/// three hypotheses: `pow_two_or_has_odd_factor` either answers directly
/// (`n` a power of two) or hands an odd-factor witness to
/// [`pow_of_pow_add_prime_contradiction`].
fn pow_of_pow_add_prime_body(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    n: ExprId,
    ha: ExprId,
    hn: ExprId,
    hp: ExprId,
) -> ExprId {
    let p = *p;
    let goal = pow2_disjunct(d, &p, n);
    let disj_applied = d.lemma(p.pow_two_or_has_odd_factor, &[n, hn]);

    let pow2_ty = pow2_disjunct(d, &p, n);
    let odd_ty = odd_disjunct(d, &p, n);

    let left_minor = {
        let hex_fv = d.fresh_fvar();
        let hex = d.kernel().fvar(hex_fv);
        d.lam_fv(hex_fv, pow2_ty, hex)
    };
    let odd_pred_n = odd_pred(d, &p, n);
    let right_minor = exists_elim_arrow_nat(d, &p, odd_pred_n, goal, &|d, e, he| {
        let inner_pred = odd_inner_pred(d, &p, n, e);
        elim_exists_nat(d, &p, inner_pred, goal, he, &|d, t, hand| {
            pow_of_pow_add_prime_contradiction(d, &p, a, n, e, t, ha, hn, hp, hand, goal)
        })
    });

    or_cases(
        d,
        &p,
        pow2_ty,
        odd_ty,
        goal,
        left_minor,
        right_minor,
        disj_applied,
    )
}

/// `Nat.pow_of_pow_add_prime : ∀ a n, Lt one a → Ne n zero → PrimeCond
/// (add (pow a n) one) → ∃ m, Eq n (pow 2 m)` — the fact itself
/// (`F:ml430-nat-pow-of-pow-add-prime-ab61d0d3`).
pub(super) fn declare_pow_of_pow_add_prime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.pow_of_pow_add_prime, 2, &|d, v| {
        let (a, n) = (v[0], v[1]);
        let one = d.num(1);
        let ha_ty = d.lt(one, a);
        let ne_ty = ne_zero_ty(d, &p, n);
        let pow_a_n = d.pow(a, n);
        let prime_arg = d.add(pow_a_n, one);
        let (prime_lower, prime_divisors) = prime_parts_local(d, &p, prime_arg);
        let prime_ty = d.const_app(p.logic.and, &[prime_lower, prime_divisors]);
        let goal = pow2_disjunct(d, &p, n);
        let stmt_inner = d.arrow(prime_ty, goal);
        let stmt_mid = d.arrow(ne_ty, stmt_inner);
        let stmt = d.arrow(ha_ty, stmt_mid);

        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let body = pow_of_pow_add_prime_body(d, &p, a, n, ha, hn, hp);

        let inner1 = d.lam_fv(hp_fv, prime_ty, body);
        let inner2 = d.lam_fv(hn_fv, ne_ty, inner1);
        let proof = d.lam_fv(ha_fv, ha_ty, inner2);
        (stmt, proof)
    })?;
    Ok(())
}

/// Wires the five declarations above into the prelude. Nothing downstream
/// needs any of this yet, so it goes last.
pub(super) fn declare_pow_add_prime_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_pow_mul(d, p)?;
    declare_dvd_pow_add_one_of_odd_exp(d, p)?;
    declare_dvd_pow_add_one_of_odd_mul_exp(d, p)?;
    declare_pow_two_or_has_odd_factor(d, p)?;
    declare_pow_of_pow_add_prime(d, p)?;
    Ok(())
}
