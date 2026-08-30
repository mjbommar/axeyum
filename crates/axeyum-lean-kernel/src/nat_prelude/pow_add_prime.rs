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
use super::ops::{NatDev, NatOps, cases_zero_succ};
use crate::KernelError;
use crate::expr::ExprId;

/// `succ (mul 2 t)` — the `t`-th odd number, `2t+1`.
fn exponent_of(d: &mut NatDev<'_>, t: ExprId) -> ExprId {
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
    let (_, proof) = d.chain(start, &[(t1, h1), (t2, h2b), (t3, h_assoc), (xx, kprime_rev)]);
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

    let dvd_sum = d.lemma(p.dvd_add, &[p_fixed, m_target, a_pow_plus_one, dvd_m, dvd_a_plus_one]);
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
        let proof = cases_zero_succ(
            d,
            x,
            &motive_x,
            &|d| at_zero_branch(d, &p, t),
            &|d, xp| {
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
            },
        );
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

/// Wires the three declarations above into the prelude. Nothing downstream
/// needs any of this yet, so it goes last.
pub(super) fn declare_pow_add_prime_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_pow_mul(d, p)?;
    declare_dvd_pow_add_one_of_odd_exp(d, p)?;
    declare_dvd_pow_add_one_of_odd_mul_exp(d, p)?;
    Ok(())
}
