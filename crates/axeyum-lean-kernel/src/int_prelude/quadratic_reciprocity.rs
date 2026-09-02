//! **The law of quadratic reciprocity.**
//!
//! Three declarations:
//!
//! ```text
//! Int.legendreSym : Nat -> Nat -> Int
//!   := fun m a => pow (neg one) (Nat.gaussNegCount (succ (mul 2 m)) a m)
//!
//! Int.legendreSym_modEq_pow : ∀ m a, Nat.PrimeCond (succ (mul 2 m)) →
//!   Eq (Nat.gcd a (succ (mul 2 m))) 1 →
//!   ModEq (ofNat (succ (mul 2 m))) (pow (ofNat a) m) (legendreSym m a)
//!
//! Int.quadraticReciprocity : ∀ m n,
//!   Eq (Nat.gcd (succ (mul 2 n)) (succ (mul 2 m))) 1 →
//!   Eq Int (mul (legendreSym m (succ (mul 2 n)))
//!               (legendreSym n (succ (mul 2 m))))
//!          (pow (neg one) (mul n m))
//! ```
//!
//! With `p := 2m+1` and `q := 2n+1` the third reads
//! `(q|p)·(p|q) = (-1)^((p-1)/2 · (q-1)/2)` — the classical law.
//!
//! # Why `legendreSym` is defined by Gauss's count, and what that costs
//!
//! There was no Legendre symbol in this kernel (measured ABSENT against a
//! `declarations=2133` positive control). The classical definition is the
//! residue indicator — `1` if `a` is a quadratic residue mod `p`, `-1` if
//! not — and **this kernel cannot yet prove that definition equals anything
//! computable**: `qr_criterion.rs`'s module doc records that the CONVERSE of
//! Euler's criterion (`a^((p-1)/2) ≡ 1 ⟹ a is a residue`) needs a primitive
//! root or a root-counting argument that has no statable form here. So a
//! residue-indicator `legendreSym` would be a definition nothing could
//! evaluate and no theorem could reach.
//!
//! The route taken instead is the standard equivalent one: define the symbol
//! by **Gauss's counting exponent**, and prove the Euler-criterion
//! characterization that justifies the name — [`declare_legendre_sym_modeq_pow`]
//! is exactly `Int.gaussLemmaSignCount` read through the definition, so
//! `a^((p-1)/2) ≡ legendreSym m a (mod p)` at every odd prime `p = 2m+1`
//! coprime to `a`. Since a nonzero residue class mod an odd prime contains at
//! most one of `1` and `-1`, that congruence pins the symbol uniquely, which
//! is what makes this the Legendre symbol rather than merely a sign.
//!
//! **What is NOT proved, and is stated here so nobody reads more into the
//! name:** `legendreSym m a = 1 ↔ Int.is_quadratic_residue (ofNat p) (ofNat a)`
//! is not a theorem in this kernel, in either direction. The `⟸` direction is
//! reachable (`Int.euler_criterion_residue_imp_one` plus `1 ≢ -1` at `p > 2`)
//! and is not built here; the `⟹` direction is the missing converse and is
//! not reachable. The two supplementary laws, which DO speak about
//! `is_quadratic_residue`, are unaffected and unchanged
//! (`first_supplementary*.rs`, `second_supplementary.rs`).
//!
//! # The proof of the law, which is pure ring algebra
//!
//! Write `A := (-1)^N_p`, `B := (-1)^N_q`, `C := (-1)^(n·m)`, `S := N_p + N_q`
//! and `T := n·m`, where `N_p := gaussNegCount p q m` and
//! `N_q := gaussNegCount q p n`. The whole mathematical content is on the
//! `Nat` side, in `Nat.gaussCount_sum_even : Even (S + T)`.
//!
//! ```text
//!   (A·B)·C = (-1)^S · (-1)^T = (-1)^(S+T) = 1        [pow_add, pow_neg_one_of_even]
//!   C·C     = (-1)^(T+T)      = 1                     [same, witness `k := T`]
//!   A·B     = (A·B)·1 = (A·B)·(C·C) = ((A·B)·C)·C = 1·C = C
//! ```
//!
//! **This deliberately avoids a parity case split.** The obvious route —
//! case on `Even S` / `Odd S`, then transfer the parity to `T` — needs two
//! parity-transfer lemmas that do not exist here (`Even (a+b) → Even a →
//! Even b`, and its odd twin) and would have to be built. Multiplying by the
//! self-inverse `C` instead needs only `Int.pow_add`, `Int.mul_assoc`,
//! `Int.mul_one`, `Int.one_mul` and `Int.pow_neg_one_of_even`, all landed.
//!
//! # What the law assumes
//!
//! **Only coprimality of the two odd numbers — not primality.** Both `Nat`
//! inputs ask only for `gcd q p = 1`, so this statement does too. It is
//! therefore strictly stronger than the textbook law, in the same way ADR-1544
//! recorded for `Nat.eisenstein_floor_sum`. Primality appears exactly once in
//! this file, in [`declare_legendre_sym_modeq_pow`], because Gauss's lemma
//! needs it to cancel `m!`.

use super::modeq::imodeq;
use super::ops::IntDev;
use super::wilson::prime_condition;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::defs::DERIVED_HEIGHT;

/// `fun k : Nat => Eq Nat n (add k k)` — `Nat.Even`'s own witness predicate.
///
/// A local mirror of `nat_prelude::parity`'s `even_predicate`, which is
/// private to that module, kept byte-identical (the same convention
/// `second_supplementary.rs` records) so `Nat.Even n` and this `Exists` are
/// the same term rather than merely definitionally equal.
fn even_predicate(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let kk = d.add(k, k);
    let body = d.eq(n, kk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `Nat.Even (add x x)`, witnessed by `x` itself.
fn even_double(d: &mut IntDev<'_>, x: ExprId) -> ExprId {
    let p = d.int();
    let nat = d.nat_ty();
    let level_one = d.level_one();
    let xx = d.add(x, x);
    let pred = even_predicate(d, xx);
    let rfl = d.refl(xx);
    let intro = d.kernel().const_(p.logic.exists_intro, vec![level_one]);
    d.apply(intro, &[nat, pred, x, rfl])
}

/// `Int.legendreSym` — see this module's doc for why it is defined by Gauss's
/// counting exponent rather than by the residue indicator.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_legendre_sym(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let two = d.num(2);
    let mul2m = d.mul(two, m);
    let pp = d.succ(mul2m);
    let count = d.const_app(p.nat.gauss_neg_count, &[pp, a, m]);
    let one_i = d.ione();
    let neg_one = d.ineg(one_i);
    let body = d.ipow(neg_one, count);

    let value = {
        let inner = d.lam_fv(a_fv, nat, body);
        d.lam_fv(m_fv, nat, inner)
    };
    let ty = {
        let inner = d.kernel().pi(anon, nat, int_ty, BinderInfo::Default);
        d.kernel().pi(anon, nat, inner, BinderInfo::Default)
    };

    d.kernel().add_declaration(Declaration::Definition {
        name: p.legendre_sym,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
    })
}

/// `Int.legendreSym_modEq_pow` — Euler's criterion for this symbol, and the
/// reason the name is honest. It is `Int.gaussLemmaSignCount` read through
/// the definition, so the proof is the application itself; the conclusions
/// differ only by delta.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_legendre_sym_modeq_pow(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.theorem(p.legendre_sym_mod_eq_pow, 2, &|d, v| {
        let (m, a) = (v[0], v[1]);
        let two = d.num(2);
        let mul2m = d.mul(two, m);
        let pp = d.succ(mul2m);

        let prime_ty = prime_condition(d, pp);
        let one_nat = d.num(1);
        let gcd_a_pp = d.gcd(a, pp);
        let cop_ty = d.eq(gcd_a_pp, one_nat);

        let n_int = d.of_nat(pp);
        let a_int = d.of_nat(a);
        let pow_a_m = d.ipow(a_int, m);
        let leg = d.const_app(p.legendre_sym, &[m, a]);
        let concl = imodeq(d, n_int, pow_a_m, leg);

        let stmt = {
            let inner = d.arrow(cop_ty, concl);
            d.arrow(prime_ty, inner)
        };

        let prime_fv = d.fresh_fvar();
        let prime = d.kernel().fvar(prime_fv);
        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);
        let body = d.lemma(p.gauss_lemma_sign_count, &[m, a, prime, cop]);

        let proof = {
            let inner = d.lam_fv(cop_fv, cop_ty, body);
            d.lam_fv(prime_fv, prime_ty, inner)
        };
        (stmt, proof)
    })?;

    Ok(())
}

/// `Int.quadraticReciprocity` — the law. See this module's doc for the
/// algebra and for what it does and does not assume.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_quadratic_reciprocity(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.theorem(p.quadratic_reciprocity, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let two = d.num(2);
        let ap = d.mul(two, m);
        let pp = d.succ(ap);
        let aq = d.mul(two, n);
        let q = d.succ(aq);

        let one_nat = d.num(1);
        let g = d.gcd(q, pp);
        let cop_ty = d.eq(g, one_nat);
        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);

        let n_p = d.const_app(p.nat.gauss_neg_count, &[pp, q, m]);
        let n_q = d.const_app(p.nat.gauss_neg_count, &[q, pp, n]);
        let s = d.add(n_p, n_q);
        let t = d.mul(n, m);

        let one_i = d.ione();
        let neg_one = d.ineg(one_i);
        let leg_p = d.const_app(p.legendre_sym, &[m, q]);
        let leg_q = d.const_app(p.legendre_sym, &[n, pp]);
        let lhs = d.imul(leg_p, leg_q);
        let c_pow = d.ipow(neg_one, t);
        let concl = d.ieq(lhs, c_pow);
        let stmt = d.arrow(cop_ty, concl);

        // The same two terms with `legendreSym` unfolded. Delta alone relates
        // them, so the chain below is built on these and accepted against
        // `stmt`.
        let a_pow = d.ipow(neg_one, n_p);
        let b_pow = d.ipow(neg_one, n_q);
        let ab = d.imul(a_pow, b_pow);

        // `A·B = (-1)^S`.
        let pow_s = d.ipow(neg_one, s);
        let hab = {
            let fwd = d.lemma(p.pow_add, &[neg_one, n_p, n_q]);
            d.isymm(pow_s, ab, fwd)
        };

        // `(A·B)·C = (-1)^(S+T) = 1`, the one step carrying the mathematics.
        let x = d.add(s, t);
        let pow_x = d.ipow(neg_one, x);
        let habc = {
            let start = d.imul(ab, c_pow);
            let step1 = d.imul(pow_s, c_pow);
            let e_1 = d.icongr(ab, pow_s, hab, &|d, z| d.imul(z, c_pow));
            let e_2 = {
                let fwd = d.lemma(p.pow_add, &[neg_one, s, t]);
                d.isymm(pow_x, step1, fwd)
            };
            let e_3 = {
                let heven = d.lemma(p.nat.gauss_count_sum_even, &[m, n, cop]);
                d.lemma(p.pow_neg_one_of_even, &[x, heven])
            };
            let (_end, proof) = d.ichain(start, &[(step1, e_1), (pow_x, e_2), (one_i, e_3)]);
            proof
        };

        // `C·C = (-1)^(T+T) = 1` — `C` is its own inverse, which is what lets
        // the law be read off without a parity case split.
        let cc = d.imul(c_pow, c_pow);
        let hcc = {
            let tt = d.add(t, t);
            let pow_tt = d.ipow(neg_one, tt);
            let e_1 = {
                let fwd = d.lemma(p.pow_add, &[neg_one, t, t]);
                d.isymm(pow_tt, cc, fwd)
            };
            let e_2 = {
                let heven = even_double(d, t);
                d.lemma(p.pow_neg_one_of_even, &[tt, heven])
            };
            let (_end, proof) = d.ichain(cc, &[(pow_tt, e_1), (one_i, e_2)]);
            proof
        };

        // `A·B = (A·B)·1 = (A·B)·(C·C) = ((A·B)·C)·C = 1·C = C`.
        let body = {
            let step1 = d.imul(ab, one_i);
            let e_1 = {
                let fwd = d.lemma(p.mul_one, &[ab]);
                d.isymm(step1, ab, fwd)
            };
            let step2 = d.imul(ab, cc);
            let e_2 = {
                let back = d.isymm(cc, one_i, hcc);
                d.icongr(one_i, cc, back, &|d, z| d.imul(ab, z))
            };
            let abc = d.imul(ab, c_pow);
            let step3 = d.imul(abc, c_pow);
            let e_3 = {
                let fwd = d.lemma(p.mul_assoc, &[ab, c_pow, c_pow]);
                d.isymm(step3, step2, fwd)
            };
            let step4 = d.imul(one_i, c_pow);
            let e_4 = d.icongr(abc, one_i, habc, &|d, z| d.imul(z, c_pow));
            let e_5 = d.lemma(p.one_mul, &[c_pow]);
            let (_end, proof) = d.ichain(
                ab,
                &[
                    (step1, e_1),
                    (step2, e_2),
                    (step3, e_3),
                    (step4, e_4),
                    (c_pow, e_5),
                ],
            );
            proof
        };

        let proof = d.lam_fv(cop_fv, cop_ty, body);
        (stmt, proof)
    })?;

    Ok(())
}

/// Declare everything this module owns.
///
/// # Errors
///
/// Returns the trusted gate's rejection for the first declaration that does
/// not type-check.
pub(super) fn declare_quadratic_reciprocity_all(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    declare_legendre_sym(d)?;
    declare_legendre_sym_modeq_pow(d)?;
    declare_quadratic_reciprocity(d)?;
    Ok(())
}
