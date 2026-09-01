//! Cassini's identity over `ℤ`: `Int.fib_cassini`.
//!
//! `fib(n+1)*fib(n-1) - fib(n)^2 = (-1)^n` alternates sign, so — as
//! `nat_prelude/fibonacci.rs`'s module doc already worked out — it is not a
//! `ℕ` statement as written, and `n-1` on `Nat.sub` is wrong at `n = 0`
//! besides. This file states it shifted so every index is a literal
//! successor, with `n` itself universally quantified from `0`:
//!
//! `Int.fib_cassini : ∀ n, fib(n+2)*fib(n) - fib(n+1)^2 = (-1)^(n+1)`
//!
//! Hand check (`fib = 0,1,1,2,3,5,8,…`):
//! `n=0`: `fib 2 * fib 0 - fib 1^2 = 1*0 - 1 = -1 = (-1)^1`.
//! `n=1`: `fib 3 * fib 1 - fib 2^2 = 2*1 - 1 = 1 = (-1)^2`.
//! `n=2`: `fib 4 * fib 2 - fib 3^2 = 3*1 - 4 = -1 = (-1)^3`.
//! `n=3`: `fib 5 * fib 3 - fib 4^2 = 5*2 - 9 = 1 = (-1)^4`.
//! All four match the brief's sketch (which itself matches
//! `nat_prelude/fibonacci.rs`'s own two-case hand check, shifted by one
//! index).
//!
//! # `(-1)^n`: `Int.pow` directly, not a parity case-split
//!
//! `Int.pow : Int → Nat → Int` is structural recursion on the *natural*
//! exponent with the base closed over (`defs.rs`), so it is total and
//! well-behaved at a negative base — no case-split on the sign of `n` is
//! needed the way the earlier two-case even/odd form (`Int.euler_criterion_pm_one`'s
//! device) would need. The step case below needs only one extra fact,
//! `pow (neg one) (succ k) = neg (pow (neg one) k)`, itself three lines from
//! `pow_succ` (`δ`/`ι`-computational, see `defs.rs::declare_pow_equations`)
//! plus `mul_neg`/`mul_one`.
//!
//! # The ℕ→ℤ bridge is free for `+`/`*`, not for `fib_add_two`
//!
//! `Int.add`/`Int.mul` on two `ofNat` arguments compute *definitionally* to
//! `ofNat` of the `Nat` sum/product (`defs.rs`'s reduction table; also spelled
//! out in `euclid.rs`'s module doc for the same reason). So no `Int.fib`
//! definition or homomorphism lemma is needed at all: `ofNat (Nat.fib n)` is
//! used directly everywhere below, and `Int.add`/`Int.mul` see straight
//! through it. What is *not* free is `Nat.fib_add_two` itself — exactly as
//! that theorem's own module doc says, it is not a bare reduction fact — so
//! every use of it here goes through [`IntDev::nat_eq_to_int`], the
//! `Eq Nat a b → Eq Int (f a) (f b)` bridge `int_prelude/ops.rs` built for
//! precisely this purpose.
//!
//! # The step case: one ring identity, reused machinery
//!
//! The inductive step needs `D(n+1) = -D(n)` where `D(n) := fib(n+2)*fib(n) -
//! fib(n+1)^2`. Writing `A,B,C,E` for `fib n, fib(n+1), fib(n+2), fib(n+3)`
//! and `s := A+B` (so `hC : C = s` from `fib_add_two n`, `hE : E = s+B` after
//! substituting `C`), the algebra is:
//!
//! `E*B = (s+B)*B = B*s + B*B` (`mul_comm` + `left_distrib`)
//! `C*C = s*s = s*A + s*B` (`left_distrib`, `s*s` and `s*(A+B)` are the same
//! term since `s` **is** `A+B`)
//!
//! so `D(n+1) = (B*s + B*B) - (s*A + s*B)`. Flipping `B*s` to `s*B` (`mul_comm`)
//! puts a shared addend `s*B` on the right of both sums, and
//! [`super::modeq::cancel_common_addend`] (already built for exactly this
//! `(x+r)-(y+r) = x-y` shape, and reused here rather than re-derived) reduces
//! this to `B*B - s*A`, i.e. `-(s*A - B*B) = -(C*A - B*B) = -D(n)` after
//! substituting `C` back and one `sub`-antisymmetry step.
//!
//! `neg_neg`, `neg_add` below are private local re-derivations of the same
//! two facts `int_prelude/gcd.rs` and `int_prelude/modeq.rs` already prove as
//! private helpers for their own inline use — not reused directly (both are
//! module-private there), but the exact same three/four-line technique
//! (`neg_one_mul` + `mul_assoc`/`left_distrib`, and `Eq.refl` at the concrete
//! literal `neg (neg one) = one` for the base of `neg_neg`).

use super::IntPrelude;
use super::ops::{IntDev, Shape, case_split, exists_elim};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

// ============================================================================
// Small ring facts this file needs and the exposed prelude does not carry.
// ============================================================================

/// `Eq Int (neg (neg x)) x`. Same technique as `gcd.rs`'s private `neg_neg`:
/// `neg (neg x) = (-1)*(-1)*x = 1*x = x`, with `neg (neg one) = one` closed by
/// `Eq.refl` at the concrete literal (two `Int.rec` computations, no variable
/// involved).
fn neg_neg(d: &mut IntDev<'_>, x: ExprId) -> ExprId {
    let p = d.int();
    let one_c = d.ione();
    let neg_one = d.ineg(one_c);
    let neg_x = d.ineg(x);
    let neg_neg_x = d.ineg(neg_x);

    let mul_negone_negx = d.imul(neg_one, neg_x);
    let step1 = {
        let fwd = d.lemma(p.neg_one_mul, &[neg_x]); // neg_one*neg_x = neg(neg_x)
        d.isymm(mul_negone_negx, neg_neg_x, fwd)
    };

    let inner = d.imul(neg_one, x);
    let mul_negone_inner = d.imul(neg_one, inner);
    let step2 = {
        let fwd = d.lemma(p.neg_one_mul, &[x]); // neg_one*x = neg x
        let negx_eq = d.isymm(inner, neg_x, fwd); // neg_x = inner
        d.icongr(neg_x, inner, negx_eq, &|d, y| d.imul(neg_one, y))
    };

    let negone_sq = d.imul(neg_one, neg_one);
    let negone_sq_x = d.imul(negone_sq, x);
    let step3 = {
        let fwd = d.lemma(p.mul_assoc, &[neg_one, neg_one, x]);
        d.isymm(negone_sq_x, mul_negone_inner, fwd)
    };

    let negone_sq_eq_one = {
        let fwd = d.lemma(p.neg_one_mul, &[neg_one]); // negone_sq = neg(neg_one)
        let neg_neg_one = d.ineg(neg_one);
        let refl_pf = d.irefl(one_c); // neg(neg_one) = one, by rfl
        d.itrans(negone_sq, neg_neg_one, one_c, fwd, refl_pf)
    };

    let one_x = d.imul(one_c, x);
    let step5 = d.icongr(negone_sq, one_c, negone_sq_eq_one, &|d, y| d.imul(y, x));
    let step6 = d.lemma(p.one_mul, &[x]);

    let (_, chained) = d.ichain(
        neg_neg_x,
        &[
            (mul_negone_negx, step1),
            (mul_negone_inner, step2),
            (negone_sq_x, step3),
            (one_x, step5),
            (x, step6),
        ],
    );
    chained
}

/// `Eq Int (neg (add a b)) (add (neg a) (neg b))`. Same technique as
/// `modeq.rs`'s private `neg_add`.
fn neg_add(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let p = d.int();
    let ab = d.iadd(a, b);
    let start = d.ineg(ab);

    let one = d.ione();
    let neg_one = d.ineg(one);
    let mul_negone_ab = d.imul(neg_one, ab);
    let step1 = {
        let fwd = d.lemma(p.neg_one_mul, &[ab]); // neg_one*ab = neg(ab)
        d.isymm(mul_negone_ab, start, fwd)
    };

    let mul_na = d.imul(neg_one, a);
    let mul_nb = d.imul(neg_one, b);
    let step2_rhs = d.iadd(mul_na, mul_nb);
    let step2 = d.lemma(p.left_distrib, &[neg_one, a, b]);

    let neg_a = d.ineg(a);
    let step3_rhs = d.iadd(neg_a, mul_nb);
    let step3 = {
        let fwd = d.lemma(p.neg_one_mul, &[a]);
        d.icongr(mul_na, neg_a, fwd, &|d, x| d.iadd(x, mul_nb))
    };

    let neg_b = d.ineg(b);
    let step4_rhs = d.iadd(neg_a, neg_b);
    let step4 = {
        let fwd = d.lemma(p.neg_one_mul, &[b]);
        d.icongr(mul_nb, neg_b, fwd, &|d, x| d.iadd(neg_a, x))
    };

    let (_, proof) = d.ichain(
        start,
        &[
            (mul_negone_ab, step1),
            (step2_rhs, step2),
            (step3_rhs, step3),
            (step4_rhs, step4),
        ],
    );
    proof
}

/// `Eq Int (sub y x) (neg (sub x y))`, for any `x, y` — the antisymmetry of
/// subtraction, via [`neg_add`] and [`neg_neg`].
fn neg_sub_eq(d: &mut IntDev<'_>, x: ExprId, y: ExprId) -> ExprId {
    let p = d.int();
    let neg_y = d.ineg(y);
    let sub_xy = d.iadd(x, neg_y); // Int.sub x y, unfolded
    let start = d.ineg(sub_xy);

    let neg_x = d.ineg(x);
    let neg_neg_y = d.ineg(neg_y);
    let step1_rhs = d.iadd(neg_x, neg_neg_y);
    let step1 = neg_add(d, x, neg_y);

    let nn_y = neg_neg(d, y); // neg(neg y) = y
    let step2_rhs = d.iadd(neg_x, y);
    let step2 = d.icongr(neg_neg_y, y, nn_y, &|d, t| d.iadd(neg_x, t));

    let step3_rhs = d.iadd(y, neg_x); // Int.sub y x, unfolded
    let step3 = d.lemma(p.add_comm, &[neg_x, y]);

    let (_, proof) = d.ichain(
        start,
        &[(step1_rhs, step1), (step2_rhs, step2), (step3_rhs, step3)],
    );
    // proof : neg (sub x y) = sub y x ; flip it.
    d.isymm(start, step3_rhs, proof)
}

/// `Eq Int (pow (neg one) (succ k)) (neg (pow (neg one) k))`.
pub(super) fn pow_neg_one_succ(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let p = d.int();
    let one_i = d.ione();
    let neg_one = d.ineg(one_i);
    let sk = d.succ(k);
    let start = d.ipow(neg_one, sk);
    let pk = d.ipow(neg_one, k);

    let step1_rhs = d.imul(pk, neg_one);
    let step1 = d.lemma(p.pow_succ, &[neg_one, k]);

    let mul_pk_one = d.imul(pk, one_i);
    let step2_rhs = d.ineg(mul_pk_one);
    let step2 = d.lemma(p.mul_neg, &[pk, one_i]);

    let neg_pk = d.ineg(pk);
    let step3 = {
        let fwd = d.lemma(p.mul_one, &[pk]); // mul pk one = pk
        d.icongr(mul_pk_one, pk, fwd, &|d, x| d.ineg(x))
    };

    let (_, proof) = d.ichain(
        start,
        &[(step1_rhs, step1), (step2_rhs, step2), (neg_pk, step3)],
    );
    proof
}

// ============================================================================
// The Cassini statement, and its pieces.
// ============================================================================

/// `Int.ofNat (Nat.fib n)`.
fn ofnat_fib(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let p = d.int();
    let fib_n = d.const_app(p.nat.fib, &[n]);
    d.of_nat(fib_n)
}

/// `(A, B, C) := (ofNat (fib n), ofNat (fib (succ n)), ofNat (fib (succ (succ n))))`.
fn cassini_pieces(d: &mut IntDev<'_>, n: ExprId) -> (ExprId, ExprId, ExprId) {
    let sn = d.succ(n);
    let ssn = d.succ(sn);
    (ofnat_fib(d, n), ofnat_fib(d, sn), ofnat_fib(d, ssn))
}

/// `D(n) := sub (mul C A) (mul B B)` — `fib(n+2)*fib(n) - fib(n+1)^2`.
fn cassini_lhs(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let (a, b, c) = cassini_pieces(d, n);
    let ca = d.imul(c, a);
    let bb = d.imul(b, b);
    d.isub(ca, bb)
}

/// `Eq Int (D n) (pow (neg one) (succ n))`.
fn cassini_stmt(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let lhs = cassini_lhs(d, n);
    let one_i = d.ione();
    let neg_one = d.ineg(one_i);
    let sn = d.succ(n);
    let rhs = d.ipow(neg_one, sn);
    d.ieq(lhs, rhs)
}

/// `Eq Int (D (succ n)) (neg (D n))` — the recurrence the induction step
/// needs. See the module doc for the algebra this executes.
fn cassini_step(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let p = d.int();
    let sn = d.succ(n);
    let ssn = d.succ(sn);
    let sssn = d.succ(ssn);

    let a = ofnat_fib(d, n);
    let b = ofnat_fib(d, sn);
    let c = ofnat_fib(d, ssn);
    let e = ofnat_fib(d, sssn);

    // hC : Eq Int C (add B A), from Nat.fib_add_two n.
    let hc = {
        let hc_nat = d.lemma(p.nat.fib_add_two, &[n]);
        let fib_ssn = d.const_app(p.nat.fib, &[ssn]);
        let fib_sn = d.const_app(p.nat.fib, &[sn]);
        let fib_n = d.const_app(p.nat.fib, &[n]);
        let rhs_nat = d.add(fib_sn, fib_n);
        d.nat_eq_to_int(fib_ssn, rhs_nat, hc_nat, &|d, x| d.of_nat(x))
    };

    // hc_s : Eq Int C s, s := add A B (flip via add_comm).
    let s = d.iadd(a, b);
    let hc_s = {
        let ba_eq_ab = d.lemma(p.add_comm, &[b, a]); // add b a = add a b
        let ba = d.iadd(b, a);
        d.itrans(c, ba, s, hc, ba_eq_ab)
    };

    // he_s : Eq Int E (add s B), from Nat.fib_add_two (succ n), then
    // substituting C -> s.
    let he_s = {
        let he_nat = d.lemma(p.nat.fib_add_two, &[sn]);
        let fib_sssn = d.const_app(p.nat.fib, &[sssn]);
        let fib_ssn2 = d.const_app(p.nat.fib, &[ssn]);
        let fib_sn2 = d.const_app(p.nat.fib, &[sn]);
        let rhs_nat2 = d.add(fib_ssn2, fib_sn2);
        let he = d.nat_eq_to_int(fib_sssn, rhs_nat2, he_nat, &|d, x| d.of_nat(x));
        // he : Eq Int E (add C B)
        let cb = d.iadd(c, b);
        let sb = d.iadd(s, b);
        let cb_to_sb = d.icongr(c, s, hc_s, &|d, x| d.iadd(x, b));
        d.itrans(e, cb, sb, he, cb_to_sb)
    };

    // L group: mul(E,B) -> add(mul(B,s), mul(B,B)).
    let eb = d.imul(e, b);
    let sb = d.iadd(s, b);
    let sb_b_mul = d.imul(sb, b);
    let l1 = d.icongr(e, sb, he_s, &|d, x| d.imul(x, b));

    let b_sb_mul = d.imul(b, sb);
    let l2 = d.lemma(p.mul_comm, &[sb, b]); // mul sb b = mul b sb

    let bs = d.imul(b, s);
    let bb = d.imul(b, b);
    let l_dist_rhs = d.iadd(bs, bb);
    let l3 = d.lemma(p.left_distrib, &[b, s, b]); // mul b (add s b) = add (mul b s) (mul b b)

    let (_, l_chain) = d.ichain(eb, &[(sb_b_mul, l1), (b_sb_mul, l2), (l_dist_rhs, l3)]);
    let k = bs;
    let big_n = bb;

    // Csq group: mul(C,C) -> add(mul(s,A), mul(s,B)).
    let cc = d.imul(c, c);
    let ss_mul = d.imul(s, s);
    let cs1 = d.icongr(c, s, hc_s, &|d, x| d.imul(x, x));

    let sa = d.imul(s, a);
    let sb2 = d.imul(s, b);
    let csq_rhs = d.iadd(sa, sb2);
    let cs2 = d.lemma(p.left_distrib, &[s, a, b]); // mul s (add a b) = add (mul s a) (mul s b)

    let (_, csq_chain) = d.ichain(cc, &[(ss_mul, cs1), (csq_rhs, cs2)]);
    let big_m = sa;
    let k_prime = sb2;

    let comm_k = d.lemma(p.mul_comm, &[b, s]); // mul b s = mul s b, i.e. K = K'

    // Assemble D(succ n) = sub(mul E B, mul C C), rewritten down to sub(N,M).
    let d_succ_n = d.isub(eb, cc);

    let kn = d.iadd(k, big_n);
    let step_d1_rhs = d.isub(kn, cc);
    let step_d1 = d.icongr(eb, kn, l_chain, &|d, x| d.isub(x, cc));

    let m_kprime = d.iadd(big_m, k_prime);
    let step_d2_rhs = d.isub(kn, m_kprime);
    let step_d2 = d.icongr(cc, m_kprime, csq_chain, &|d, x| d.isub(kn, x));

    let k_prime_to_k = d.isymm(k, k_prime, comm_k); // K' = K
    let m_k = d.iadd(big_m, k);
    let step_d3_rhs = d.isub(kn, m_k);
    let step_d3 = d.icongr(k_prime, k, k_prime_to_k, &|d, x| {
        let mx = d.iadd(big_m, x);
        d.isub(kn, mx)
    });

    let nk = d.iadd(big_n, k);
    let nk_comm = d.lemma(p.add_comm, &[k, big_n]); // add k n = add n k
    let step_d4_rhs = d.isub(nk, m_k);
    let step_d4 = d.icongr(kn, nk, nk_comm, &|d, x| d.isub(x, m_k));

    let step_d5 = super::modeq::cancel_common_addend(d, big_n, big_m, k);
    let nm_sub = d.isub(big_n, big_m);

    // sub(N,M) = neg(sub(M,N)).
    let step_d6 = neg_sub_eq(d, big_m, big_n);

    // sub(M,N) = D(n), via M = mul(C,A) (s -> C, the reverse substitution).
    let s_to_c = d.isymm(c, s, hc_s); // s = C
    let ca = d.imul(c, a);
    let m_to_ca = d.icongr(s, c, s_to_c, &|d, x| d.imul(x, a));

    let mn_sub = d.isub(big_m, big_n);
    let d_n = d.isub(ca, big_n); // == cassini_lhs(n)
    let mn_to_dn = d.icongr(big_m, ca, m_to_ca, &|d, x| d.isub(x, big_n));

    let neg_mn = d.ineg(mn_sub);
    let neg_dn = d.ineg(d_n);
    let step_d7 = d.icongr(mn_sub, d_n, mn_to_dn, &|d, x| d.ineg(x));

    let nm_to_negdn = d.itrans(nm_sub, neg_mn, neg_dn, step_d6, step_d7);

    let (_, final_chain) = d.ichain(
        d_succ_n,
        &[
            (step_d1_rhs, step_d1),
            (step_d2_rhs, step_d2),
            (step_d3_rhs, step_d3),
            (step_d4_rhs, step_d4),
            (nm_sub, step_d5),
            (neg_dn, nm_to_negdn),
        ],
    );
    final_chain
}

/// `Int.fib_cassini : ∀ n, Eq Int (sub (mul (ofNat (fib (n+2))) (ofNat (fib
/// n))) (mul (ofNat (fib (n+1))) (ofNat (fib (n+1))))) (pow (neg one) (succ
/// n))` — Cassini's identity, by induction on `n` via [`cassini_step`] and
/// [`pow_neg_one_succ`].
fn declare_fib_cassini(d: &mut IntDev<'_>, p: &IntPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let motive = |d: &mut IntDev<'_>, m: ExprId| -> ExprId { cassini_stmt(d, m) };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let p = d.int();
        let zero = d.zero();
        let one_n = d.num(1);
        let two_n = d.num(2);
        let a = ofnat_fib(d, zero);
        let b = ofnat_fib(d, one_n);
        let c = ofnat_fib(d, two_n);
        let zero_i = d.izero();
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);

        // `fib` computes on concrete numerals: `a ~ zero_i`, `b ~ one_i`,
        // `c ~ one_i`, all by `rfl` (`fib 0 = 0`, `fib 1 = 1`, `fib 2 = 1`,
        // each a couple of `δ`/`ι` steps — see `nat_prelude/fibonacci.rs`'s
        // module doc). `d.irefl` at the SOURCE term, read at the (defeq)
        // target type by the outer kernel check, is the same device
        // `gcd.rs`'s `neg_neg` uses for `neg (neg one) = one`.
        let a_eq = d.irefl(a); // read as Eq Int a zero_i
        let b_eq = d.irefl(b); // read as Eq Int b one_i
        let c_eq = d.irefl(c); // read as Eq Int c one_i

        let ca = d.imul(c, a);
        let bb = d.imul(b, b);
        let start = d.isub(ca, bb);

        let s1 = {
            let m = d.imul(one_i, a);
            d.isub(m, bb)
        };
        let step1 = d.icongr(c, one_i, c_eq, &|d, x| {
            let m = d.imul(x, a);
            d.isub(m, bb)
        });

        let s2 = {
            let m = d.imul(one_i, zero_i);
            d.isub(m, bb)
        };
        let step2 = d.icongr(a, zero_i, a_eq, &|d, x| {
            let m = d.imul(one_i, x);
            d.isub(m, bb)
        });

        let mul_zero_pf = d.lemma(p.mul_zero, &[one_i]); // mul one_i zero_i = zero_i
        let mul_zero_lhs = d.imul(one_i, zero_i);
        let s3 = d.isub(zero_i, bb);
        let step3 = d.icongr(mul_zero_lhs, zero_i, mul_zero_pf, &|d, x| d.isub(x, bb));

        let s4 = {
            let m = d.imul(one_i, one_i);
            d.isub(zero_i, m)
        };
        let step4 = d.icongr(b, one_i, b_eq, &|d, x| {
            let m = d.imul(x, x);
            d.isub(zero_i, m)
        });

        let mul_one_pf = d.lemma(p.mul_one, &[one_i]); // mul one_i one_i = one_i
        let mul_one_lhs = d.imul(one_i, one_i);
        let s5 = d.isub(zero_i, one_i);
        let step5 = d.icongr(mul_one_lhs, one_i, mul_one_pf, &|d, x| d.isub(zero_i, x));

        // `s5 = Int.sub zero_i one_i` unfolds (one `δ` step) to
        // `Int.add zero_i (Int.neg one_i) = Int.add zero_i neg_one`, which is
        // exactly `add_comm`'s left-hand side below.
        let add_comm_pf = d.lemma(p.add_comm, &[zero_i, neg_one]);
        let s6 = d.iadd(neg_one, zero_i);
        let add_zero_pf = d.lemma(p.add_zero, &[neg_one]); // add neg_one zero_i = neg_one

        let sz = d.succ(zero);
        let target = d.ipow(neg_one, sz);
        let pow_zero_term = d.ipow(neg_one, zero);
        let mul_form = d.imul(pow_zero_term, neg_one);
        let pow_succ_pf = d.lemma(p.pow_succ, &[neg_one, zero]);
        let pow_zero_pf = d.lemma(p.pow_zero, &[neg_one]); // pow neg_one zero = one_i
        let mul_after_pz = d.imul(one_i, neg_one);
        let step_pz = d.icongr(pow_zero_term, one_i, pow_zero_pf, &|d, x| {
            d.imul(x, neg_one)
        });
        let one_mul_pf = d.lemma(p.one_mul, &[neg_one]); // mul one_i neg_one = neg_one

        let (_, target_to_negone) = d.ichain(
            target,
            &[
                (mul_form, pow_succ_pf),
                (mul_after_pz, step_pz),
                (neg_one, one_mul_pf),
            ],
        );
        let negone_to_target = d.isymm(target, neg_one, target_to_negone);

        let (_, whole_chain) = d.ichain(
            start,
            &[
                (s1, step1),
                (s2, step2),
                (s3, step3),
                (s4, step4),
                (s5, step5),
                (s6, add_comm_pf),
                (neg_one, add_zero_pf),
                (target, negone_to_target),
            ],
        );
        whole_chain
    };

    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let cs = cassini_step(d, j); // D(succ j) = neg(D j)
        let dj = cassini_lhs(d, j);
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);
        let sj = d.succ(j);
        let pow_sj = d.ipow(neg_one, sj);
        let neg_dj = d.ineg(dj);
        let neg_pow_sj = d.ineg(pow_sj);
        let ih_neg = d.icongr(dj, pow_sj, ih, &|d, x| d.ineg(x)); // neg(D j) = neg(pow neg_one (succ j))

        let pns = pow_neg_one_succ(d, sj); // pow neg_one (succ succ j) = neg(pow neg_one (succ j))
        let ssj = d.succ(sj);
        let pow_ssj = d.ipow(neg_one, ssj);
        let pns_rev = d.isymm(pow_ssj, neg_pow_sj, pns); // neg(pow neg_one (succ j)) = pow neg_one (succ succ j)

        let d_succ_j = cassini_lhs(d, sj);
        let step1 = d.itrans(d_succ_j, neg_dj, neg_pow_sj, cs, ih_neg);
        d.itrans(d_succ_j, neg_pow_sj, pow_ssj, step1, pns_rev)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let proof = d.induct(&motive, &base, &step, n);
    let stmt = motive(d, n);
    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.fib_cassini, ty, value)
}

/// Declare every theorem in this module.
pub(super) fn declare_fib_cassini_all(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    declare_fib_cassini(d, &p)
}

// ============================================================================
// `Int.fib` — the sign-extended Fibonacci sequence, and its first new law.
// ============================================================================
//
// `Int.fib : ℤ → ℤ` did not exist before this: `Nat.fib` (`nat_prelude`) only
// ever takes a `Nat`, and everything above builds `ofNat (Nat.fib n)` terms
// directly rather than a genuine `Int`-valued function (`Int.fib_cassini`
// needs no such thing). All five open `integer-fibonacci` facts quantify over
// `Int.fib m`/`Int.fib n` for potentially NEGATIVE `m, n : ℤ`, so they were
// unstatable, not merely unproved, until this definition landed.
//
// The standard extension is `fib(-n) = (-1)^(n+1) fib(n)`. Written over the
// `Int` constructors (`ofNat n` / `negSucc m`, `m` standing for `-(m+1)`):
//
// `fib (ofNat n)   := ofNat (Nat.fib n)`
// `fib (negSucc m) := pow (neg one) m * ofNat (Nat.fib (succ m))`
//
// The `negSucc` branch's exponent is `m`, not `m+2`: substituting `n := m+1`
// into the extension gives `(-1)^(m+2) fib(m+1)`, and `(-1)^(m+2) = (-1)^m`
// (an even shift), so using `m` directly gives the same value with a smaller
// term and no extra parity bookkeeping in the definition itself. Hand check
// against `fib = 0,1,1,2,3,5,…`: `fib(-1) = fib(negSucc 0) = (-1)^0 · fib(1) =
// 1`; `fib(-2) = fib(negSucc 1) = (-1)^1 · fib(2) = -1`; `fib(-3) =
// fib(negSucc 2) = (-1)^2 · fib(3) = 2` — matches the well-known
// `1, -1, 2, -3, 5, -8, …` sequence for `fib(-1), fib(-2), fib(-3), …`.
//
// This is ONE `Int.rec` case split with no new recursion device -- closer to
// `Nat.bit` than to `Nat.log`'s fuel device, exactly as the definition needs
// no recursion of its OWN: `Int.pow` (already total and structural on its
// `Nat` exponent) supplies the sign, and `Nat.fib` supplies the magnitude.

/// Delta height for `Int.fib`: it calls `Int.pow` (`POW_HEIGHT`, `defs.rs`)
/// directly, so it must strictly outrank it -- the same relationship
/// `Int.prodRange` has to `Int.pow` (`prod.rs`'s `PROD_RANGE_HEIGHT`).
const FIB_HEIGHT: u16 = super::defs::POW_HEIGHT + 1;

/// Admit `Int.fib : Int → Int`. See the module doc above for the definition
/// and the hand check.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_fib(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();

    let motive = d.kernel().lam(anon, int_ty, int_ty, BinderInfo::Default);
    let minor_of = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fib_n = d.const_app(p.nat.fib, &[n]);
        let body = d.of_nat(fib_n);
        d.lam_fv(n_fv, nat, body)
    };
    let minor_neg = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let sm = d.succ(m);
        let fib_sm = d.const_app(p.nat.fib, &[sm]);
        let ofnat_fib_sm = d.of_nat(fib_sm);
        let one_nat = d.num(1);
        let one_i = d.of_nat(one_nat);
        let neg_one = d.ineg(one_i);
        let sign = d.ipow(neg_one, m);
        let body = d.imul(sign, ofnat_fib_sm);
        d.lam_fv(m_fv, nat, body)
    };
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let rec = d.kernel().const_(p.rec, vec![one]);
    let body = d.apply(rec, &[motive, minor_of, minor_neg, a]);
    let value = d.lam_fv(a_fv, int_ty, body);
    let ty = d.arrow(int_ty, int_ty);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.fib,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(FIB_HEIGHT),
    })?;
    Ok(())
}

/// `Eq Int (pow neg_one (mul two j)) (ofNat one)` — `(-1)` raised to an EVEN
/// exponent is `1`, by induction on `j` (the exponent is `mul two j`, i.e.
/// `2j`).
///
/// `mul two (succ j)` reduces PURELY (no lemma needed) to
/// `succ (succ (mul two j))`: `Nat.mul` recurses on its right argument
/// (`mul_succ : mul n (succ m) = add (mul n m) n`, one of this kernel's
/// defining-equation theorems, `nat_prelude.rs`), giving `add (mul two j)
/// two`; `Nat.add` then recurses on ITS right argument, which here is the
/// LITERAL `two`, so it peels two successors off with `mul two j` held fixed
/// on the (symbolic) left -- the safe orientation the `Nat.add` gotcha
/// documents (`CLAUDE.md`: symbolic side left, literal side right). So the
/// step case needs only [`pow_neg_one_succ`] (already built for
/// `fib_cassini`, this file) applied twice, plus [`neg_neg`] to cancel the
/// resulting double negation against the induction hypothesis -- no new
/// arithmetic lemma at all.
fn pow_neg_one_two_mul(d: &mut IntDev<'_>, j: ExprId) -> ExprId {
    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let two = d.num(2);
        let exponent = d.mul(two, v);
        let one_nat = d.num(1);
        let one_i = d.of_nat(one_nat);
        let neg_one = d.ineg(one_i);
        let lhs = d.ipow(neg_one, exponent);
        let rhs_nat = d.num(1);
        let rhs = d.of_nat(rhs_nat);
        d.ieq(lhs, rhs)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        // `mul two zero` reduces to `zero` (`Nat.mul`'s own base case);
        // `pow neg_one zero` reduces to `Int.one`; `Int.one` unfolds
        // (`defs.rs`'s leaf table) to `ofNat 1`. All pure delta/iota, so
        // `d.irefl` at the raw (unreduced) term reads at the target type.
        let two = d.num(2);
        let zero = d.zero();
        let exponent = d.mul(two, zero);
        let one_nat = d.num(1);
        let one_i = d.of_nat(one_nat);
        let neg_one = d.ineg(one_i);
        let lhs = d.ipow(neg_one, exponent);
        d.irefl(lhs)
    };

    let step = |d: &mut IntDev<'_>, k: ExprId, ih: ExprId| -> ExprId {
        // ih : Eq Int (pow neg_one (mul two k)) (ofNat one)
        let two = d.num(2);
        let mul_two_k = d.mul(two, k);
        let sk = d.succ(k);
        let mul_two_sk = d.mul(two, sk);

        let one_nat = d.num(1);
        let one_i = d.of_nat(one_nat);
        let neg_one = d.ineg(one_i);

        let start = d.ipow(neg_one, mul_two_sk);
        let succ_succ = {
            let inner = d.succ(mul_two_k);
            d.succ(inner)
        };
        let reduced_start = d.ipow(neg_one, succ_succ);
        // `mul two (succ k)` reduces PURELY to `succ (succ (mul two k))` --
        // see the module doc above -- so `start` and `reduced_start` are the
        // same term up to reduction.
        let bridge = d.irefl(start);

        // pow neg_one (succ (succ K)) = neg (pow neg_one (succ K))
        let sk_of_mul = d.succ(mul_two_k);
        let step_a = pow_neg_one_succ(d, sk_of_mul);
        let pow_at_sk = d.ipow(neg_one, sk_of_mul);
        let neg_pow_at_sk = d.ineg(pow_at_sk);

        // pow neg_one (succ K) = neg (pow neg_one K)
        let step_b = pow_neg_one_succ(d, mul_two_k);
        let pow_at_k = d.ipow(neg_one, mul_two_k);
        let neg_pow_at_k = d.ineg(pow_at_k);
        let step_b_lifted = d.icongr(pow_at_sk, neg_pow_at_k, step_b, &|d, t| d.ineg(t));
        let neg_neg_pow_at_k = d.ineg(neg_pow_at_k);

        let (_, double_neg_chain) = d.ichain(
            reduced_start,
            &[(neg_pow_at_sk, step_a), (neg_neg_pow_at_k, step_b_lifted)],
        );

        // Lift `ih` through `neg . neg`, then cancel with `neg_neg`.
        let ih_neg1 = d.icongr(pow_at_k, one_i, ih, &|d, t| d.ineg(t));
        let neg_one_i = d.ineg(one_i);
        let ih_neg2 = d.icongr(neg_pow_at_k, neg_one_i, ih_neg1, &|d, t| d.ineg(t));
        let neg_neg_one_i = d.ineg(neg_one_i);
        let cancel = neg_neg(d, one_i);

        let (_, ih_chain) = d.ichain(
            neg_neg_pow_at_k,
            &[(neg_neg_one_i, ih_neg2), (one_i, cancel)],
        );

        let (_, whole) = d.ichain(
            start,
            &[
                (reduced_start, bridge),
                (neg_neg_pow_at_k, double_neg_chain),
                (one_i, ih_chain),
            ],
        );
        whole
    };

    d.induct(&motive, &base, &step, j)
}

/// `fib_two_mul_add_one_pos : ∀ (n : Int), Lt zero (fib (2*n+1))` — the
/// Fibonacci sequence is strictly positive at every ODD index, in EITHER
/// direction of `ℤ`.
///
/// Case split on `n`. In both branches `2*n+1` reduces PURELY (no named
/// lemma for the arithmetic itself -- `Int.mul`/`Int.add` on `ofNat`/`ofNat`
/// and `ofNat`/`negSucc` pairs, and `Int.subNatNat`'s own `Nat.sub`-based
/// case split, are all structural, per `defs.rs`'s module doc) down to either
/// `ofNat E` (`ofNat k` branch, `E := 2k+1` as a `Nat`) or `negSucc (2j)`
/// (`negSucc j` branch):
///
/// - `ofNat` branch: `fib (ofNat E)` reduces ([`declare_fib`]'s own case
///   split) to `ofNat (Nat.fib E)`, and `Lt (ofNat 0) (ofNat _)` reduces to
///   `Nat.lt` (the `Int.le`/`Int.lt` four-case table, `defs.rs`) -- so
///   `Nat.fib_pos_of_pos` fed `Nat.zero_lt_succ` at `E`'s predecessor closes
///   it directly; the kernel's own defeq check accepts the `Nat`-typed term
///   where the `Int`-typed conclusion is expected.
/// - `negSucc` branch: `fib (negSucc (2j))` does NOT reduce further on its
///   own -- the exponent `2j` in [`declare_fib`]'s `pow (neg one) _` factor
///   is symbolic in `j` -- so [`pow_neg_one_two_mul`] supplies the one
///   non-structural fact this branch needs (`(-1)^(2j) = 1`), and an
///   `Int`-level transport moves the resulting `Nat`-side positivity fact
///   across the `Eq Int (fib …) (ofNat …)` this gives.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_fib_two_mul_add_one_pos(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let izero = d.izero();

    let statement = |d: &mut IntDev<'_>, args: &[ExprId]| -> ExprId {
        let n = args[0];
        let two_nat = d.num(2);
        let two_i = d.of_nat(two_nat);
        let one_nat = d.num(1);
        let one_i = d.of_nat(one_nat);
        let doubled = d.imul(two_i, n);
        let index = d.iadd(doubled, one_i);
        let fib_index = d.const_app(p.fib, &[index]);
        d.ilt(izero, fib_index)
    };

    d.int_theorem(p.fib_two_mul_add_one_pos, 1, &|d, v| {
        let n = v[0];
        let stmt = statement(d, v);
        let proof = case_split(d, &[n], &statement, &|d, b| match b[0].0 {
            Shape::OfNat => {
                let k = b[0].1;
                let two_nat = d.num(2);
                let mul_2k = d.mul(two_nat, k);
                let one_nat = d.num(1);
                let e_arg = d.add(mul_2k, one_nat);
                let pos_hyp = d.zero_lt_succ(mul_2k);
                d.lemma(p.nat.fib_pos_of_pos, &[e_arg, pos_hyp])
            }
            Shape::NegSucc => {
                let j = b[0].1;
                let two_nat = d.num(2);
                let x = d.mul(two_nat, j);
                let sx = d.succ(x);

                // `fib (negSucc x) = pow (neg one) x * ofNat (Nat.fib (succ
                // x))`, this module's own `declare_fib`.
                let neg_succ_x = d.neg_succ(x);
                let fib_neg_succ_x = d.const_app(p.fib, &[neg_succ_x]);

                let one_nat = d.num(1);
                let one_i = d.of_nat(one_nat);
                let neg_one = d.ineg(one_i);
                let sign = d.ipow(neg_one, x);
                let fib_sx = d.const_app(p.nat.fib, &[sx]);
                let ofnat_fib_sx = d.of_nat(fib_sx);
                let mul_form = d.imul(sign, ofnat_fib_sx);
                // `fib (negSucc x)` reduces PURELY to `mul_form` -- one
                // step of `declare_fib`'s own recursor.
                let bridge_fib = d.irefl(fib_neg_succ_x);

                // `(-1)^x = 1`.
                let sign_eq_one = pow_neg_one_two_mul(d, j);
                let one_mul_form = d.imul(one_i, ofnat_fib_sx);
                let lifted = d.icongr(sign, one_i, sign_eq_one, &|d, t| d.imul(t, ofnat_fib_sx));

                // `1 * ofNat (Nat.fib sx)` reduces to `ofNat (mul one
                // (Nat.fib sx))`, then `Nat.one_mul` collapses it.
                let mul_reduced = {
                    let one_nat2 = d.num(1);
                    let lhs = d.imul(one_i, ofnat_fib_sx);
                    let rhs_nat = d.mul(one_nat2, fib_sx);
                    let rhs = d.of_nat(rhs_nat);
                    let br = d.irefl(lhs);
                    let one_mul_pf = d.lemma(p.nat.one_mul, &[fib_sx]);
                    let cast = d.nat_eq_to_int(rhs_nat, fib_sx, one_mul_pf, &|d, t| d.of_nat(t));
                    d.itrans(lhs, rhs, ofnat_fib_sx, br, cast)
                };

                let (_, eq_to_ofnat) = d.ichain(
                    fib_neg_succ_x,
                    &[
                        (mul_form, bridge_fib),
                        (one_mul_form, lifted),
                        (ofnat_fib_sx, mul_reduced),
                    ],
                );

                let h_pos_nat = {
                    let hyp = d.zero_lt_succ(x);
                    d.lemma(p.nat.fib_pos_of_pos, &[sx, hyp])
                };

                let reversed = d.isymm(fib_neg_succ_x, ofnat_fib_sx, eq_to_ofnat);
                let motive = d.ieq_motive(ofnat_fib_sx, &|d, x2| {
                    let z = d.izero();
                    d.ilt(z, x2)
                });
                d.itransport(ofnat_fib_sx, motive, h_pos_nat, fib_neg_succ_x, reversed)
            }
        });
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Int.fib_of_odd` — at an odd index, `fib` agrees with the plain `Nat`
// sequence at the magnitude, in either direction of `ℤ`.
// ============================================================================

/// `Int.natAbs a`. Module-private mirror of `parity.rs`'s/`gcd.rs`'s own
/// copies (`nat_abs.rs`'s `NatAbsOps` trait is private to that module).
fn nat_abs(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let f = d.int().nat_abs;
    d.const_app(f, &[a])
}

/// `Eq Nat (add (succ m) (succ m)) (succ (succ (add m m)))` — the same
/// `add_succ` then `succ_add` peel `nat_prelude/parity.rs`'s private
/// `succ_double_eq` performs, rebuilt here over `IntDev` (which implements
/// `NatOps` in full, so every `Nat`-level term/`Eq` combinator this needs is
/// already available) rather than reused, since that helper is private to
/// `nat_prelude`.
fn succ_double_eq_nat(d: &mut IntDev<'_>, m: ExprId) -> ExprId {
    let p = d.int().nat;
    let succ_m = d.succ(m);
    let lhs = d.add(succ_m, succ_m);
    let inner = d.add(succ_m, m);
    let succ_inner = d.succ(inner);
    let add_succ_eq = d.lemma(p.add_succ, &[succ_m, m]);

    let mm = d.add(m, m);
    let succ_mm = d.succ(mm);
    let succ_add_eq = d.lemma(p.succ_add, &[m, m]);
    let congr_succ = d.congr(inner, succ_mm, succ_add_eq, &|d, x| d.succ(x));
    let succ_succ_mm = d.succ(succ_mm);

    let (_, result) = d.chain(
        lhs,
        &[(succ_inner, add_succ_eq), (succ_succ_mm, congr_succ)],
    );
    result
}

/// `Eq Int (pow (neg one) (add k k)) (ofNat one)` — `(-1)` raised to an
/// exponent of the shape `k + k` (the witness form `Nat.Even`'s own
/// definition uses, `nat_prelude/parity.rs`) is `1`.
///
/// Same induction and the same four supporting facts as
/// [`pow_neg_one_two_mul`], but over `add k k` rather than `mul two k`:
/// `add (succ k) (succ k)` does **not** reduce purely the way `mul two (succ
/// k)` does (`Nat.add` recurses on its right argument, which here is
/// symbolic `succ k`, not the literal `two` the `mul`-shaped version has), so
/// the step case bridges with an actual equation ([`succ_double_eq_nat`])
/// lifted to `Int` via `nat_eq_to_int`, rather than `d.irefl`.
pub(super) fn pow_neg_one_add_self(d: &mut IntDev<'_>, j: ExprId) -> ExprId {
    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let exponent = d.add(v, v);
        let one_nat = d.num(1);
        let one_i = d.of_nat(one_nat);
        let neg_one = d.ineg(one_i);
        let lhs = d.ipow(neg_one, exponent);
        let rhs_nat = d.num(1);
        let rhs = d.of_nat(rhs_nat);
        d.ieq(lhs, rhs)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        // `add zero zero` reduces PURELY to `zero` (`Nat.add`'s own base
        // case), exactly like `mul two zero` in `pow_neg_one_two_mul`.
        let zero = d.zero();
        let exponent = d.add(zero, zero);
        let one_nat = d.num(1);
        let one_i = d.of_nat(one_nat);
        let neg_one = d.ineg(one_i);
        let lhs = d.ipow(neg_one, exponent);
        d.irefl(lhs)
    };

    let step = |d: &mut IntDev<'_>, k: ExprId, ih: ExprId| -> ExprId {
        // ih : Eq Int (pow neg_one (add k k)) (ofNat one)
        let add_k_k = d.add(k, k);
        let sk = d.succ(k);
        let add_sk_sk = d.add(sk, sk);

        let one_nat = d.num(1);
        let one_i = d.of_nat(one_nat);
        let neg_one = d.ineg(one_i);

        let start = d.ipow(neg_one, add_sk_sk);

        // Bridge: add (succ k) (succ k) = succ (succ (add k k)) -- NOT pure
        // reduction, lift the Nat equation to Int.
        let succ_succ = {
            let inner = d.succ(add_k_k);
            d.succ(inner)
        };
        let reduced_start = d.ipow(neg_one, succ_succ);
        let nat_eq = succ_double_eq_nat(d, k);
        let bridge = d.nat_eq_to_int(add_sk_sk, succ_succ, nat_eq, &|d, x| d.ipow(neg_one, x));

        // pow neg_one (succ (succ K)) = neg (pow neg_one (succ K))
        let sk_of_add = d.succ(add_k_k);
        let step_a = pow_neg_one_succ(d, sk_of_add);
        let pow_at_sk = d.ipow(neg_one, sk_of_add);
        let neg_pow_at_sk = d.ineg(pow_at_sk);

        // pow neg_one (succ K) = neg (pow neg_one K)
        let step_b = pow_neg_one_succ(d, add_k_k);
        let pow_at_k = d.ipow(neg_one, add_k_k);
        let neg_pow_at_k = d.ineg(pow_at_k);
        let step_b_lifted = d.icongr(pow_at_sk, neg_pow_at_k, step_b, &|d, t| d.ineg(t));
        let neg_neg_pow_at_k = d.ineg(neg_pow_at_k);

        let (_, double_neg_chain) = d.ichain(
            reduced_start,
            &[(neg_pow_at_sk, step_a), (neg_neg_pow_at_k, step_b_lifted)],
        );

        // Lift `ih` through `neg . neg`, then cancel with `neg_neg`.
        let ih_neg1 = d.icongr(pow_at_k, one_i, ih, &|d, t| d.ineg(t));
        let neg_one_i = d.ineg(one_i);
        let ih_neg2 = d.icongr(neg_pow_at_k, neg_one_i, ih_neg1, &|d, t| d.ineg(t));
        let neg_neg_one_i = d.ineg(neg_one_i);
        let cancel = neg_neg(d, one_i);

        let (_, ih_chain) = d.ichain(
            neg_neg_pow_at_k,
            &[(neg_neg_one_i, ih_neg2), (one_i, cancel)],
        );

        let (_, whole) = d.ichain(
            start,
            &[
                (reduced_start, bridge),
                (neg_neg_pow_at_k, double_neg_chain),
                (one_i, ih_chain),
            ],
        );
        whole
    };

    d.induct(&motive, &base, &step, j)
}

/// `Int.fib_of_odd : ∀ n, Odd n → Eq Int (fib n) (ofNat (Nat.fib (natAbs
/// n)))`.
///
/// Case split on `n`. `Odd`/`Even` are defined via `natAbs`
/// (`parity.rs`'s module doc), so both branches reach their goal cheaply:
///
/// - `ofNat` branch: `fib (ofNat a)` reduces ([`declare_fib`]'s own case
///   split) to `ofNat (Nat.fib a)`, and `natAbs (ofNat a)` reduces to `a`, so
///   both sides of the target equation reduce to the identical term -- the
///   hypothesis is not even used.
/// - `negSucc` branch: `Odd (negSucc m)` reduces to `Nat.Odd (succ m)`, and
///   `NatPrelude::even_iff_odd_succ`'s `mpr` direction gives `Nat.Even m`
///   directly -- no `Int`-level parity lemma needed, exactly as the earlier
///   lane predicted. `Nat.Even m`'s witness `k` (with `m = k + k`) is
///   eliminated (`Exists.rec`, `Prop`-only, legal here since the target is a
///   `Prop`) to invoke [`pow_neg_one_add_self`], transported from exponent
///   `k + k` to `m` along the witness equation, giving `(-1)^m = 1`; the rest
///   is the same `one_mul` collapse [`declare_fib_two_mul_add_one_pos`]'s own
///   `negSucc` branch already performs.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_fib_of_odd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    let statement = |d: &mut IntDev<'_>, args: &[ExprId]| -> ExprId {
        let n = args[0];
        let odd_ty = d.const_app(p.odd, &[n]);
        let fib_n = d.const_app(p.fib, &[n]);
        let mag = nat_abs(d, n);
        let fib_mag = d.const_app(p.nat.fib, &[mag]);
        let rhs = d.of_nat(fib_mag);
        let concl = d.ieq(fib_n, rhs);
        d.arrow(odd_ty, concl)
    };

    d.int_theorem(p.fib_of_odd, 1, &|d, v| {
        let stmt = statement(d, v);
        let proof = case_split(d, v, &statement, &|d, b| match b[0].0 {
            Shape::OfNat => {
                let a = b[0].1;
                let ofnat_a = d.of_nat(a);
                let odd_ofnat_a_ty = d.const_app(p.odd, &[ofnat_a]);
                let fib_ofnat_a = d.const_app(p.fib, &[ofnat_a]);

                // `fib (ofNat a)` and `ofNat (Nat.fib (natAbs (ofNat a)))`
                // both reduce PURELY to `ofNat (Nat.fib a)` -- `d.irefl` at
                // the raw (unreduced) `fib (ofNat a)` term reads at the
                // target type, and the hypothesis is unused.
                let body = d.irefl(fib_ofnat_a);
                let h_fv = d.fresh_fvar();
                d.lam_fv(h_fv, odd_ofnat_a_ty, body)
            }
            Shape::NegSucc => {
                let m = b[0].1;
                let neg_succ_m = d.neg_succ(m);
                let fib_neg_succ_m = d.const_app(p.fib, &[neg_succ_m]);
                let odd_neg_succ_m_ty = d.const_app(p.odd, &[neg_succ_m]);

                let sm = d.succ(m);
                let odd_sm_ty = d.const_app(p.nat.odd, &[sm]);
                let even_m_ty = d.const_app(p.nat.even, &[m]);

                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);

                // Odd (negSucc m) reduces to Nat.Odd (succ m); even_iff_odd_succ's
                // mpr direction gives Nat.Even m directly.
                let iff_ty = d.lemma(p.nat.even_iff_odd_succ, &[m]);
                let mpr = d.const_app(p.logic.iff_mpr, &[even_m_ty, odd_sm_ty, iff_ty]);
                let even_m = d.apply(mpr, &[h]);

                let target = {
                    let mag = nat_abs(d, neg_succ_m);
                    let fib_mag = d.const_app(p.nat.fib, &[mag]);
                    let rhs = d.of_nat(fib_mag);
                    d.ieq(fib_neg_succ_m, rhs)
                };

                let nat = d.nat_ty();
                let even_pred = {
                    let k_fv = d.fresh_fvar();
                    let k = d.kernel().fvar(k_fv);
                    let kk = d.add(k, k);
                    let body = d.eq(m, kk);
                    d.lam_fv(k_fv, nat, body)
                };

                let minor = {
                    let k_fv = d.fresh_fvar();
                    let k = d.kernel().fvar(k_fv);
                    let hk_fv = d.fresh_fvar();
                    let hk = d.kernel().fvar(hk_fv);
                    let kk = d.add(k, k);
                    let hk_ty = d.eq(m, kk);

                    // pow (neg one) (k+k) = 1, transported to exponent m via hk.
                    let sign_eq_one_at_kk = pow_neg_one_add_self(d, k);

                    let one_nat = d.num(1);
                    let one_i = d.of_nat(one_nat);
                    let neg_one = d.ineg(one_i);
                    let kk_eq_m = d.symm(m, kk, hk);
                    let bridge = d.nat_eq_to_int(kk, m, kk_eq_m, &|d, x| d.ipow(neg_one, x));
                    let pow_kk = d.ipow(neg_one, kk);
                    let pow_m = d.ipow(neg_one, m);
                    let bridge_rev = d.isymm(pow_kk, pow_m, bridge);
                    let sign_eq_one = d.itrans(pow_m, pow_kk, one_i, bridge_rev, sign_eq_one_at_kk);

                    // fib (negSucc m) reduces PURELY to pow(neg one)(m) *
                    // ofNat(Nat.fib(succ m)) -- declare_fib's own recursor step.
                    let sign = d.ipow(neg_one, m);
                    let fib_sm = d.const_app(p.nat.fib, &[sm]);
                    let ofnat_fib_sm = d.of_nat(fib_sm);
                    let mul_form = d.imul(sign, ofnat_fib_sm);
                    let bridge_fib = d.irefl(fib_neg_succ_m);

                    let one_mul_form = d.imul(one_i, ofnat_fib_sm);
                    let lifted =
                        d.icongr(sign, one_i, sign_eq_one, &|d, t| d.imul(t, ofnat_fib_sm));

                    let mul_reduced = {
                        let lhs = d.imul(one_i, ofnat_fib_sm);
                        let rhs_nat = d.mul(one_nat, fib_sm);
                        let rhs = d.of_nat(rhs_nat);
                        let br = d.irefl(lhs);
                        let one_mul_pf = d.lemma(p.nat.one_mul, &[fib_sm]);
                        let cast =
                            d.nat_eq_to_int(rhs_nat, fib_sm, one_mul_pf, &|d, t| d.of_nat(t));
                        d.itrans(lhs, rhs, ofnat_fib_sm, br, cast)
                    };

                    let (_, eq_to_ofnat) = d.ichain(
                        fib_neg_succ_m,
                        &[
                            (mul_form, bridge_fib),
                            (one_mul_form, lifted),
                            (ofnat_fib_sm, mul_reduced),
                        ],
                    );

                    let inner = d.lam_fv(hk_fv, hk_ty, eq_to_ofnat);
                    d.lam_fv(k_fv, nat, inner)
                };

                let even_m_elim = exists_elim(d, even_pred, target, even_m, minor);
                d.lam_fv(h_fv, odd_neg_succ_m_ty, even_m_elim)
            }
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.fib x`.
fn fibt(d: &mut IntDev<'_>, x: ExprId) -> ExprId {
    let f = d.int().fib;
    d.const_app(f, &[x])
}

/// `h : Eq Int a b  ⊢  Eq Int (fib a) (fib b)`.
fn fib_congr(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.icongr(a, b, h, &|d, t| fibt(d, t))
}

// ============================================================================
// `Int.fib_rec` — the Fibonacci recurrence at EVERY integer index.
// ============================================================================

/// `Eq Int (mul (neg a) b) (neg (mul a b))`.
///
/// `sub.rs` proves the mirrored `Int.mul_neg` (`a * (-b) = -(a*b)`) and
/// exposes it; the left-hand form is three `mul_comm` steps away and is not a
/// prelude name, so it is local here.
fn neg_mul(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let p = d.int();
    let neg_a = d.ineg(a);
    let start = d.imul(neg_a, b);

    let flipped = d.imul(b, neg_a);
    let step1 = d.lemma(p.mul_comm, &[neg_a, b]);

    let mul_ba = d.imul(b, a);
    let neg_ba = d.ineg(mul_ba);
    let step2 = d.lemma(p.mul_neg, &[b, a]);

    let mul_ab = d.imul(a, b);
    let neg_ab = d.ineg(mul_ab);
    let step3 = {
        let comm = d.lemma(p.mul_comm, &[b, a]);
        d.icongr(mul_ba, mul_ab, comm, &|d, t| d.ineg(t))
    };

    let (_, proof) = d.ichain(start, &[(flipped, step1), (neg_ba, step2), (neg_ab, step3)]);
    proof
}

/// `Eq Int (add (neg w) w) zero` — the left-handed additive cancellation.
///
/// The prelude carries `add_neg` (`a + (-a) = 0`) only; instantiating it at
/// `neg w` and collapsing `neg (neg w)` with this module's [`neg_neg`] gives
/// the other side without an `add_comm` step.
fn neg_add_cancel(d: &mut IntDev<'_>, w: ExprId) -> ExprId {
    let p = d.int();
    let neg_w = d.ineg(w);
    let neg_neg_w = d.ineg(neg_w);
    let start = d.iadd(neg_w, w);
    let via = d.iadd(neg_w, neg_neg_w);
    let zero = d.izero();

    let collapse = neg_neg(d, w);
    let lifted = d.icongr(neg_neg_w, w, collapse, &|d, t| d.iadd(neg_w, t));
    let back = d.isymm(via, start, lifted);
    let cancel = d.lemma(p.add_neg, &[neg_w]);
    d.itrans(start, via, zero, back, cancel)
}

/// `Eq Int (add zero x) x`. The prelude has `add_zero`, not `zero_add`.
fn zero_add(d: &mut IntDev<'_>, x: ExprId) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let start = d.iadd(zero, x);
    let flipped = d.iadd(x, zero);
    let comm = d.lemma(p.add_comm, &[zero, x]);
    let collapse = d.lemma(p.add_zero, &[x]);
    d.itrans(start, flipped, x, comm, collapse)
}

/// `Int.fib_rec : ∀ n, Eq Int (fib (add n (ofNat 2))) (add (fib (add n one))
/// (fib n))` — the Fibonacci recurrence, at **every** integer index, negative
/// ones included.
///
/// `Nat.fib_add_two` is the `ℕ` recurrence and says nothing below `0`;
/// [`declare_fib`]'s `negSucc` branch is a *definition*, not a recurrence, so
/// nothing in the development previously related `fib(-k-1)` to its
/// neighbours. This is the fact the two-sided induction combinator
/// (`two_sided_induction.rs`) needs as its step ingredient, and the one
/// `Int.fib_add` is blocked on.
///
/// # Three cases, and only one of them does algebra
///
/// `Int.rec` on `n`, then two further `Nat` splits inside the `negSucc`
/// branch — the recurrence straddles zero, so `n = -1` and `n = -2` are
/// genuinely different from `n <= -3`:
///
/// - `n = ofNat a`: every index reduces (`add (ofNat a) (ofNat 2) ≡ ofNat
///   (succ (succ a))`, `Nat.add` recursing on the literal right argument),
///   so the whole goal is `Nat.fib_add_two a` pushed through
///   [`IntDev::nat_eq_to_int`]. One line.
/// - `n = -1` (`negSucc 0`) and `n = -2` (`negSucc (succ 0))`: `1 = 0 + 1`
///   and `0 = 1 + (-1)`. Both sides are closed terms — `subNatNat` decides,
///   `Nat.fib` computes at the literal, `pow (neg one)` computes at the
///   literal exponent — so `d.irefl` reads at the goal and no lemma is used.
///   Their magnitudes are `fib 1` and `fib 2`, which is why walking them is
///   cheap.
/// - `n = -(j+3)` (`negSucc (succ (succ j))`): the only real work. Writing
///   `s := (-1)^j` and `F1,F2,F3 := fib(j+1), fib(j+2), fib(j+3)` over `ℕ`,
///   `declare_fib`'s own `negSucc` clause makes the goal
///   `s*F1 = (-s)*F2 + s*F3` (the two sign flips come from
///   [`pow_neg_one_succ`] applied twice, the second collapsed by [`neg_neg`]),
///   and `Nat.fib_add_two (succ j)` supplies `F3 = F2 + F1`. Then
///   `left_distrib`, one `add_assoc` reversal, [`neg_mul`], [`neg_add_cancel`]
///   and [`zero_add`] close it: the `(-s)*F2` and `s*F2` terms annihilate.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_fib_rec(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    let statement = |d: &mut IntDev<'_>, args: &[ExprId]| -> ExprId {
        let n = args[0];
        let two_nat = d.num(2);
        let two = d.of_nat(two_nat);
        let one = d.ione();
        let n_plus_two = d.iadd(n, two);
        let n_plus_one = d.iadd(n, one);
        let lhs = d.const_app(p.fib, &[n_plus_two]);
        let f_next = d.const_app(p.fib, &[n_plus_one]);
        let f_here = d.const_app(p.fib, &[n]);
        let rhs = d.iadd(f_next, f_here);
        d.ieq(lhs, rhs)
    };

    d.int_theorem(p.fib_rec, 1, &|d, v| {
        let stmt = statement(d, v);
        let proof = case_split(d, v, &statement, &|d, b| match b[0].0 {
            Shape::OfNat => {
                // Every index reduces; the goal IS `Nat.fib_add_two a` cast.
                let a = b[0].1;
                let nat_pf = d.lemma(p.nat.fib_add_two, &[a]);
                let sa = d.succ(a);
                let ssa = d.succ(sa);
                let fib_ssa = d.const_app(p.nat.fib, &[ssa]);
                let fib_sa = d.const_app(p.nat.fib, &[sa]);
                let fib_a = d.const_app(p.nat.fib, &[a]);
                let sum = d.add(fib_sa, fib_a);
                d.nat_eq_to_int(fib_ssa, sum, nat_pf, &|d, t| d.of_nat(t))
            }
            Shape::NegSucc => {
                let m = b[0].1;
                // Split `m` twice with `Nat.rec` (the induction hypotheses are
                // unused -- this is a case analysis, not an induction).
                let at_neg_succ = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                    let term = d.neg_succ(k);
                    statement(d, &[term])
                };
                let at_neg_succ_succ = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                    let sk = d.succ(k);
                    let term = d.neg_succ(sk);
                    statement(d, &[term])
                };

                d.induct(
                    &at_neg_succ,
                    // n = -1: `fib 1 = fib 0 + fib (-1)`, i.e. `1 = 0 + 1`.
                    // Closed on both sides.
                    &|d| {
                        let zero_nat = d.zero();
                        let n = d.neg_succ(zero_nat);
                        let two_nat = d.num(2);
                        let two = d.of_nat(two_nat);
                        let shifted = d.iadd(n, two);
                        let lhs = d.const_app(p.fib, &[shifted]);
                        d.irefl(lhs)
                    },
                    &|d, m1, _ih| {
                        d.induct(
                            &at_neg_succ_succ,
                            // n = -2: `fib 0 = fib (-1) + fib (-2)`, i.e.
                            // `0 = 1 + (-1)`. Closed on both sides.
                            &|d| {
                                let zero_nat = d.zero();
                                let one_nat = d.succ(zero_nat);
                                let n = d.neg_succ(one_nat);
                                let two_nat = d.num(2);
                                let two = d.of_nat(two_nat);
                                let shifted = d.iadd(n, two);
                                let lhs = d.const_app(p.fib, &[shifted]);
                                d.irefl(lhs)
                            },
                            &|d, j, _ih| fib_rec_deep_negative(d, j),
                            m1,
                        )
                    },
                    m,
                )
            }
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// The `n = -(j+3)` branch of [`declare_fib_rec`].
///
/// Proves `s*F1 = (-s)*F2 + s*F3` for `s = (-1)^j` and `F1,F2,F3` the `ℕ`
/// Fibonacci values at `j+1, j+2, j+3` — which is what the goal
/// `fib (negSucc j) = fib (negSucc (succ j)) + fib (negSucc (succ (succ j)))`
/// reduces to under [`declare_fib`]'s own `negSucc` clause. The chain runs
/// right-to-left and is flipped at the end.
fn fib_rec_deep_negative(d: &mut IntDev<'_>, j: ExprId) -> ExprId {
    let p = d.int();

    let one_i = d.ione();
    let neg_one = d.ineg(one_i);

    let sign = d.ipow(neg_one, j); // s = (-1)^j
    let sj = d.succ(j);
    let ssj = d.succ(sj);
    let sssj = d.succ(ssj);
    let sign_succ = d.ipow(neg_one, sj); // (-1)^(j+1)
    let sign_succ_succ = d.ipow(neg_one, ssj); // (-1)^(j+2)

    let fib1_nat = d.const_app(p.nat.fib, &[sj]);
    let fib2_nat = d.const_app(p.nat.fib, &[ssj]);
    let fib3_nat = d.const_app(p.nat.fib, &[sssj]);
    let f1 = d.of_nat(fib1_nat);
    let f2 = d.of_nat(fib2_nat);
    let f3 = d.of_nat(fib3_nat);

    let neg_sign = d.ineg(sign);

    // Start from the right-hand side of the goal.
    let term_a = d.imul(sign_succ, f2);
    let term_b = d.imul(sign_succ_succ, f3);
    let start = d.iadd(term_a, term_b);

    // (-1)^(j+1) = -(-1)^j
    let sign_succ_eq = pow_neg_one_succ(d, j);
    let after_first = {
        let left = d.imul(neg_sign, f2);
        d.iadd(left, term_b)
    };
    let step1 = d.icongr(sign_succ, neg_sign, sign_succ_eq, &|d, t| {
        let left = d.imul(t, f2);
        d.iadd(left, term_b)
    });

    // (-1)^(j+2) = -(-1)^(j+1) = -(-(-1)^j) = (-1)^j
    let sign_succ_succ_eq = {
        let outer = pow_neg_one_succ(d, sj); // = neg sign_succ
        let neg_sign_succ = d.ineg(sign_succ);
        let neg_neg_sign = d.ineg(neg_sign);
        let lifted = d.icongr(sign_succ, neg_sign, sign_succ_eq, &|d, t| d.ineg(t));
        let collapse = neg_neg(d, sign);
        let (_, chained) = d.ichain(
            sign_succ_succ,
            &[
                (neg_sign_succ, outer),
                (neg_neg_sign, lifted),
                (sign, collapse),
            ],
        );
        chained
    };
    let neg_sign_f2 = d.imul(neg_sign, f2);
    let after_second = {
        let right = d.imul(sign, f3);
        d.iadd(neg_sign_f2, right)
    };
    let step2 = d.icongr(sign_succ_succ, sign, sign_succ_succ_eq, &|d, t| {
        let right = d.imul(t, f3);
        d.iadd(neg_sign_f2, right)
    });

    // F3 = F2 + F1  (Nat.fib_add_two at `succ j`, lifted to Int).
    let f2_plus_f1 = d.iadd(f2, f1);
    let step3 = {
        let nat_pf = d.lemma(p.nat.fib_add_two, &[sj]);
        let sum_nat = d.add(fib2_nat, fib1_nat);
        let lifted = d.nat_eq_to_int(fib3_nat, sum_nat, nat_pf, &|d, t| d.of_nat(t));
        d.icongr(f3, f2_plus_f1, lifted, &|d, t| {
            let right = d.imul(sign, t);
            d.iadd(neg_sign_f2, right)
        })
    };
    let after_third = {
        let right = d.imul(sign, f2_plus_f1);
        d.iadd(neg_sign_f2, right)
    };

    // s*(F2+F1) = s*F2 + s*F1
    let sign_f2 = d.imul(sign, f2);
    let sign_f1 = d.imul(sign, f1);
    let distributed = d.iadd(sign_f2, sign_f1);
    let step4 = {
        let distrib = d.lemma(p.left_distrib, &[sign, f2, f1]);
        let mul_form = d.imul(sign, f2_plus_f1);
        d.icongr(mul_form, distributed, distrib, &|d, t| {
            d.iadd(neg_sign_f2, t)
        })
    };
    let after_fourth = d.iadd(neg_sign_f2, distributed);

    // Re-associate to expose the annihilating pair.
    let paired = d.iadd(neg_sign_f2, sign_f2);
    let after_fifth = d.iadd(paired, sign_f1);
    let step5 = {
        let assoc = d.lemma(p.add_assoc, &[neg_sign_f2, sign_f2, sign_f1]);
        d.isymm(after_fifth, after_fourth, assoc)
    };

    // (-s)*F2 = -(s*F2), then (-(s*F2)) + (s*F2) = 0.
    let neg_of_sign_f2 = d.ineg(sign_f2);
    let cancelled_pair = d.iadd(neg_of_sign_f2, sign_f2);
    let after_sixth = d.iadd(cancelled_pair, sign_f1);
    let step6 = {
        let pull = neg_mul(d, sign, f2);
        d.icongr(neg_sign_f2, neg_of_sign_f2, pull, &|d, t| {
            let left = d.iadd(t, sign_f2);
            d.iadd(left, sign_f1)
        })
    };

    let zero = d.izero();
    let after_seventh = d.iadd(zero, sign_f1);
    let step7 = {
        let cancel = neg_add_cancel(d, sign_f2);
        d.icongr(cancelled_pair, zero, cancel, &|d, t| d.iadd(t, sign_f1))
    };

    let step8 = zero_add(d, sign_f1);

    let (_, forward) = d.ichain(
        start,
        &[
            (after_first, step1),
            (after_second, step2),
            (after_third, step3),
            (after_fourth, step4),
            (after_fifth, step5),
            (after_sixth, step6),
            (after_seventh, step7),
            (sign_f1, step8),
        ],
    );
    // `forward : RHS = LHS`; the goal is stated the other way round.
    d.isymm(start, sign_f1, forward)
}

// ============================================================================
// `Int.fib_add` — the addition formula over all of `ℤ`.
// ============================================================================

/// `Eq Int (add (add w x) (add y z)) (add (add w y) (add x z))`.
///
/// The prelude has no `add_add_add_comm`; `nat_prelude/fibonacci.rs` needed the
/// same regroup for `Nat.fib_add` and built its own private `add_regroup_four`
/// for exactly this reason. Five `add_assoc`/`add_comm` steps.
fn add_regroup_four(d: &mut IntDev<'_>, w: ExprId, x: ExprId, y: ExprId, z: ExprId) -> ExprId {
    let p = d.int();
    let wx = d.iadd(w, x);
    let yz = d.iadd(y, z);
    let start = d.iadd(wx, yz);

    let x_yz = d.iadd(x, yz);
    let w_x_yz = d.iadd(w, x_yz);
    let s1 = d.lemma(p.add_assoc, &[w, x, yz]);

    let xy = d.iadd(x, y);
    let xy_z = d.iadd(xy, z);
    let w_xy_z = d.iadd(w, xy_z);
    let s2 = {
        let assoc = d.lemma(p.add_assoc, &[x, y, z]);
        let back = d.isymm(xy_z, x_yz, assoc);
        d.icongr(x_yz, xy_z, back, &|d, t| d.iadd(w, t))
    };

    let yx = d.iadd(y, x);
    let yx_z = d.iadd(yx, z);
    let w_yx_z = d.iadd(w, yx_z);
    let s3 = {
        let comm = d.lemma(p.add_comm, &[x, y]);
        d.icongr(xy, yx, comm, &|d, t| {
            let inner = d.iadd(t, z);
            d.iadd(w, inner)
        })
    };

    let xz = d.iadd(x, z);
    let y_xz = d.iadd(y, xz);
    let w_y_xz = d.iadd(w, y_xz);
    let s4 = {
        let assoc = d.lemma(p.add_assoc, &[y, x, z]);
        d.icongr(yx_z, y_xz, assoc, &|d, t| d.iadd(w, t))
    };

    let wy = d.iadd(w, y);
    let goal = d.iadd(wy, xz);
    let s5 = {
        let assoc = d.lemma(p.add_assoc, &[w, y, xz]);
        d.isymm(goal, w_y_xz, assoc)
    };

    let (_, proof) = d.ichain(
        start,
        &[
            (w_x_yz, s1),
            (w_xy_z, s2),
            (w_yx_z, s3),
            (w_y_xz, s4),
            (goal, s5),
        ],
    );
    proof
}

/// `h : Eq Int (add x z) (add y z)  ⊢  Eq Int x y`.
///
/// The additive cancellation the down-step needs so the whole derivation can
/// stay inside `add`/`mul` and never form a difference — `Int.sub` is total,
/// but every subtraction would have to be re-folded against `fib`'s own
/// `negSucc` clause later, and this is one lemma instead.
fn add_right_cancel(d: &mut IntDev<'_>, x: ExprId, y: ExprId, z: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let neg_z = d.ineg(z);
    let xz = d.iadd(x, z);
    let yz = d.iadd(y, z);
    let xz_neg = d.iadd(xz, neg_z);
    let yz_neg = d.iadd(yz, neg_z);

    let s1 = {
        let cancel = d.lemma(p.add_neg_cancel_right, &[x, z]);
        d.isymm(xz_neg, x, cancel)
    };
    let s2 = d.icongr(xz, yz, h, &|d, t| d.iadd(t, neg_z));
    let s3 = d.lemma(p.add_neg_cancel_right, &[y, z]);

    let (_, proof) = d.ichain(x, &[(xz_neg, s1), (yz_neg, s2), (y, s3)]);
    proof
}

/// The addition formula's statement at a given index: `fib (m + k) =
/// fib (m - 1) * fib k + fib m * fib (k + 1)`.
fn fib_add_stmt(d: &mut IntDev<'_>, m: ExprId, k: ExprId) -> ExprId {
    let one = d.ione();
    let m_minus = d.isub(m, one);
    let a = fibt(d, m_minus);
    let b = fibt(d, m);
    let shifted = d.iadd(m, k);
    let lhs = fibt(d, shifted);
    let fk = fibt(d, k);
    let k1 = d.iadd(k, one);
    let fk1 = fibt(d, k1);
    let left = d.imul(a, fk);
    let right = d.imul(b, fk1);
    let rhs = d.iadd(left, right);
    d.ieq(lhs, rhs)
}

/// `Eq Int (add (sub k one) one) k` — `(k-1)+1 = k`.
///
/// `add_neg_cancel_right k (neg one)` states
/// `((k + -1) + -(-1)) = k`, and `neg (neg one)` reduces to `one`
/// (`neg one ≡ negSucc 0`, `neg (negSucc 0) ≡ ofNat 1 ≡ one`), so this is that
/// lemma read at a definitionally equal type — no rewriting at all.
fn sub_add_cancel(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let p = d.int();
    let one = d.ione();
    let neg_one = d.ineg(one);
    d.lemma(p.add_neg_cancel_right, &[k, neg_one])
}

/// `Eq Int (add k two) (add (add k one) one)` reversed: `(k+1)+1 = k + 2`.
///
/// `add_assoc k one one` gives `((k+1)+1) = (k + (1+1))`, and `add one one`
/// reduces to `ofNat 2` — so the shift between the two spellings of "plus two"
/// costs one lemma and one defeq.
fn plus_two_spelling(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let p = d.int();
    let one = d.ione();
    d.lemma(p.add_assoc, &[k, one, one])
}

/// `Eq Int (fib (add (add k one) one)) (add (fib (add k one)) (fib k))` — the
/// recurrence with the index spelled `(k+1)+1` rather than `k+2`.
fn fib_step(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let p = d.int();
    let one = d.ione();
    let two_nat = d.num(2);
    let two = d.of_nat(two_nat);
    let k1 = d.iadd(k, one);
    let k2 = d.iadd(k1, one);
    let k_two = d.iadd(k, two);
    let spelling = plus_two_spelling(d, k);
    let bridge = fib_congr(d, k2, k_two, spelling);
    let f_k_two = fibt(d, k_two);
    let f_k2 = fibt(d, k2);
    let rec = d.lemma(p.fib_rec, &[k]);
    let f_k1 = fibt(d, k1);
    let f_k = fibt(d, k);
    let sum = d.iadd(f_k1, f_k);
    d.itrans(f_k2, f_k_two, sum, bridge, rec)
}

/// `Int.fib_add : ∀ m n, Eq Int (fib (add m n))
/// (add (mul (fib (sub m one)) (fib n)) (mul (fib m) (fib (add n one))))`.
///
/// Mathlib's `Int.fib_add`, over the constructed `ℤ`.
///
/// # It does NOT reduce to `Nat.fib_add`
///
/// `Nat.fib_add m n : fib (succ (m+n)) = fib m * fib n + fib (succ m) *
/// fib (succ n)` is exactly this statement restricted to `m ≥ 1, n ≥ 0`, so
/// the `ofNat`/`ofNat` corner with `m = ofNat (succ a)` is a cast away. That
/// is one of *four* constructor pairs, and it is not even all of the
/// non-negative case: at `m = 0` the statement reads
/// `fib n = fib(-1) * fib n + fib 0 * fib(n+1)`, whose leading coefficient is
/// a value at a NEGATIVE index. So sign bookkeeping over `Nat.fib_add` cannot
/// reach it, and this proof does not use `Nat.fib_add` at all.
///
/// # Two-sided induction on `n` with a paired motive
///
/// [`super::two_sided_induction`]'s `Int.induction_on` supplies the recursion.
/// Fibonacci is a two-step recurrence, so no single-index motive can step: the
/// motive here is `Q k := P k ∧ P (k+1)` (the same pairing device
/// `nat_prelude/fibonacci.rs` uses for `Nat.fib_add`, and the reason that file
/// says pairing PROVES a two-index proposition even though it cannot DEFINE a
/// two-step function). [`declare_fib_rec`] supplies the recurrence at every
/// index, positive and negative, which is what makes the *downward* step
/// possible at all.
///
/// - `Q 0 = P 0 ∧ P 1`. `P 0` is `mul_zero`/`mul_one`; `P 1` is
///   `fib(m+1) = fib(m-1) + fib m`, i.e. [`declare_fib_rec`] at `m-1`.
/// - Up: `P n, P (n+1) ⊢ P (n+2)`. `fib(m+n+2) = fib(m+n+1) + fib(m+n)`
///   substitutes both hypotheses, [`add_regroup_four`] collects the `fib(m-1)`
///   and `fib m` coefficients, and two `left_distrib` reversals plus two more
///   recurrences rebuild the goal.
/// - Down: `P n, P (n+1) ⊢ P (n-1)`. Stated as an addition and closed by
///   [`add_right_cancel`] rather than by subtracting: both
///   `(target + fib(m+n))` and `(fib(m+n-1) + fib(m+n))` are shown equal to
///   `fib(m+n+1)`, so no difference is ever formed.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_fib_add(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.int_theorem(p.fib_add, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let stmt = fib_add_stmt(d, m, n);

        let int_ty = d.int_ty();
        let one = d.ione();
        let m_minus = d.isub(m, one);
        let a = fibt(d, m_minus);
        let b = fibt(d, m);

        // Q k := P k ∧ P (k+1)
        let paired = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
            let here = fib_add_stmt(d, m, k);
            let k1 = d.iadd(k, one);
            let next = fib_add_stmt(d, m, k1);
            d.and(here, next)
        };
        let motive = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let body = paired(d, k);
            d.lam_fv(k_fv, int_ty, body)
        };

        let base = fib_add_base(d, m, a, b);
        let up = fib_add_up_step(d, m, a, b);
        let down = fib_add_down_step(d, m, a, b);

        let at_n = d.const_app(p.induction_on, &[motive, base, up, down]);
        let q_n = d.apply(at_n, &[n]);
        let here = fib_add_stmt(d, m, n);
        let n1 = d.iadd(n, one);
        let next = fib_add_stmt(d, m, n1);
        let proof = d.and_left(here, next, q_n);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Q 0 = P 0 ∧ P (0+1)` — see [`declare_fib_add`].
fn fib_add_base(d: &mut IntDev<'_>, m: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let p = d.int();
    let one = d.ione();
    let zero = d.izero();
    let z1 = d.iadd(zero, one);

    // --- P 0: fib (m+0) = A * fib 0 + B * fib (0+1) = 0 + B = B.
    let p0 = {
        let m_zero = d.iadd(m, zero);
        let lhs = fibt(d, m_zero);
        let collapse = d.lemma(p.add_zero, &[m]);
        let to_b = fib_congr(d, m_zero, m, collapse);

        let f0 = fibt(d, zero);
        let f01 = fibt(d, z1);
        let left = d.imul(a, f0);
        let right = d.imul(b, f01);
        let rhs = d.iadd(left, right);

        // `fib zero` reduces to `zero` and `fib (add zero one)` to `one`, so
        // `mul_zero`/`mul_one` read at these types without a rewrite.
        let s1 = {
            let kill = d.lemma(p.mul_zero, &[a]);
            d.icongr(left, zero, kill, &|d, t| d.iadd(t, right))
        };
        let after1 = d.iadd(zero, right);
        let s2 = {
            let unit = d.lemma(p.mul_one, &[b]);
            d.icongr(right, b, unit, &|d, t| d.iadd(zero, t))
        };
        let after2 = d.iadd(zero, b);
        let s3 = zero_add(d, b);
        let (_, rhs_chain) = d.ichain(rhs, &[(after1, s1), (after2, s2), (b, s3)]);
        let back = d.isymm(rhs, b, rhs_chain);
        d.itrans(lhs, b, rhs, to_b, back)
    };

    // --- P 1: fib (m+1) = A * fib 1 + B * fib 2 = A + B.
    let p1 = {
        let two_nat = d.num(2);
        let two = d.of_nat(two_nat);
        let neg_one = d.ineg(one);
        let m_minus = m_minus_of(d, m);
        let mm_two = d.iadd(m_minus, two);
        let mm_one = d.iadd(m_minus, one);
        let f_mm_two = fibt(d, mm_two);
        let f_mm_one = fibt(d, mm_one);

        // (m-1)+2 = m+1, by `add_assoc` and `(-1)+2 ≡ 1`.
        let idx_two = d.lemma(p.add_assoc, &[m, neg_one, two]);
        let m_one = d.iadd(m, one);
        let f_m_one = fibt(d, m_one);
        let bridge = fib_congr(d, mm_two, m_one, idx_two);
        let s1 = d.isymm(f_mm_two, f_m_one, bridge);

        let rec = d.lemma(p.fib_rec, &[m_minus]);
        let sum1 = d.iadd(f_mm_one, a);

        // (m-1)+1 = m, by `add_assoc`, `(-1)+1 ≡ 0` and `add_zero`.
        let idx_one = {
            let assoc = d.lemma(p.add_assoc, &[m, neg_one, one]);
            let m_zero = d.iadd(m, zero);
            let collapse = d.lemma(p.add_zero, &[m]);
            d.itrans(mm_one, m_zero, m, assoc, collapse)
        };
        let to_b = fib_congr(d, mm_one, m, idx_one);
        let sum2 = d.iadd(b, a);
        let s3 = d.icongr(f_mm_one, b, to_b, &|d, t| d.iadd(t, a));
        let sum3 = d.iadd(a, b);
        let s4 = d.lemma(p.add_comm, &[b, a]);
        let (_, lhs_chain) = d.ichain(
            f_m_one,
            &[(f_mm_two, s1), (sum1, rec), (sum2, s3), (sum3, s4)],
        );

        let f_z1 = fibt(d, z1);
        let z11 = d.iadd(z1, one);
        let f_z11 = fibt(d, z11);
        let left = d.imul(a, f_z1);
        let right = d.imul(b, f_z11);
        let rhs = d.iadd(left, right);
        let r1 = {
            let unit = d.lemma(p.mul_one, &[a]);
            d.icongr(left, a, unit, &|d, t| d.iadd(t, right))
        };
        let after1 = d.iadd(a, right);
        let r2 = {
            let unit = d.lemma(p.mul_one, &[b]);
            d.icongr(right, b, unit, &|d, t| d.iadd(a, t))
        };
        let (_, rhs_chain) = d.ichain(rhs, &[(after1, r1), (sum3, r2)]);
        let back = d.isymm(rhs, sum3, rhs_chain);

        let m_z1 = d.iadd(m, z1);
        let lhs = fibt(d, m_z1);
        d.itrans(lhs, sum3, rhs, lhs_chain, back)
    };

    let s0 = fib_add_stmt(d, m, zero);
    let s1_ty = fib_add_stmt(d, m, z1);
    let intro = d.int().logic.and_intro;
    d.const_app(intro, &[s0, s1_ty, p0, p1])
}

/// `sub m one`.
fn m_minus_of(d: &mut IntDev<'_>, m: ExprId) -> ExprId {
    let one = d.ione();
    d.isub(m, one)
}

/// `∀ n, Q n → Q (n+1)` — see [`declare_fib_add`].
fn fib_add_up_step(d: &mut IntDev<'_>, m: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let p = d.int();
    let int_ty = d.int_ty();
    let one = d.ione();
    let two_nat = d.num(2);
    let two = d.of_nat(two_nat);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let n1 = d.iadd(n, one);
    let n2 = d.iadd(n1, one);
    let n3 = d.iadd(n2, one);

    let here = fib_add_stmt(d, m, n);
    let next = fib_add_stmt(d, m, n1);
    let hyp_ty = d.and(here, next);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let hp = d.and_left(here, next, h);
    let hq = d.and_right(here, next, h);

    let fn_ = fibt(d, n);
    let fn1 = fibt(d, n1);
    let fn2 = fibt(d, n2);
    let fn3 = fibt(d, n3);

    let m_n = d.iadd(m, n);
    let m_n1 = d.iadd(m, n1);
    let m_n2 = d.iadd(m, n2);
    let f_m_n = fibt(d, m_n);
    let f_m_n1 = fibt(d, m_n1);
    let f_m_n2 = fibt(d, m_n2);

    // fib (m + (n+1)+1) = fib ((m+n) + 2)
    let m_n_two = d.iadd(m_n, two);
    let f_m_n_two = fibt(d, m_n_two);
    let idx = {
        let spelling = plus_two_spelling(d, n);
        let n_two = d.iadd(n, two);
        let inner = d.icongr(n2, n_two, spelling, &|d, t| d.iadd(m, t));
        let m_n_two_form = d.iadd(m, n_two);
        let assoc = d.lemma(p.add_assoc, &[m, n, two]);
        let back = d.isymm(m_n_two, m_n_two_form, assoc);
        d.itrans(m_n2, m_n_two_form, m_n_two, inner, back)
    };
    let s1 = fib_congr(d, m_n2, m_n_two, idx);

    // the recurrence, then the index of its first summand
    let m_n_one = d.iadd(m_n, one);
    let f_m_n_one = fibt(d, m_n_one);
    let s2 = d.lemma(p.fib_rec, &[m_n]);
    let after2 = d.iadd(f_m_n_one, f_m_n);

    let s3 = {
        let assoc = d.lemma(p.add_assoc, &[m, n, one]);
        let bridge = fib_congr(d, m_n_one, m_n1, assoc);
        d.icongr(f_m_n_one, f_m_n1, bridge, &|d, t| d.iadd(t, f_m_n))
    };
    let after3 = d.iadd(f_m_n1, f_m_n);

    // substitute the two hypotheses
    let q_left = d.imul(a, fn1);
    let q_right = d.imul(b, fn2);
    let q_rhs = d.iadd(q_left, q_right);
    let s4 = d.icongr(f_m_n1, q_rhs, hq, &|d, t| d.iadd(t, f_m_n));
    let after4 = d.iadd(q_rhs, f_m_n);

    let p_left = d.imul(a, fn_);
    let p_right = d.imul(b, fn1);
    let p_rhs = d.iadd(p_left, p_right);
    let s5 = d.icongr(f_m_n, p_rhs, hp, &|d, t| d.iadd(q_rhs, t));
    let after5 = d.iadd(q_rhs, p_rhs);

    // (A*f(n+1) + B*f(n+2)) + (A*f n + B*f(n+1))
    //   = (A*f(n+1) + A*f n) + (B*f(n+2) + B*f(n+1))
    let s6 = add_regroup_four(d, q_left, q_right, p_left, p_right);
    let a_group = d.iadd(q_left, p_left);
    let b_group = d.iadd(q_right, p_right);
    let after6 = d.iadd(a_group, b_group);

    let fn1_fn = d.iadd(fn1, fn_);
    let a_folded = d.imul(a, fn1_fn);
    let s7 = {
        let distrib = d.lemma(p.left_distrib, &[a, fn1, fn_]);
        let back = d.isymm(a_folded, a_group, distrib);
        d.icongr(a_group, a_folded, back, &|d, t| d.iadd(t, b_group))
    };
    let after7 = d.iadd(a_folded, b_group);

    let fn2_fn1 = d.iadd(fn2, fn1);
    let b_folded = d.imul(b, fn2_fn1);
    let s8 = {
        let distrib = d.lemma(p.left_distrib, &[b, fn2, fn1]);
        let back = d.isymm(b_folded, b_group, distrib);
        d.icongr(b_group, b_folded, back, &|d, t| d.iadd(a_folded, t))
    };
    let after8 = d.iadd(a_folded, b_folded);

    let s9 = {
        let step = fib_step(d, n);
        let back = d.isymm(fn2, fn1_fn, step);
        d.icongr(fn1_fn, fn2, back, &|d, t| {
            let left = d.imul(a, t);
            d.iadd(left, b_folded)
        })
    };
    let a_final = d.imul(a, fn2);
    let after9 = d.iadd(a_final, b_folded);

    let s10 = {
        let step = fib_step(d, n1);
        let back = d.isymm(fn3, fn2_fn1, step);
        d.icongr(fn2_fn1, fn3, back, &|d, t| {
            let right = d.imul(b, t);
            d.iadd(a_final, right)
        })
    };
    let b_final = d.imul(b, fn3);
    let goal_rhs = d.iadd(a_final, b_final);

    let (_, proof_next) = d.ichain(
        f_m_n2,
        &[
            (f_m_n_two, s1),
            (after2, s2),
            (after3, s3),
            (after4, s4),
            (after5, s5),
            (after6, s6),
            (after7, s7),
            (after8, s8),
            (after9, s9),
            (goal_rhs, s10),
        ],
    );

    let at_n1 = fib_add_stmt(d, m, n1);
    let at_n2 = fib_add_stmt(d, m, n2);
    let intro = d.int().logic.and_intro;
    let pair = d.const_app(intro, &[at_n1, at_n2, hq, proof_next]);
    let inner = d.lam_fv(h_fv, hyp_ty, pair);
    d.lam_fv(n_fv, int_ty, inner)
}

/// `∀ n, Q n → Q (n-1)` — see [`declare_fib_add`].
fn fib_add_down_step(d: &mut IntDev<'_>, m: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let p = d.int();
    let int_ty = d.int_ty();
    let one = d.ione();
    let two_nat = d.num(2);
    let two = d.of_nat(two_nat);
    let neg_one = d.ineg(one);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let n1 = d.iadd(n, one);
    let n2 = d.iadd(n1, one);
    let nm1 = d.isub(n, one);

    let here = fib_add_stmt(d, m, n);
    let next = fib_add_stmt(d, m, n1);
    let hyp_ty = d.and(here, next);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let hp = d.and_left(here, next, h);
    let hq = d.and_right(here, next, h);

    let fn_ = fibt(d, n);
    let fn1 = fibt(d, n1);
    let fn2 = fibt(d, n2);
    let fnm1 = fibt(d, nm1);

    let m_n = d.iadd(m, n);
    let m_n1 = d.iadd(m, n1);
    let m_nm1 = d.iadd(m, nm1);
    let f_m_n = fibt(d, m_n);
    let f_m_n1 = fibt(d, m_n1);
    let f_m_nm1 = fibt(d, m_nm1);

    // `(n-1)+1 = n`, the one index identity the down-step turns on.
    let cancel = sub_add_cancel(d, n);
    let nm1_one = d.iadd(nm1, one);

    // --- right side: fib(m + (n-1)) + fib(m+n) = fib(m + (n+1)).
    // From `fib_rec` at `m + (n-1)`, whose two indices are `(m+(n-1))+2 = m+(n+1)`
    // and `(m+(n-1))+1 = m+n`.
    let right_chain = {
        let base = d.iadd(m_nm1, two);
        let f_base = fibt(d, base);
        let idx_two = {
            let assoc = d.lemma(p.add_assoc, &[m, nm1, two]);
            let nm1_two = d.iadd(nm1, two);
            let inner_assoc = d.lemma(p.add_assoc, &[n, neg_one, two]);
            let bridge = d.icongr(nm1_two, n1, inner_assoc, &|d, t| d.iadd(m, t));
            let mid = d.iadd(m, nm1_two);
            d.itrans(base, mid, m_n1, assoc, bridge)
        };
        let to_m_n1 = fib_congr(d, base, m_n1, idx_two);
        let flip = d.isymm(f_base, f_m_n1, to_m_n1);

        let step = d.iadd(m_nm1, one);
        let f_step = fibt(d, step);
        let rec = d.lemma(p.fib_rec, &[m_nm1]);
        let after_rec = d.iadd(f_step, f_m_nm1);

        let idx_one = {
            let assoc = d.lemma(p.add_assoc, &[m, nm1, one]);
            let mid = d.iadd(m, nm1_one);
            let bridge = d.icongr(nm1_one, n, cancel, &|d, t| d.iadd(m, t));
            d.itrans(step, mid, m_n, assoc, bridge)
        };
        let to_m_n = fib_congr(d, step, m_n, idx_one);
        let fixed = d.icongr(f_step, f_m_n, to_m_n, &|d, t| d.iadd(t, f_m_nm1));
        let after_fixed = d.iadd(f_m_n, f_m_nm1);

        let comm = d.lemma(p.add_comm, &[f_m_n, f_m_nm1]);
        let swapped = d.iadd(f_m_nm1, f_m_n);
        let (_, forward) = d.ichain(
            f_m_n1,
            &[
                (f_base, flip),
                (after_rec, rec),
                (after_fixed, fixed),
                (swapped, comm),
            ],
        );
        // forward : fib(m+n1) = fib(m+(n-1)) + fib(m+n); flip it.
        d.isymm(f_m_n1, swapped, forward)
    };
    let target_rhs = {
        let left = d.imul(a, fnm1);
        let right = d.imul(b, fn_);
        d.iadd(left, right)
    };
    let right_start = d.iadd(f_m_nm1, f_m_n);

    // --- left side: (A*f(n-1) + B*f n) + fib(m+n) = fib(m + (n+1)).
    let left_start = d.iadd(target_rhs, f_m_n);
    let a_nm1 = d.imul(a, fnm1);
    let b_n = d.imul(b, fn_);
    let p_left = d.imul(a, fn_);
    let p_right = d.imul(b, fn1);
    let p_rhs = d.iadd(p_left, p_right);

    let l1 = d.icongr(f_m_n, p_rhs, hp, &|d, t| d.iadd(target_rhs, t));
    let after1 = d.iadd(target_rhs, p_rhs);

    let l2 = add_regroup_four(d, a_nm1, b_n, p_left, p_right);
    let a_group = d.iadd(a_nm1, p_left);
    let b_group = d.iadd(b_n, p_right);
    let after2 = d.iadd(a_group, b_group);

    let fnm1_fn = d.iadd(fnm1, fn_);
    let a_folded = d.imul(a, fnm1_fn);
    let l3 = {
        let distrib = d.lemma(p.left_distrib, &[a, fnm1, fn_]);
        let back = d.isymm(a_folded, a_group, distrib);
        d.icongr(a_group, a_folded, back, &|d, t| d.iadd(t, b_group))
    };
    let after3 = d.iadd(a_folded, b_group);

    let fn_fn1 = d.iadd(fn_, fn1);
    let b_folded = d.imul(b, fn_fn1);
    let l4 = {
        let distrib = d.lemma(p.left_distrib, &[b, fn_, fn1]);
        let back = d.isymm(b_folded, b_group, distrib);
        d.icongr(b_group, b_folded, back, &|d, t| d.iadd(a_folded, t))
    };
    let after4 = d.iadd(a_folded, b_folded);

    // fib(n-1) + fib n = fib(n+1): the recurrence at `n-1`, with both indices
    // rewritten along `(n-1)+1 = n`.
    let l5 = {
        let step = fib_step(d, nm1); // fib((n-1)+1+1) = fib((n-1)+1) + fib(n-1)
        let f_nm1_one = fibt(d, nm1_one);
        let inner = d.iadd(f_nm1_one, fnm1);
        let nm1_two = d.iadd(nm1_one, one);
        let f_nm1_two = fibt(d, nm1_two);
        let to_fn = fib_congr(d, nm1_one, n, cancel);
        let fixed_left = {
            let lifted = d.icongr(nm1_one, n, cancel, &|d, t| {
                let shifted = d.iadd(t, one);
                fibt(d, shifted)
            });
            d.isymm(f_nm1_two, fn1, lifted)
        };
        let fixed_right = d.icongr(f_nm1_one, fn_, to_fn, &|d, t| d.iadd(t, fnm1));
        let after_fix = d.iadd(fn_, fnm1);
        let comm = d.lemma(p.add_comm, &[fn_, fnm1]);
        let (_, forward) = d.ichain(
            fn1,
            &[
                (f_nm1_two, fixed_left),
                (inner, step),
                (after_fix, fixed_right),
                (fnm1_fn, comm),
            ],
        );
        let back = d.isymm(fn1, fnm1_fn, forward);
        d.icongr(fnm1_fn, fn1, back, &|d, t| {
            let left = d.imul(a, t);
            d.iadd(left, b_folded)
        })
    };
    let a_final = d.imul(a, fn1);
    let after5 = d.iadd(a_final, b_folded);

    // fib n + fib(n+1) = fib(n+2)
    let l6 = {
        let step = fib_step(d, n); // fib(n+2) = fib(n+1) + fib n
        let fn1_fn = d.iadd(fn1, fn_);
        let comm = d.lemma(p.add_comm, &[fn_, fn1]);
        let back = d.isymm(fn2, fn1_fn, step);
        let forward = d.itrans(fn_fn1, fn1_fn, fn2, comm, back);
        d.icongr(fn_fn1, fn2, forward, &|d, t| {
            let right = d.imul(b, t);
            d.iadd(a_final, right)
        })
    };
    let b_final = d.imul(b, fn2);
    let after6 = d.iadd(a_final, b_final);

    let l7 = d.isymm(f_m_n1, after6, hq);

    let (_, left_chain) = d.ichain(
        left_start,
        &[
            (after1, l1),
            (after2, l2),
            (after3, l3),
            (after4, l4),
            (after5, l5),
            (after6, l6),
            (f_m_n1, l7),
        ],
    );

    // Cancel `fib(m+n)` from both sides.
    let joined = {
        let back = d.isymm(right_start, f_m_n1, right_chain);
        d.itrans(left_start, f_m_n1, right_start, left_chain, back)
    };
    let cancelled = add_right_cancel(d, target_rhs, f_m_nm1, f_m_n, joined);
    let flipped = d.isymm(target_rhs, f_m_nm1, cancelled);

    // Restate `fib n` as `fib ((n-1)+1)`, the spelling `P (n-1)` uses.
    let f_nm1_one = fibt(d, nm1_one);
    let restated = {
        let to_fn = fib_congr(d, nm1_one, n, cancel);
        let back = d.isymm(f_nm1_one, fn_, to_fn);
        d.icongr(fn_, f_nm1_one, back, &|d, t| {
            let right = d.imul(b, t);
            d.iadd(a_nm1, right)
        })
    };
    let goal_rhs = {
        let right = d.imul(b, f_nm1_one);
        d.iadd(a_nm1, right)
    };
    let at_nm1_proof = d.itrans(f_m_nm1, target_rhs, goal_rhs, flipped, restated);

    // The second component of `Q (n-1)` is `P ((n-1)+1)`, which is `P n`
    // transported along `(n-1)+1 = n` -- NOT definitionally the same index.
    let at_nm1_plus_one = {
        let back = d.isymm(nm1_one, n, cancel);
        d.int_eq_rewrite(n, nm1_one, back, hp, &|d, t| fib_add_stmt(d, m, t))
    };

    let at_nm1 = fib_add_stmt(d, m, nm1);
    let at_nm1_next = fib_add_stmt(d, m, nm1_one);
    let intro = d.int().logic.and_intro;
    let pair = d.const_app(intro, &[at_nm1, at_nm1_next, at_nm1_proof, at_nm1_plus_one]);
    let inner = d.lam_fv(h_fv, hyp_ty, pair);
    d.lam_fv(n_fv, int_ty, inner)
}

// ============================================================================
// The subtraction bridge: `Int.fib_two_mul` and `Int.fib_two_mul_add_two`
// need `Int.fib_rec`'s recurrence turned into a difference (`fib(n-1) =
// fib(n+1) - fib n`), and every other addition-formula proof in this file
// deliberately stays inside `add`/`mul` and never forms one. This is the
// first place that changes.
// ============================================================================

/// `h : Eq Int (add a b) c  ⊢  Eq Int b (sub c a)` — `eq_sub_of_add_eq_left`.
///
/// From `a + b = c` derive `b = c - a`. The mirror image of
/// [`add_right_cancel`] (which needs the SAME addend on both sides to
/// cancel, and concludes an equation between the two remaining terms); this
/// needs only one occurrence of `a` and concludes a DIFFERENCE. There is no
/// `eq_sub_of_add_eq`-shaped lemma anywhere in `int_prelude/` (`eq_add_sub`
/// in `modeq.rs` is a different identity, `x + (y-x) = y`, private to that
/// module and built for a different purpose).
///
/// Route: commute `a+b` to `b+a` (so `h`, transported, reads `b+a = c`);
/// `add_neg_cancel_right b a : (b+a)+(-a) = b`; substituting `c` for `b+a`
/// gives `c+(-a) = b`, i.e. (folding `Int.sub`) `sub c a = b`; flip.
fn eq_sub_of_add_eq_left(d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let ab = d.iadd(a, b);
    let ba = d.iadd(b, a);
    let comm = d.lemma(p.add_comm, &[a, b]); // Eq(add a b, add b a)
    let comm_rev = d.isymm(ab, ba, comm); // Eq(add b a, add a b)
    let h_ba = d.itrans(ba, ab, c, comm_rev, h); // Eq(add b a, c)

    let neg_a = d.ineg(a);
    let cancel = d.lemma(p.add_neg_cancel_right, &[b, a]); // Eq((b+a)+(-a), b)
    let ba_neg_a = d.iadd(ba, neg_a);
    let c_neg_a = d.iadd(c, neg_a); // == sub c a, unfolded
    let congr_step = d.icongr(ba, c, h_ba, &|d, t| d.iadd(t, neg_a)); // Eq(ba_neg_a, c_neg_a)
    let back = d.isymm(ba_neg_a, b, cancel); // Eq(b, ba_neg_a)
    d.itrans(b, ba_neg_a, c_neg_a, back, congr_step) // Eq(b, sub c a)
}

/// `Eq Int (mul (ofNat 2) t) (add t t)` — `2*t = t+t`. There is no
/// `right_distrib` in this prelude (`left_distrib` only), so this goes
/// through `mul_comm` first: `2*t = t*2 = t*(1+1) = t*1+t*1 = t+t`. The
/// `2 ≡ 1+1` step is a pure reduction (`Int.add` on two `ofNat`s, the trick
/// `plus_two_spelling` already uses), not a named lemma.
fn mul_two_eq_add_self(d: &mut IntDev<'_>, t: ExprId) -> ExprId {
    let p = d.int();
    let two_nat = d.num(2);
    let two = d.of_nat(two_nat);
    let t_two_l = d.imul(two, t);
    let t_two_r = d.imul(t, two);
    let comm = d.lemma(p.mul_comm, &[two, t]); // Eq(mul two t, mul t two)

    let one = d.ione();
    let dist = d.lemma(p.left_distrib, &[t, one, one]);
    // dist's real type: Eq(mul t (add one one), add(mul t one)(mul t one));
    // `two` and `add one one` are defeq (both reduce to `ofNat 2`).
    let mt1 = d.imul(t, one);
    let sum_mt1 = d.iadd(mt1, mt1);

    let mo = d.lemma(p.mul_one, &[t]); // Eq(mul t one, t)
    let t_mt1 = d.iadd(t, mt1);
    let after_mo1 = d.icongr(mt1, t, mo, &|d, x| d.iadd(x, mt1)); // Eq(sum_mt1, t_mt1)
    let tt = d.iadd(t, t);
    let after_mo2 = d.icongr(mt1, t, mo, &|d, x| d.iadd(t, x)); // Eq(t_mt1, tt)

    let (_, chain) = d.ichain(
        t_two_l,
        &[
            (t_two_r, comm),
            (sum_mt1, dist),
            (t_mt1, after_mo1),
            (tt, after_mo2),
        ],
    );
    chain
}

/// `Eq Int (add (sub x y) x) (sub (add x x) y)` — `(x-y)+x = (x+x)-y`. Ring
/// rearrangement, unfolding `sub` and folding it back (the `sub.rs` idiom):
/// `(x+(-y))+x = x+(x+(-y))` (`add_comm`) `= (x+x)+(-y)` (`add_assoc`,
/// reversed).
fn add_sub_self_left(d: &mut IntDev<'_>, x: ExprId, y: ExprId) -> ExprId {
    let p = d.int();
    let neg_y = d.ineg(y);
    let x_negy = d.iadd(x, neg_y); // sub x y, unfolded
    let start = d.iadd(x_negy, x);

    let x_x_negy = d.iadd(x, x_negy);
    let s1 = d.lemma(p.add_comm, &[x_negy, x]); // Eq(add x_negy x, add x x_negy)

    let xx = d.iadd(x, x);
    let xx_negy = d.iadd(xx, neg_y);
    let assoc = d.lemma(p.add_assoc, &[x, x, neg_y]); // Eq((x+x)+(-y), x+(x+(-y)))
    let s2 = d.isymm(xx_negy, x_x_negy, assoc);

    let (_, chain) = d.ichain(start, &[(x_x_negy, s1), (xx_negy, s2)]);
    chain
}

/// `Eq Int (add p (add q p)) (add (add p p) q)` — `p+(q+p) = (p+p)+q`.
/// Another ring rearrangement of the same flavour as [`add_sub_self_left`]:
/// `p+(q+p) = p+(p+q)` (`add_comm`) `= (p+p)+q` (`add_assoc`, reversed).
fn add_p_qp_eq_pp_q(d: &mut IntDev<'_>, p_: ExprId, q_: ExprId) -> ExprId {
    let p = d.int();
    let qp = d.iadd(q_, p_);
    let start = d.iadd(p_, qp);

    let pq = d.iadd(p_, q_);
    let p_pq = d.iadd(p_, pq);
    let s1 = {
        let comm = d.lemma(p.add_comm, &[q_, p_]); // Eq(add q_ p_, add p_ q_)
        d.icongr(qp, pq, comm, &|d, t| d.iadd(p_, t))
    };

    let pp = d.iadd(p_, p_);
    let pp_q = d.iadd(pp, q_);
    let s2 = {
        let assoc = d.lemma(p.add_assoc, &[p_, p_, q_]); // Eq((p+p)+q, p+(p+q))
        d.isymm(pp_q, p_pq, assoc)
    };

    let (_, chain) = d.ichain(start, &[(p_pq, s1), (pp_q, s2)]);
    chain
}

/// `Eq Int (fib (add (sub k one) two)) (fib (add k one))` — the index bridge
/// `(k-1)+2 = k+1`, lifted through `fib`. Same `add_assoc` computation
/// [`declare_fib_add`]'s `P 1` base case uses inline (there at `m`, generic
/// here), extracted because [`fib_pred_eq_sub`] needs it too.
fn fib_shift_minus_one_plus_two(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let p = d.int();
    let one = d.ione();
    let neg_one = d.ineg(one);
    let two_nat = d.num(2);
    let two = d.of_nat(two_nat);
    let k_minus = d.isub(k, one);
    let kk_two = d.iadd(k_minus, two);
    let idx_two = d.lemma(p.add_assoc, &[k, neg_one, two]); // Eq((k+(-1))+2, k+((-1)+2))
    let k_one = d.iadd(k, one);
    fib_congr(d, kk_two, k_one, idx_two)
}

/// `Eq Int (fib (sub k one)) (sub (fib (add k one)) (fib k))` — `fib(k-1) =
/// fib(k+1) - fib(k)`, the recurrence read as a subtraction. Built from
/// [`declare_fib_rec`] at `k-1` (which gives `fib((k-1)+2) = fib((k-1)+1) +
/// fib(k-1)`), the two index bridges [`fib_shift_minus_one_plus_two`] and
/// [`sub_add_cancel`] (already built for [`declare_fib_add`]: `(k-1)+1 =
/// k`), and [`eq_sub_of_add_eq_left`] to turn the resulting addition into
/// the difference both `fib_two_mul*` statements are stated with.
fn fib_pred_eq_sub(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let p = d.int();
    let one = d.ione();
    let two_nat = d.num(2);
    let two = d.of_nat(two_nat);
    let k_minus = d.isub(k, one);

    let rec_at = d.lemma(p.fib_rec, &[k_minus]);
    // rec_at : Eq(fib((k-1)+2), add(fib((k-1)+1), fib(k-1)))
    let kk2 = d.iadd(k_minus, two);
    let kk1 = d.iadd(k_minus, one);
    let f_kk2 = fibt(d, kk2);
    let f_kk1 = fibt(d, kk1);
    let f_km1 = fibt(d, k_minus);
    let rec_rhs = d.iadd(f_kk1, f_km1);

    let k_one = d.iadd(k, one);
    let f_k1 = fibt(d, k_one);
    let bridge_two = fib_shift_minus_one_plus_two(d, k); // Eq(f_kk2, f_k1)
    let back_two = d.isymm(f_kk2, f_k1, bridge_two); // Eq(f_k1, f_kk2)

    let f_k = fibt(d, k);
    let cancel_k1 = sub_add_cancel(d, k); // Eq(kk1, k)
    let bridge_one = fib_congr(d, kk1, k, cancel_k1); // Eq(f_kk1, f_k)
    let sum_after = d.iadd(f_k, f_km1);
    let lift_sum = d.icongr(f_kk1, f_k, bridge_one, &|d, t| d.iadd(t, f_km1)); // Eq(rec_rhs, sum_after)

    let (_, forward) = d.ichain(
        f_k1,
        &[(f_kk2, back_two), (rec_rhs, rec_at), (sum_after, lift_sum)],
    );
    // forward : Eq(f_k1, add f_k f_km1)
    let h_ba = d.isymm(f_k1, sum_after, forward); // Eq(add f_k f_km1, f_k1)
    eq_sub_of_add_eq_left(d, f_k, f_km1, f_k1, h_ba)
    // result : Eq(f_km1, sub f_k1 f_k), i.e. fib(k-1) = fib(k+1) - fib(k)
}

// ============================================================================
// `Int.fib_two_mul` : `fib (2*n) = fib n * (2*fib(n+1) - fib n)`.
// ============================================================================

/// The statement, at a given `n`.
fn fib_two_mul_stmt(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let two_nat = d.num(2);
    let two = d.of_nat(two_nat);
    let idx = d.imul(two, n);
    let lhs = fibt(d, idx);

    let one = d.ione();
    let n1 = d.iadd(n, one);
    let a = fibt(d, n);
    let bp1 = fibt(d, n1);
    let two_bp1 = d.imul(two, bp1);
    let inner = d.isub(two_bp1, a);
    let rhs = d.imul(a, inner);
    d.ieq(lhs, rhs)
}

/// `Int.fib_two_mul : ∀ n, Eq Int (fib (mul two n)) (mul (fib n)
/// (sub (mul two (fib (add n one))) (fib n)))` — Mathlib's `Int.fib_two_mul`.
///
/// No induction: [`declare_fib_add`] at `(n, n)` already gives
/// `fib(n+n) = fib(n-1)*fib n + fib n*fib(n+1)`; [`fib_pred_eq_sub`]
/// rewrites the `fib(n-1)` factor as `fib(n+1) - fib n`; the rest is ring
/// algebra (`mul_comm`, `Int.mul_sub`, `left_distrib`,
/// [`add_sub_self_left`], [`mul_two_eq_add_self`]) to fold the result into
/// the `2*fib(n+1) - fib n` shape the statement names, plus
/// [`mul_two_eq_add_self`] again to bridge the index `2*n` to `n+n`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_fib_two_mul(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.fib_two_mul, 1, &|d, v| {
        let n = v[0];
        let stmt = fib_two_mul_stmt(d, n);

        let one = d.ione();
        let two_nat = d.num(2);
        let two = d.of_nat(two_nat);
        let a = fibt(d, n);
        let n1 = d.iadd(n, one);
        let bp1 = fibt(d, n1);
        let n_minus = d.isub(n, one);
        let bm1 = fibt(d, n_minus);
        let idx_nn = d.iadd(n, n);
        let f_nn = fibt(d, idx_nn);

        // Step 1: `Int.fib_add n n`.
        let h1 = d.lemma(p.fib_add, &[n, n]);
        let mul_bm1_a = d.imul(bm1, a);
        let mul_a_bp1 = d.imul(a, bp1);
        let h1_rhs = d.iadd(mul_bm1_a, mul_a_bp1);

        // Step 2/3: substitute `fib(n-1) = fib(n+1) - fib n`.
        let hc = fib_pred_eq_sub(d, n); // Eq(bm1, sub bp1 a)
        let sub_bp1_a = d.isub(bp1, a);
        let mul_sub_a = d.imul(sub_bp1_a, a);
        let sub_lift = d.icongr(bm1, sub_bp1_a, hc, &|d, t| d.imul(t, a)); // Eq(mul_bm1_a, mul_sub_a)
        let h2_rhs = d.iadd(mul_sub_a, mul_a_bp1);
        let lift_add = d.icongr(mul_bm1_a, mul_sub_a, sub_lift, &|d, t| d.iadd(t, mul_a_bp1));
        let h2 = d.itrans(f_nn, h1_rhs, h2_rhs, h1, lift_add);

        // Step 4: `mul (sub bp1 a) a = mul a (sub bp1 a) = sub (mul a bp1) (mul a a)`.
        let x1 = mul_a_bp1;
        let y1 = d.imul(a, a);
        let mul_a_sub = d.imul(a, sub_bp1_a);
        let comm1 = d.lemma(p.mul_comm, &[sub_bp1_a, a]); // Eq(mul_sub_a, mul_a_sub)
        let sub_x1_y1 = d.isub(x1, y1);
        let mulsub1 = d.lemma(p.mul_sub, &[a, bp1, a]); // Eq(mul_a_sub, sub_x1_y1)
        let (_, step4) = d.ichain(mul_sub_a, &[(mul_a_sub, comm1), (sub_x1_y1, mulsub1)]);
        let h3_rhs = d.iadd(sub_x1_y1, x1);
        let lift4 = d.icongr(mul_sub_a, sub_x1_y1, step4, &|d, t| d.iadd(t, x1));
        let h3 = d.itrans(f_nn, h2_rhs, h3_rhs, h2, lift4);

        // Step 5: `add (sub x1 y1) x1 = sub (add x1 x1) y1`.
        let step5 = add_sub_self_left(d, x1, y1);
        let add_x1x1 = d.iadd(x1, x1);
        let h4_rhs = d.isub(add_x1x1, y1);
        let h4 = d.itrans(f_nn, h3_rhs, h4_rhs, h3, step5);

        // Step 6: `add x1 x1 = mul a (mul two bp1)`.
        let add_bp1bp1 = d.iadd(bp1, bp1);
        let mul_a_addbp1bp1 = d.imul(a, add_bp1bp1);
        let ld1 = d.lemma(p.left_distrib, &[a, bp1, bp1]); // Eq(mul_a_addbp1bp1, add_x1x1)
        let s1 = d.isymm(mul_a_addbp1bp1, add_x1x1, ld1);
        let mts = mul_two_eq_add_self(d, bp1); // Eq(mul two bp1, add_bp1bp1)
        let mul_two_bp1 = d.imul(two, bp1);
        let mts_back = d.isymm(mul_two_bp1, add_bp1bp1, mts); // Eq(add_bp1bp1, mul_two_bp1)
        let mul_a_2bp1 = d.imul(a, mul_two_bp1);
        let s2 = d.icongr(add_bp1bp1, mul_two_bp1, mts_back, &|d, t| d.imul(a, t));
        let (_, step6) = d.ichain(add_x1x1, &[(mul_a_addbp1bp1, s1), (mul_a_2bp1, s2)]);
        let h5_rhs = d.isub(mul_a_2bp1, y1);
        let lift6 = d.icongr(add_x1x1, mul_a_2bp1, step6, &|d, t| d.isub(t, y1));
        let h5 = d.itrans(f_nn, h4_rhs, h5_rhs, h4, lift6);

        // Step 7: fold back via `mul_sub`.
        let sub_2bp1_a = d.isub(mul_two_bp1, a);
        let mul_a_final = d.imul(a, sub_2bp1_a);
        let mulsub2 = d.lemma(p.mul_sub, &[a, mul_two_bp1, a]); // Eq(mul_a_final, h5_rhs)
        let step7 = d.isymm(mul_a_final, h5_rhs, mulsub2);
        let h6 = d.itrans(f_nn, h5_rhs, mul_a_final, h5, step7);

        // Step 8: bridge `fib (mul two n)` to `fib (add n n)`.
        let bridge0 = mul_two_eq_add_self(d, n); // Eq(mul two n, add n n)
        let mul_two_n = d.imul(two, n);
        let fib_idx = fibt(d, mul_two_n);
        let bridge0_fib = fib_congr(d, mul_two_n, idx_nn, bridge0); // Eq(fib_idx, f_nn)
        let final_proof = d.itrans(fib_idx, f_nn, mul_a_final, bridge0_fib, h6);

        (stmt, final_proof)
    })?;
    Ok(())
}

// ============================================================================
// `Int.fib_two_mul_add_two` : `fib (2*n+2) = fib(n+1) * (2*fib n + fib(n+1))`.
// ============================================================================

/// The statement, at a given `n`.
fn fib_two_mul_add_two_stmt(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let two_nat = d.num(2);
    let two = d.of_nat(two_nat);
    let mul_two_n = d.imul(two, n);
    let idx = d.iadd(mul_two_n, two);
    let lhs = fibt(d, idx);

    let one = d.ione();
    let n1 = d.iadd(n, one);
    let a = fibt(d, n);
    let bp1 = fibt(d, n1);
    let two_a = d.imul(two, a);
    let inner = d.iadd(two_a, bp1);
    let rhs = d.imul(bp1, inner);
    d.ieq(lhs, rhs)
}

/// `Int.fib_two_mul_add_two : ∀ n, Eq Int (fib (add (mul two n) two))
/// (mul (fib (add n one)) (add (mul two (fib n)) (fib (add n one))))` —
/// Mathlib's `Int.fib_two_mul_add_two`.
///
/// Same shape of proof as [`declare_fib_two_mul`], one index up:
/// [`declare_fib_add`] at `(n+1, n+1)` gives `fib((n+1)+(n+1)) =
/// fib n * fib(n+1) + fib(n+1) * fib(n+2)`, [`declare_fib_rec`] at `n`
/// rewrites `fib(n+2)` as `fib(n+1) + fib n` (an ADDITION this time, not a
/// subtraction — [`fib_pred_eq_sub`] is not needed here), and the rest is
/// the same ring algebra plus [`add_p_qp_eq_pp_q`] (the addition-side
/// analogue of [`add_sub_self_left`]) to reach the
/// `fib(n+1)*(2*fib n + fib(n+1))` shape, plus index bridges for
/// `(n+1)-1 = n`, `(n+1)+1 = n+2` (`Int.add_neg_cancel_right`,
/// [`plus_two_spelling`]) and `(n+1)+(n+1) = 2n+2` ([`add_regroup_four`]).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_fib_two_mul_add_two(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.fib_two_mul_add_two, 1, &|d, v| {
        let n = v[0];
        let stmt = fib_two_mul_add_two_stmt(d, n);

        let one = d.ione();
        let two_nat = d.num(2);
        let two = d.of_nat(two_nat);
        let a = fibt(d, n);
        let n1 = d.iadd(n, one);
        let bp1 = fibt(d, n1);
        let n1_1 = d.iadd(n1, n1);
        let f_n1n1 = fibt(d, n1_1);

        // Step 1: `Int.fib_add (n+1) (n+1)`, then bridge both index shifts.
        let h1 = d.lemma(p.fib_add, &[n1, n1]);
        let n1_minus = d.isub(n1, one);
        let f_n1_minus = fibt(d, n1_minus);
        let n1_plus = d.iadd(n1, one);
        let f_n1_plus = fibt(d, n1_plus);
        let mul_fn1m_bp1 = d.imul(f_n1_minus, bp1);
        let mul_bp1_fn1p = d.imul(bp1, f_n1_plus);
        let h1_rhs = d.iadd(mul_fn1m_bp1, mul_bp1_fn1p);

        // Bridge `(n+1)-1 = n`.
        let cancel_a = d.lemma(p.add_neg_cancel_right, &[n, one]); // Eq((n+1)+(-1), n) ~ Eq(n1_minus, n)
        let bridge_a = fib_congr(d, n1_minus, n, cancel_a); // Eq(f_n1_minus, a)
        let mul_a_bp1 = d.imul(a, bp1);
        let lift_a = d.icongr(f_n1_minus, a, bridge_a, &|d, t| d.imul(t, bp1)); // Eq(mul_fn1m_bp1, mul_a_bp1)

        // Bridge `(n+1)+1 = n+2`.
        let n_two = d.iadd(n, two);
        let f_n2 = fibt(d, n_two);
        let plus_two = plus_two_spelling(d, n); // Eq(n1_plus, n_two) [via defeq (1+1)=two]
        let bridge_b = fib_congr(d, n1_plus, n_two, plus_two); // Eq(f_n1_plus, f_n2)
        let mul_bp1_fn2 = d.imul(bp1, f_n2);
        let lift_b = d.icongr(f_n1_plus, f_n2, bridge_b, &|d, t| d.imul(bp1, t)); // Eq(mul_bp1_fn1p, mul_bp1_fn2)

        let mid_rhs = d.iadd(mul_a_bp1, mul_bp1_fn1p);
        let step_a = d.icongr(mul_fn1m_bp1, mul_a_bp1, lift_a, &|d, t| {
            d.iadd(t, mul_bp1_fn1p)
        });
        let h2_rhs = d.iadd(mul_a_bp1, mul_bp1_fn2);
        let step_b = d.icongr(mul_bp1_fn1p, mul_bp1_fn2, lift_b, &|d, t| {
            d.iadd(mul_a_bp1, t)
        });
        let (_, subst) = d.ichain(h1_rhs, &[(mid_rhs, step_a), (h2_rhs, step_b)]);
        let h2 = d.itrans(f_n1n1, h1_rhs, h2_rhs, h1, subst);

        // Step 2: `fib_rec n` rewrites `fib(n+2) = fib(n+1) + fib n`.
        let rec_n = d.lemma(p.fib_rec, &[n]); // Eq(f_n2, add bp1 a)
        let add_bp1_a = d.iadd(bp1, a);
        let mul_bp1_addbp1a = d.imul(bp1, add_bp1_a);
        let lift_rec = d.icongr(f_n2, add_bp1_a, rec_n, &|d, t| d.imul(bp1, t)); // Eq(mul_bp1_fn2, mul_bp1_addbp1a)
        let h3_rhs = d.iadd(mul_a_bp1, mul_bp1_addbp1a);
        let lift_rec_add = d.icongr(mul_bp1_fn2, mul_bp1_addbp1a, lift_rec, &|d, t| {
            d.iadd(mul_a_bp1, t)
        });
        let h3 = d.itrans(f_n1n1, h2_rhs, h3_rhs, h2, lift_rec_add);

        // Step 3: `mul bp1 (add bp1 a) = add (mul bp1 bp1) (mul bp1 a)`.
        let q_ = d.imul(bp1, bp1);
        let p_prime = d.imul(bp1, a); // "P'" = mul bp1 a
        let dist1 = d.lemma(p.left_distrib, &[bp1, bp1, a]); // Eq(mul_bp1_addbp1a, add q_ p_prime)
        let sum_q_pprime = d.iadd(q_, p_prime);
        let h4_rhs = d.iadd(mul_a_bp1, sum_q_pprime);
        let lift_dist = d.icongr(mul_bp1_addbp1a, sum_q_pprime, dist1, &|d, t| {
            d.iadd(mul_a_bp1, t)
        });
        let h4 = d.itrans(f_n1n1, h3_rhs, h4_rhs, h3, lift_dist);

        // Step 4: convert `P' = mul bp1 a` to `P = mul a bp1` (commute) inside the inner sum.
        let p_ = mul_a_bp1; // "P" = mul a bp1
        let comm_p = d.lemma(p.mul_comm, &[bp1, a]); // Eq(p_prime, p_)
        let sum_q_p = d.iadd(q_, p_);
        let lift_comm = d.icongr(p_prime, p_, comm_p, &|d, t| d.iadd(q_, t)); // Eq(sum_q_pprime, sum_q_p)
        let h5_rhs = d.iadd(p_, sum_q_p);
        let lift_comm_outer = d.icongr(sum_q_pprime, sum_q_p, lift_comm, &|d, t| d.iadd(p_, t));
        let h5 = d.itrans(f_n1n1, h4_rhs, h5_rhs, h4, lift_comm_outer);

        // Step 5: `add p_ (add q_ p_) = add (add p_ p_) q_`.
        let step5 = add_p_qp_eq_pp_q(d, p_, q_);
        let pp = d.iadd(p_, p_);
        let h6_rhs = d.iadd(pp, q_);
        let h6 = d.itrans(f_n1n1, h5_rhs, h6_rhs, h5, step5);

        // Step 6: `add p_ p_ = mul bp1 (mul two a)`.
        let add_a_a = d.iadd(a, a);
        let mul_bp1_addaa = d.imul(bp1, add_a_a);
        let symm_comm_p = d.isymm(p_prime, p_, comm_p); // Eq(p_, p_prime)
        let p_prime_p = d.iadd(p_prime, p_);
        let sa = d.icongr(p_, p_prime, symm_comm_p, &|d, t| d.iadd(t, p_)); // Eq(pp, p_prime_p)
        let p_prime_p_prime = d.iadd(p_prime, p_prime);
        let sb = d.icongr(p_, p_prime, symm_comm_p, &|d, t| d.iadd(p_prime, t)); // Eq(p_prime_p, p_prime_p_prime)
        let dist2 = d.lemma(p.left_distrib, &[bp1, a, a]); // Eq(mul_bp1_addaa, p_prime_p_prime)
        let dist2_back = d.isymm(mul_bp1_addaa, p_prime_p_prime, dist2);
        let (_, pp_to_mul) = d.ichain(
            pp,
            &[
                (p_prime_p, sa),
                (p_prime_p_prime, sb),
                (mul_bp1_addaa, dist2_back),
            ],
        );

        let mts = mul_two_eq_add_self(d, a); // Eq(mul two a, add_a_a)
        let mul_two_a = d.imul(two, a);
        let mts_back = d.isymm(mul_two_a, add_a_a, mts); // Eq(add_a_a, mul_two_a)
        let mul_bp1_2a = d.imul(bp1, mul_two_a);
        let sc = d.icongr(add_a_a, mul_two_a, mts_back, &|d, t| d.imul(bp1, t)); // Eq(mul_bp1_addaa, mul_bp1_2a)
        let (_, step6) = d.ichain(pp, &[(mul_bp1_addaa, pp_to_mul), (mul_bp1_2a, sc)]);
        let h7_rhs = d.iadd(mul_bp1_2a, q_);
        let lift7 = d.icongr(pp, mul_bp1_2a, step6, &|d, t| d.iadd(t, q_));
        let h7 = d.itrans(f_n1n1, h6_rhs, h7_rhs, h6, lift7);

        // Step 7: fold back via `left_distrib`, reversed.
        let two_a_bp1 = d.iadd(mul_two_a, bp1);
        let mul_bp1_final = d.imul(bp1, two_a_bp1);
        let dist3 = d.lemma(p.left_distrib, &[bp1, mul_two_a, bp1]); // Eq(mul_bp1_final, add mul_bp1_2a q_)
        let step7 = d.isymm(mul_bp1_final, h7_rhs, dist3);
        let h8 = d.itrans(f_n1n1, h7_rhs, mul_bp1_final, h7, step7);

        // Step 8: bridge `(n+1)+(n+1)` to `2*n+2`.
        let regroup = add_regroup_four(d, n, one, n, one);
        // regroup : Eq((n+one)+(n+one), (n+n)+(one+one)) ~ Eq(n1_1, (n+n)+two)
        let nn = d.iadd(n, n);
        let nn_two = d.iadd(nn, two);
        let mul_two_n = d.imul(two, n);
        let mts_n = mul_two_eq_add_self(d, n); // Eq(mul_two_n, nn)
        let nn_to_mtn = d.isymm(mul_two_n, nn, mts_n); // Eq(nn, mul_two_n)
        let mtn_two = d.iadd(mul_two_n, two);
        let lift_nn = d.icongr(nn, mul_two_n, nn_to_mtn, &|d, t| d.iadd(t, two)); // Eq(nn_two, mtn_two)
        let (_, idx_chain) = d.ichain(n1_1, &[(nn_two, regroup), (mtn_two, lift_nn)]);
        let f_idx = fibt(d, mtn_two);
        let idx_fib = fib_congr(d, n1_1, mtn_two, idx_chain); // Eq(f_n1n1, f_idx)
        let idx_fib_back = d.isymm(f_n1n1, f_idx, idx_fib); // Eq(f_idx, f_n1n1)
        let final_proof = d.itrans(f_idx, f_n1n1, mul_bp1_final, idx_fib_back, h8);

        (stmt, final_proof)
    })?;
    Ok(())
}

// ============================================================================
// Base case theorems: `fib 0 = 0`, `fib 1 = 1`, `fib 2 = 1`,
// `fib (-1) = 1`, `fib (-2) = -1`.
//
// These reduce by definition: `Int.fib` for `ofNat n` returns `ofNat
// (Nat.fib n)`, and for `negSucc m` returns `pow (neg one) m * ofNat
// (Nat.fib (succ m))`. The `Nat.fib` base cases reduce (Nat.fib 0 = 0,
// Nat.fib 1 = 1, Nat.fib 2 = 1), and `pow (neg one) 0 = 1` reduces. So
// all five goals reduce PURELY to closed-term arithmetic on numerals.
// ============================================================================

/// `Int.fib_zero : Eq Int (fib 0) 0` — `fib 0` reduces to
/// `ofNat (Nat.fib 0) = ofNat 0 = 0` by definition.
pub(super) fn declare_fib_zero(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let zero = d.izero();
    let fib_zero = d.const_app(p.fib, &[zero]);
    d.int_theorem(p.fib_zero, 0, &|d, _v| {
        let stmt = d.ieq(fib_zero, zero);
        let proof = d.irefl(fib_zero);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.fib_one : Eq Int (fib 1) 1` — `fib 1` reduces to
/// `ofNat (Nat.fib 1) = ofNat 1 = 1` by definition.
pub(super) fn declare_fib_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let one_nat = d.num(1);
    let one_i = d.of_nat(one_nat);
    let fib_one = d.const_app(p.fib, &[one_i]);
    d.int_theorem(p.fib_one, 0, &|d, _v| {
        let stmt = d.ieq(fib_one, one_i);
        let proof = d.irefl(fib_one);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.fib_two : Eq Int (fib 2) 1` — `fib 2` reduces to
/// `ofNat (Nat.fib 2) = ofNat 1 = 1` by definition.
pub(super) fn declare_fib_two(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let two_nat = d.num(2);
    let two_i = d.of_nat(two_nat);
    let one_nat = d.num(1);
    let one_i = d.of_nat(one_nat);
    let fib_two = d.const_app(p.fib, &[two_i]);
    d.int_theorem(p.fib_two, 0, &|d, _v| {
        let stmt = d.ieq(fib_two, one_i);
        let proof = d.irefl(fib_two);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.fib_neg_one : Eq Int (fib (-1)) 1` — `fib (-1)` reduces to
/// `pow (neg one) 0 * ofNat (Nat.fib 1) = 1 * 1 = 1` by definition.
pub(super) fn declare_fib_neg_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let one_nat = d.num(1);
    let one_i = d.of_nat(one_nat);
    let neg_one = d.ineg(one_i);
    let fib_neg_one = d.const_app(p.fib, &[neg_one]);
    d.int_theorem(p.fib_neg_one, 0, &|d, _v| {
        let stmt = d.ieq(fib_neg_one, one_i);
        let proof = d.irefl(fib_neg_one);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.fib_neg_two : Eq Int (fib (-2)) (-1)` — `fib (-2)` reduces to
/// `pow (neg one) 1 * ofNat (Nat.fib 2) = (-1) * 1 = -1` by definition.
pub(super) fn declare_fib_neg_two(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let two_nat = d.num(2);
    let two_i = d.of_nat(two_nat);
    let neg_two = d.ineg(two_i);
    let fib_neg_two = d.const_app(p.fib, &[neg_two]);
    let one_nat = d.num(1);
    let one_i = d.of_nat(one_nat);
    let neg_one = d.ineg(one_i);
    d.int_theorem(p.fib_neg_two, 0, &|d, _v| {
        let stmt = d.ieq(fib_neg_two, neg_one);
        let proof = d.irefl(fib_neg_two);
        (stmt, proof)
    })?;
    Ok(())
}
