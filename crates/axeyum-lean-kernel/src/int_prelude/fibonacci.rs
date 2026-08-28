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
fn pow_neg_one_succ(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
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
fn pow_neg_one_add_self(d: &mut IntDev<'_>, j: ExprId) -> ExprId {
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
                        let cast = d.nat_eq_to_int(rhs_nat, fib_sm, one_mul_pf, &|d, t| {
                            d.of_nat(t)
                        });
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
