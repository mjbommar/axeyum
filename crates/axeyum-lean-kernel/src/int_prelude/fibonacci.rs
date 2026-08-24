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
use super::ops::IntDev;
use crate::KernelError;
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
