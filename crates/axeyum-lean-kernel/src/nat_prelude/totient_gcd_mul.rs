//! `Nat.totient_gcd_mul_totient_mul` — the last of the three `ml430` totient
//! mirrors ADR-0668 names, and the largest: `∀ a b, φ(gcd a b) * φ(a*b) =
//! φ(a) * φ(b) * gcd a b`, the non-coprime generalization of
//! `Nat.totient_mul_of_coprime` (which is this identity at `gcd a b = 1`,
//! where it collapses to `φ(1)*φ(a*b) = φ(a)*φ(b)*1`).
//!
//! # Route: strong induction on `gcd(a,b)`, no multiset (ADR-0668)
//!
//! By well-founded induction on `d := gcd(a,b)` (`Nat.lt`, exactly the
//! `WellFounded.fix` machinery `totient_dvd_chain.rs`'s
//! `Nat.totient_dvd_totient_mul` already uses). The family is generalized
//! over the MEASURE rather than over `(a,b)` directly, since many pairs share
//! one gcd:
//!
//! ```text
//! Nat.totient_gcd_mul_aux : ∀ d a b, Eq (gcd a b) d →
//!   Eq (mul (totient d) (totient (mul a b))) (mul (mul (totient a) (totient b)) d)
//! ```
//!
//! - `d = 0`: forces `a = b = 0` is not even needed — both sides are `0`
//!   unconditionally (`Nat.zero_mul` on the left, iota on the right, since
//!   `mul` recurses on its RIGHT argument and `d`'s literal `0` is exactly
//!   that argument).
//! - `d = 1`: `gcd a b = 1` is coprimality itself, and the identity is
//!   `Nat.totient_mul_of_coprime` plus `mul_one`/`totient one = one` (the
//!   latter by pure reduction, like `totient_eq_one_iff`'s reverse
//!   direction).
//! - `d ≥ 2`: peel ONE prime `q ∣ d` (`Nat.exists_prime_dvd`, exactly
//!   `totient_dvd_chain.rs`'s peeling step). Since `q ∣ d ∣ a` and `q ∣ d ∣
//!   b`, write `a = q·a₁`, `b = q·b₁` (`Nat.dvd` elimination). By
//!   `Nat.gcd_mul_right`, `gcd(a,b) = q·gcd(a₁,b₁)`, so the new measure
//!   `g₁ := gcd(a₁,b₁)` is **strictly smaller** (`derive_cofactor_lt`, copied
//!   from `totient_dvd_chain.rs`'s private helper of the same name — this
//!   prelude's house style duplicates rather than shares such helpers), and
//!   the induction hypothesis applies at `(a₁, b₁)`.
//!
//!   The whole identity then reduces to a FOUR-LEAF case split on
//!   `[q ∣ a₁]`, `[q ∣ b₁]` (`Nat.coprime_or_dvd_of_prime` applied to each of
//!   `a₁`, `b₁` independently — **not** to `gcd(a₁,b₁)` or `a₁·b₁` directly;
//!   THEIR status is derived from `a₁`'s and `b₁`'s via `Nat.dvd_gcd` /
//!   `Nat.coprime_of_dvd_right` / `Nat.coprime_mul_of_coprime` / the two
//!   `dvd_mul_{left,right}_of_dvd` lemmas, never decided independently — an
//!   independent decision would need reconciling with the `a₁`/`b₁` split,
//!   which is exactly the reconciliation Euclid's lemma would supply and
//!   which this route avoids by never asking the question).
//!
//!   Euclid's lemma is NOT used: `q ∣ a₁·b₁` is derived directly from `q ∣
//!   a₁` or `q ∣ b₁` (one implication, not the disjunction `q ∣ a₁·b₁ → q∣a₁
//!   ∨ q∣b₁` Euclid supplies), and the leaf split is already exhaustive and
//!   mutually exclusive because it is literally the `coprime_or_dvd_of_prime`
//!   disjunction on `a₁` and on `b₁` — nothing needs reconciling. This is a
//!   narrower route than ADR-0668's own sketch (which reduces to an `ε`
//!   identity where Euclid IS load-bearing); both are correct, and this one
//!   needs one fewer number-theoretic input.
//!
//!   Per leaf, `Nat.totient_mul_of_dvd`/`Nat.totient_mul_of_coprime` give
//!   `φ(y·q) = φ(y)·M` for `y ∈ {g₁, a₁, b₁, a₁·b₁}` with `M ∈ {q, φ(q)}`
//!   decided by that leaf; substituting all four into the target and the
//!   induction hypothesis reduces it to a pure commutative-monoid
//!   rearrangement over six factors, checked by `assemble_gcd_mul_step`
//!   below. No factor multiset is ever named — the chain is built from
//!   **some** factorisation of `gcd(a,b)`, one prime at a time, exactly as
//!   ADR-0668 describes for the other two mirrors.
//!
//! # Numeric checks (re-executable)
//!
//! Every claim above — including that the leaf split is exhaustive and that
//! no case needs an independent decision on `gcd(a₁,b₁)` or `a₁·b₁` — is
//! covered by the pre-existing, re-run (not inherited) suite:
//!
//! ```text
//! python3 scripts/tests/check-totient-prime-power-numerics.py
//! ```
//!
//! Checks `8`, `8A`, `8N`, `8E`, `8EN`, `8G`, `8R` are this target's; `8N`
//! shows the identity is STRICTLY STRONGER than multiplicativity (53
//! non-coprime pairs with `1 ≤ a,b ≤ 12`), `8EN` shows the reduced `ε`
//! identity fails at 450 composite triples (Euclid load-bearing on ADR-0668's
//! sketch route; not consulted on this file's narrower route, which instead
//! leans on `coprime_or_dvd_of_prime` deciding `a₁`/`b₁` directly).
//!
//! # Magnitudes
//!
//! Every numeral this file forms is `0`, `1`, `2`, or a bound free variable;
//! nothing here evaluates a large `pow`/`mul` (see `totient_prime_pow.rs`'s
//! module doc for why that budget matters in this prelude).

use super::NatPrelude;
use super::binomial::mul_left_comm;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use super::steps::dvd_elim;
use super::steps::or_cases;
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// Local term builders and small private helpers (this prelude's
// per-file-copy convention; see `totient_dvd_chain.rs`, `dvd_mul_split.rs`
// for the originals these are copied from).
// ============================================================================

/// `(2 ≤ x) ∧ (∀ c, c ∣ x → c = 1 ∨ c = x)` — primality spelled inline,
/// matching `totient_dvd_chain.rs`/`totient_prime_pow.rs`/`factorization.rs`.
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

fn prime_ty(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let (two_le, divisor_clause) = prime_parts(d, p, x);
    d.const_app(p.logic.and, &[two_le, divisor_clause])
}

/// Copied verbatim from `totient_dvd_chain.rs`'s private helper of the same
/// name: from `heq : Eq n (mul pw q)`, `hp2 : Le two pw`, `hq1 : Le one q`,
/// derive `Lt q n`. `pw ≥ 2` gives `2*q ≤ pw*q = n`, and `2*q = q+q ≥ q+1 =
/// succ q` since `q ≥ 1`, so `succ q ≤ n`.
#[allow(clippy::too_many_arguments)]
fn derive_cofactor_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pw: ExprId,
    n: ExprId,
    q: ExprId,
    heq: ExprId,
    hp2: ExprId,
    hq1: ExprId,
) -> ExprId {
    let one_v = d.num(1);
    let two = d.num(2);

    let step_a = d.lemma(p.mul_le_mul_left, &[q, two, pw, hp2]);
    let mc1 = d.lemma(p.mul_comm, &[q, two]);
    let mc2 = d.lemma(p.mul_comm, &[q, pw]);

    let q_two = d.mul(q, two);
    let q_pw = d.mul(q, pw);
    let two_q = d.mul(two, q);
    let pw_q = d.mul(pw, q);

    let motive_l = d.eq_motive(q_two, &|d, x| d.le(x, q_pw));
    let step_b = d.transport(q_two, motive_l, step_a, two_q, mc1);

    let motive_r = d.eq_motive(q_pw, &|d, x| d.le(two_q, x));
    let step_c = d.transport(q_pw, motive_r, step_b, pw_q, mc2);

    let heq_sym = d.symm(n, pw_q, heq);
    let motive_n = d.eq_motive(pw_q, &|d, x| d.le(two_q, x));
    let step_d = d.transport(pw_q, motive_n, step_c, n, heq_sym);

    let sm = d.lemma(p.succ_mul, &[one_v, q]);
    let one_mul_q = d.lemma(p.one_mul, &[q]);
    let one_q = d.mul(one_v, q);
    let cong_add = d.congr(one_q, q, one_mul_q, &|d, x| d.add(x, q));
    let add_one_q_q = d.add(one_q, q);
    let q_q = d.add(q, q);
    let two_q_eq_add_qq = d.trans(two_q, add_one_q_q, q_q, sm, cong_add);

    let motive_e = d.eq_motive(two_q, &|d, x| d.le(x, n));
    let step_e = d.transport(two_q, motive_e, step_d, q_q, two_q_eq_add_qq);

    let al = d.lemma(p.add_le_add_left, &[q, one_v, q, hq1]);
    let succ_q = d.succ(q);
    d.lemma(p.le_trans, &[succ_q, q_q, n, al, step_e])
}

/// `Eq (mul (mul a b) (mul c dd)) (mul (mul a c) (mul b dd))` — the
/// four-factor regrouping this file's final assembly needs twice. Copied
/// from `dvd_mul_split.rs`'s private helper of the same name.
fn mul_mul_mul_comm(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
) -> ExprId {
    let p = *p;
    let ab = d.mul(a, b);
    let cd = d.mul(c, dd);
    let start = d.mul(ab, cd);

    let bcd = d.mul(b, cd);
    let step1 = d.lemma(p.mul_assoc, &[a, b, cd]);
    let a_bcd = d.mul(a, bcd);

    let bd = d.mul(b, dd);
    let cbd = d.mul(c, bd);
    let step2 = mul_left_comm(d, &p, b, c, dd);
    let congr2 = d.congr(bcd, cbd, step2, &|d, t| d.mul(a, t));
    let a_cbd = d.mul(a, cbd);

    let ac = d.mul(a, c);
    let target = d.mul(ac, bd);
    let step3 = d.lemma(p.mul_assoc, &[a, c, bd]);
    let step3_rev = d.symm(target, a_cbd, step3);

    let (_, proof) = d.chain(
        start,
        &[(a_bcd, step1), (a_cbd, congr2), (target, step3_rev)],
    );
    proof
}

/// `Eq (mul (mul a b) c) (mul (mul a c) b)` — swap the last two factors of a
/// three-factor product, first fixed. `mul_left_comm`'s companion (that one
/// swaps the first two, third fixed); not present elsewhere in this prelude.
fn mul_right_comm(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let p = *p;
    let ab = d.mul(a, b);
    let start = d.mul(ab, c);
    let bc = d.mul(b, c);
    let a_bc = d.mul(a, bc);
    let step1 = d.lemma(p.mul_assoc, &[a, b, c]); // ab_c = a_bc

    let cb = d.mul(c, b);
    let a_cb = d.mul(a, cb);
    let comm = d.lemma(p.mul_comm, &[b, c]); // bc = cb
    let step2 = d.congr(bc, cb, comm, &|d, t| d.mul(a, t)); // a_bc = a_cb

    let ac = d.mul(a, c);
    let target = d.mul(ac, b);
    let step3 = d.lemma(p.mul_assoc, &[a, c, b]); // ac_b = a_cb
    let step3_rev = d.symm(target, a_cb, step3); // a_cb = ac_b

    let (_, proof) = d.chain(start, &[(a_bc, step1), (a_cb, step2), (target, step3_rev)]);
    proof
}

/// Given `hcop_q_y : Eq (gcd q y) one`, derive `Eq (gcd y q) one` — the
/// `Nat.totient_mul_of_coprime` call sites in this file all want the
/// coprimality witness with the multiplicative "left" argument first, while
/// `Nat.coprime_or_dvd_of_prime` hands back the witness with `q` first.
/// Verbatim copy of `totient_dvd_totient_mul_prime`'s own flip (`gcd_comm`
/// plus `symm`/`trans`).
fn flip_coprime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    q: ExprId,
    y: ExprId,
    hcop_q_y: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let gcd_qy = d.gcd(q, y);
    let gcd_yq = d.gcd(y, q);
    let comm = d.lemma(p.gcd_comm, &[q, y]); // gcd q y = gcd y q
    let flipped = d.symm(gcd_qy, gcd_yq, comm); // gcd y q = gcd q y
    d.trans(gcd_yq, gcd_qy, one, flipped, hcop_q_y)
}

// ============================================================================
// The per-leaf assembly: given the four `totient (y*q) = totient y * M`
// equations (for y in {g1, a1, b1, z := a1*b1}) and the eps-identity `mul mg
// minner = mul ma mb`, close the goal for THIS (a,b) pair.
// ============================================================================

/// All the shared per-step context the four leaves need, computed once
/// before the `a1`/`b1` case split.
struct StepContext {
    q: ExprId,
    g1: ExprId,
    a1: ExprId,
    b1: ExprId,
    z: ExprId,
    a: ExprId,
    b: ExprId,
    kx: ExprId,
    heq_a: ExprId,      // Eq a (mul q a1)
    heq_b: ExprId,      // Eq b (mul q b1)
    kx_eq_q_g1: ExprId, // Eq kx (mul q g1)
    ih_at: ExprId, // Eq (mul (totient g1) (totient z)) (mul (mul (totient a1) (totient b1)) g1)
}

#[allow(clippy::too_many_arguments)]
fn assemble_gcd_mul_step(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    ctx: &StepContext,
    mg: ExprId,
    ma: ExprId,
    mb: ExprId,
    minner: ExprId,
    eq_g1_step: ExprId,   // Eq (totient (mul g1 q)) (mul (totient g1) mg)
    eq_a1_step: ExprId,   // Eq (totient (mul a1 q)) (mul (totient a1) ma)
    eq_b1_step: ExprId,   // Eq (totient (mul b1 q)) (mul (totient b1) mb)
    eq_z_step: ExprId,    // Eq (totient (mul z q)) (mul (totient z) minner)
    eps_identity: ExprId, // Eq (mul mg minner) (mul ma mb)
) -> ExprId {
    let p = *p;
    let StepContext {
        q,
        g1,
        a1,
        b1,
        z,
        a,
        b,
        kx,
        heq_a,
        heq_b,
        kx_eq_q_g1,
        ih_at,
    } = *ctx;

    let tot_g1 = d.const_app(p.totient, &[g1]);
    let tot_a1 = d.const_app(p.totient, &[a1]);
    let tot_b1 = d.const_app(p.totient, &[b1]);
    let tot_z = d.const_app(p.totient, &[z]);
    let tot_kx = d.const_app(p.totient, &[kx]);
    let tot_a = d.const_app(p.totient, &[a]);
    let tot_b = d.const_app(p.totient, &[b]);
    let mul_a_b0 = d.mul(a, b);
    let tot_ab = d.const_app(p.totient, &[mul_a_b0]);

    // --- totient(kx) = mul (totient g1) mg ---------------------------------
    let mul_comm_qg1 = d.lemma(p.mul_comm, &[q, g1]); // mul q g1 = mul g1 q
    let mul_g1_q = d.mul(g1, q);
    let mul_q_g1 = d.mul(q, g1);
    let kx_eq_g1q = d.trans(kx, mul_q_g1, mul_g1_q, kx_eq_q_g1, mul_comm_qg1);
    let tot_kx_eq1 = d.congr(kx, mul_g1_q, kx_eq_g1q, &|d, t| {
        d.const_app(p.totient, &[t])
    });
    let mg_tg1 = d.mul(tot_g1, mg);
    let tot_mul_g1_q = d.const_app(p.totient, &[mul_g1_q]);
    let tot_kx_final = d.trans(tot_kx, tot_mul_g1_q, mg_tg1, tot_kx_eq1, eq_g1_step);

    // --- totient(a) = mul (totient a1) ma -----------------------------------
    let mul_comm_qa1 = d.lemma(p.mul_comm, &[q, a1]);
    let mul_a1_q = d.mul(a1, q);
    let mul_q_a1 = d.mul(q, a1);
    let heq_a_comm = d.trans(a, mul_q_a1, mul_a1_q, heq_a, mul_comm_qa1);
    let tot_a_eq1 = d.congr(a, mul_a1_q, heq_a_comm, &|d, t| {
        d.const_app(p.totient, &[t])
    });
    let ma_ta1 = d.mul(tot_a1, ma);
    let tot_mul_a1_q = d.const_app(p.totient, &[mul_a1_q]);
    let tot_a_final = d.trans(tot_a, tot_mul_a1_q, ma_ta1, tot_a_eq1, eq_a1_step);

    // --- totient(b) = mul (totient b1) mb -----------------------------------
    let mul_comm_qb1 = d.lemma(p.mul_comm, &[q, b1]);
    let mul_b1_q = d.mul(b1, q);
    let mul_q_b1 = d.mul(q, b1);
    let heq_b_comm = d.trans(b, mul_q_b1, mul_b1_q, heq_b, mul_comm_qb1);
    let tot_b_eq1 = d.congr(b, mul_b1_q, heq_b_comm, &|d, t| {
        d.const_app(p.totient, &[t])
    });
    let mb_tb1 = d.mul(tot_b1, mb);
    let tot_mul_b1_q = d.const_app(p.totient, &[mul_b1_q]);
    let tot_b_final = d.trans(tot_b, tot_mul_b1_q, mb_tb1, tot_b_eq1, eq_b1_step);

    // --- totient(a*b) = mul (mul (totient z) minner) q ----------------------
    let mul_a_b = d.mul(a, b);
    let cong1 = d.congr(a, mul_q_a1, heq_a, &|d, t| d.mul(t, b));
    let mul_qa1_b = d.mul(mul_q_a1, b);
    let cong2 = d.congr(b, mul_q_b1, heq_b, &|d, t| d.mul(mul_q_a1, t));
    let mul_qa1_qb1 = d.mul(mul_q_a1, mul_q_b1);
    let ab_eq1 = d.trans(mul_a_b, mul_qa1_b, mul_qa1_qb1, cong1, cong2);

    let mmc = mul_mul_mul_comm(d, &p, q, a1, q, b1); // (q*a1)*(q*b1) = (q*q)*(a1*b1)
    let mul_qq = d.mul(q, q);
    let mul_qq_z = d.mul(mul_qq, z);
    let ab_eq2 = d.trans(mul_a_b, mul_qa1_qb1, mul_qq_z, ab_eq1, mmc);

    let assoc_qqz = d.lemma(p.mul_assoc, &[q, q, z]); // (q*q)*z = q*(q*z)
    let mul_q_z = d.mul(q, z);
    let mul_q_qz = d.mul(q, mul_q_z);
    let ab_eq3 = d.trans(mul_a_b, mul_qq_z, mul_q_qz, ab_eq2, assoc_qqz);

    let tot_ab_eq_qy = d.congr(mul_a_b, mul_q_qz, ab_eq3, &|d, t| {
        d.const_app(p.totient, &[t])
    });

    let commute_qy = d.lemma(p.mul_comm, &[q, mul_q_z]); // mul q Y = mul Y q
    let mul_yq = d.mul(mul_q_z, q);
    let tot_qy_eq_yq = d.congr(mul_q_qz, mul_yq, commute_qy, &|d, t| {
        d.const_app(p.totient, &[t])
    });

    let dvd_q_y = d.lemma(p.dvd_mul, &[q, z]); // Dvd q (mul q z) = Dvd q Y
    let step_outer = {
        let applied = d.lemma(p.totient_mul_of_dvd, &[mul_q_z, q]);
        d.apply(applied, &[dvd_q_y])
    }; // Eq (totient (mul Y q)) (mul (totient Y) q)

    let tot_mul_q_qz = d.const_app(p.totient, &[mul_q_qz]);
    let tot_mul_yq = d.const_app(p.totient, &[mul_yq]);
    let tot_ab_eq_qy_to_yq = d.trans(tot_ab, tot_mul_q_qz, tot_mul_yq, tot_ab_eq_qy, tot_qy_eq_yq);
    let tot_y = d.const_app(p.totient, &[mul_q_z]);
    let mul_toty_q = d.mul(tot_y, q);
    let tot_ab_eq_tyq = d.trans(
        tot_ab,
        tot_mul_yq,
        mul_toty_q,
        tot_ab_eq_qy_to_yq,
        step_outer,
    );

    let commute_qz = d.lemma(p.mul_comm, &[q, z]); // mul q z = mul z q
    let mul_zq = d.mul(z, q);
    let tot_y_eq = d.congr(mul_q_z, mul_zq, commute_qz, &|d, t| {
        d.const_app(p.totient, &[t])
    });
    let mb_minner_tz = d.mul(tot_z, minner);
    let tot_mul_zq = d.const_app(p.totient, &[mul_zq]);
    let tot_y_final = d.trans(tot_y, tot_mul_zq, mb_minner_tz, tot_y_eq, eq_z_step);

    let cong_final = d.congr(tot_y, mb_minner_tz, tot_y_final, &|d, t| d.mul(t, q));
    let mul_tzminner_q = d.mul(mb_minner_tz, q);
    let tot_ab_final = d.trans(
        tot_ab,
        mul_toty_q,
        mul_tzminner_q,
        tot_ab_eq_tyq,
        cong_final,
    );

    // --- LEFT: totient(kx) * totient(a*b) -----------------------------------
    let target_lhs = d.mul(tot_kx, tot_ab);
    let lhs_step1 = d.congr(tot_kx, mg_tg1, tot_kx_final, &|d, t| d.mul(t, tot_ab));
    let mg_tg1_tot_ab = d.mul(mg_tg1, tot_ab);
    let lhs_step2 = d.congr(tot_ab, mul_tzminner_q, tot_ab_final, &|d, t| {
        d.mul(mg_tg1, t)
    });
    let mg_tg1_mtzminner_q = d.mul(mg_tg1, mul_tzminner_q);
    let lhs_combined = d.trans(
        target_lhs,
        mg_tg1_tot_ab,
        mg_tg1_mtzminner_q,
        lhs_step1,
        lhs_step2,
    );

    // LEFT_EXPANDED = mul (mul tot_g1 mg) (mul (mul tot_z minner) q)
    // -> ((tot_g1 * tot_z) * (mg * minner)) * q   [mul_assoc_symm; mul_mul_mul_comm]
    // -> ((ih_rhs) * (mg*minner)) * q             [IH]
    // -> ((ih_rhs) * (ma*mb)) * q                 [eps identity]
    // -> ((tot_a1*tot_b1)*g1*ma)*mb*q             [expand]
    let x_left = mg_tg1; // mul tot_g1 mg
    let w_inner = d.mul(tot_z, minner);
    let assoc1 = d.lemma(p.mul_assoc, &[x_left, w_inner, q]); // (X*W)*q = X*(W*q)
    let x_wq = d.mul(x_left, mul_tzminner_q);
    let xw = d.mul(x_left, w_inner);
    let xw_q = d.mul(xw, q);
    let assoc1_rev = d.symm(xw_q, x_wq, assoc1); // X*(W*q) = (X*W)*q

    let mmc2 = mul_mul_mul_comm(d, &p, tot_g1, mg, tot_z, minner); // (tot_g1*mg)*(tot_z*minner) = (tot_g1*tot_z)*(mg*minner)
    let tg1_tz = d.mul(tot_g1, tot_z);
    let mg_minner = d.mul(mg, minner);
    let tg1tz_mgminner = d.mul(tg1_tz, mg_minner);
    let cong_mmc2 = d.congr(xw, tg1tz_mgminner, mmc2, &|d, t| d.mul(t, q));
    let mid1 = d.mul(tg1tz_mgminner, q);

    let left_step1 = d.trans(x_wq, xw_q, mid1, assoc1_rev, cong_mmc2);

    // substitute IH: tot_g1 * tot_z = (tot_a1 * tot_b1) * g1
    let ta1_tb1_for_ih = d.mul(tot_a1, tot_b1);
    let ih_rhs = d.mul(ta1_tb1_for_ih, g1);
    let cong_ih = d.congr(tg1_tz, ih_rhs, ih_at, &|d, t| {
        let t_mg_minner = d.mul(t, mg_minner);
        d.mul(t_mg_minner, q)
    });
    let ih_rhs_mg_minner = d.mul(ih_rhs, mg_minner);
    let mid2 = d.mul(ih_rhs_mg_minner, q);
    let left_step2 = d.trans(x_wq, mid1, mid2, left_step1, cong_ih);

    // substitute eps identity: mg * minner = ma * mb
    let ma_mb = d.mul(ma, mb);
    let cong_eps = d.congr(mg_minner, ma_mb, eps_identity, &|d, t| {
        let ih_rhs_t = d.mul(ih_rhs, t);
        d.mul(ih_rhs_t, q)
    });
    let ih_rhs_ma_mb0 = d.mul(ih_rhs, ma_mb);
    let mid3 = d.mul(ih_rhs_ma_mb0, q);
    let left_step3 = d.trans(x_wq, mid2, mid3, left_step2, cong_eps);

    // expand ih_rhs * (ma*mb) -> (ih_rhs * ma) * mb
    let assoc_final = d.lemma(p.mul_assoc, &[ih_rhs, ma, mb]); // (ih_rhs*ma)*mb = ih_rhs*(ma*mb)
    let ih_rhs_ma = d.mul(ih_rhs, ma);
    let ih_rhs_ma_mb = d.mul(ih_rhs_ma, mb);
    let assoc_final_rev = d.symm(ih_rhs_ma_mb, ih_rhs_ma_mb0, assoc_final);
    let cong_assoc_final = d.congr(ih_rhs_ma_mb0, ih_rhs_ma_mb, assoc_final_rev, &|d, t| {
        d.mul(t, q)
    });
    let normal_form = d.mul(ih_rhs_ma_mb, q);
    let left_step4 = d.trans(x_wq, mid3, normal_form, left_step3, cong_assoc_final);

    let left_to_normal = d.trans(target_lhs, x_wq, normal_form, lhs_combined, left_step4);

    // --- RIGHT: mul (totient a) (totient b) * kx ----------------------------
    let tot_a_tot_b = d.mul(tot_a, tot_b);
    let target_rhs = d.mul(tot_a_tot_b, kx);
    let rhs_step1 = d.congr(tot_a, ma_ta1, tot_a_final, &|d, t| d.mul(t, tot_b));
    let ma_ta1_tot_b = d.mul(ma_ta1, tot_b);
    let rhs_step2 = d.congr(tot_b, mb_tb1, tot_b_final, &|d, t| d.mul(ma_ta1, t));
    let ma_ta1_mb_tb1 = d.mul(ma_ta1, mb_tb1);
    let rhs_combined1 = d.trans(
        tot_a_tot_b,
        ma_ta1_tot_b,
        ma_ta1_mb_tb1,
        rhs_step1,
        rhs_step2,
    );

    let rhs_step1_full = d.congr(tot_a_tot_b, ma_ta1_mb_tb1, rhs_combined1, &|d, t| {
        d.mul(t, kx)
    });
    let r1 = d.mul(ma_ta1_mb_tb1, kx);
    let rhs_step2_full = d.congr(kx, mul_q_g1, kx_eq_q_g1, &|d, t| d.mul(ma_ta1_mb_tb1, t));
    let r2 = d.mul(ma_ta1_mb_tb1, mul_q_g1);
    let right_combined = d.trans(target_rhs, r1, r2, rhs_step1_full, rhs_step2_full);

    // R2 = mul (mul (mul tot_a1 ma) (mul tot_b1 mb)) (mul q g1)
    // -> mul (mul (mul tot_a1 tot_b1) (mul ma mb)) (mul q g1)    [mul_mul_mul_comm]
    // -> mul (mul (mul tot_a1 tot_b1) (mul ma mb)) (mul g1 q)    [mul_comm q g1]
    // -> mul (mul (mul tot_a1 tot_b1) g1) (mul ma mb)) q         [assoc; mul_right_comm; assoc]
    let mmc3 = mul_mul_mul_comm(d, &p, tot_a1, ma, tot_b1, mb); // (Ta1*ma)*(Tb1*mb) = (Ta1*Tb1)*(ma*mb)
    let ta1_tb1 = d.mul(tot_a1, tot_b1);
    let ta1tb1_mamb = d.mul(ta1_tb1, ma_mb);
    let cong_mmc3 = d.congr(ma_ta1_mb_tb1, ta1tb1_mamb, mmc3, &|d, t| d.mul(t, mul_q_g1));
    let r3 = d.mul(ta1tb1_mamb, mul_q_g1);
    let right_step1 = d.trans(target_rhs, r2, r3, right_combined, cong_mmc3);

    let mul_comm_qg1_2 = d.lemma(p.mul_comm, &[q, g1]); // mul q g1 = mul g1 q
    let cong_qg1 = d.congr(mul_q_g1, mul_g1_q, mul_comm_qg1_2, &|d, t| {
        d.mul(ta1tb1_mamb, t)
    });
    let r4 = d.mul(ta1tb1_mamb, mul_g1_q);
    let right_step2 = d.trans(target_rhs, r3, r4, right_step1, cong_qg1);

    let xr = d.mul(ta1_tb1, ma_mb);
    let assoc_r = d.lemma(p.mul_assoc, &[xr, g1, q]); // (xr*g1)*q = xr*(g1*q)
    let xr_g1 = d.mul(xr, g1);
    let xr_g1_q = d.mul(xr_g1, q);
    let assoc_r_rev = d.symm(xr_g1_q, r4, assoc_r);
    let right_step3 = d.trans(target_rhs, r4, xr_g1_q, right_step2, assoc_r_rev);

    // (Ta1Tb1 * (ma*mb)) * g1 = (Ta1Tb1 * g1) * (ma*mb)   [mul_right_comm]
    let ta1tb1_g1 = d.mul(ta1_tb1, g1);
    let mrc = mul_right_comm(d, &p, ta1_tb1, ma_mb, g1);
    let ta1tb1_g1_mamb = d.mul(ta1tb1_g1, ma_mb);
    let cong_mrc = d.congr(xr_g1, ta1tb1_g1_mamb, mrc, &|d, t| d.mul(t, q));
    let r5 = d.mul(ta1tb1_g1_mamb, q);
    let right_step4 = d.trans(target_rhs, xr_g1_q, r5, right_step3, cong_mrc);

    // (Y'*(ma*mb))*q -> ((Y'*ma)*mb)*q
    let assoc_r2 = d.lemma(p.mul_assoc, &[ta1tb1_g1, ma, mb]); // (Y'*ma)*mb = Y'*(ma*mb)
    let ta1tb1_g1_ma = d.mul(ta1tb1_g1, ma);
    let ta1tb1_g1_ma_mb = d.mul(ta1tb1_g1_ma, mb);
    let assoc_r2_rev = d.symm(ta1tb1_g1_ma_mb, ta1tb1_g1_mamb, assoc_r2);
    let cong_assoc_r2 = d.congr(ta1tb1_g1_mamb, ta1tb1_g1_ma_mb, assoc_r2_rev, &|d, t| {
        d.mul(t, q)
    });
    let right_normal_form = d.mul(ta1tb1_g1_ma_mb, q);
    let right_step5 = d.trans(
        target_rhs,
        r5,
        right_normal_form,
        right_step4,
        cong_assoc_r2,
    );

    // Confirm both normal forms are literally the same ExprId (ih_rhs_ma_mb
    // vs ta1tb1_g1_ma_mb): ih_rhs = mul (mul tot_a1 tot_b1) g1 = ta1tb1_g1
    // (same sub-expression built two ways -- both are `mul (mul tot_a1
    // tot_b1) g1`), so `normal_form` and `right_normal_form` are the SAME
    // ExprId by construction (structural hashing/interning), and this
    // `debug_assert_eq!` documents that rather than needing a separate proof.
    debug_assert_eq!(normal_form, right_normal_form);

    let right_to_normal = right_step5;

    let normal_to_right = d.symm(target_rhs, normal_form, right_to_normal);
    d.trans(
        target_lhs,
        normal_form,
        target_rhs,
        left_to_normal,
        normal_to_right,
    )
}

// ============================================================================
// `Nat.totient_gcd_mul_aux` — the WF-fix'd generalized family.
// ============================================================================

/// `Nat.totient_gcd_mul_aux : ∀ d a b, Eq (gcd a b) d → Eq (mul (totient d)
/// (totient (mul a b))) (mul (mul (totient a) (totient b)) d)` — the
/// measure-generalized form `F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7`
/// needs for its induction hypothesis to apply to a DIFFERENT pair `(a1,b1)`
/// sharing the smaller gcd `g1`. See this file's module doc for the full
/// route.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_totient_gcd_mul_aux(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one_lvl = d.level_one();
    let zero_lvl = d.kernel().level_zero();

    // family(val) := ∀ a b, Eq (gcd a b) val →
    //   Eq (mul (totient val) (totient (mul a b))) (mul (mul (totient a) (totient b)) val)
    let family_body = |d: &mut NatDev<'_>, val: ExprId| -> ExprId {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let gcd_ab = d.gcd(a, b);
        let hgcd_ty = d.eq(gcd_ab, val);
        let tot_val = d.const_app(p.totient, &[val]);
        let mul_ab = d.mul(a, b);
        let tot_ab = d.const_app(p.totient, &[mul_ab]);
        let lhs = d.mul(tot_val, tot_ab);
        let tot_a = d.const_app(p.totient, &[a]);
        let tot_b = d.const_app(p.totient, &[b]);
        let tot_a_tot_b = d.mul(tot_a, tot_b);
        let rhs = d.mul(tot_a_tot_b, val);
        let body = d.eq(lhs, rhs);
        let inner = d.arrow(hgcd_ty, body);
        let with_b = d.pi_fv(b_fv, nat, inner);
        d.pi_fv(a_fv, nat, with_b)
    };

    let relation = d.kernel().const_(p.lt, vec![]);
    let family = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = family_body(d, k);
        d.lam_fv(k_fv, nat, body)
    };
    let well_founded = d.kernel().const_(p.lt_well_founded, vec![]);

    let step = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let ih_ty = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let lt_ty = d.lt(y, x);
            let family_y = family_body(d, y);
            let inner = d.arrow(lt_ty, family_y);
            d.pi_fv(y_fv, nat, inner)
        };
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);

        let goal = family_body(d, x);
        let disj = d.lemma(p.zero_or_succ, &[x]);
        let zero = d.zero();
        let eq_zero_ty = d.eq(x, zero);
        let succ_pred_ty = {
            let pv_fv = d.fresh_fvar();
            let pv = d.kernel().fvar(pv_fv);
            let spv = d.succ(pv);
            let body = d.eq(x, spv);
            d.lam_fv(pv_fv, nat, body)
        };
        let succ_ex_ty = {
            let exists_c = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
            d.apply(exists_c, &[nat, succ_pred_ty])
        };

        // ---- x = 0: both sides are 0 unconditionally ----------------------
        let case_zero = {
            let hz_fv = d.fresh_fvar();
            let hz = d.kernel().fvar(hz_fv);
            let proof_at_zero = {
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let b_fv = d.fresh_fvar();
                let b = d.kernel().fvar(b_fv);
                let hgcd_fv = d.fresh_fvar();
                let gcd_ab0 = d.gcd(a, b);
                let hgcd_ty0 = d.eq(gcd_ab0, zero);
                let mul_ab = d.mul(a, b);
                let tot_ab = d.const_app(p.totient, &[mul_ab]);
                // Eq (mul zero tot_ab) zero, used at the slot expecting
                // Eq (mul (totient zero) tot_ab) zero via defeq (totient zero
                // ≡ zero by iota, same as `totient (mul a 0) ≡ 0` elsewhere
                // in this prelude).
                let zm = d.lemma(p.zero_mul, &[tot_ab]);
                let body = d.lam_fv(hgcd_fv, hgcd_ty0, zm);
                let with_b = d.lam_fv(b_fv, nat, body);
                d.lam_fv(a_fv, nat, with_b)
            };
            let hz_sym = d.symm(x, zero, hz);
            let motive_x = d.eq_motive(zero, &|d, t| family_body(d, t));
            let result = d.transport(zero, motive_x, proof_at_zero, x, hz_sym);
            d.lam_fv(hz_fv, eq_zero_ty, result)
        };

        // ---- x = succ pv -----------------------------------------------------
        let case_succ = {
            let hex_fv = d.fresh_fvar();
            let hex = d.kernel().fvar(hex_fv);
            let motive_ex = {
                let anon = d.anon_name();
                d.kernel()
                    .lam(anon, succ_ex_ty, goal, crate::BinderInfo::Default)
            };
            let minor = {
                let pv_fv = d.fresh_fvar();
                let pv = d.kernel().fvar(pv_fv);
                let heq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(heq_fv);
                let kx = d.succ(pv);
                let heq_ty = d.eq(x, kx);

                let disj_kx = d.lemma(p.two_le_succ_or_eq_one, &[pv]);
                let two = d.num(2);
                let one = d.num(1);
                let two_le_ty = d.le(two, kx);
                let eq_one_ty = d.eq(kx, one);
                let goal_kx = family_body(d, kx);

                // -- kx = 1: the coprime base case, = totient_mul_of_coprime --
                let right_minor = {
                    let heq1_fv = d.fresh_fvar();
                    let heq1 = d.kernel().fvar(heq1_fv);
                    let proof_at_one = {
                        let a_fv = d.fresh_fvar();
                        let a = d.kernel().fvar(a_fv);
                        let b_fv = d.fresh_fvar();
                        let b = d.kernel().fvar(b_fv);
                        let hgcd_fv = d.fresh_fvar();
                        let hgcd1 = d.kernel().fvar(hgcd_fv);
                        let gcd_ab1 = d.gcd(a, b);
                        let hgcd1_ty = d.eq(gcd_ab1, one);

                        let mul_ab = d.mul(a, b);
                        let tot_ab = d.const_app(p.totient, &[mul_ab]);
                        let tot_a = d.const_app(p.totient, &[a]);
                        let tot_b = d.const_app(p.totient, &[b]);
                        let tot_a_tot_b = d.mul(tot_a, tot_b);

                        // Eq (totient (mul a b)) (mul (totient a) (totient b))
                        let eq1 = d.lemma(p.totient_mul_of_coprime, &[a, b, hgcd1]);

                        // Eq (mul (totient one) tot_ab) tot_ab, via one_mul
                        // (totient one ≡ one by pure reduction, like
                        // totient_eq_one_iff's reverse direction).
                        let om = d.lemma(p.one_mul, &[tot_ab]);
                        let one_lit = d.num(1);
                        let mul_one_tot_ab = d.mul(one_lit, tot_ab);
                        let lhs_eq = d.trans(mul_one_tot_ab, tot_ab, tot_a_tot_b, om, eq1);

                        // Eq (mul tot_a_tot_b one) tot_a_tot_b, via mul_one.
                        let mo = d.lemma(p.mul_one, &[tot_a_tot_b]);
                        let mul_tatb_one = d.mul(tot_a_tot_b, one);
                        let mo_sym = d.symm(mul_tatb_one, tot_a_tot_b, mo);

                        let final_eq =
                            d.trans(mul_one_tot_ab, tot_a_tot_b, mul_tatb_one, lhs_eq, mo_sym);
                        let body = d.lam_fv(hgcd_fv, hgcd1_ty, final_eq);
                        let with_b = d.lam_fv(b_fv, nat, body);
                        d.lam_fv(a_fv, nat, with_b)
                    };
                    let heq1_sym = d.symm(kx, one, heq1);
                    let motive_kx = d.eq_motive(one, &|d, t| family_body(d, t));
                    let result = d.transport(one, motive_kx, proof_at_one, kx, heq1_sym);
                    d.lam_fv(heq1_fv, eq_one_ty, result)
                };

                // -- kx >= 2: peel a prime and dispatch to the four leaves ----
                let left_minor = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv);
                    let ep = d.lemma(p.exists_prime_dvd, &[kx, h2]);

                    let pred_outer = {
                        let q_fv = d.fresh_fvar();
                        let q = d.kernel().fvar(q_fv);
                        let prime_q_ty = prime_ty(d, &p, q);
                        let dvd_q_kx = d.dvd(q, kx);
                        let conj = d.const_app(p.logic.and, &[prime_q_ty, dvd_q_kx]);
                        d.lam_fv(q_fv, nat, conj)
                    };
                    let motive_outer = {
                        let h_fv = d.fresh_fvar();
                        let ex_const = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
                        let ex_ty = d.apply(ex_const, &[nat, pred_outer]);
                        d.lam_fv(h_fv, ex_ty, goal_kx)
                    };
                    let minor_outer = {
                        let q_fv = d.fresh_fvar();
                        let q = d.kernel().fvar(q_fv);
                        let hpand_fv = d.fresh_fvar();
                        let hpand = d.kernel().fvar(hpand_fv);
                        let (two_le_q_ty, divisor_q_ty) = prime_parts(d, &p, q);
                        let prime_q_ty = d.const_app(p.logic.and, &[two_le_q_ty, divisor_q_ty]);
                        let dvd_q_kx_ty = d.dvd(q, kx);
                        let hpand_ty = d.const_app(p.logic.and, &[prime_q_ty, dvd_q_kx_ty]);

                        let prime_q = and_left(d, prime_q_ty, dvd_q_kx_ty, hpand);
                        let dvd_q_kx = and_right(d, prime_q_ty, dvd_q_kx_ty, hpand);
                        let hp2 = and_left(d, two_le_q_ty, divisor_q_ty, prime_q);

                        // a, b, hgcd bound BEFORE peeling into a1/b1 (dvd_q_a/
                        // dvd_q_b need hgcd).
                        let a_fv = d.fresh_fvar();
                        let a = d.kernel().fvar(a_fv);
                        let b_fv = d.fresh_fvar();
                        let b = d.kernel().fvar(b_fv);
                        let hgcd_fv = d.fresh_fvar();
                        let hgcd = d.kernel().fvar(hgcd_fv);
                        let gcd_ab_outer = d.gcd(a, b);
                        let hgcd_ty = d.eq(gcd_ab_outer, kx);

                        let final_goal = {
                            let tot_kx = d.const_app(p.totient, &[kx]);
                            let mul_ab = d.mul(a, b);
                            let tot_ab = d.const_app(p.totient, &[mul_ab]);
                            let lhs = d.mul(tot_kx, tot_ab);
                            let tot_a = d.const_app(p.totient, &[a]);
                            let tot_b = d.const_app(p.totient, &[b]);
                            let tot_a_tot_b = d.mul(tot_a, tot_b);
                            let rhs = d.mul(tot_a_tot_b, kx);
                            d.eq(lhs, rhs)
                        };

                        let dvd_gcd_a = {
                            let motive = d.eq_motive(gcd_ab_outer, &|d, t| d.dvd(t, a));
                            let base = d.lemma(p.gcd_dvd_left, &[a, b]);
                            d.transport(gcd_ab_outer, motive, base, kx, hgcd)
                        };
                        let dvd_gcd_b = {
                            let motive = d.eq_motive(gcd_ab_outer, &|d, t| d.dvd(t, b));
                            let base = d.lemma(p.gcd_dvd_right, &[a, b]);
                            d.transport(gcd_ab_outer, motive, base, kx, hgcd)
                        };
                        let dvd_q_a = d.lemma(p.dvd_trans, &[q, kx, a, dvd_q_kx, dvd_gcd_a]);
                        let dvd_q_b = d.lemma(p.dvd_trans, &[q, kx, b, dvd_q_kx, dvd_gcd_b]);

                        let inner_ab = dvd_elim(d, q, a, final_goal, dvd_q_a, &|d, a1, heq_a| {
                            dvd_elim(d, q, b, final_goal, dvd_q_b, &|d, b1, heq_b| {
                                let z = d.mul(a1, b1);
                                let g1 = d.gcd(a1, b1);

                                // kx = mul q g1
                                let gcd_scaled = d.lemma(p.gcd_mul_right, &[a1, b1, q]);
                                let mul_comm_qa1 = d.lemma(p.mul_comm, &[q, a1]);
                                let mul_a1_q = d.mul(a1, q);
                                let mul_q_a1 = d.mul(q, a1);
                                let full_a_eq = d.trans(a, mul_q_a1, mul_a1_q, heq_a, mul_comm_qa1);
                                let mul_comm_qb1 = d.lemma(p.mul_comm, &[q, b1]);
                                let mul_b1_q = d.mul(b1, q);
                                let mul_q_b1 = d.mul(q, b1);
                                let full_b_eq = d.trans(b, mul_q_b1, mul_b1_q, heq_b, mul_comm_qb1);

                                let gcd_a_b_inner = d.gcd(a, b);
                                let cong_gab_1 =
                                    d.congr(a, mul_a1_q, full_a_eq, &|d, t| d.gcd(t, b));
                                let gcd_a1q_b = d.gcd(mul_a1_q, b);
                                let cong_gab_2 =
                                    d.congr(b, mul_b1_q, full_b_eq, &|d, t| d.gcd(mul_a1_q, t));
                                let gcd_a1q_b1q = d.gcd(mul_a1_q, mul_b1_q);
                                let gab_eq1 = d.trans(
                                    gcd_a_b_inner,
                                    gcd_a1q_b,
                                    gcd_a1q_b1q,
                                    cong_gab_1,
                                    cong_gab_2,
                                );
                                let mul_g1_q = d.mul(g1, q);
                                let gab_eq2 = d.trans(
                                    gcd_a_b_inner,
                                    gcd_a1q_b1q,
                                    mul_g1_q,
                                    gab_eq1,
                                    gcd_scaled,
                                );
                                let hgcd_sym = d.symm(gcd_a_b_inner, kx, hgcd);
                                let kx_eq_g1q =
                                    d.trans(kx, gcd_a_b_inner, mul_g1_q, hgcd_sym, gab_eq2);
                                let mul_comm_g1q = d.lemma(p.mul_comm, &[g1, q]);
                                let mul_q_g1 = d.mul(q, g1);
                                let kx_eq_q_g1 =
                                    d.trans(kx, mul_g1_q, mul_q_g1, kx_eq_g1q, mul_comm_g1q);

                                // g1 < kx
                                let one = d.num(1);
                                let two = d.num(2);
                                let le_refl_one = d.lemma(p.le_refl, &[one]);
                                let le_one_two = d.lemma(p.le_step, &[one, one, le_refl_one]);
                                let h1_kx = d.lemma(p.le_trans, &[one, two, kx, le_one_two, h2]);
                                let motive_h1 = d.eq_motive(kx, &|d, t| d.le(one, t));
                                let h1_mul =
                                    d.transport(kx, motive_h1, h1_kx, mul_q_g1, kx_eq_q_g1);
                                let hq1 = d.lemma(p.one_le_right_of_mul, &[q, g1, h1_mul]);
                                let lt_g1_kx =
                                    derive_cofactor_lt(d, &p, q, kx, g1, kx_eq_q_g1, hp2, hq1);

                                // `ih`'s type is stated in terms of the outer
                                // fix's own bound variable `x`, not `kx` --
                                // transport along `heq : Eq x kx` first
                                // (mirroring `totient_dvd_chain.rs`'s
                                // `lt_proof_kx` -> `lt_proof_x` step).
                                let heq_sym_lt = d.symm(x, kx, heq);
                                let motive_lt = d.eq_motive(kx, &|d, t| d.lt(g1, t));
                                let lt_g1_x = d.transport(kx, motive_lt, lt_g1_kx, x, heq_sym_lt);

                                let ih_g1 = d.apply(ih, &[g1, lt_g1_x]);
                                let g1_refl = d.refl(g1);
                                let ih_at = d.apply(ih_g1, &[a1, b1, g1_refl]);

                                let ctx = StepContext {
                                    q,
                                    g1,
                                    a1,
                                    b1,
                                    z,
                                    a,
                                    b,
                                    kx,
                                    heq_a,
                                    heq_b,
                                    kx_eq_q_g1,
                                    ih_at,
                                };

                                let decided_a1 =
                                    d.lemma(p.coprime_or_dvd_of_prime, &[q, a1, prime_q]);
                                let gcd_q_a1 = d.gcd(q, a1);
                                let coprime_ty_a1 = d.eq(gcd_q_a1, one);
                                let dvd_ty_a1 = d.dvd(q, a1);

                                // ---- a1 coprime branch ----
                                let on_a1_coprime = {
                                    let hcop_a1_fv = d.fresh_fvar();
                                    let hcop_a1 = d.kernel().fvar(hcop_a1_fv);
                                    let ma = d.const_app(p.totient, &[q]);
                                    let hcop_a1_flip = flip_coprime(d, &p, q, a1, hcop_a1);
                                    let eq_a1_step =
                                        d.lemma(p.totient_mul_of_coprime, &[a1, q, hcop_a1_flip]);

                                    let dvd_g1_a1 = d.lemma(p.gcd_dvd_left, &[a1, b1]);
                                    let hcop_g1 = d.lemma(
                                        p.coprime_of_dvd_right,
                                        &[q, g1, a1, dvd_g1_a1, hcop_a1],
                                    );
                                    let hcop_g1_flip = flip_coprime(d, &p, q, g1, hcop_g1);
                                    let mg = d.const_app(p.totient, &[q]);
                                    let eq_g1_step =
                                        d.lemma(p.totient_mul_of_coprime, &[g1, q, hcop_g1_flip]);

                                    let decided_b1 =
                                        d.lemma(p.coprime_or_dvd_of_prime, &[q, b1, prime_q]);
                                    let gcd_q_b1 = d.gcd(q, b1);
                                    let coprime_ty_b1 = d.eq(gcd_q_b1, one);
                                    let dvd_ty_b1 = d.dvd(q, b1);

                                    // LEAF D: a1 coprime, b1 coprime
                                    let leaf_d = {
                                        let hcop_b1_fv = d.fresh_fvar();
                                        let hcop_b1 = d.kernel().fvar(hcop_b1_fv);
                                        let mb = d.const_app(p.totient, &[q]);
                                        let hcop_b1_flip = flip_coprime(d, &p, q, b1, hcop_b1);
                                        let eq_b1_step = d.lemma(
                                            p.totient_mul_of_coprime,
                                            &[b1, q, hcop_b1_flip],
                                        );

                                        let hcop_z = d.lemma(
                                            p.coprime_mul_of_coprime,
                                            &[q, a1, b1, hcop_a1, hcop_b1],
                                        );
                                        let hcop_z_flip = flip_coprime(d, &p, q, z, hcop_z);
                                        let minner = d.const_app(p.totient, &[q]);
                                        let eq_z_step =
                                            d.lemma(p.totient_mul_of_coprime, &[z, q, hcop_z_flip]);

                                        let mg_minner_d = d.mul(mg, minner);
                                        let eps_identity = d.refl(mg_minner_d);
                                        let proof = assemble_gcd_mul_step(
                                            d,
                                            &p,
                                            &ctx,
                                            mg,
                                            ma,
                                            mb,
                                            minner,
                                            eq_g1_step,
                                            eq_a1_step,
                                            eq_b1_step,
                                            eq_z_step,
                                            eps_identity,
                                        );
                                        d.lam_fv(hcop_b1_fv, coprime_ty_b1, proof)
                                    };

                                    // LEAF C: a1 coprime, b1 dvd
                                    let leaf_c = {
                                        let hdvd_b1_fv = d.fresh_fvar();
                                        let hdvd_b1 = d.kernel().fvar(hdvd_b1_fv);
                                        let mb = q;
                                        let tmd_b1 = d.lemma(p.totient_mul_of_dvd, &[b1, q]);
                                        let eq_b1_step = d.apply(tmd_b1, &[hdvd_b1]);

                                        let dmlod = d.lemma(p.dvd_mul_left_of_dvd, &[q, b1, a1]);
                                        let dvd_q_z = d.apply(dmlod, &[hdvd_b1]);
                                        let minner = q;
                                        let tmd_z = d.lemma(p.totient_mul_of_dvd, &[z, q]);
                                        let eq_z_step = d.apply(tmd_z, &[dvd_q_z]);

                                        let mg_minner_c = d.mul(mg, minner);
                                        let eps_identity = d.refl(mg_minner_c);
                                        let proof = assemble_gcd_mul_step(
                                            d,
                                            &p,
                                            &ctx,
                                            mg,
                                            ma,
                                            mb,
                                            minner,
                                            eq_g1_step,
                                            eq_a1_step,
                                            eq_b1_step,
                                            eq_z_step,
                                            eps_identity,
                                        );
                                        d.lam_fv(hdvd_b1_fv, dvd_ty_b1, proof)
                                    };

                                    let inner = or_cases(
                                        d,
                                        coprime_ty_b1,
                                        dvd_ty_b1,
                                        final_goal,
                                        leaf_d,
                                        leaf_c,
                                        decided_b1,
                                    );
                                    d.lam_fv(hcop_a1_fv, coprime_ty_a1, inner)
                                };

                                // ---- a1 dvd branch ----
                                let on_a1_dvd = {
                                    let hdvd_a1_fv = d.fresh_fvar();
                                    let hdvd_a1 = d.kernel().fvar(hdvd_a1_fv);
                                    let ma = q;
                                    let tmd_a1 = d.lemma(p.totient_mul_of_dvd, &[a1, q]);
                                    let eq_a1_step = d.apply(tmd_a1, &[hdvd_a1]);

                                    let dmrod = d.lemma(p.dvd_mul_right_of_dvd, &[q, a1, b1]);
                                    let dvd_q_z = d.apply(dmrod, &[hdvd_a1]);
                                    let minner = q;
                                    let tmd_z2 = d.lemma(p.totient_mul_of_dvd, &[z, q]);
                                    let eq_z_step = d.apply(tmd_z2, &[dvd_q_z]);

                                    let decided_b1 =
                                        d.lemma(p.coprime_or_dvd_of_prime, &[q, b1, prime_q]);
                                    let gcd_q_b1_2 = d.gcd(q, b1);
                                    let coprime_ty_b1 = d.eq(gcd_q_b1_2, one);
                                    let dvd_ty_b1 = d.dvd(q, b1);

                                    // LEAF B: a1 dvd, b1 coprime
                                    let leaf_b = {
                                        let hcop_b1_fv = d.fresh_fvar();
                                        let hcop_b1 = d.kernel().fvar(hcop_b1_fv);
                                        let mb = d.const_app(p.totient, &[q]);
                                        let hcop_b1_flip = flip_coprime(d, &p, q, b1, hcop_b1);
                                        let eq_b1_step = d.lemma(
                                            p.totient_mul_of_coprime,
                                            &[b1, q, hcop_b1_flip],
                                        );

                                        let dvd_g1_b1 = d.lemma(p.gcd_dvd_right, &[a1, b1]);
                                        let hcop_g1 = d.lemma(
                                            p.coprime_of_dvd_right,
                                            &[q, g1, b1, dvd_g1_b1, hcop_b1],
                                        );
                                        let hcop_g1_flip = flip_coprime(d, &p, q, g1, hcop_g1);
                                        let mg = d.const_app(p.totient, &[q]);
                                        let eq_g1_step = d.lemma(
                                            p.totient_mul_of_coprime,
                                            &[g1, q, hcop_g1_flip],
                                        );

                                        // Eq (mul mg minner) (mul ma mb) = Eq (mul Tq q) (mul q Tq)
                                        let eps_identity = d.lemma(p.mul_comm, &[mg, minner]);
                                        let proof = assemble_gcd_mul_step(
                                            d,
                                            &p,
                                            &ctx,
                                            mg,
                                            ma,
                                            mb,
                                            minner,
                                            eq_g1_step,
                                            eq_a1_step,
                                            eq_b1_step,
                                            eq_z_step,
                                            eps_identity,
                                        );
                                        d.lam_fv(hcop_b1_fv, coprime_ty_b1, proof)
                                    };

                                    // LEAF A: a1 dvd, b1 dvd
                                    let leaf_a = {
                                        let hdvd_b1_fv = d.fresh_fvar();
                                        let hdvd_b1 = d.kernel().fvar(hdvd_b1_fv);
                                        let mb = q;
                                        let tmd_b1_2 = d.lemma(p.totient_mul_of_dvd, &[b1, q]);
                                        let eq_b1_step = d.apply(tmd_b1_2, &[hdvd_b1]);

                                        let dvd_q_g1 =
                                            d.lemma(p.dvd_gcd, &[q, a1, b1, hdvd_a1, hdvd_b1]);
                                        let mg = q;
                                        let tmd_g1 = d.lemma(p.totient_mul_of_dvd, &[g1, q]);
                                        let eq_g1_step = d.apply(tmd_g1, &[dvd_q_g1]);

                                        let mg_minner_a = d.mul(mg, minner);
                                        let eps_identity = d.refl(mg_minner_a);
                                        let proof = assemble_gcd_mul_step(
                                            d,
                                            &p,
                                            &ctx,
                                            mg,
                                            ma,
                                            mb,
                                            minner,
                                            eq_g1_step,
                                            eq_a1_step,
                                            eq_b1_step,
                                            eq_z_step,
                                            eps_identity,
                                        );
                                        d.lam_fv(hdvd_b1_fv, dvd_ty_b1, proof)
                                    };

                                    let inner = or_cases(
                                        d,
                                        coprime_ty_b1,
                                        dvd_ty_b1,
                                        final_goal,
                                        leaf_b,
                                        leaf_a,
                                        decided_b1,
                                    );
                                    d.lam_fv(hdvd_a1_fv, dvd_ty_a1, inner)
                                };

                                or_cases(
                                    d,
                                    coprime_ty_a1,
                                    dvd_ty_a1,
                                    final_goal,
                                    on_a1_coprime,
                                    on_a1_dvd,
                                    decided_a1,
                                )
                            })
                        });

                        let body_with_hgcd = d.lam_fv(hgcd_fv, hgcd_ty, inner_ab);
                        let body_with_b = d.lam_fv(b_fv, nat, body_with_hgcd);
                        let body_with_a = d.lam_fv(a_fv, nat, body_with_b);

                        let with_hpand = d.lam_fv(hpand_fv, hpand_ty, body_with_a);
                        d.lam_fv(q_fv, nat, with_hpand)
                    };
                    let exists_rec_outer = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
                    let body = d.apply(
                        exists_rec_outer,
                        &[nat, pred_outer, motive_outer, minor_outer, ep],
                    );
                    d.lam_fv(h2_fv, two_le_ty, body)
                };

                let proof_at_kx = or_cases(
                    d,
                    two_le_ty,
                    eq_one_ty,
                    goal_kx,
                    left_minor,
                    right_minor,
                    disj_kx,
                );

                let heq_sym = d.symm(x, kx, heq);
                let motive_x2 = d.eq_motive(kx, &|d, t| family_body(d, t));
                let result = d.transport(kx, motive_x2, proof_at_kx, x, heq_sym);

                let body = d.lam_fv(heq_fv, heq_ty, result);
                d.lam_fv(pv_fv, nat, body)
            };
            let exists_rec_ = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
            let body = d.apply(exists_rec_, &[nat, succ_pred_ty, motive_ex, minor, hex]);
            d.lam_fv(hex_fv, succ_ex_ty, body)
        };

        let body = or_cases(d, eq_zero_ty, succ_ex_ty, goal, case_zero, case_succ, disj);
        let with_ih = d.lam_fv(ih_fv, ih_ty, body);
        d.lam_fv(x_fv, nat, with_ih)
    };

    let fix = d
        .kernel()
        .const_(p.logic.well_founded_fix, vec![one_lvl, zero_lvl]);
    let value = d.apply(fix, &[nat, relation, family, well_founded, step]);

    let stmt = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = family_body(d, k);
        d.pi_fv(k_fv, nat, body)
    };
    d.declare_theorem(p.totient_gcd_mul_aux, stmt, value)?;
    Ok(())
}

// ============================================================================
// `Nat.totient_gcd_mul_totient_mul` — the `ml430` mirror itself.
// ============================================================================

/// `Nat.totient_gcd_mul_totient_mul : ∀ a b, Eq (mul (totient (gcd a b))
/// (totient (mul a b))) (mul (mul (totient a) (totient b)) (gcd a b))` —
/// `F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7`. One application of
/// [`declare_totient_gcd_mul_aux`] at `val := gcd a b`, with the hypothesis
/// discharged by `Eq.refl`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_totient_gcd_mul_totient_mul(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.totient_gcd_mul_totient_mul, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let gcd_ab = d.gcd(a, b);
        let tot_gcd = d.const_app(p.totient, &[gcd_ab]);
        let mul_ab = d.mul(a, b);
        let tot_ab = d.const_app(p.totient, &[mul_ab]);
        let lhs = d.mul(tot_gcd, tot_ab);
        let tot_a = d.const_app(p.totient, &[a]);
        let tot_b = d.const_app(p.totient, &[b]);
        let tot_a_tot_b = d.mul(tot_a, tot_b);
        let rhs = d.mul(tot_a_tot_b, gcd_ab);
        let stmt = d.eq(lhs, rhs);

        let aux = d.lemma(p.totient_gcd_mul_aux, &[gcd_ab]);
        let refl_gcd = d.refl(gcd_ab);
        let proof = d.apply(aux, &[a, b, refl_gcd]);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare everything in this file, in dependency order.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_totient_gcd_mul_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_totient_gcd_mul_aux(d, p)?;
    declare_totient_gcd_mul_totient_mul(d, p)?;
    Ok(())
}
