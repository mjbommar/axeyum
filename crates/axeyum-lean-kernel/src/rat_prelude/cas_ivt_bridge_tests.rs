//! CAS -> kernel bridge, slice 2: the exact polynomial IVT's **sign
//! bracket**, `p(a) < 0 ∧ 0 < p(b)`, for `axeyum-cas`'s
//! `real_algebraic::IvtCertificate` — ADR-0601 SS2's `kernel-reconstructed`
//! row for the `cas-certificate` route (measured 2026-08-27 at
//! `kernel-reconstructed 0` across 24 facts by
//! `scripts/validate-facts.py`).
//!
//! # Scope, stated up front (this IS the design content, not a limitation to
//! hide)
//!
//! [`IvtCertificate`] carries three claims of very different
//! reconstructibility, and this module reconstructs **only the first**:
//!
//! 1. **The sign bracket** — `p(a) < 0` and `0 < p(b)` for rational `a`, `b`
//!    and a rational-coefficient `p` — pure exact `Rat` arithmetic. THIS is
//!    what this module admits through [`crate::Kernel::add_declaration`].
//! 2. **Root containment** (`cert.root`'s minimal polynomial divides `p` by
//!    exact division) — not attempted here; would need `Rat` polynomial
//!    division reconstructed in the kernel, which does not exist yet.
//! 3. **The Sturm count** (`cert.root`'s bracket contains EXACTLY one real
//!    root of `p`) — NOT attempted. Reconstructing a Sturm chain and its
//!    sign-variation count inside the kernel is a much larger lift (see the
//!    module-level test's doc for a sizing estimate); `F:cas-ivt-cbrt2-in-1-2`
//!    keeps this part `cas-internal`, checked only by
//!    `real_algebraic::verify_ivt_certificate`.
//!
//! So this module's target statement is deliberately WEAKER than the
//! `IvtCertificate`'s full claim: it does not name `cert.root` at all, and it
//! does not claim uniqueness. `F:cas-ivt-sign-bracket-cbrt2-kernel-checked`
//! (a SIBLING fact, not an edit to `F:cas-ivt-cbrt2-in-1-2` — see that fact's
//! own `notes` and `docs/plan/status/bridge-ivt.md` for why folding this into
//! the same fact would make `classify_cas_certificate_fact` mislabel the
//! WHOLE certificate, root-containment and Sturm count included, as
//! kernel-reconstructed) is the ledger's row for exactly this weaker claim.
//!
//! # The translator
//!
//! [`sign_bracket_to_int`] takes an [`IvtCertificate`] and extracts `poly`,
//! `a`, `b` as `i128` — declining (`None`) if any coefficient or endpoint is
//! non-integer, mirroring `complex::cas_bridge_tests::cas_poly_to_int_coeffs`'s
//! own integer-only restriction. `axeyum-cas`'s `Rational` is fixed-width
//! (`i128` numerator/denominator, ADR-0038), not the CReal-style bignum
//! `Rational` this kernel's `rat_prelude` reasons about, so the translator's
//! job is exactly "extract the integer value", not a general `Rational ->
//! Rat` embedding — that (a `Rat.ofRat`-style cast for genuinely fractional
//! CAS output) is future work, out of scope here. `cert.root` is deliberately
//! never touched (see Scope above).
//!
//! # The kernel-side construction
//!
//! `Rat.ofInt`/`Rat.ofInt_add`/`Rat.ofInt_mul` (`rat_prelude/matrix.rs`,
//! landed for `Rat.det2_fib`/Cramer's rule) are exactly the missing piece: no
//! NEW `rat_prelude` lemma was needed for this slice. `Rat.add`/`Rat.mul`
//! do NOT reduce integer literals to a normalised value by pure `δι`
//! (`Rat.normalize` calls `Nat.gcd`, which is `ι`-inert on literals — see
//! `CLAUDE.md`'s kernel-facts §1), so every accumulation step below is an
//! explicit `Eq Rat` chain through `ofInt_add`/`ofInt_mul` (`rsymm`'d, since
//! those lemmas run `ofInt(x op y) = ofInt(x) op ofInt(y)`, the OPPOSITE
//! direction from what collapsing needs) rather than a `rrefl` shortcut.
//! `Rat.pow`'s recursion and `Rat.polyEval`'s `sumRange` unfolding, by
//! contrast, ARE pure `δι` on a LITERAL degree bound (no `Rat.mul`/`Rat.add`
//! is invoked to walk the recursion itself, only to combine the terms it
//! produces), exactly as `polynomial.rs`'s own module doc states for
//! `polyEval_zero`/`polyEval_succ` — this is the same defeq [`rrefl`] trick
//! `complex::cas_bridge_tests::n_term_poly_eval_clean` already uses for
//! `Complex.polyEval`, carried over to `Rat`.
//!
//! [`poly_eval_to_of_int`] is the shared engine: `polyEval c n x` for a
//! LITERAL `n` and coefficient function `c` built by [`n_term_polynomial`]
//! from literal `ofInt` coefficients — `δι`-unfolds to a raw nested
//! `add`/`mul`/`pow` tree (`rrefl`, mirroring the Complex bridge's
//! `h_defeq`), which this function then collapses term by term to a single
//! `ofInt(total_int_expr)`, where `total_int_expr` is itself a nested (but
//! `Rat`-free, hence gcd-free) `Int.add`/`Int.mul` tree that the kernel's own
//! defeq engine fully reduces to a literal `Int.ofNat`/`Int.negSucc` when the
//! final sign fact is checked.
//!
//! The final sign fact needs no case-split machinery at all:
//! `Int.lt (Int.negSucc _) (Int.ofNat _)` reduces BY DEFINITION (the
//! `negSucc`/`ofNat` branch of `Int.lt`'s four-case definition,
//! `int_prelude/defs.rs::declare_order_definitions`) to `True`, so
//! [`crate::int_prelude::ops::IntDev::true_intro`] closes the negative
//! bracket outright; the positive bracket needs one genuine `Nat.le` proof
//! ([`nat_le_lit`], a `le_refl`/`le_step` chain), since `Int.lt (ofNat _)
//! (ofNat _)` reduces to an actual `Nat.lt` obligation, not `True`.
//!
//! # Cost curve
//!
//! See the module-level test's own doc comment for the measured wall-clock
//! at this certificate's degree (3) and the next one up (4) — this module's
//! third data point (after `complex/poly.rs`'s degree-2 concrete `infer` at
//! ~356s and this bridge's own slice 1 at ~8.5s for a degree-2 FREE-`x`
//! identity) on whether certified computation over this kernel scales.

use axeyum_cas::real_algebraic::{IvtCertificate, polynomial_ivt};
use axeyum_ir::Rational;

use super::ops::{
    radd, rat_ty, rchain, rcongr, rlt, rmul, rpoly_eval, rpow, rrefl, rsymm, rtrans, rzero,
};
use super::{RatPrelude, build_rat_prelude};
use crate::BinderInfo;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{Kernel, on_a_deep_stack};

pub(crate) fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("Rat prelude must build");
    (kernel, prelude)
}

// ---------------------------------------------------------------------------
// The translator: CAS `IvtCertificate` -> integer sign-bracket data.
// ---------------------------------------------------------------------------

/// `axeyum_cas`/`axeyum_ir`'s `Rational` (fixed-width `i128`) -> `i128`,
/// requiring an integer value. `None` on any genuinely fractional value —
/// this slice does not attempt a general `Rat.ofRat` cast (see module doc).
pub(crate) fn rational_to_int(r: Rational) -> Option<i128> {
    if r.is_integer() {
        Some(r.numerator())
    } else {
        None
    }
}

/// Translate an [`IvtCertificate`]'s SIGN BRACKET ONLY — `poly` (LSB-first)
/// and the two endpoints `a`, `b` — into `i128`s. Declines (`None`) if any
/// value is non-integer. Deliberately drops `cert.root`: the root-containment
/// and Sturm-count parts of the certificate are out of this slice's scope
/// (see module doc) and untouched by this translator.
fn sign_bracket_to_int(cert: &IvtCertificate) -> Option<(Vec<i128>, i128, i128)> {
    let coeffs: Vec<i128> = cert
        .poly
        .iter()
        .copied()
        .map(rational_to_int)
        .collect::<Option<_>>()?;
    let a = rational_to_int(cert.a)?;
    let b = rational_to_int(cert.b)?;
    Some((coeffs, a, b))
}

// ---------------------------------------------------------------------------
// Kernel-side literal builders.
// ---------------------------------------------------------------------------

/// An `Int` literal for `n`: `Int.ofNat n` for `n >= 0`, else
/// `Int.neg (Int.ofNat (-n))` (which `δι`-reduces to `Int.negOfNat`/
/// `Int.negSucc`, `int_prelude/defs.rs`'s own table).
pub(crate) fn int_lit(d: &mut IntDev<'_>, n: i128) -> ExprId {
    if n >= 0 {
        let mag = d.num(u32::try_from(n).expect("int_lit: magnitude fits u32"));
        d.of_nat(mag)
    } else {
        let mag = d.num(u32::try_from(-n).expect("int_lit: magnitude fits u32"));
        let of = d.of_nat(mag);
        d.ineg(of)
    }
}

/// `Rat.ofInt x` — the folded application, for building statements (matches
/// `rat_prelude/matrix.rs`'s own private `of_int` helper; rebuilt here rather
/// than exposed, per this crate's convention of not widening a live file's
/// surface for a single external caller).
pub(crate) fn of_int(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    d.const_app(p.of_int, &[x])
}

/// `Nat.le lo hi`'s proof, for LITERAL `lo <= hi`, by a `le_refl` base case
/// chained through `le_step` (`Nat.le.step : Le n m -> Le n (succ m)`) up to
/// `hi`. Generic numeral-bound builder, used here for the positive bracket's
/// `1 <= n` obligation (`Int.lt (ofNat 0) (ofNat n)` reduces to `Nat.le 1
/// n`, not to `True` — only the `negSucc`/`ofNat` mixed case of `Int.lt` is
/// unconditionally `True`).
pub(super) fn nat_le_lit(d: &mut IntDev<'_>, lo: u32, hi: u32) -> ExprId {
    assert!(lo <= hi, "nat_le_lit: {lo} > {hi}");
    let n = d.prelude();
    let lo_e = d.num(lo);
    let mut cur = d.lemma(n.le_refl, &[lo_e]);
    for k in lo..hi {
        let k_e = d.num(k);
        cur = d.lemma(n.le_step, &[lo_e, k_e, cur]);
    }
    cur
}

// ---------------------------------------------------------------------------
// The coefficient function, generalized from `complex::cas_bridge_tests`'s
// `n_term_polynomial` (carrier `Rat`, terminal minor `Rat.zero`).
// ---------------------------------------------------------------------------

/// `fun i => Nat.rec(motive, coeffs[0], minor_1, i)` — `c : Nat -> Rat` built
/// from `coeffs` by nested `Nat.rec`, terminating in a minor case that
/// unconditionally returns `Rat.zero`. Identical recipe to
/// `complex::cas_bridge_tests::n_term_polynomial`, over `Rat` instead of
/// `Complex`.
pub(crate) fn n_term_polynomial(d: &mut IntDev<'_>, p: RatPrelude, coeffs: &[ExprId]) -> ExprId {
    assert!(
        !coeffs.is_empty(),
        "n_term_polynomial: at least one coefficient is required"
    );
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let zero_c = rzero(d, p);
    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);

    #[allow(clippy::items_after_statements)]
    fn minor_succ(
        d: &mut IntDev<'_>,
        carrier: ExprId,
        nat: ExprId,
        motive: ExprId,
        rec: ExprId,
        zero_c: ExprId,
        rest: &[ExprId],
    ) -> ExprId {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let body = if let Some((&head, tail)) = rest.split_first() {
            let next = minor_succ(d, carrier, nat, motive, rec, zero_c, tail);
            d.apply(rec, &[motive, head, next, j])
        } else {
            zero_c
        };
        let with_ih = d.lam_fv(ih_fv, carrier, body);
        d.lam_fv(j_fv, nat, with_ih)
    }

    let minor = minor_succ(d, carrier, nat, motive, rec, zero_c, &coeffs[1..]);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let body = d.apply(rec, &[motive, coeffs[0], minor, i]);
    d.lam_fv(i_fv, nat, body)
}

// ---------------------------------------------------------------------------
// The evaluation engine: `polyEval c n x` -> `ofInt(total_int_expr)`.
// ---------------------------------------------------------------------------

/// Evaluate `Rat.polyEval c n x` at a LITERAL degree bound `n = coeffs.len()`
/// and a LITERAL `x = ofInt(x_int_expr)`, where `c` was built by
/// [`n_term_polynomial`] from EXACTLY `coeffs_rat` (the same `ExprId`s, same
/// order — `coeffs_int` gives the same values as `Int` literal `ExprId`s,
/// needed for `Rat.ofInt_mul`).
///
/// Returns `(total_int_expr, proof)` where `proof : Eq Rat (polyEval c n x)
/// (ofInt total_int_expr)`. See module doc for why this needs an explicit
/// `Eq` chain (`ofInt_add`/`ofInt_mul`) rather than a `rrefl` shortcut.
pub(crate) fn poly_eval_to_of_int(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    c: ExprId,
    coeffs_int: &[ExprId],
    coeffs_rat: &[ExprId],
    x: ExprId,
    x_int: ExprId,
) -> (ExprId, ExprId) {
    let n = coeffs_int.len();
    assert_eq!(n, coeffs_rat.len());
    let zero_c = rzero(d, p);
    let n_lit = d.num(u32::try_from(n).expect("poly length fits u32"));
    let eval_c_n_x = rpoly_eval(d, p, c, n_lit, x);

    // Raw accumulate form ("ec"): `c`/`pow` applied to LITERAL indices,
    // mirroring `complex::cas_bridge_tests::n_term_poly_eval_clean`'s `ec`.
    let mut ec = zero_c;
    let mut fis = Vec::with_capacity(n);
    let mut pis = Vec::with_capacity(n);
    let mut terms = Vec::with_capacity(n);
    for idx in 0..n {
        let i_lit = d.num(u32::try_from(idx).expect("index fits u32"));
        let fi = d.apply(c, &[i_lit]);
        let pi = rpow(d, p, x, i_lit);
        let term = rmul(d, fi, pi);
        ec = radd(d, ec, term);
        fis.push(fi);
        pis.push(pi);
        terms.push(term);
    }
    // `polyEval c n x` and `ec` are the SAME expression up to pure `δι`
    // unfolding of `polyEval`/`sumRange`'s `Nat.rec` on the literal `n` —
    // ascribed below via `rtrans`, exactly `h_defeq` in the Complex bridge.
    let h_defeq = rrefl(d, ec);

    // Pow chain: `pow(x, idx)` -> `ofInt(pow_int[idx])`, idx = 0..n-1, by
    // unrolling `pow_succ`/`pow_zero` + `ofInt_mul`. `pow(x,0) = Rat.one` is
    // defeq to `ofInt(Int.one)` (both unfold to the identical `Rat.mk`
    // application — see module doc / `matrix.rs::declare_of_int_def`), so no
    // extra step is needed for the base case.
    let one_int = int_lit(d, 1);
    let mut pow_int: Vec<ExprId> = Vec::with_capacity(n);
    let mut pow_target: Vec<ExprId> = Vec::with_capacity(n);
    let mut pow_proof: Vec<ExprId> = Vec::with_capacity(n);
    {
        let pow0_proof = d.lemma(p.pow_zero, &[x]);
        pow_int.push(one_int);
        pow_target.push(of_int(d, p, one_int));
        pow_proof.push(pow0_proof);
    }
    for idx in 1..n {
        let j_lit = d.num(u32::try_from(idx - 1).expect("index fits u32"));
        let pow_x_j = rpow(d, p, x, j_lit);
        let pow_x_succj = pis[idx];
        let step1 = d.lemma(p.pow_succ, &[x, j_lit]);
        let mul_powxj_x = rmul(d, pow_x_j, x);

        let ih = pow_proof[idx - 1];
        let prev_target = pow_target[idx - 1];
        let step_ih = rcongr(d, pow_x_j, prev_target, ih, &|d, t| rmul(d, t, x));
        let mul_target_x = rmul(d, prev_target, x);

        let prev_int = pow_int[idx - 1];
        let new_int = d.imul(prev_int, x_int);
        let new_target = of_int(d, p, new_int);
        let of_mul = d.lemma(p.of_int_mul, &[prev_int, x_int]);
        let of_mul_symm = rsymm(d, new_target, mul_target_x, of_mul);

        let (_, pow_step_proof) = rchain(
            d,
            pow_x_succj,
            &[
                (mul_powxj_x, step1),
                (mul_target_x, step_ih),
                (new_target, of_mul_symm),
            ],
        );
        pow_int.push(new_int);
        pow_target.push(new_target);
        pow_proof.push(pow_step_proof);
    }

    // Terms and accumulation: `c_i * pow(x,i)` -> `ofInt(term_int[i])`, then
    // running sum -> `ofInt(clean_int)`.
    let mut clean_int = int_lit(d, 0);
    let mut clean_raw = of_int(d, p, clean_int);
    // `zero_c` (= `Rat.zero`) is defeq to `ofInt(Int.zero)` for the same
    // reason as the `pow_zero` base case above; `rrefl` here is ascribed
    // against `Eq Rat zero_c clean_raw` when first used below.
    let mut h_clean = rrefl(d, zero_c);
    let mut ec_partial = zero_c;

    for idx in 0..n {
        let fi = fis[idx];
        let pi = pis[idx];
        let term_i = terms[idx];
        let coeff_rat = coeffs_rat[idx];
        let coeff_int = coeffs_int[idx];
        let pow_tgt = pow_target[idx];
        let h_pi = pow_proof[idx];
        // `fi` (= `c` applied to a literal index) reduces to `coeff_rat` by
        // the SAME `Nat.rec` `δι`-unfolding `n_term_polynomial` relies on;
        // ascribed via defeq exactly like the Complex bridge's `h_fi`.
        let h_fi = rrefl(d, coeff_rat);

        let step_c = rcongr(d, fi, coeff_rat, h_fi, &|d, t| rmul(d, t, pi));
        let mid1 = rmul(d, coeff_rat, pi);
        let step_p = rcongr(d, pi, pow_tgt, h_pi, &|d, t| rmul(d, coeff_rat, t));
        let mid2 = rmul(d, coeff_rat, pow_tgt);

        let term_int = d.imul(coeff_int, pow_int[idx]);
        let term_target = of_int(d, p, term_int);
        let of_mul_term = d.lemma(p.of_int_mul, &[coeff_int, pow_int[idx]]);
        let of_mul_term_symm = rsymm(d, term_target, mid2, of_mul_term);

        let (_, h_term_i) = rchain(
            d,
            term_i,
            &[
                (mid1, step_c),
                (mid2, step_p),
                (term_target, of_mul_term_symm),
            ],
        );

        let ec_partial_next = radd(d, ec_partial, term_i);
        let step_add1 = rcongr(d, ec_partial, clean_raw, h_clean, &|d, t| {
            radd(d, t, term_i)
        });
        let mid_a1 = radd(d, clean_raw, term_i);
        let step_add2 = rcongr(d, term_i, term_target, h_term_i, &|d, t| {
            radd(d, clean_raw, t)
        });
        let mid_a2 = radd(d, clean_raw, term_target);

        let new_clean_int = d.iadd(clean_int, term_int);
        let new_clean_raw = of_int(d, p, new_clean_int);
        let of_add = d.lemma(p.of_int_add, &[clean_int, term_int]);
        let of_add_symm = rsymm(d, new_clean_raw, mid_a2, of_add);

        let (_, h_clean_next) = rchain(
            d,
            ec_partial_next,
            &[
                (mid_a1, step_add1),
                (mid_a2, step_add2),
                (new_clean_raw, of_add_symm),
            ],
        );

        ec_partial = ec_partial_next;
        clean_int = new_clean_int;
        clean_raw = new_clean_raw;
        h_clean = h_clean_next;
    }

    let final_proof = rtrans(d, eval_c_n_x, ec, clean_raw, h_defeq, h_clean);
    (clean_int, final_proof)
}

/// From `h : Eq Rat p q` and a proof of `motive(q)`, derive `motive(p)` — the
/// REVERSE of `super::ops::rat_eq_rewrite` (which goes `motive(p) ->
/// motive(q)`), needed here to turn a proof about `ofInt(total_int)` into one
/// about `polyEval c n x`.
fn rat_eq_rewrite_back(
    d: &mut IntDev<'_>,
    p_expr: ExprId,
    q_expr: ExprId,
    h: ExprId,
    proof_q: ExprId,
    motive: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let h_symm = rsymm(d, p_expr, q_expr, h);
    super::ops::rat_eq_rewrite(d, q_expr, p_expr, h_symm, proof_q, motive)
}

// ---------------------------------------------------------------------------
// The two sign-bracket lemmas.
// ---------------------------------------------------------------------------

/// `Eq Rat (polyEval c n x) Rat.zero`-free proof of `Rat.lt (polyEval c n x)
/// Rat.zero`, given `polyEval c n x` provably equals `ofInt(total_int)` for a
/// `total_int` that reduces (by pure kernel computation — no lemma) to a
/// NEGATIVE literal. `Rat.lt (ofInt m) Rat.zero` unfolds, since neither side
/// needs `Rat.normalize`, to `Int.lt (Int.mul m (ofNat 1)) (Int.mul (ofNat 0)
/// (ofNat 1))`, which for `m` negative reduces (the `negSucc`/`ofNat` branch
/// of `Int.lt`'s definition) to `True` regardless of magnitude — so
/// `d.true_intro()` closes it, and the kernel's own defeq check is what does
/// (or refuses) the sign verification, not this Rust code.
pub(crate) fn lt_zero_via_true(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    eval_expr: ExprId,
    total_int: ExprId,
    eq_proof: ExprId,
) -> ExprId {
    let zero_c = rzero(d, p);
    let target = of_int(d, p, total_int);
    let trivial = d.true_intro();
    rat_eq_rewrite_back(d, eval_expr, target, eq_proof, trivial, &|d, t| {
        rlt(d, p, t, zero_c)
    })
}

/// The positive-bracket companion: `Rat.lt Rat.zero (polyEval c n x)`, given
/// `total_int` reduces to a literal in `[1, hi]` (so `nat_le_lit(1, hi)`
/// supplies the underlying `Nat.le` obligation — see [`nat_le_lit`]'s doc for
/// why this direction is NOT unconditionally `True`).
pub(crate) fn zero_lt_via_nat_le(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    eval_expr: ExprId,
    total_int: ExprId,
    eq_proof: ExprId,
    hi: u32,
) -> ExprId {
    let zero_c = rzero(d, p);
    let target = of_int(d, p, total_int);
    let nat_bound = nat_le_lit(d, 1, hi);
    rat_eq_rewrite_back(d, eval_expr, target, eq_proof, nat_bound, &|d, t| {
        rlt(d, p, zero_c, t)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Declaration as Decl;

    /// The concrete certificate this test reconstructs: `p(x) = x^3 - 2` on
    /// `(1, 2)` — `F:cas-ivt-cbrt2-in-1-2`'s own instance, so the
    /// kernel-reconstructed sibling fact is about the SAME certificate, not a
    /// hand-picked easier one.
    ///
    /// Measured (this machine, `cargo test -p axeyum-lean-kernel --lib
    /// rat_prelude::cas_ivt_bridge_tests:: -- --exact --nocapture`, single
    /// invocation, includes the one-time `Rat` prelude build): see the
    /// commit/status note for the exact wall-clock; this is a degree-3
    /// evaluation at two points, structurally similar in size to
    /// `complex::cas_bridge_tests`'s degree-2 FREE-`x` identity (~8.5s there)
    /// but CONCRETE at both evaluation points rather than symbolic, so the
    /// `Nat.rec`/`Int` computation is bounded rather than needing a bigger
    /// stack.
    #[test]
    fn ivt_sign_bracket_cbrt2_kernel_checked() {
        on_a_deep_stack(ivt_sign_bracket_cbrt2_kernel_checked_body);
    }

    fn ivt_sign_bracket_cbrt2_kernel_checked_body() {
        let (mut kernel, prelude) = built();
        let anon = kernel.anon();

        // The CAS's own "fast search" half, entirely independent of anything
        // below: produce the SAME certificate `F:cas-ivt-cbrt2-in-1-2` cites.
        let poly = vec![
            Rational::integer(-2),
            Rational::integer(0),
            Rational::integer(0),
            Rational::integer(1),
        ];
        let cert = polynomial_ivt(&poly, Rational::integer(1), Rational::integer(2))
            .expect("the CAS must produce an IVT certificate for x^3-2 on (1,2)");
        assert_eq!(
            cert.root.degree(),
            3,
            "sanity: the named root must be the genuine irreducible cubic root"
        );

        // The translator: certificate -> integer sign-bracket data.
        let (coeffs_int_vals, a_int_val, b_int_val) = sign_bracket_to_int(&cert)
            .expect("x^3-2 and the bracket (1,2) are integer-valued: translator must accept");
        assert_eq!(
            coeffs_int_vals,
            vec![-2, 0, 0, 1],
            "translator: x^3-2 -> [-2,0,0,1]"
        );
        assert_eq!((a_int_val, b_int_val), (1, 2));

        let mut d = IntDev::new(&mut kernel, prelude.int);
        let p = prelude;

        // Build the coefficient function ONCE, shared by both endpoints.
        let coeffs_int: Vec<ExprId> = coeffs_int_vals
            .iter()
            .map(|&n| int_lit(&mut d, n))
            .collect();
        let coeffs_rat: Vec<ExprId> = coeffs_int.iter().map(|&i| of_int(&mut d, p, i)).collect();
        let c = n_term_polynomial(&mut d, p, &coeffs_rat);

        // --- lower bracket: p(1) < 0 ---------------------------------------
        let a_int = int_lit(&mut d, a_int_val);
        let a_rat = of_int(&mut d, p, a_int);
        let (total_a, eq_a) =
            poly_eval_to_of_int(&mut d, p, c, &coeffs_int, &coeffs_rat, a_rat, a_int);
        let n_lit = d.num(u32::try_from(coeffs_int.len()).expect("fits"));
        let eval_a = rpoly_eval(&mut d, p, c, n_lit, a_rat);
        let proof_lower = lt_zero_via_true(&mut d, p, eval_a, total_a, eq_a);
        let zero_c1 = rzero(&mut d, p);
        let stmt_lower = rlt(&mut d, p, eval_a, zero_c1);

        let name_lower = d
            .kernel()
            .name_str(anon, "Check.ivt_sign_bracket_cbrt2_lower");
        let admitted_lower = d.kernel().add_declaration(Decl::Theorem {
            name: name_lower,
            uparams: vec![],
            ty: stmt_lower,
            value: proof_lower,
        });
        assert!(
            admitted_lower.is_ok(),
            "p(1) < 0 for p = x^3-2, reconstructed through Rat.polyEval, must \
             kernel-check: {admitted_lower:?}"
        );

        // --- upper bracket: 0 < p(2) ---------------------------------------
        let b_int = int_lit(&mut d, b_int_val);
        let b_rat = of_int(&mut d, p, b_int);
        let (total_b, eq_b) =
            poly_eval_to_of_int(&mut d, p, c, &coeffs_int, &coeffs_rat, b_rat, b_int);
        let eval_b = rpoly_eval(&mut d, p, c, n_lit, b_rat);
        // p(2) = 6 exactly -- `nat_le_lit`'s `hi` must be the EXACT value the
        // fully-reduced `Int.mul total_b (ofNat 1)` computes to, not a round
        // "safe" upper bound: `Nat.le 1 6` and `Nat.le 1 8` are different
        // (non-defeq) propositions, so a slack value here is simply wrong,
        // not conservative.
        let proof_upper = zero_lt_via_nat_le(&mut d, p, eval_b, total_b, eq_b, 6);
        let zero_c2 = rzero(&mut d, p);
        let stmt_upper = rlt(&mut d, p, zero_c2, eval_b);

        let name_upper = d
            .kernel()
            .name_str(anon, "Check.ivt_sign_bracket_cbrt2_upper");
        let admitted_upper = d.kernel().add_declaration(Decl::Theorem {
            name: name_upper,
            uparams: vec![],
            ty: stmt_upper,
            value: proof_upper,
        });
        assert!(
            admitted_upper.is_ok(),
            "0 < p(2) for p = x^3-2, reconstructed through Rat.polyEval, must \
             kernel-check: {admitted_upper:?}"
        );

        // --- negative control: SAME proof, WRONG (swapped) statement -------
        //
        // Mirrors `complex::cas_bridge_tests`'s own negative control: do NOT
        // ask any decision procedure to "prove" a falsehood (nothing here
        // would panic the way `ring_law_proof` does, but the discipline is
        // the same) -- reuse a TRUE proof term verbatim and ascribe it
        // against the FALSE statement's type, exercising
        // `Kernel::add_declaration`'s own type check. `p(1) < 0` is TRUE;
        // `0 < p(1)` is FALSE (p(1) = -1).
        let zero_c3 = rzero(&mut d, p);
        let false_stmt = rlt(&mut d, p, zero_c3, eval_a);
        let name_wrong = d
            .kernel()
            .name_str(anon, "Check.ivt_sign_bracket_cbrt2_wrong");
        let admitted_wrong = d.kernel().add_declaration(Decl::Theorem {
            name: name_wrong,
            uparams: vec![],
            ty: false_stmt,
            value: proof_lower,
        });
        assert!(
            admitted_wrong.is_err(),
            "the proof of p(1) < 0 must be REJECTED against the FALSE \
             statement 0 < p(1): {admitted_wrong:?}"
        );
    }

    /// One degree higher: `p(x) = x^4 - 2` on `(1, 2)` (`p(1) = -1 < 0`,
    /// `p(2) = 14 > 0`) — the cost-curve companion the task asks for. Same
    /// construction, one more `pow`/term step.
    #[test]
    fn ivt_sign_bracket_degree_four_kernel_checked() {
        on_a_deep_stack(ivt_sign_bracket_degree_four_kernel_checked_body);
    }

    fn ivt_sign_bracket_degree_four_kernel_checked_body() {
        let (mut kernel, prelude) = built();
        let anon = kernel.anon();

        let poly = vec![
            Rational::integer(-2),
            Rational::integer(0),
            Rational::integer(0),
            Rational::integer(0),
            Rational::integer(1),
        ];
        let cert = polynomial_ivt(&poly, Rational::integer(1), Rational::integer(2))
            .expect("the CAS must produce an IVT certificate for x^4-2 on (1,2)");
        let (coeffs_int_vals, a_int_val, b_int_val) =
            sign_bracket_to_int(&cert).expect("x^4-2 and the bracket (1,2) are integer-valued");
        assert_eq!(coeffs_int_vals, vec![-2, 0, 0, 0, 1]);

        let mut d = IntDev::new(&mut kernel, prelude.int);
        let p = prelude;

        let coeffs_int: Vec<ExprId> = coeffs_int_vals
            .iter()
            .map(|&n| int_lit(&mut d, n))
            .collect();
        let coeffs_rat: Vec<ExprId> = coeffs_int.iter().map(|&i| of_int(&mut d, p, i)).collect();
        let c = n_term_polynomial(&mut d, p, &coeffs_rat);
        let n_lit = d.num(u32::try_from(coeffs_int.len()).expect("fits"));

        let a_int = int_lit(&mut d, a_int_val);
        let a_rat = of_int(&mut d, p, a_int);
        let (total_a, eq_a) =
            poly_eval_to_of_int(&mut d, p, c, &coeffs_int, &coeffs_rat, a_rat, a_int);
        let eval_a = rpoly_eval(&mut d, p, c, n_lit, a_rat);
        let proof_lower = lt_zero_via_true(&mut d, p, eval_a, total_a, eq_a);
        let zero_c1 = rzero(&mut d, p);
        let stmt_lower = rlt(&mut d, p, eval_a, zero_c1);
        let name_lower = d
            .kernel()
            .name_str(anon, "Check.ivt_sign_bracket_deg4_lower");
        let admitted_lower = d.kernel().add_declaration(Decl::Theorem {
            name: name_lower,
            uparams: vec![],
            ty: stmt_lower,
            value: proof_lower,
        });
        assert!(
            admitted_lower.is_ok(),
            "p(1) < 0 for x^4-2: {admitted_lower:?}"
        );

        let b_int = int_lit(&mut d, b_int_val);
        let b_rat = of_int(&mut d, p, b_int);
        let (total_b, eq_b) =
            poly_eval_to_of_int(&mut d, p, c, &coeffs_int, &coeffs_rat, b_rat, b_int);
        let eval_b = rpoly_eval(&mut d, p, c, n_lit, b_rat);
        let proof_upper = zero_lt_via_nat_le(&mut d, p, eval_b, total_b, eq_b, 14);
        let zero_c2 = rzero(&mut d, p);
        let stmt_upper = rlt(&mut d, p, zero_c2, eval_b);
        let name_upper = d
            .kernel()
            .name_str(anon, "Check.ivt_sign_bracket_deg4_upper");
        let admitted_upper = d.kernel().add_declaration(Decl::Theorem {
            name: name_upper,
            uparams: vec![],
            ty: stmt_upper,
            value: proof_upper,
        });
        assert!(
            admitted_upper.is_ok(),
            "0 < p(2) for x^4-2: {admitted_upper:?}"
        );
    }
}
