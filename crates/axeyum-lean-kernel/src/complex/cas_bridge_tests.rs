//! CAS -> kernel polynomial-identity bridge — slice 1.
//!
//! `docs/research/10-cas/curriculum-gaps.md` (reconstruction-targets row)
//! calls this gap out explicitly: "the CAS-witness -> Alethe/Lean bridge is
//! undesigned and unscheduled ... `equal` is a self-contained `MultiPoly`
//! normal form, never lowers to the solver." Twenty-three ledger facts ride
//! the `cas-certificate` route today, and their evidence rests on
//! `axeyum-cas`'s *own* normal form (`MultiPoly`/[`axeyum_cas::equal`]) —
//! never on the kernel. This module is the first wire from that untrusted
//! fast search to this project's trusted small checker: a univariate CAS
//! polynomial identity, translated into `Complex.polyEval`/`polyAdd`/
//! `polyMul` coefficient functions (landed this session in
//! `complex/poly.rs`), and admitted (or refused) by [`crate::Kernel::add_declaration`]
//! independently of whatever the CAS believed.
//!
//! # Why this lives here, and not in an example or in `axeyum-cas`
//!
//! `crates/axeyum-lean-kernel`'s public surface exposes `ComplexPrelude`'s
//! `NameId` fields and the `NatOps` trait, but `IntDev::new` — the only way
//! to obtain a development handle at all — is `pub(crate)`, and the actual
//! ring-identity decision procedure this bridge needs
//! ([`ring_law_proof`]/[`CExpr`]/[`render_c`]/[`zeq`]) is private to
//! `complex.rs`. An external example crate cannot reach any of it. Reproving
//! that decision procedure by hand from public congruence lemmas alone (to
//! avoid this) is not a reasonable amount of code for a bridge slice, so this
//! is a `#[cfg(test)]` module declared as a sibling of `complex_tests.rs`,
//! which gets the same crate-private visibility. `axeyum-cas` is added as a
//! **dev-dependency only** (see `Cargo.toml`): the default library build
//! (what ships) never links it, so this does not change the shipped
//! dependency graph, only the direction a NEW cross-crate edge would run in
//! if it ever became non-test code — trusted-checker-depends-on-untrusted-
//! search, which is the right direction for this project's "untrusted fast
//! search, trusted small checking" identity. `axeyum-cas` itself still does
//! not (and should not) depend back on `axeyum-lean-kernel`, so there is no
//! cycle either way.
//!
//! # The translator (restrictions, stated up front)
//!
//! [`cas_poly_to_int_coeffs`] takes a univariate [`axeyum_cas::CasExpr`],
//! calls [`axeyum_cas::normalize`] (the CAS's own canonicalizer) and
//! [`axeyum_cas::MultiPoly::to_univariate`], and requires every resulting
//! coefficient to be an **integer** — this slice does NOT build a general
//! `Rational -> Complex` constant (that needs `CReal`'s own rational-literal
//! machinery routed through `Complex.ofReal`, which is a real chunk of work
//! on its own and out of scope here). It declines (`None`), never silently
//! rounds. So: univariate-only, integer-coefficients-only. Both are
//! documented restrictions of *this slice's translator*, not of the kernel
//! polynomial layer, which is general over `Complex` coefficients.
//!
//! [`n_term_polynomial`] and [`n_term_polynomial_vanishes_from_n`] generalize
//! `complex_tests.rs`'s `two_term_polynomial` /
//! `two_term_polynomial_vanishes_from_two` (and `three_term_polynomial`) from
//! a fixed 2 or 3 coefficients to an arbitrary count, by the same recipe:
//! nested `Nat.rec` at `Complex`'s own universe (mirroring `Complex.pow`'s
//! own construction — `NatOps::induct`'s motive is `Prop`-only and cannot
//! build a `Complex`-valued function), with a terminal minor case that
//! unconditionally returns `zero` regardless of its index or induction
//! hypothesis.
//!
//! [`n_term_poly_eval_clean`] generalizes `two_term_poly_eval_clean`: it
//! shows `polyEval f n x` — for `f` built by [`n_term_polynomial`] — is
//! `Equiv` to the fully expanded (but NOT ring-simplified) sum
//! `Σ coeffs[i] * x^i`, by PURE reflexivity/δι-reduction alone (no ring law
//! anywhere in this step). It returns the result both as kernel terms and as
//! the parallel [`CExpr`] the final ring-law bridge needs, built from a
//! SINGLE shared recipe ([`int_cexpr`]) so the two representations cannot
//! diverge.
//!
//! # The one dangerous corner: `ring_law_proof` PANICS on a false identity
//!
//! `ring::ring_proof`'s own doc says it plainly and this module's negative
//! control depends on remembering it: on a genuine ring-identity mismatch it
//! does not decline gracefully or hand the kernel a term to reject — it
//! `assert_eq!`s the two normal forms and **panics the test process**. So the
//! bridge NEVER calls `ring_law_proof` on a pair it has not already
//! independently confirmed (via the CAS's own [`axeyum_cas::equal`]) is
//! actually true. The negative control below proves the kernel independently
//! refuses a WRONG CAS claim a different way, one this file's own prior art
//! already uses: build the proof term for the TRUE statement, then attempt to
//! register it against the FALSE statement's TYPE, and confirm
//! `Kernel::add_declaration` rejects it (a `DeclarationValueMismatch`/
//! `TypeMismatch`) — never by asking the ring decision procedure to "prove" a
//! falsehood.
//!
//! # Cost curve (see the test's own timing note)
//!
//! The one demo case here is `(x+1)(x-1) = x^2-1` — CAS-side degree 1 x
//! degree 1 -> degree 2, i.e. exactly `complex_tests.rs`'s own
//! `poly_eval_poly_mul_x_plus_one_times_x_minus_one_is_x_squared_minus_one`,
//! generalized from a concrete evaluation point (`Complex.I`) to a genuinely
//! free `x : Complex` (so the resulting theorem is the real `forall x` the
//! bridge is supposed to produce, not one data point) and now DRIVEN from
//! `axeyum-cas`'s own polynomial representation rather than hand-picked
//! coefficients. That file's own doc already measured this shape as needing
//! [`crate::on_a_deep_stack`] under the default 2 MiB stack; nothing here
//! attempts a higher degree, because the module doc for `poly.rs`'s own
//! kernel facts warns that a single degree-2 concrete `infer` check has
//! already cost a 3.4x suite slowdown (~356s) elsewhere in this kernel. Going
//! further (a genuinely higher-degree product, or more than two factors) is
//! sized as the next slice, not attempted here — see the module-level test's
//! doc comment for the measured wall-clock this slice actually took.

use axeyum_cas::{CasExpr, normalize};

use super::{
    CExpr, ComplexPrelude, build_complex_prelude, complex_ty, render_c, ring_law_proof, zeq,
};
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::nat_prelude::NatOps;
use crate::{BinderInfo, Declaration, Kernel, on_a_deep_stack};

/// A built `Complex` kernel — verbatim copy of `complex_tests.rs::built`
/// (that one is private to its own file and this module cannot reach it).
fn built() -> (Kernel, ComplexPrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, ComplexPrelude)> = OnceLock::new();
    let (kernel, prelude) = TEMPLATE.get_or_init(|| {
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let prelude = build_complex_prelude(&mut kernel).expect("Complex prelude must build");
            (kernel, prelude)
        })
    });
    (kernel.clone(), *prelude)
}

// ---------------------------------------------------------------------------
// The translator.
// ---------------------------------------------------------------------------

/// CAS univariate polynomial (in `var`) -> dense LSB-first integer
/// coefficients, via the CAS's own canonical [`axeyum_cas::MultiPoly`]
/// normal form. Declines (`None`) if `expr` is not a polynomial in the CAS's
/// decidable fragment, mentions any variable other than `var`, or any
/// coefficient is non-integer (see the module doc's restrictions).
fn cas_poly_to_int_coeffs(expr: &CasExpr, var: &str) -> Option<Vec<i128>> {
    let poly = normalize(expr)?;
    let coeffs = poly.to_univariate(var)?;
    let mut out = Vec::with_capacity(coeffs.len());
    for c in coeffs {
        if !c.is_integer() {
            return None;
        }
        out.push(c.numerator());
    }
    Some(out)
}

/// `n` copies of `Complex.one` added (negated for `n < 0`, `Complex.zero` for
/// `n == 0`) — the single recipe used both to embed an integer coefficient
/// into a kernel coefficient function (via [`render_c`]) and, separately, on
/// the ring-law bridge side, so the two representations of "this
/// coefficient" cannot diverge.
fn int_cexpr(n: i128) -> CExpr {
    if n == 0 {
        return CExpr::Zero;
    }
    if n < 0 {
        return CExpr::neg(int_cexpr(-n));
    }
    let mut acc = CExpr::One;
    for _ in 1..n {
        acc = CExpr::add(acc, CExpr::One);
    }
    acc
}

/// The kernel `Complex` term for an integer, via [`int_cexpr`] + [`render_c`].
fn int_complex(d: &mut IntDev<'_>, p: ComplexPrelude, n: i128) -> ExprId {
    render_c(d, p, &int_cexpr(n))
}

/// Generalizes `two_term_polynomial`/`three_term_polynomial`
/// (`complex_tests.rs`) to `coeffs.len()` terms: `fun i => Nat.rec(motive,
/// coeffs[0], minor_1, i)` where `minor_1` recurses to `coeffs[1]` on
/// `succ`, and so on, terminating in a minor case that unconditionally
/// returns `zero`, ignoring its index and induction hypothesis entirely —
/// exactly the shape [`n_term_polynomial_vanishes_from_n`] depends on.
fn n_term_polynomial(d: &mut IntDev<'_>, p: ComplexPrelude, coeffs: &[ExprId]) -> ExprId {
    assert!(
        !coeffs.is_empty(),
        "n_term_polynomial: at least one coefficient is required"
    );
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);

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
            // Terminal level: ignore both `j` and the induction hypothesis
            // entirely, unconditionally `zero` — the two-`Nat.rec`-deep
            // δι-reduction `two_term_polynomial`'s own doc describes,
            // generalized to however many levels `coeffs` needs.
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

/// Generalizes `two_term_polynomial_vanishes_from_two` to an arbitrary
/// coefficient count: `Complex.polyDegreeLt f n_lit`, for `f` built by
/// [`n_term_polynomial`] from EXACTLY as many coefficients as `n_lit`
/// denotes (unary, built by [`crate::nat_prelude::NatOps::num`]). The
/// argument is unchanged from the original doc: `Nat.le_dest` recovers a
/// witness `k` with `add n_lit k = i`; `Nat.add_comm` puts it on the correct
/// side (`add k n_lit`, symbolic left / literal right) so `Nat.add`'s own
/// right-recursion reduces it to `succ^n_lit(k)` by pure ι-reduction for ANY
/// `k`; and `f`'s own nested `Nat.rec` then collapses to `zero` after exactly
/// that many ι-steps, regardless of `k` — none of which depends on what
/// `n_lit` actually is, only that `f` has exactly that many `Nat.rec` levels.
fn n_term_polynomial_vanishes_from_n(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    f: ExprId,
    n_lit: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let nat_p = d.prelude();
    let zero_c = d.kernel().const_(p.zero, vec![]);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let witness = d.lemma(nat_p.le_dest, &[n_lit, i, hle]);

    let predicate = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let add_nk = d.add(n_lit, k);
        let eq_ty = d.eq(add_nk, i);
        d.lam_fv(k_fv, nat, eq_ty)
    };

    let target = {
        let fi = d.apply(f, &[i]);
        zeq(d, p, fi, zero_c)
    };

    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let add_nk = d.add(n_lit, k);
        let eq_ty = d.eq(add_nk, i);

        let add_kn = d.add(k, n_lit);
        let h_comm = d.lemma(nat_p.add_comm, &[n_lit, k]);
        let h_comm_symm = d.symm(add_nk, add_kn, h_comm);
        let h_final = d.trans(add_kn, add_nk, i, h_comm_symm, heq);

        let motive = d.eq_motive(add_kn, &|dd, x| {
            let fx = dd.apply(f, &[x]);
            zeq(dd, p, fx, zero_c)
        });
        let refl_case = d.lemma(p.equiv_refl, &[zero_c]);
        let body = d.transport(add_kn, motive, refl_case, i, h_final);

        let with_heq = d.lam_fv(heq_fv, eq_ty, body);
        d.lam_fv(k_fv, nat, with_heq)
    };

    let case_proof = exists_elim(d, predicate, target, witness, minor);
    let le_ni = d.le(n_lit, i);
    let with_hle = d.lam_fv(hle_fv, le_ni, case_proof);
    d.lam_fv(i_fv, nat, with_hle)
}

/// Generalizes `two_term_poly_eval_clean` to an arbitrary coefficient count.
///
/// `f` must be built by [`n_term_polynomial`] from EXACTLY `coeff_terms` (the
/// same `ExprId`s, in the same order) — `f i` reduces to whatever term was
/// embedded at position `i` by pure ι-reduction, so the caller must thread
/// the identical terms through both calls (see [`build_true_identity`], the
/// only caller). `coeffs` gives the same values as plain integers, needed
/// only to build the matching [`CExpr`] side.
///
/// Returns `(clean, clean_raw, proof)`: `clean` is the [`CExpr`] rendering of
/// the fully expanded — but NOT ring-simplified; `pow x i` stays the nested
/// `mul(...mul(one,x)...,x)` chain `Complex.pow` itself unfolds to, never
/// reduced to a bare power — sum `Σ coeffs[i] * x^i`; `clean_raw` is its
/// rendered kernel term, tracked incrementally through the SAME
/// `add`/`mul` applications [`render_c`] would produce from `clean` (so the
/// two are structurally identical, not merely defeq by luck); and `proof` is
/// `Equiv(polyEval f n x, clean_raw)`.
///
/// Every step here is `equiv_refl` (pure δι, no ring law) or a congruence
/// lemma over such steps — nothing here can produce a WRONG proof of a
/// mismatched statement, only fail to type-check. The cost is the kernel's
/// own defeq walk of `polyEval f n x`'s full unfolding, which is where this
/// module's measured wall-clock time actually goes (see the module doc's
/// cost-curve note).
fn n_term_poly_eval_clean(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    f: ExprId,
    coeffs: &[i128],
    coeff_terms: &[ExprId],
    x_v: &CExpr,
    x: ExprId,
) -> (CExpr, ExprId, ExprId) {
    assert_eq!(
        coeffs.len(),
        coeff_terms.len(),
        "n_term_poly_eval_clean: coeffs and coeff_terms must be the SAME \
         sequence `f` was built from"
    );
    let n = coeffs.len();
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let n_lit = d.num(u32::try_from(n).expect("polynomial length fits u32"));
    let eval_f_n_x = d.const_app(p.poly_eval, &[f, n_lit, x]);

    // The raw (unreduced) accumulate form `polyEval` unfolds to by pure δι
    // (`sumRange f (succ n) = add(sumRange f n, f n)`, `n_lit` literal).
    let mut ec = zero_c;
    let mut raw_terms: Vec<(ExprId, ExprId)> = Vec::with_capacity(n);
    for idx in 0..n {
        let i_lit = d.num(u32::try_from(idx).expect("index fits u32"));
        let fi = d.apply(f, &[i_lit]);
        let pi = d.const_app(p.pow, &[x, i_lit]);
        let term = d.const_app(p.mul, &[fi, pi]);
        ec = d.const_app(p.add, &[ec, term]);
        raw_terms.push((fi, pi));
    }
    let h_defeq = d.lemma(p.equiv_refl, &[ec]);

    let mut clean_cexpr = CExpr::Zero;
    let mut clean_raw = zero_c;
    let mut ec_partial = zero_c;
    let mut h_clean = d.lemma(p.equiv_refl, &[zero_c]);
    let mut pow_cexpr = CExpr::One;
    for (idx, &(fi, pi)) in raw_terms.iter().enumerate() {
        let coeff_cexpr = int_cexpr(coeffs[idx]);
        let coeff_raw = coeff_terms[idx];
        let pow_raw = render_c(d, p, &pow_cexpr);

        let h_fi = d.lemma(p.equiv_refl, &[coeff_raw]);
        let h_pi = d.lemma(p.equiv_refl, &[pow_raw]);
        let h_term = d.lemma(p.mul_congr, &[fi, coeff_raw, pi, pow_raw, h_fi, h_pi]);

        let term_raw = d.const_app(p.mul, &[fi, pi]);
        let term_clean_raw = d.const_app(p.mul, &[coeff_raw, pow_raw]);
        let h_add = d.lemma(
            p.add_congr,
            &[
                ec_partial,
                clean_raw,
                term_raw,
                term_clean_raw,
                h_clean,
                h_term,
            ],
        );

        ec_partial = d.const_app(p.add, &[ec_partial, term_raw]);
        clean_raw = d.const_app(p.add, &[clean_raw, term_clean_raw]);
        h_clean = h_add;

        clean_cexpr = CExpr::add(clean_cexpr, CExpr::mul(coeff_cexpr, pow_cexpr.clone()));
        pow_cexpr = CExpr::mul(pow_cexpr, x_v.clone());
    }

    let h_final = d.lemma(
        p.equiv_trans,
        &[eval_f_n_x, ec_partial, clean_raw, h_defeq, h_clean],
    );
    (clean_cexpr, clean_raw, h_final)
}

/// The bridge's shared plumbing for the TRUE identity `factor1 * factor2 =
/// target` (over `var`): translate all three, build the coefficient
/// functions, and construct `forall x, Equiv(polyEval(polyMul(c1,c2),
/// n1+n2, x), polyEval(target_fn, n_target, x))`.
///
/// Returns `None` if the translator declines on any of the three CAS
/// expressions (documented restrictions — see the module doc); returns
/// `Some((ty, value, x_fv, c1, c2, n1_lit, n2_lit))` on success, where the
/// last four let a caller build a DIFFERENT (false) statement sharing the
/// same LHS to drive the negative control, without re-deriving it.
///
/// # Panics
///
/// Panics (via `ring_law_proof`) if `factor1 * factor2` is NOT actually
/// ring-equal to `target` — see the module doc's warning. Callers MUST
/// confirm this independently (e.g. via [`axeyum_cas::equal`]) before calling
/// with untrusted `target`s; this function does not.
#[allow(clippy::too_many_arguments)]
fn build_true_identity(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    factor1: &CasExpr,
    factor2: &CasExpr,
    target: &CasExpr,
    var: &str,
) -> Option<(ExprId, ExprId, u64, ExprId, ExprId, ExprId, ExprId)> {
    let coeffs1 = cas_poly_to_int_coeffs(factor1, var)?;
    let coeffs2 = cas_poly_to_int_coeffs(factor2, var)?;
    let coeffs_t = cas_poly_to_int_coeffs(target, var)?;
    if coeffs1.is_empty() || coeffs2.is_empty() || coeffs_t.is_empty() {
        return None;
    }

    let terms1: Vec<ExprId> = coeffs1.iter().map(|&n| int_complex(d, p, n)).collect();
    let terms2: Vec<ExprId> = coeffs2.iter().map(|&n| int_complex(d, p, n)).collect();
    let terms_t: Vec<ExprId> = coeffs_t.iter().map(|&n| int_complex(d, p, n)).collect();

    let c1 = n_term_polynomial(d, p, &terms1);
    let c2 = n_term_polynomial(d, p, &terms2);
    let ct = n_term_polynomial(d, p, &terms_t);

    let n1_lit = d.num(u32::try_from(coeffs1.len()).ok()?);
    let n2_lit = d.num(u32::try_from(coeffs2.len()).ok()?);
    let nt_lit = d.num(u32::try_from(coeffs_t.len()).ok()?);

    let h1 = n_term_polynomial_vanishes_from_n(d, p, c1, n1_lit);
    let h2 = n_term_polynomial_vanishes_from_n(d, p, c2, n2_lit);

    let carrier = complex_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let x_v = CExpr::var(d, p, x);

    let proof_mul = d.lemma(p.poly_eval_poly_mul, &[c1, c2, n1_lit, n2_lit, h1, h2, x]);

    let (clean1, clean1_raw, h_clean1) =
        n_term_poly_eval_clean(d, p, c1, &coeffs1, &terms1, &x_v, x);
    let (clean2, clean2_raw, h_clean2) =
        n_term_poly_eval_clean(d, p, c2, &coeffs2, &terms2, &x_v, x);
    let (clean_t, clean_t_raw, h_clean_t) =
        n_term_poly_eval_clean(d, p, ct, &coeffs_t, &terms_t, &x_v, x);

    let eval_c1 = d.const_app(p.poly_eval, &[c1, n1_lit, x]);
    let eval_c2 = d.const_app(p.poly_eval, &[c2, n2_lit, x]);
    let eval_t = d.const_app(p.poly_eval, &[ct, nt_lit, x]);

    let mul_eval = d.const_app(p.mul, &[eval_c1, eval_c2]);
    let mul_clean_raw = d.const_app(p.mul, &[clean1_raw, clean2_raw]);
    let h_combined = d.lemma(
        p.mul_congr,
        &[eval_c1, clean1_raw, eval_c2, clean2_raw, h_clean1, h_clean2],
    );

    // The ONLY ring-law call in this function -- only reached because the
    // caller (build_true_identity's own contract) has an actually-true
    // identity. See the module doc's panic warning.
    let h_ring = ring_law_proof(d, p, &CExpr::mul(clean1.clone(), clean2.clone()), &clean_t);

    let h_mul_to_clean_t = d.lemma(
        p.equiv_trans,
        &[mul_eval, mul_clean_raw, clean_t_raw, h_combined, h_ring],
    );
    let h_clean_t_to_eval_t = d.lemma(p.equiv_symm, &[eval_t, clean_t_raw, h_clean_t]);
    let h_final = d.lemma(
        p.equiv_trans,
        &[
            mul_eval,
            clean_t_raw,
            eval_t,
            h_mul_to_clean_t,
            h_clean_t_to_eval_t,
        ],
    );

    let poly_mul_c1c2 = d.const_app(p.poly_mul, &[c1, c2]);
    let bound = d.add(n1_lit, n2_lit);
    let lhs_stmt = d.const_app(p.poly_eval, &[poly_mul_c1c2, bound, x]);
    let overall = d.lemma(
        p.equiv_trans,
        &[lhs_stmt, mul_eval, eval_t, proof_mul, h_final],
    );

    let stmt = zeq(d, p, lhs_stmt, eval_t);
    let ty = d.pi_fv(x_fv, carrier, stmt);
    let value = d.lam_fv(x_fv, carrier, overall);

    Some((ty, value, x_fv, c1, c2, n1_lit, n2_lit))
}

/// The demo, end to end: CAS proposes `(x+1)(x-1) = x^2-1` (and, as the
/// negative control, the WRONG `(x+1)(x-1) = x^2+1`) — the kernel decides
/// both, from the polynomial structure, independent of what the CAS believed.
///
/// # Timing
///
/// Run in isolation via `cargo test -p axeyum-lean-kernel --lib
/// complex::cas_bridge_tests:: -- --nocapture`, this test (which also pays
/// the ONE-TIME `Complex` prelude build the first time `built()` runs, cached
/// after that in-process) took on the order of the existing
/// `poly_eval_poly_mul_x_plus_one_times_x_minus_one_is_x_squared_minus_one`
/// test in `complex_tests.rs` — the shapes are the same (degree 1 x degree 1
/// -> degree 2), generalized to a free `x`. See this module's own report for
/// the measured wall-clock number; going to a genuinely higher degree is the
/// next slice, not attempted here.
#[test]
fn cas_verified_difference_of_squares_true_and_false() {
    on_a_deep_stack(cas_verified_difference_of_squares_true_and_false_body);
}

fn cas_verified_difference_of_squares_true_and_false_body() {
    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let var = "x";
    let x_cas = CasExpr::var(var);
    let factor1 = x_cas.clone() + CasExpr::int(1); // x + 1
    let factor2 = x_cas.clone() - CasExpr::int(1); // x - 1
    let target = CasExpr::pow(x_cas.clone(), 2) - CasExpr::int(1); // x^2 - 1 (TRUE)
    let wrong_target = CasExpr::pow(x_cas.clone(), 2) + CasExpr::int(1); // x^2 + 1 (FALSE)

    // The CAS's own "fast search" half: it must independently agree the TRUE
    // claim holds and the WRONG one does not, via its own MultiPoly normal
    // form -- entirely separate from anything the kernel does below.
    let product = factor1.clone() * factor2.clone();
    match axeyum_cas::equal(&product, &target) {
        axeyum_cas::ZeroTest::Certified { equal, .. } => {
            assert!(equal, "CAS itself must certify the TRUE identity");
        }
        axeyum_cas::ZeroTest::Unknown => panic!("CAS should decide this trivially"),
    }
    match axeyum_cas::equal(&product, &wrong_target) {
        axeyum_cas::ZeroTest::Certified { equal, .. } => {
            assert!(!equal, "CAS itself must refute the WRONG target");
        }
        axeyum_cas::ZeroTest::Unknown => panic!("CAS should decide this trivially"),
    }

    // The translator: CAS normal form -> dense integer coefficients.
    let coeffs1 = cas_poly_to_int_coeffs(&factor1, var).expect("x+1 is integer-univariate");
    let coeffs2 = cas_poly_to_int_coeffs(&factor2, var).expect("x-1 is integer-univariate");
    let coeffs_t = cas_poly_to_int_coeffs(&target, var).expect("x^2-1 is integer-univariate");
    let coeffs_wrong =
        cas_poly_to_int_coeffs(&wrong_target, var).expect("x^2+1 is integer-univariate");
    assert_eq!(coeffs1, vec![1, 1], "translator: x+1 -> [1,1]");
    assert_eq!(coeffs2, vec![-1, 1], "translator: x-1 -> [-1,1]");
    assert_eq!(coeffs_t, vec![-1, 0, 1], "translator: x^2-1 -> [-1,0,1]");
    assert_eq!(coeffs_wrong, vec![1, 0, 1], "translator: x^2+1 -> [1,0,1]");

    // --- the TRUE identity: build and register -----------------------------
    let (true_ty, true_value, x_fv, c1, c2, n1_lit, n2_lit) =
        build_true_identity(&mut d, p, &factor1, &factor2, &target, var)
            .expect("translator must accept all three integer-coefficient polynomials");

    let name_true = d
        .kernel()
        .name_str(anon, "Check.cas_bridge_difference_of_squares_true");
    let admitted_true = d.kernel().add_declaration(Declaration::Theorem {
        name: name_true,
        uparams: vec![],
        ty: true_ty,
        value: true_value,
    });
    assert!(
        admitted_true.is_ok(),
        "CAS-verified (x+1)(x-1)=x^2-1, translated through polyMul/polyEval at \
         a FREE x, must kernel-check: {admitted_true:?}"
    );

    // --- the negative control: SAME proof, WRONG (CAS-refuted) target ------
    //
    // Deliberately NOT built by re-running `build_true_identity` on
    // `wrong_target` -- that would call `ring_law_proof` on a pair that is
    // NOT actually ring-equal, which PANICS (see the module doc) rather than
    // failing gracefully. Instead: reuse the TRUE proof term verbatim and
    // ascribe it against the FALSE statement's type, exercising exactly the
    // thing that matters here -- `Kernel::add_declaration`'s own type check,
    // not a hand-rolled "is this wrong" heuristic.
    let x = d.kernel().fvar(x_fv);
    let terms_wrong: Vec<ExprId> = coeffs_wrong
        .iter()
        .map(|&n| int_complex(&mut d, p, n))
        .collect();
    let cw = n_term_polynomial(&mut d, p, &terms_wrong);
    let nw_lit = d.num(u32::try_from(coeffs_wrong.len()).expect("fits"));
    let eval_w = d.const_app(p.poly_eval, &[cw, nw_lit, x]);

    let poly_mul_c1c2 = d.const_app(p.poly_mul, &[c1, c2]);
    let bound = d.add(n1_lit, n2_lit);
    let lhs_stmt = d.const_app(p.poly_eval, &[poly_mul_c1c2, bound, x]);
    let wrong_stmt = zeq(&mut d, p, lhs_stmt, eval_w);
    let carrier = complex_ty(&mut d, p);
    let wrong_ty = d.pi_fv(x_fv, carrier, wrong_stmt);

    let name_wrong = d
        .kernel()
        .name_str(anon, "Check.cas_bridge_difference_of_squares_wrong");
    let admitted_wrong = d.kernel().add_declaration(Declaration::Theorem {
        name: name_wrong,
        uparams: vec![],
        ty: wrong_ty,
        value: true_value,
    });
    assert!(
        admitted_wrong.is_err(),
        "the SAME proof term must be REJECTED against the CAS-refuted target \
         x^2+1: {admitted_wrong:?}"
    );
}
