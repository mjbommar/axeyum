//! Tests for `creal/power_series.rs` — roadmap W2-5, power series with a
//! radius of convergence.
//!
//! In its own file rather than in `creal_tests.rs` because that file is the
//! append point every concurrent `creal` lane collides on; `omniscience_tests`
//! and `lub_boundary_tests` are here for the same reason.
//!
//! **What these tests have to rule out.** Three distinct failure modes, one per
//! test:
//!
//! 1. `CReal.powerSeriesPartial` is a `Definition`, and the trusted gate cannot
//!    tell a `Definition` it computes the wrong value — a partial sum that
//!    dropped the `xᵏ` factor, or raised it to the wrong exponent, has exactly
//!    the same type. So it is unfolded at a CONCRETE, small `n` against an
//!    independently rebuilt term, and pinned NOT to be the exponent-shifted
//!    variant, which differs in one small subterm.
//! 2. `CReal.powerSeriesCauchyWithinRadius` is an implication, and an
//!    implication whose hypotheses nothing can satisfy type-checks and says
//!    nothing. So it is applied at GENUINELY FREE hypotheses and its inferred
//!    conclusion pinned; then the ratio is removed from the point hypothesis
//!    (`le (abs x) (mul r R)` weakened to `le (abs x) R`) and rejection
//!    required. That one subterm is the entire content of "strictly inside the
//!    radius".
//! 3. The brief asks which relation the exp/cos instances are. Rather than
//!    assert it, `exp_instance_is_a_proved_equiv_because_the_sides_are_not_def_eq`
//!    MEASURES it: at `n = 1` the two sides are shown not definitionally equal,
//!    so the instance cannot be `Eq.refl` and the proved `Equiv` is doing real
//!    work.

use super::creal_tests::built;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{BinderInfo, CRealPrelude, LocalContext, LocalDecl, on_a_deep_stack};

/// A free variable of type `ty`, pushed into `ctx`. Verbatim in shape to
/// `omniscience_tests.rs`'s own `free_of`.
fn free_of(d: &mut IntDev<'_>, ctx: &mut LocalContext, ty: ExprId) -> ExprId {
    let anon = d.anon_name();
    let fv = d.fresh_fvar();
    ctx.push(LocalDecl {
        fvar: fv,
        name: anon,
        ty,
        info: BinderInfo::Default,
    });
    d.kernel().fvar(fv)
}

// ---------------------------------------------------------------------------
// 1. `powerSeriesPartial` computes the sum it claims to.
// ---------------------------------------------------------------------------

/// `CReal.powerSeriesPartial a x 2` must unfold to `add (add zero (mul (a 0)
/// (pow x 0))) (mul (a 1) (pow x 1))` — `sumRange`'s own `Nat.rec zero (fun j
/// ih => add ih (f j))` shape at `f := fun k => powerSeriesTerm a k x`.
///
/// NEGATIVE CONTROL: it must NOT be the same term with every exponent shifted
/// by one. The two differ in two `pow` arguments and nothing else, which is
/// precisely the off-by-one a `Definition` can carry past the trusted gate.
#[test]
fn power_series_partial_unfolds_to_the_stated_sum_and_rejects_a_shifted_exponent() {
    on_a_deep_stack(power_series_partial_unfolds_body);
}

fn power_series_partial_unfolds_body() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let mut ctx = LocalContext::new();

    let carrier = d.kernel().const_(p.creal, vec![]);
    let nat = d.nat_ty();
    let coeff_ty = d.arrow(nat, carrier);
    let a = free_of(&mut d, &mut ctx, coeff_ty);
    let x = free_of(&mut d, &mut ctx, carrier);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let n0 = d.num(0);
    let n1 = d.num(1);
    let n2 = d.num(2);

    let a0 = d.apply(a, &[n0]);
    let a1 = d.apply(a, &[n1]);

    // the honest expansion
    let term0 = {
        let px = d.const_app(p.pow, &[x, n0]);
        d.const_app(p.mul, &[a0, px])
    };
    let term1 = {
        let px = d.const_app(p.pow, &[x, n1]);
        d.const_app(p.mul, &[a1, px])
    };
    let partial = d.const_app(p.power_series.power_series_partial, &[a, x, n2]);
    let expected = {
        let first = d.const_app(p.add, &[zero_c, term0]);
        d.const_app(p.add, &[first, term1])
    };
    assert!(
        d.kernel().def_eq_in(partial, expected, &mut ctx),
        "powerSeriesPartial a x 2 must unfold to `(0 + a 0 * x^0) + a 1 * x^1`"
    );

    // and the empty sum is `zero`, not something merely equivalent to it
    let partial0 = d.const_app(p.power_series.power_series_partial, &[a, x, n0]);
    assert!(
        d.kernel().def_eq_in(partial0, zero_c, &mut ctx),
        "powerSeriesPartial a x 0 must unfold to `zero`"
    );

    // NEGATIVE CONTROL: exponents shifted by one.
    let shifted = {
        let px0 = d.const_app(p.pow, &[x, n1]);
        let t0 = d.const_app(p.mul, &[a0, px0]);
        let px1 = d.const_app(p.pow, &[x, n2]);
        let t1 = d.const_app(p.mul, &[a1, px1]);
        let first = d.const_app(p.add, &[zero_c, t0]);
        d.const_app(p.add, &[first, t1])
    };
    assert!(
        !d.kernel().def_eq_in(partial, shifted, &mut ctx),
        "powerSeriesPartial must NOT be the exponent-shifted sum -- if this \
         passes, the definition's exponent is not pinned by anything"
    );
}

// ---------------------------------------------------------------------------
// 2. the radius theorem applies at free hypotheses and needs the ratio.
// ---------------------------------------------------------------------------

/// The hypothesis block of `CReal.powerSeriesCauchyWithinRadius`, all free:
/// returns `(a, x, [hcoef, hr0, hlt, hx], kk, hpb, r, r_big)`.
struct RadiusHyps {
    a: ExprId,
    m: ExprId,
    x: ExprId,
    r: ExprId,
    r_big: ExprId,
    hcoef: ExprId,
    hr0: ExprId,
    hlt: ExprId,
    hx: ExprId,
    kk: ExprId,
    hpb: ExprId,
}

fn radius_hyps(d: &mut IntDev<'_>, p: CRealPrelude, ctx: &mut LocalContext) -> RadiusHyps {
    let carrier = d.kernel().const_(p.creal, vec![]);
    let nat = d.nat_ty();
    let coeff_ty = d.arrow(nat, carrier);

    let a = free_of(d, ctx, coeff_ty);
    let m = free_of(d, ctx, carrier);
    let r_big = free_of(d, ctx, carrier);
    let r = free_of(d, ctx, carrier);
    let x = free_of(d, ctx, carrier);

    let hcoef_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ak = d.apply(a, &[k]);
        let aak = d.const_app(p.abs, &[ak]);
        let pr = d.const_app(p.pow, &[r_big, k]);
        let lhs = d.const_app(p.mul, &[aak, pr]);
        let body = d.const_app(p.le, &[lhs, m]);
        d.pi_fv(k_fv, nat, body)
    };
    let hcoef = free_of(d, ctx, hcoef_ty);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let hr0_ty = d.const_app(p.le, &[zero_c, r]);
    let hr0 = free_of(d, ctx, hr0_ty);
    let hlt_ty = d.const_app(p.lt, &[r, one_c]);
    let hlt = free_of(d, ctx, hlt_ty);

    let rr = d.const_app(p.mul, &[r, r_big]);
    let ax = d.const_app(p.abs, &[x]);
    let hx_ty = d.const_app(p.le, &[ax, rr]);
    let hx = free_of(d, ctx, hx_ty);

    let kk = free_of(d, ctx, nat);
    let neg_r = d.const_app(p.neg, &[r]);
    let one_minus_r = d.const_app(p.add, &[one_c, neg_r]);
    let hpb_ty = d.const_app(p.pos_bound, &[one_minus_r, kk]);
    let hpb = free_of(d, ctx, hpb_ty);

    RadiusHyps {
        a,
        m,
        x,
        r,
        r_big,
        hcoef,
        hr0,
        hlt,
        hx,
        kk,
        hpb,
    }
}

/// `CReal.powerSeriesCauchyWithinRadius` applied at genuinely free hypotheses
/// must infer exactly `Cauchy (powerSeriesPartial a x)`.
///
/// NEGATIVE CONTROL: replacing the point hypothesis `le (abs x) (mul r R)` by
/// the ratio-free `le (abs x) R` must be REJECTED. Those two differ in one
/// subterm — the `mul r` — and that subterm is the whole difference between
/// "inside the radius" and "on the boundary", where the series need not
/// converge. If the weaker form were accepted the theorem would be false.
#[test]
fn radius_theorem_lands_on_cauchy_and_rejects_a_ratio_free_point_hypothesis() {
    on_a_deep_stack(radius_theorem_body);
}

fn radius_theorem_body() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let mut ctx = LocalContext::new();
    let h = radius_hyps(&mut d, p, &mut ctx);

    let m = h.m;

    let applied = d.lemma(
        p.power_series.power_series_cauchy_within_radius,
        &[
            h.a, m, h.r_big, h.r, h.x, h.hcoef, h.hr0, h.hlt, h.hx, h.kk, h.hpb,
        ],
    );
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .expect("powerSeriesCauchyWithinRadius must apply at free hypotheses");

    let partial = d.const_app(p.power_series.power_series_partial, &[h.a, h.x]);
    let expected = d.const_app(p.cauchy, &[partial]);
    assert!(
        d.kernel().def_eq_in(inferred, expected, &mut ctx),
        "conclusion must be `Cauchy (powerSeriesPartial a x)`"
    );

    // NEGATIVE CONTROL: drop the ratio from the point hypothesis.
    let ax = d.const_app(p.abs, &[h.x]);
    let weak_ty = d.const_app(p.le, &[ax, h.r_big]);
    let weak = free_of(&mut d, &mut ctx, weak_ty);
    let bogus = d.lemma(
        p.power_series.power_series_cauchy_within_radius,
        &[
            h.a, m, h.r_big, h.r, h.x, h.hcoef, h.hr0, h.hlt, weak, h.kk, h.hpb,
        ],
    );
    assert!(
        d.kernel().infer_in(bogus, &mut ctx).is_err(),
        "`le (abs x) R` must NOT discharge the `le (abs x) (mul r R)` slot -- \
         without the ratio the point may sit on the boundary, where the \
         series need not converge"
    );
}

// ---------------------------------------------------------------------------
// 3. the exp instance is a proved `Equiv`, and this test proves it is not refl.
// ---------------------------------------------------------------------------

/// The brief asks whether `expSeriesPartial` is *definitionally* the generic
/// `powerSeriesPartial` at the factorial-inverse coefficients, or only `Equiv`
/// to it. This test answers by measurement, and the measurement has two halves
/// that point OPPOSITE WAYS — which is the whole reason it is a test and not a
/// sentence in an ADR.
///
/// At a **symbolic** `n` the two sides are NOT definitionally equal. Both are
/// stuck `Nat.rec` applications whose minor premises differ: `expTerm i`
/// against `mul (expTerm i) (pow one i)`, where `i` is a bound variable, so
/// neither `pow` nor `mul` reduces. That is the case the theorem quantifies
/// over, so no `Eq.refl` inhabits it and
/// `CReal.expSeriesPartialIsPowerSeries`'s proved `Equiv` is load-bearing.
///
/// At the **concrete** `n = 1` they ARE definitionally equal. Everything is
/// closed there — `expTerm 0` is a literal `ofRat`, `pow one Nat.zero`
/// ι-reduces to `one`, and the kernel normalizes `mul (ofRat q) one` and `ofRat
/// q` to the same regular sequence. This half was a surprise: this test first
/// asserted non-def-eq at `n = 1` and FAILED, which is how the asymmetry was
/// found rather than assumed. It is pinned because it is the exact trap for a
/// reader who tries to discharge the instance by `Eq.refl` after checking one
/// small case.
#[test]
fn exp_instance_is_a_proved_equiv_at_symbolic_n_but_def_eq_at_n_one() {
    on_a_deep_stack(exp_instance_body);
}

fn exp_instance_body() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let mut ctx = LocalContext::new();

    let nat = d.nat_ty();
    let one_c = d.kernel().const_(p.one, vec![]);
    let exp_term = d.kernel().const_(p.exp_term, vec![]);
    let hand = d.kernel().const_(p.exp_series_partial, vec![]);

    // --- the load-bearing half: a symbolic index ---
    let n = free_of(&mut d, &mut ctx, nat);
    let lhs = d.apply(hand, &[n]);
    let rhs = d.const_app(p.power_series.power_series_partial, &[exp_term, one_c, n]);
    assert!(
        !d.kernel().def_eq_in(lhs, rhs, &mut ctx),
        "at a SYMBOLIC n the two sides must NOT be definitionally equal -- if \
         they were, `expSeriesPartialIsPowerSeries` would be `Eq.refl` and \
         this lane's `one_pow`/`mul_one` route would be dead code"
    );

    // the theorem nevertheless relates them, at that same symbolic index
    let applied = d.lemma(p.power_series.exp_series_partial_is_power_series, &[n]);
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .expect("expSeriesPartialIsPowerSeries must apply at a symbolic n");
    let expected = d.const_app(p.equiv, &[lhs, rhs]);
    assert!(
        d.kernel().def_eq_in(inferred, expected, &mut ctx),
        "the instance must land on `Equiv (expSeriesPartial n) \
         (powerSeriesPartial expTerm one n)`"
    );

    // --- the surprising half: one concrete index is not enough to see it ---
    let n1 = d.num(1);
    let lhs1 = d.apply(hand, &[n1]);
    let rhs1 = d.const_app(p.power_series.power_series_partial, &[exp_term, one_c, n1]);
    assert!(
        d.kernel().def_eq_in(lhs1, rhs1, &mut ctx),
        "at the CONCRETE n = 1 the two sides ARE definitionally equal -- \
         everything is closed and normalizes. Pinned so nobody concludes from \
         one small case that the general instance is `Eq.refl`; if this ever \
         flips, this note and ADR-1638 are both stale"
    );
}
