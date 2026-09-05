//! ADR-1616, third piece: the finite probability shelf and the integration
//! space, joined by a theorem instead of an analogy.
//!
//! ADR-1612 named this as its next step and did not land it. The reason it
//! could not be landed as stated is worth recording exactly, because it is a
//! property of the `IntSpace` record and not of the probability layer:
//!
//! > **`IntSpace` is generic over the FUNCTION space and hard-wired in the
//! > VALUE type.** Its `carrier` is a field, so an integration space can
//! > integrate any family of functions; but `integral : (f : carrier) →
//! > Integrable f → CReal` returns a `CReal`, and `total : CReal` is a
//! > `CReal`. There is therefore no `ℚ`-valued `IntSpace` and there cannot
//! > be one without a second carrier field. `Rat.expectation` is `ℚ`-valued.
//! > So "the rational finite-probability layer IS an `IntSpace` instance" is
//! > not a theorem that can be stated, and no amount of proof effort would
//! > have produced it.
//!
//! What CAN be stated, and is stated here, is the same content routed
//! through the transfer the obstruction demands:
//!
//! 1. [`declare_creal_finite_expectation`] — the ℝ-valued finite
//!    expectation IS the `crealFinite` integral. Nothing is embedded; the
//!    generic `AlgS.OrderedRing.expectation` at `CReal.orderedRingS` and
//!    `IntSpace.integral (crealFinite m)` are the same number.
//! 2. [`declare_rat_expectation_integral`] — the RATIONAL expectation is
//!    that integral, once carried across `CReal.ofRat`. The transfer is
//!    `AlgS.OrderedRing.expectation_map` (ADR-1616), instantiated at
//!    `AlgS.Rat.orderedRingS`, `CReal.orderedRingS` and `CReal.ofRat`, whose
//!    `ofRat_add`/`ofRat_mul` were already proved; `CReal.zero` is
//!    definitionally `CReal.ofRat Rat.zero`, so the zero obligation is
//!    `equivRefl`.
//!
//! Together those two say: every theorem the generic integration layer
//! proves — congruence, nonnegativity, the constant law, the derived
//! counting measure, monotone convergence — applies to the rational
//! expectation, through one named embedding and not through a resemblance.

use super::{INTEGRAL, IntSpacePrelude, radd, req, rmul, rrefl, rsymm, rtrans, rty, theorem};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

pub(super) fn declare_all(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    declare_creal_finite_expectation(d, p)?;
    declare_rat_expectation_integral(d, p)?;
    Ok(())
}

/// `IntSpace.integral (crealFinite m) f t`, for an `f` the caller supplies.
fn integral_of(d: &mut IntDev<'_>, p: IntSpacePrelude, m: ExprId, f: ExprId, t: ExprId) -> ExprId {
    let s = d.const_app(p.creal_finite, &[m]);
    let sel = d.kernel().const_(p.record.sel(INTEGRAL), vec![]);
    let head = d.apply(sel, &[s]);
    d.apply(head, &[f, t])
}

/// `AlgS.OrderedRing.expectation CReal.orderedRingS X p n`.
fn creal_expectation(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
    x: ExprId,
    pf: ExprId,
    n: ExprId,
) -> ExprId {
    let r = d.kernel().const_(p.creal.ordered_ring_s, vec![]);
    let name = p.creal.rat.probability_s.expectation;
    d.const_app(name, &[r, x, pf, n])
}

/// `IntSpace.crealFinite_expectation : ∀ X p m t, CReal.Equiv (integral
/// (crealFinite m) (fun k => X k * p k) t) (AlgS.OrderedRing.expectation
/// CReal.orderedRingS X p (Nat.succ m))`.
///
/// The ℝ-valued half of the bridge, and it costs one application: the
/// generic expectation at `CReal.orderedRingS` δ/ι-reduces to `CReal.sumRange
/// (fun k => X k * p k) (succ m)`, which is precisely what
/// `IntSpace.crealFinite_integral` already says the integral is. The two
/// developments — a `Nat.rec` over a record's `add`/`zero`, and a
/// Petrakis–Zeuner integration space — meet definitionally, with no
/// reconciling lemma in between.
fn declare_creal_finite_expectation(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let r = rty(d, c);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, r);
    let triv_ty = d.kernel().const_(p.triv, vec![]);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let n = d.succ(m);

    let weighted = {
        let k_fv = d.fresh_fvar();
        let kv = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[kv]);
        let pk = d.apply(pf, &[kv]);
        let body = rmul(d, c, xk, pk);
        d.lam_fv(k_fv, nat, body)
    };

    let lhs = integral_of(d, p, m, weighted, t);
    let rhs = creal_expectation(d, p, x, pf, n);
    let value = d.const_app(p.creal_finite_integral, &[weighted, m, t]);
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t2 = d.pi_fv(t_fv, triv_ty, concl);
        let t2 = d.pi_fv(m_fv, nat, t2);
        let t2 = d.pi_fv(pf_fv, fn_ty, t2);
        d.pi_fv(x_fv, fn_ty, t2)
    };
    let value = {
        let t2 = d.lam_fv(t_fv, triv_ty, value);
        let t2 = d.lam_fv(m_fv, nat, t2);
        let t2 = d.lam_fv(pf_fv, fn_ty, t2);
        d.lam_fv(x_fv, fn_ty, t2)
    };
    theorem(d, p.creal_finite_expectation, ty, value)
}

/// `IntSpace.ratExpectation_integral : ∀ X p m t, CReal.Equiv (integral
/// (crealFinite m) (fun k => ofRat (X k) * ofRat (p k)) t) (CReal.ofRat
/// (Rat.expectation X p (Nat.succ m)))`.
///
/// **The join ADR-1612 asked for, with the carrier mismatch discharged
/// rather than ignored.** `Rat.expectation X p n` is `ℚ`-valued and
/// `IntSpace.integral` is not, so the statement carries the embedding
/// explicitly. Its proof is the generic transfer
/// `AlgS.OrderedRing.expectation_map` at `(AlgS.Rat.orderedRingS,
/// CReal.orderedRingS, CReal.ofRat)`, composed with
/// [`declare_creal_finite_expectation`]; the three obligations are
/// `CReal.equivRefl` (because `CReal.zero` IS `CReal.ofRat Rat.zero`) and
/// the symmetric forms of `CReal.ofRat_add` and `CReal.ofRat_mul`, both of
/// which the reals already had.
fn declare_rat_expectation_integral(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
) -> Result<(), KernelError> {
    let c = p.creal;

    let nat = d.nat_ty();
    let rat_ty = d.kernel().const_(c.rat.int.rat, vec![]);
    let rat_fn_ty = d.arrow(nat, rat_ty);
    let triv_ty = d.kernel().const_(p.triv, vec![]);
    let creal_zero = d.kernel().const_(c.zero, vec![]);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let n = d.succ(m);

    let embed = |d: &mut IntDev<'_>, q: ExprId| -> ExprId { d.const_app(c.of_rat, &[q]) };
    let compose = |d: &mut IntDev<'_>, g: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let kv = d.kernel().fvar(k_fv);
        let gk = d.apply(g, &[kv]);
        let body = embed(d, gk);
        d.lam_fv(k_fv, nat, body)
    };
    let phi_x = compose(d, x);
    let phi_p = compose(d, pf);
    let weighted = {
        let k_fv = d.fresh_fvar();
        let kv = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[kv]);
        let pk = d.apply(pf, &[kv]);
        let ex = embed(d, xk);
        let ep = embed(d, pk);
        let body = rmul(d, c, ex, ep);
        d.lam_fv(k_fv, nat, body)
    };

    // `hzero : Equiv (ofRat Rat.zero) CReal.zero`, by reflexivity —
    // `CReal.zero` is DEFINED as `CReal.ofRat Rat.zero`.
    let hzero = rrefl(d, c, creal_zero);
    // `hadd : ∀ a b, Equiv (ofRat (a + b)) (ofRat a + ofRat b)`, the symmetric
    // form of `CReal.ofRat_add`.
    let hadd = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let ea = embed(d, a);
        let eb = embed(d, b);
        let sum = radd(d, c, ea, eb);
        let ab = d.const_app(c.rat.int.rat_add, &[a, b]);
        let eab = embed(d, ab);
        let raw = d.const_app(c.of_rat_add, &[a, b]);
        let body = rsymm(d, c, sum, eab, raw);
        let over_b = d.lam_fv(b_fv, rat_ty, body);
        d.lam_fv(a_fv, rat_ty, over_b)
    };
    // `hmul : ∀ a b, Equiv (ofRat (a * b)) (ofRat a * ofRat b)`.
    let hmul = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let ea = embed(d, a);
        let eb = embed(d, b);
        let prod = rmul(d, c, ea, eb);
        let ab = d.const_app(c.rat.int.rat_mul, &[a, b]);
        let eab = embed(d, ab);
        let raw = d.const_app(c.of_rat_mul, &[a, b]);
        let body = rsymm(d, c, prod, eab, raw);
        let over_b = d.lam_fv(b_fv, rat_ty, body);
        d.lam_fv(a_fv, rat_ty, over_b)
    };

    let rat_s = d
        .kernel()
        .const_(c.rat.ordered_ring_ext_s.rat_ordered_ring_s, vec![]);
    let creal_s = d.kernel().const_(c.ordered_ring_s, vec![]);
    let of_rat_fn = d.kernel().const_(c.of_rat, vec![]);
    let hmap = d.const_app(
        c.rat.probability_s.expectation_map,
        &[rat_s, creal_s, of_rat_fn, hzero, hadd, hmul, x, pf, n],
    );

    let rat_e = d.const_app(c.rat.expectation, &[x, pf, n]);
    let embedded = embed(d, rat_e);
    let creal_e = creal_expectation(d, p, phi_x, phi_p, n);
    let lhs = integral_of(d, p, m, weighted, t);

    let step1 = d.const_app(p.creal_finite_expectation, &[phi_x, phi_p, m, t]);
    let step2 = rsymm(d, c, embedded, creal_e, hmap);
    let core = rtrans(d, c, lhs, creal_e, embedded, step1, step2);

    let ty = {
        let concl = req(d, c, lhs, embedded);
        let t2 = d.pi_fv(t_fv, triv_ty, concl);
        let t2 = d.pi_fv(m_fv, nat, t2);
        let t2 = d.pi_fv(pf_fv, rat_fn_ty, t2);
        d.pi_fv(x_fv, rat_fn_ty, t2)
    };
    let value = {
        let t2 = d.lam_fv(t_fv, triv_ty, core);
        let t2 = d.lam_fv(m_fv, nat, t2);
        let t2 = d.lam_fv(pf_fv, rat_fn_ty, t2);
        d.lam_fv(x_fv, rat_fn_ty, t2)
    };
    theorem(d, p.rat_expectation_integral, ty, value)
}

#[cfg(test)]
#[path = "probability_bridge_tests.rs"]
mod probability_bridge_tests;
