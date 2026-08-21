//! The **definitions**: the two constants, the order, the inverse, and the
//! three small `ℕ`/`ℤ` facts they need.
//!
//! Every definition here is admitted as a `Definition`, so its defining
//! equation holds definitionally and no equation lemma is needed. In
//! particular `Rat.zero` and `Rat.one` are built with `Rat.mk` rather than
//! `Rat.normalize`: `Rat.num Rat.one` then ι-reduces to `Int.ofNat 1`, which is
//! what lets `mul_one` and `add_zero` be stated against a computed projection
//! instead of an opaque one.

use super::RatPrelude;
use super::ops::{den, den_z, mk, normalize, num, one_le_succ, positive_ty, rat_ty, reduced_ty};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for the rational definitions: above every `Int` definition (the
/// tallest is 21) so a `Rat` definition outranks everything it unfolds to.
const LEAF_HEIGHT: u16 = 30;
/// Height for a definition that calls a leaf one.
const DERIVED_HEIGHT: u16 = 31;

/// Admit the three supporting facts: `gcd m 1 = 1`, and the two `ℤ`-sign facts
/// about `Int.ofNat` that the order definition immediately needs.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_support(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = p.int.nat;

    // gcd_one_right : ∀ m, gcd m 1 = 1 — a divisor of 1 IS 1.
    d.theorem(p.gcd_one_right, 1, &|d, v| {
        let m = v[0];
        let unit = d.num(1);
        let common = NatOps::gcd(d, m, unit);
        let stmt = d.eq(common, unit);
        let divides = d.lemma(nat.gcd_dvd_right, &[m, unit]);
        let proof = d.lemma(nat.eq_one_of_dvd_one, &[common, divides]);
        (stmt, proof)
    })?;

    // int_zero_le_of_nat : ∀ n, Int.le Int.zero (Int.ofNat n).
    // `Int.le (ofNat 0) (ofNat n)` unfolds to `Nat.le 0 n`, so `zero_le` IS the
    // proof — the statement is the only thing that changes.
    d.theorem(p.int_zero_le_of_nat, 1, &|d, v| {
        let n = v[0];
        let zero = d.izero();
        let lifted = d.of_nat(n);
        let stmt = d.ile(zero, lifted);
        let proof = d.lemma(nat.zero_le, &[n]);
        (stmt, proof)
    })?;

    // int_of_nat_pos : ∀ n, 1 ≤ n → Int.lt Int.zero (Int.ofNat n).
    // `Int.lt (ofNat 0) (ofNat n)` unfolds to `Nat.lt 0 n`, which is *literally*
    // `Nat.le (succ 0) n` — the hypothesis, unchanged.
    d.theorem(p.int_of_nat_pos, 1, &|d, v| {
        let n = v[0];
        let zero = d.izero();
        let lifted = d.of_nat(n);
        let conclusion = d.ilt(zero, lifted);
        let unit = d.num(1);
        let hypothesis = NatOps::le(d, unit, n);
        let stmt = d.arrow(hypothesis, conclusion);
        let proof = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, hypothesis, h)
        };
        (stmt, proof)
    })?;
    Ok(())
}

/// Admit `Rat.zero` and `Rat.one`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_constants(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let nat = p.int.nat;

    let constant = |d: &mut IntDev<'_>, name, value: u32| -> Result<(), KernelError> {
        let magnitude = d.num(value);
        let numerator = d.of_nat(magnitude);
        let unit = d.num(1);
        let positive = d.lemma(nat.le_refl, &[unit]);
        let reduced = {
            let nat_abs = d.const_app(p.int.nat_abs, &[numerator]);
            d.lemma(p.gcd_one_right, &[nat_abs])
        };
        let built = mk(d, numerator, unit, positive, reduced);
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty: carrier,
            value: built,
            hint: ReducibilityHint::Regular(LEAF_HEIGHT),
        })
    };
    constant(d, p.zero, 0)?;
    constant(d, p.one, 1)
}

/// Admit `Rat.le` and `Rat.lt`, both by cross-multiplication.
///
/// `le q r := Int.le (num q * ofNat (den r)) (num r * ofNat (den q))`.
///
/// The denominators are positive by construction, so multiplying across is
/// order-preserving and the definition is faithful; the two cancellation
/// lemmas in [`super::core`] are what make that usable in proofs.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_order(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let prop = d.kernel().sort_zero();

    let relation = |d: &mut IntDev<'_>,
                    name,
                    build: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId|
     -> Result<(), KernelError> {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let left = {
            let numerator = num(d, q);
            let scale = den_z(d, r);
            d.imul(numerator, scale)
        };
        let right = {
            let numerator = num(d, r);
            let scale = den_z(d, q);
            d.imul(numerator, scale)
        };
        let body = build(d, left, right);
        let value = {
            let with_r = d.lam_fv(r_fv, carrier, body);
            d.lam_fv(q_fv, carrier, with_r)
        };
        let ty = {
            let inner = d.arrow(carrier, prop);
            d.arrow(carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(LEAF_HEIGHT),
        })
    };
    relation(d, p.le, &|d, a, b| d.ile(a, b))?;
    relation(d, p.lt, &|d, a, b| d.ilt(a, b))
}

/// The body of [`Rat.inv`](RatPrelude::inv), as a function of the **integer it
/// dispatches on** rather than of the rational it came from.
///
/// `Rat.inv q` is `inv_body q (num q)` by definition, so a proof that needs
/// `Rat.inv q` to *reduce* — which needs `num q` in constructor form, and
/// therefore a case split — rewrites inside this application instead of
/// duplicating the three-way dispatch. That is the only reason it is factored
/// out: `super::field` builds the same term with `Int.ofNat (Nat.succ k)` in
/// place of `num q`, and the two agree by construction rather than by a comment
/// claiming they do.
pub(super) fn inv_body(d: &mut IntDev<'_>, p: RatPrelude, q: ExprId, dispatch: ExprId) -> ExprId {
    let carrier = rat_ty(d);
    let nat_ty = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let denominator = den(d, q);

    // The reciprocal `± den q / k`, for a positive natural magnitude `k`.
    let reciprocal = |d: &mut IntDev<'_>, k: ExprId, negative: bool| -> ExprId {
        let lifted = d.of_nat(denominator);
        let numerator = if negative { d.ineg(lifted) } else { lifted };
        let positive = one_le_succ(d, k);
        let magnitude = d.succ(k);
        normalize(d, numerator, magnitude, positive)
    };

    let minor_of_nat = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        // Nat.rec on the magnitude: zero ↦ Rat.zero, succ k ↦ (den q)/(k+1).
        let motive = d.kernel().lam(anon, nat_ty, carrier, BinderInfo::Default);
        let zero_case = d.kernel().const_(p.zero, vec![]);
        let succ_case = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let ih_fv = d.fresh_fvar();
            let body = reciprocal(d, k, false);
            let inner = d.lam_fv(ih_fv, carrier, body);
            d.lam_fv(k_fv, nat_ty, inner)
        };
        let rec_name = d.prelude().rec;
        let rec = d.kernel().const_(rec_name, vec![one]);
        let body = d.apply(rec, &[motive, zero_case, succ_case, n]);
        d.lam_fv(n_fv, nat_ty, body)
    };
    let minor_neg_succ = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let body = reciprocal(d, m, true);
        d.lam_fv(m_fv, nat_ty, body)
    };
    let motive = {
        let int_ty = d.int_ty();
        d.kernel().lam(anon, int_ty, carrier, BinderInfo::Default)
    };
    let rec = d.kernel().const_(p.int.rec, vec![one]);
    d.apply(rec, &[motive, minor_of_nat, minor_neg_succ, dispatch])
}

/// Admit `Rat.inv`, and the two derived operations `Rat.sub` and `Rat.div`.
///
/// The inverse is total, with `inv 0 = 0` — the same convention SMT-LIB takes
/// for `bvudiv` by zero, and Lean's own `Rat.inv`. The three-way split is on
/// the *numerator*'s constructor:
///
/// ```text
/// num q = ofNat 0        ↦ 0
/// num q = ofNat (k+1)    ↦ normalize (ofNat (den q)) (k+1)
/// num q = negSucc m      ↦ normalize (-(ofNat (den q))) (m+1)
/// ```
///
/// `normalize` is used rather than `mk` because `den q / |num q|` need not be
/// reduced as written — it is, in fact, already reduced, but proving that costs
/// `gcd`-commutativity and buys nothing: `normalize` discharges both proof
/// fields itself.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_inverse(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);

    // Rat.inv q := inv_body q (num q).
    {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let numerator = num(d, q);
        let body = inv_body(d, p, q, numerator);
        let value = d.lam_fv(q_fv, carrier, body);
        let ty = d.arrow(carrier, carrier);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.inv,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
        })?;
    }

    // Rat.sub a b := a + (-b);  Rat.div a b := a * b⁻¹.
    let derived = |d: &mut IntDev<'_>,
                   name,
                   build: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId|
     -> Result<(), KernelError> {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let body = build(d, a, b);
        let value = {
            let with_b = d.lam_fv(b_fv, carrier, body);
            d.lam_fv(a_fv, carrier, with_b)
        };
        let ty = {
            let inner = d.arrow(carrier, carrier);
            d.arrow(carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 1),
        })
    };
    derived(d, p.sub, &|d, a, b| {
        let negated = super::ops::rneg(d, b);
        super::ops::radd(d, a, negated)
    })?;
    derived(d, p.div, &|d, a, b| {
        let inverse = d.const_app(p.inv, &[b]);
        super::ops::rmul(d, a, inverse)
    })
}

/// Unused today, kept because every `Rat.mk` in this module is built through it
/// and a future field would otherwise be silently missed.
#[allow(dead_code)]
pub(super) fn mk_fields(d: &mut IntDev<'_>, n: ExprId, denominator: ExprId) -> (ExprId, ExprId) {
    let positive = positive_ty(d, denominator);
    let reduced = reduced_ty(d, n, denominator);
    (positive, reduced)
}
