//! **Apartness**, and the theorem that says why a total inverse cannot exist
//! (ADR-0473, phase F1).
//!
//! ## Why the field structure starts with a *relation*
//!
//! `x⁻¹` is the first operation in this development that is not defined
//! everywhere. Classically the domain is `{x | x ≠ 0}` and nothing more needs
//! saying; constructively `¬(x = 0)` is too weak to compute with, and the
//! usable domain is `{x | x # 0}` — the reals **apart** from zero. The two
//! differ exactly where excluded middle would be needed: `x # 0` says a
//! *positive rational* separates `x` from `0`, `¬(x ≈ 0)` says no such
//! separation can be refuted, and no constructive argument turns the second
//! into the first (that is Markov's principle, which this kernel does not
//! have and this module does not use).
//!
//! So `CReal.Apart` is defined first, and the inverse is stated over it.
//!
//! ## Apartness is `lt` both ways, and that is not a shortcut
//!
//! [`CReal.lt`](super::CRealPrelude::lt) already carries the separation as a
//! **rational gap** — `lt x y := ∃ q, 0 < q ∧ x + q ≤ y` — which is precisely
//! the data Bishop's `x # y` carries. So
//!
//! ```text
//! Apart x y := lt x y ∨ lt y x
//! ```
//!
//! is Bishop's apartness verbatim, not an encoding of it, and every law below
//! is a rearrangement of the strict order rather than a new estimate. The
//! alternative shape — `Apart x y := Not (Equiv x y)` — is the one that must be
//! avoided: it satisfies symmetry and irreflexivity just as happily, and it is
//! the relation the inverse **cannot** be defined over.
//!
//! ## What the `Or` costs, and where that bill arrives
//!
//! `Or` is a `Prop`, so `Or.rec` eliminates only into `Prop`. Every law here
//! lands in `Prop` and none of them notices. A *definition* would:
//! `inv : (x : CReal) → Apart x zero → CReal` is **not** definable, because
//! choosing which reciprocal to compute means eliminating the disjunction into
//! `Type`. That is not a limitation of this kernel — it is the reason CoRN
//! carries apartness in `CProp` (a `Type`-valued logic) rather than in `Prop`,
//! and the reason the inverse here takes the separating modulus as an explicit
//! `Nat` argument. See `super::CRealPrelude::apart` for the statement of that
//! trade and [`declare_no_total_inverse`] for the half of it that is a theorem.
//!
//! ## The one theorem that is about what is *missing*
//!
//! [`CReal.no_total_inverse`](super::CRealPrelude::no_total_inverse) —
//! `∀ (f : CReal → CReal), ¬ ∀ x, x · f x ≈ 1` — refutes every total inverse
//! at once, by evaluating at `zero`. It is the field analogue of
//! `Complex.no_compatible_order`: the missing structure is missing as a
//! *proved* obstruction, not as a scoping note, so "the inverse is partial"
//! cannot quietly become "the inverse is not built yet".

use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

use super::{CRealPrelude, DERIVED_HEIGHT, clt, creal_ty, equiv};

/// `CReal.Apart x y`.
fn apart(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.apart, &[x, y])
}

/// `CReal.mul x y`.
fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

/// `CReal.zero`.
fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `CReal.one`.
fn cone(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.one, vec![])
}

/// Admit `CReal.Apart`, its four laws, its non-vacuity witness, and the
/// refutation of a total inverse.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_field(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_apart(d, p)?;
    declare_apart_laws(d, p)?;
    declare_apart_zero_one(d, p)?;
    declare_no_total_inverse(d, p)
}

/// `CReal.Apart x y := Or (lt x y) (lt y x)`.
fn declare_apart(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let prop = d.kernel().sort_zero();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let below = clt(d, p, x, y);
    let above = clt(d, p, y, x);
    let body = d.or(below, above);
    let value = {
        let with_y = d.lam_fv(y_fv, carrier, body);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let inner = d.arrow(carrier, prop);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.apart,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 9),
    })
}

/// Symmetry, irreflexivity, the setoid congruence, and the one-way bridge to
/// `Not (Equiv x y)`.
fn declare_apart_laws(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_apart_symm(d, p)?;
    declare_apart_irrefl(d, p)?;
    declare_apart_congr(d, p)?;
    declare_not_equiv_of_apart(d, p)
}

/// `apart_symm : ∀ x y, Apart x y → Apart y x` — the disjunction, the other way
/// round.
fn declare_apart_symm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let hypothesis = apart(d, p, x, y);
    let conclusion = apart(d, p, y, x);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let below = clt(d, p, x, y);
    let above = clt(d, p, y, x);
    let swapped = d.or_elim(
        below,
        above,
        conclusion,
        h,
        &|d, proof| d.or_inr(above, below, proof),
        &|d, proof| d.or_inl(above, below, proof),
    );

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, swapped);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let inner = d.arrow(hypothesis, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, inner);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.apart_symm,
        uparams: vec![],
        ty,
        value,
    })
}

/// `apart_irrefl : ∀ x, Not (Apart x x)` — both branches are
/// [`lt_irrefl`](super::CRealPrelude::lt_irrefl).
///
/// This is the law `Apart := Not ∘ Equiv` would also satisfy, which is why it
/// is not on its own evidence that `Apart` is apartness; the pairing with
/// [`declare_apart_zero_one`] is.
fn declare_apart_irrefl(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hypothesis = apart(d, p, x, x);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let strict = clt(d, p, x, x);
    let false_ty = d.false_ty();
    let refuted = d.lemma(p.lt_irrefl, &[x]);
    let contradiction = d.or_elim(
        strict,
        strict,
        false_ty,
        h,
        &|d, proof| d.apply(refuted, &[proof]),
        &|d, proof| d.apply(refuted, &[proof]),
    );

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, contradiction);
        d.lam_fv(x_fv, carrier, with_h)
    };
    let ty = {
        let negated = d.not(hypothesis);
        d.pi_fv(x_fv, carrier, negated)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.apart_irrefl,
        uparams: vec![],
        ty,
        value,
    })
}

/// `apart_congr : ∀ a b c e, Equiv a b → Equiv c e → Apart a c → Apart b e` —
/// the setoid obligation, one [`lt_congr`](super::CRealPrelude::lt_congr) per
/// branch with the two equalities swapped in the second.
fn declare_apart_congr(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let left_equal = equiv(d, p, a, b);
    let right_equal = equiv(d, p, c, e);
    let hypothesis = apart(d, p, a, c);
    let conclusion = apart(d, p, b, e);

    let le_fv = d.fresh_fvar();
    let le_h = d.kernel().fvar(le_fv);
    let re_fv = d.fresh_fvar();
    let re_h = d.kernel().fvar(re_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let below = clt(d, p, a, c);
    let above = clt(d, p, c, a);
    let moved_below = clt(d, p, b, e);
    let moved_above = clt(d, p, e, b);
    let transported = d.or_elim(
        below,
        above,
        conclusion,
        h,
        &|d, proof| {
            let moved = d.lemma(p.lt_congr, &[a, b, c, e, le_h, re_h, proof]);
            d.or_inl(moved_below, moved_above, moved)
        },
        &|d, proof| {
            let moved = d.lemma(p.lt_congr, &[c, e, a, b, re_h, le_h, proof]);
            d.or_inr(moved_below, moved_above, moved)
        },
    );

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, transported);
        let with_re = d.lam_fv(re_fv, right_equal, with_h);
        let with_le = d.lam_fv(le_fv, left_equal, with_re);
        let with_e = d.lam_fv(e_fv, carrier, with_le);
        let with_c = d.lam_fv(c_fv, carrier, with_e);
        let with_b = d.lam_fv(b_fv, carrier, with_c);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let inner = d.arrow(hypothesis, conclusion);
        let with_re = d.arrow(right_equal, inner);
        let with_le = d.arrow(left_equal, with_re);
        let with_e = d.pi_fv(e_fv, carrier, with_le);
        let with_c = d.pi_fv(c_fv, carrier, with_e);
        let with_b = d.pi_fv(b_fv, carrier, with_c);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.apart_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `not_equiv_of_apart : ∀ x y, Apart x y → Not (Equiv x y)`.
///
/// **One-way, and that is the whole point.** The converse —
/// `Not (Equiv x y) → Apart x y` — is Markov's principle for the reals; it is
/// not proved here, not assumed here, and not provable from anything here. This
/// direction costs one `lt_of_lt_of_le` and one `lt_irrefl` per branch.
fn declare_not_equiv_of_apart(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let separated = apart(d, p, x, y);
    let equal = equiv(d, p, x, y);

    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);
    let he_fv = d.fresh_fvar();
    let he = d.kernel().fvar(he_fv);

    let below = clt(d, p, x, y);
    let above = clt(d, p, y, x);
    let false_ty = d.false_ty();
    let contradiction = d.or_elim(
        below,
        above,
        false_ty,
        ha,
        &|d, proof| {
            // `x < y` and `y ≤ x` (from `y ≈ x`) give `x < x`.
            let flipped = d.lemma(p.equiv_symm, &[x, y, he]);
            let bounded = d.lemma(p.le_of_equiv, &[y, x, flipped]);
            let strict = d.lemma(p.lt_of_lt_of_le, &[x, y, x, proof, bounded]);
            let refuted = d.lemma(p.lt_irrefl, &[x]);
            d.apply(refuted, &[strict])
        },
        &|d, proof| {
            let bounded = d.lemma(p.le_of_equiv, &[x, y, he]);
            let strict = d.lemma(p.lt_of_lt_of_le, &[y, x, y, proof, bounded]);
            let refuted = d.lemma(p.lt_irrefl, &[y]);
            d.apply(refuted, &[strict])
        },
    );

    let value = {
        let with_he = d.lam_fv(he_fv, equal, contradiction);
        let with_ha = d.lam_fv(ha_fv, separated, with_he);
        let with_y = d.lam_fv(y_fv, carrier, with_ha);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let negated = d.not(equal);
        let inner = d.arrow(separated, negated);
        let with_y = d.pi_fv(y_fv, carrier, inner);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.not_equiv_of_apart,
        uparams: vec![],
        ty,
        value,
    })
}

/// `apart_zero_one : Apart zero one` — the **non-vacuity** witness.
///
/// `apart_symm`, `apart_irrefl` and `apart_congr` all hold, footprint-free, of
/// the relation that separates nothing; this exhibits a pair `Apart` separates,
/// and it inherits [`zero_lt_one`](super::CRealPrelude::zero_lt_one)'s
/// computation.
fn declare_apart_zero_one(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let zero = czero(d, p);
    let one = cone(d, p);
    let below = clt(d, p, zero, one);
    let above = clt(d, p, one, zero);
    let witness = d.lemma(p.zero_lt_one, &[]);
    let value = d.or_inl(below, above, witness);
    let ty = apart(d, p, zero, one);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.apart_zero_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `no_total_inverse : ∀ (f : CReal → CReal), Not (∀ x, Equiv (mul x (f x)) one)`.
///
/// Evaluate at `zero`: `0 · f 0 ≈ 0 · 0 = 0` by
/// [`mul_comm`](super::CRealPrelude::mul_comm) and
/// [`mul_zero`](super::CRealPrelude::mul_zero), so the assumed inverse law
/// makes `0 ≈ 1`, which
/// [`Equiv.not_zero_one`](super::CRealPrelude::not_zero_one) refutes **by
/// computation** at index 3.
///
/// Stated over an arbitrary `f`, so it refutes every candidate at once —
/// including one defined by cases on a `Prop`-valued hypothesis, had that been
/// possible.
fn declare_no_total_inverse(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let function_ty = d.arrow(carrier, carrier);

    let one = cone(d, p);
    let law = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let applied = d.apply(f, &[x]);
        let product = cmul(d, p, x, applied);
        let claim = equiv(d, p, product, one);
        d.pi_fv(x_fv, carrier, claim)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero = czero(d, p);
    let reciprocal = d.apply(f, &[zero]);
    let product = cmul(d, p, zero, reciprocal);
    let flipped = cmul(d, p, reciprocal, zero);

    let commuted = d.lemma(p.mul_comm, &[zero, reciprocal]);
    let vanishes = d.lemma(p.mul_zero, &[reciprocal]);
    let collapses = d.lemma(p.equiv_trans, &[product, flipped, zero, commuted, vanishes]);
    let restored = d.lemma(p.equiv_symm, &[product, zero, collapses]);
    let at_zero = d.apply(h, &[zero]);
    let degenerate = d.lemma(p.equiv_trans, &[zero, product, one, restored, at_zero]);
    let refuted = d.lemma(p.not_zero_one, &[]);
    let contradiction = d.apply(refuted, &[degenerate]);

    let value = {
        let with_h = d.lam_fv(h_fv, law, contradiction);
        d.lam_fv(f_fv, function_ty, with_h)
    };
    let ty = {
        let negated = d.not(law);
        d.pi_fv(f_fv, function_ty, negated)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.no_total_inverse,
        uparams: vec![],
        ty,
        value,
    })
}
