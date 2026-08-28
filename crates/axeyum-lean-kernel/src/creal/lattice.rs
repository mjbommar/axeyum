//! **The lattice on ℝ**: `CReal.max`, `CReal.min` and `CReal.abs`, pointwise
//! and with **no index shift** (ADR-0519, phase R5).
//!
//! ## Why this costs so little
//!
//! Every previous operation on `CReal` paid for itself in indices. `CReal.add`
//! samples at Bishop's `2n+1` because adding two regular sequences doubles the
//! error; `CReal.mul` samples at a shift computed from both factors'
//! magnitudes; `CReal.inv` samples at `(C+1)n + C` and needed two degree-2
//! identities in `ℕ` to justify it. The lattice needs **none of that**, and
//! the reason is one lemma:
//!
//! ```text
//! Rat.sub_max_le : a − c ≤ q → b − e ≤ q → max a b − max c e ≤ q
//! ```
//!
//! `max` is one-Lipschitz in both arguments *jointly*, so it does not degrade
//! the modulus at all — exactly like [`CReal.neg`](super::CRealPrelude::neg),
//! and unlike everything in between. `maxSeq x y n := Rat.max (x_n) (y_n)` is
//! therefore regular at the *same* modulus its arguments are, and the whole
//! regularity proof is that lemma twice, once per side of the two-sided bound.
//!
//! ## The obstacle that is not there
//!
//! `max` looks like it needs a decision, and a decision over a setoid of
//! regular sequences is exactly what constructive analysis does **not** have —
//! `le` on `CReal` is undecidable and no totality law is stated. But the
//! decision is never taken at this level: it is taken once, on the
//! *representation*, inside [`Rat.max`](crate::RatPrelude::max), where the sign
//! of an integer is a constructor. See [`crate::rat_prelude::lattice`].
//!
//! ## `abs` is `max x (−x)`, and that is the whole definition
//!
//! No new sequence, no new regularity obligation: `CReal.abs` composes two
//! declarations that already exist, so its own footprint is theirs.
//! [`abs_le`](super::CRealPrelude::abs_le) is
//! [`max_le`](super::CRealPrelude::max_le) verbatim,
//! [`abs_congr`](super::CRealPrelude::abs_congr) is `max_congr` with
//! `neg_congr` in its second slot, and the only genuinely new fact is
//! [`abs_nonneg`](super::CRealPrelude::abs_nonneg), which rests on the one `ℚ`
//! lemma the lattice module proves with `Rat.le_total`.
//!
//! Note what this does **not** give: `Equiv (abs x) x ∨ Equiv (abs x) (neg x)`
//! is a decision on the sign of a real number and is not constructively
//! available. Everything here is one-sided, and that is not an omission.
//!
//! ## Vacuity, and the two things that rule it out
//!
//! The six lattice laws hold, footprint-free, of degenerate operations: a
//! `max` that always returns its first argument satisfies
//! [`le_max_left`](super::CRealPrelude::le_max_left) by reflexivity, and an
//! `abs` that is the identity satisfies `le_abs_self`, `neg_le_abs` and
//! `abs_le` — the last two only against arguments it happens to dominate, but
//! a statement test cannot see that. So two facts are proved **from the laws
//! alone**, and neither survives a degenerate operation:
//!
//! - [`not_le_zero_neg_one`](super::CRealPrelude::not_le_zero_neg_one) —
//!   `¬ (0 ≤ −1)`, from `add_le_add`, `add_comm`, `add_zero`, `add_neg`,
//!   `le_congr` and `not_le_one_zero`. It mentions no lattice operation and is
//!   the discriminator the next one consumes.
//! - [`not_equiv_abs_neg_one`](super::CRealPrelude::not_equiv_abs_neg_one) —
//!   `¬ (|−1| ≈ −1)`, i.e. **`abs` is not the identity**, from `abs_nonneg`
//!   and the above. An `abs` that returned its argument unchanged would satisfy
//!   every other theorem in this module.

// Proof scripts are long, straight-line term constructions with short
// mathematical names, exactly as in `super`.
#![allow(
    clippy::doc_markdown,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::lattice::{rmax, rmin};
use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rle, rneg, rsymm, rzero};

use super::{
    CRealPrelude, DERIVED_HEIGHT, and_intro, cle, creal_ty, div_succ, equiv, halves, modulus,
    sample,
};

/// Admit the lattice on `ℝ`: the three operations, the six order laws, the
/// three congruences, the four `abs` laws, and the two non-triviality
/// discriminations.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_lattice(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_operation(d, p, p.max, true)?;
    declare_operation(d, p, p.min, false)?;
    declare_abs(d, p)?;
    declare_order_laws(d, p)?;
    declare_congruences(d, p)?;
    declare_abs_laws(d, p)?;
    declare_discrimination(d, p)
}

// --- shared estimates -------------------------------------------------------

/// `h : −q ≤ u − v  ⊢  v − u ≤ q`.
fn flip(d: &mut IntDev<'_>, p: CRealPrelude, u: ExprId, v: ExprId, q: ExprId, h: ExprId) -> ExprId {
    let rat = p.rat;
    let negated_q = rneg(d, q);
    let forward = rsub(d, rat, u, v);
    let backward = rsub(d, rat, v, u);
    let raised = d.lemma(rat.neg_le_neg, &[negated_q, forward, h]);
    let twice = rneg(d, negated_q);
    let negated_forward = rneg(d, forward);
    let swap = d.lemma(rat.neg_sub, &[u, v]);
    let at_left = rat_eq_rewrite(d, negated_forward, backward, swap, raised, &|d, t| {
        rle(d, rat, t, twice)
    });
    let collapse = d.lemma(rat.neg_neg, &[q]);
    rat_eq_rewrite(d, twice, q, collapse, at_left, &|d, t| {
        rle(d, rat, backward, t)
    })
}

/// `h : v − u ≤ q  ⊢  −q ≤ u − v` — the inverse of [`flip`].
fn unflip(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let rat = p.rat;
    let negated_q = rneg(d, q);
    let backward = rsub(d, rat, v, u);
    let forward = rsub(d, rat, u, v);
    let raised = d.lemma(rat.neg_le_neg, &[backward, q, h]);
    let negated_backward = rneg(d, backward);
    let swap = d.lemma(rat.neg_sub, &[v, u]);
    rat_eq_rewrite(d, negated_backward, forward, swap, raised, &|d, t| {
        rle(d, rat, negated_q, t)
    })
}

/// From `Within (a₁ − a₂) q` and `Within (b₁ − b₂) q`, derive
/// `Within (op a₁ b₁ − op a₂ b₂) q` — the **one-Lipschitz** estimate, both
/// sides.
///
/// This single helper is the regularity proof of both operations *and* both
/// congruences: regularity supplies the two `Within`s from
/// [`CReal.regular`](super::CRealPrelude::regular), congruence supplies them
/// from the `Equiv` hypotheses, and nothing else differs.
fn lattice_within(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    join: bool,
    a1: ExprId,
    b1: ExprId,
    a2: ExprId,
    b2: ExprId,
    q: ExprId,
    wa: ExprId,
    wb: ExprId,
) -> ExprId {
    let rat = p.rat;
    let estimate = if join { rat.sub_max_le } else { rat.sub_min_le };
    let combine = |d: &mut IntDev<'_>, u: ExprId, v: ExprId| -> ExprId {
        if join {
            rmax(d, rat, u, v)
        } else {
            rmin(d, rat, u, v)
        }
    };

    let first = rsub(d, rat, a1, a2);
    let second = rsub(d, rat, b1, b2);
    let (lower_a, upper_a) = halves(d, p, first, q, wa);
    let (lower_b, upper_b) = halves(d, p, second, q, wb);

    let left = combine(d, a1, b1);
    let right = combine(d, a2, b2);
    let upper = d.lemma(estimate, &[a1, b1, a2, b2, q, upper_a, upper_b]);

    let reversed_a = flip(d, p, a1, a2, q, lower_a);
    let reversed_b = flip(d, p, b1, b2, q, lower_b);
    let reversed = d.lemma(estimate, &[a2, b2, a1, b1, q, reversed_a, reversed_b]);
    let lower = unflip(d, p, left, right, q, reversed);

    let difference = rsub(d, rat, left, right);
    let negated_q = rneg(d, q);
    let lower_ty = rle(d, rat, negated_q, difference);
    let upper_ty = rle(d, rat, difference, q);
    and_intro(d, p, lower_ty, upper_ty, lower, upper)
}

/// From `hle : α ≤ β`, derive `α − β ≤ 2/(n+1)` — the shape every `le` on
/// `CReal` unfolds to when the two samples are already ordered.
fn dominated(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    alpha: ExprId,
    beta: ExprId,
    hle: ExprId,
    n: ExprId,
) -> ExprId {
    let rat = p.rat;
    let zero = rzero(d, rat);
    let padded = radd(d, beta, zero);
    let expand = {
        let forward = d.lemma(rat.add_zero, &[beta]);
        rsymm(d, padded, beta, forward)
    };
    let shifted = rat_eq_rewrite(d, beta, padded, expand, hle, &|d, t| rle(d, rat, alpha, t));
    let nonpos = d.lemma(rat.sub_le_of_le, &[alpha, beta, zero, shifted]);
    let bound = div_succ(d, p, 2, n);
    let two = d.num(2);
    let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two, n]);
    let difference = rsub(d, rat, alpha, beta);
    d.lemma(rat.le_trans, &[difference, zero, bound, nonpos, nonneg])
}

// --- the operations ---------------------------------------------------------

/// `CReal.max` / `CReal.min`: pointwise, at the **same** index, with regularity
/// from [`lattice_within`].
fn declare_operation(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    name: NameId,
    join: bool,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let representative = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let left = sample(d, p, x, n);
        let right = sample(d, p, y, n);
        let body = if join {
            rmax(d, rat, left, right)
        } else {
            rmin(d, rat, left, right)
        };
        d.lam_fv(n_fv, nat, body)
    };
    let regularity = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let xm = sample(d, p, x, m);
        let xn = sample(d, p, x, n);
        let ym = sample(d, p, y, m);
        let yn = sample(d, p, y, n);
        let bound = modulus(d, p, m, n);
        let wx = d.lemma(p.regular, &[x, m, n]);
        let wy = d.lemma(p.regular, &[y, m, n]);
        let body = lattice_within(d, p, join, xm, ym, xn, yn, bound, wx, wy);
        let over_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(m_fv, nat, over_n)
    };
    let constructor = d.kernel().const_(p.mk, vec![]);
    let built = d.apply(constructor, &[representative, regularity]);
    let value = {
        let with_y = d.lam_fv(y_fv, carrier, built);
        d.lam_fv(x_fv, carrier, with_y)
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
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 5),
    })
}

/// `CReal.abs x := CReal.max x (CReal.neg x)` — no new sequence, no new
/// regularity obligation.
fn declare_abs(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let negated = d.const_app(p.neg, &[x]);
    let body = d.const_app(p.max, &[x, negated]);
    let value = d.lam_fv(x_fv, carrier, body);
    let ty = d.arrow(carrier, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.abs,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 6),
    })
}

// --- the six order laws -----------------------------------------------------

/// A law of the shape `le u v` where one side is a lattice operation and the
/// other is one of its arguments, proved pointwise from the matching `ℚ`
/// domination.
///
/// The `CReal` operation and the `ℚ` operation are **separate** parameters on
/// purpose: the statement is built over `CReal` and the proof over the samples,
/// and a single builder used for both silently applies `CReal.max` to two
/// rationals — which is what the kernel refuses first.
fn declare_domination(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    name: NameId,
    creal_op: NameId,
    rat_op: NameId,
    op_on_right: bool,
    plain_second: bool,
    witness: NameId,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let body = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let xn = sample(d, p, x, n);
        let yn = sample(d, p, y, n);
        let combined = d.const_app(rat_op, &[xn, yn]);
        let plain = if plain_second { yn } else { xn };
        let (alpha, beta) = if op_on_right {
            (plain, combined)
        } else {
            (combined, plain)
        };
        let hle = d.lemma(witness, &[xn, yn]);
        let at_index = dominated(d, p, alpha, beta, hle, n);
        d.lam_fv(n_fv, nat, at_index)
    };
    let value = {
        let with_y = d.lam_fv(y_fv, carrier, body);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let combined = d.const_app(creal_op, &[x, y]);
        let plain = if plain_second { y } else { x };
        let conclusion = if op_on_right {
            cle(d, p, plain, combined)
        } else {
            cle(d, p, combined, plain)
        };
        let with_y = d.pi_fv(y_fv, carrier, conclusion);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

/// The two universal properties: `max_le` and `le_min`, each one `ℚ` case split
/// at every index.
fn declare_universal(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    name: NameId,
    join: bool,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let rat_carrier = crate::rat_prelude::ops::rat_ty(d);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let side = |d: &mut IntDev<'_>, point: ExprId| -> ExprId {
        if join {
            cle(d, p, point, z)
        } else {
            cle(d, p, z, point)
        }
    };
    let first = side(d, x);
    let second = side(d, y);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let body = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let xn = sample(d, p, x, n);
        let yn = sample(d, p, y, n);
        let zn = sample(d, p, z, n);
        let q = div_succ(d, p, 2, n);
        let at_x = d.apply(h1, &[n]);
        let at_y = d.apply(h2, &[n]);
        let predicate = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let difference = if join {
                rsub(d, rat, t, zn)
            } else {
                rsub(d, rat, zn, t)
            };
            let claim = rle(d, rat, difference, q);
            d.lam_fv(t_fv, rat_carrier, claim)
        };
        // `max_cases` selects `y` when `x ≤ y`; `min_cases` selects `x`.
        let (on_le, on_ge) = if join { (at_y, at_x) } else { (at_x, at_y) };
        let forward = {
            let hypothesis = rle(d, rat, xn, yn);
            let fv = d.fresh_fvar();
            d.lam_fv(fv, hypothesis, on_le)
        };
        let backward = {
            let hypothesis = rle(d, rat, yn, xn);
            let fv = d.fresh_fvar();
            d.lam_fv(fv, hypothesis, on_ge)
        };
        let cases = if join { rat.max_cases } else { rat.min_cases };
        let at_index = d.lemma(cases, &[xn, yn, predicate, forward, backward]);
        d.lam_fv(n_fv, nat, at_index)
    };
    let operation = if join { p.max } else { p.min };
    let value = {
        let with_h2 = d.lam_fv(h2_fv, second, body);
        let with_h1 = d.lam_fv(h1_fv, first, with_h2);
        let with_z = d.lam_fv(z_fv, carrier, with_h1);
        let with_y = d.lam_fv(y_fv, carrier, with_z);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let combined = d.const_app(operation, &[x, y]);
        let conclusion = if join {
            cle(d, p, combined, z)
        } else {
            cle(d, p, z, combined)
        };
        let with_h2 = d.arrow(second, conclusion);
        let with_h1 = d.arrow(first, with_h2);
        let with_z = d.pi_fv(z_fv, carrier, with_h1);
        let with_y = d.pi_fv(y_fv, carrier, with_z);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

fn declare_order_laws(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    declare_domination(
        d,
        p,
        p.le_max_left,
        p.max,
        rat.max,
        true,
        false,
        rat.le_max_left,
    )?;
    declare_domination(
        d,
        p,
        p.le_max_right,
        p.max,
        rat.max,
        true,
        true,
        rat.le_max_right,
    )?;
    declare_domination(
        d,
        p,
        p.min_le_left,
        p.min,
        rat.min,
        false,
        false,
        rat.min_le_left,
    )?;
    declare_domination(
        d,
        p,
        p.min_le_right,
        p.min,
        rat.min,
        false,
        true,
        rat.min_le_right,
    )?;
    declare_universal(d, p, p.max_le, true)?;
    declare_universal(d, p, p.le_min, false)
}

// --- the congruences --------------------------------------------------------

fn declare_congruence(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    name: NameId,
    join: bool,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let x2_fv = d.fresh_fvar();
    let x2 = d.kernel().fvar(x2_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let y2_fv = d.fresh_fvar();
    let y2 = d.kernel().fvar(y2_fv);
    let first = equiv(d, p, x, x2);
    let second = equiv(d, p, y, y2);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let body = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let xn = sample(d, p, x, n);
        let x2n = sample(d, p, x2, n);
        let yn = sample(d, p, y, n);
        let y2n = sample(d, p, y2, n);
        let q = div_succ(d, p, 2, n);
        let wa = d.apply(h1, &[n]);
        let wb = d.apply(h2, &[n]);
        let at_index = lattice_within(d, p, join, xn, yn, x2n, y2n, q, wa, wb);
        d.lam_fv(n_fv, nat, at_index)
    };
    let operation = if join { p.max } else { p.min };
    let value = {
        let with_h2 = d.lam_fv(h2_fv, second, body);
        let with_h1 = d.lam_fv(h1_fv, first, with_h2);
        let with_y2 = d.lam_fv(y2_fv, carrier, with_h1);
        let with_y = d.lam_fv(y_fv, carrier, with_y2);
        let with_x2 = d.lam_fv(x2_fv, carrier, with_y);
        d.lam_fv(x_fv, carrier, with_x2)
    };
    let ty = {
        let left = d.const_app(operation, &[x, y]);
        let right = d.const_app(operation, &[x2, y2]);
        let conclusion = equiv(d, p, left, right);
        let with_h2 = d.arrow(second, conclusion);
        let with_h1 = d.arrow(first, with_h2);
        let with_y2 = d.pi_fv(y2_fv, carrier, with_h1);
        let with_y = d.pi_fv(y_fv, carrier, with_y2);
        let with_x2 = d.pi_fv(x2_fv, carrier, with_y);
        d.pi_fv(x_fv, carrier, with_x2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

fn declare_congruences(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_congruence(d, p, p.max_congr, true)?;
    declare_congruence(d, p, p.min_congr, false)?;

    // abs_congr : Equiv x y → Equiv (abs x) (abs y) — `max_congr` with
    // `neg_congr` in its second slot.
    let carrier = creal_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let hypothesis = equiv(d, p, x, y);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let negated_x = d.const_app(p.neg, &[x]);
    let negated_y = d.const_app(p.neg, &[y]);
    let flipped = d.lemma(p.neg_congr, &[x, y, h]);
    let body = d.lemma(p.max_congr, &[x, y, negated_x, negated_y, h, flipped]);
    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, body);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let left = d.const_app(p.abs, &[x]);
        let right = d.const_app(p.abs, &[y]);
        let conclusion = equiv(d, p, left, right);
        let with_h = d.arrow(hypothesis, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, with_h);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.abs_congr,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `abs` ------------------------------------------------------------------

fn declare_abs_laws(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    // le_abs_self : le x (abs x)  —  le_max_left x (−x).
    // neg_le_abs  : le (neg x) (abs x)  —  le_max_right x (−x).
    let projection = |d: &mut IntDev<'_>,
                      name: NameId,
                      witness: NameId,
                      on_neg: bool|
     -> Result<(), KernelError> {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let negated = d.const_app(p.neg, &[x]);
        let body = d.lemma(witness, &[x, negated]);
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = {
            let source = if on_neg { negated } else { x };
            let target = d.const_app(p.abs, &[x]);
            let conclusion = cle(d, p, source, target);
            d.pi_fv(x_fv, carrier, conclusion)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
    };
    projection(d, p.le_abs_self, p.le_max_left, false)?;
    projection(d, p.neg_le_abs, p.le_max_right, true)?;

    // abs_le : le x z → le (neg x) z → le (abs x) z  —  max_le verbatim.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let negated = d.const_app(p.neg, &[x]);
        let first = cle(d, p, x, z);
        let second = cle(d, p, negated, z);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let body = d.lemma(p.max_le, &[x, negated, z, h1, h2]);
        let value = {
            let with_h2 = d.lam_fv(h2_fv, second, body);
            let with_h1 = d.lam_fv(h1_fv, first, with_h2);
            let with_z = d.lam_fv(z_fv, carrier, with_h1);
            d.lam_fv(x_fv, carrier, with_z)
        };
        let ty = {
            let target = d.const_app(p.abs, &[x]);
            let conclusion = cle(d, p, target, z);
            let with_h2 = d.arrow(second, conclusion);
            let with_h1 = d.arrow(first, with_h2);
            let with_z = d.pi_fv(z_fv, carrier, with_h1);
            d.pi_fv(x_fv, carrier, with_z)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.abs_le,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // abs_nonneg : le zero (abs x). The only genuinely new fact, and it rests
    // on the one `ℚ` lemma the lattice module proves with `Rat.le_total`.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let zero = d.kernel().const_(p.zero, vec![]);
        let magnitude = d.const_app(p.abs, &[x]);
        let body = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let alpha = sample(d, p, zero, n);
            let beta = sample(d, p, magnitude, n);
            let xn = sample(d, p, x, n);
            let hle = d.lemma(rat.zero_le_max_neg, &[xn]);
            let at_index = dominated(d, p, alpha, beta, hle, n);
            d.lam_fv(n_fv, nat, at_index)
        };
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = {
            let conclusion = cle(d, p, zero, magnitude);
            d.pi_fv(x_fv, carrier, conclusion)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.abs_nonneg,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

// --- non-triviality ---------------------------------------------------------

/// The two discriminations, **derived from the laws alone** — no computation on
/// a representative, and no appeal to a rendered statement.
fn declare_discrimination(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);
    let negative = d.const_app(p.neg, &[one]);

    // not_le_zero_neg_one : ¬ (0 ≤ −1).
    //
    // Adding `1` to both sides of `0 ≤ −1` gives `0 + 1 ≤ (−1) + 1`, and the
    // two sides are `Equiv`-equal to `1` and `0`. Mentions no lattice
    // operation: it is the discriminator the next theorem consumes.
    {
        let hypothesis = cle(d, p, zero, negative);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let reflexive = d.lemma(p.le_refl, &[one]);
        let scaled = d.lemma(p.add_le_add, &[zero, negative, one, one, h, reflexive]);

        let left = d.const_app(p.add, &[zero, one]);
        let left_swapped = d.const_app(p.add, &[one, zero]);
        let left_eq = {
            let commute = d.lemma(p.add_comm, &[zero, one]);
            let collapse = d.lemma(p.add_zero, &[one]);
            d.lemma(p.equiv_trans, &[left, left_swapped, one, commute, collapse])
        };
        let right = d.const_app(p.add, &[negative, one]);
        let right_swapped = d.const_app(p.add, &[one, negative]);
        let right_eq = {
            let commute = d.lemma(p.add_comm, &[negative, one]);
            let cancel = d.lemma(p.add_neg, &[one]);
            d.lemma(
                p.equiv_trans,
                &[right, right_swapped, zero, commute, cancel],
            )
        };
        let absurd = d.lemma(
            p.le_congr,
            &[left, one, right, zero, left_eq, right_eq, scaled],
        );
        let refuted = d.lemma(p.not_le_one_zero, &[]);
        let contradiction = d.apply(refuted, &[absurd]);
        let value = d.lam_fv(h_fv, hypothesis, contradiction);
        let ty = d.not(hypothesis);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.not_le_zero_neg_one,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // not_equiv_abs_neg_one : ¬ (|−1| ≈ −1) — **`abs` is not the identity**.
    //
    // Every other theorem in this module holds of `abs x := x`; this one does
    // not, and it needs nothing but `abs_nonneg` and the theorem above.
    {
        let magnitude = d.const_app(p.abs, &[negative]);
        let hypothesis = equiv(d, p, magnitude, negative);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let nonneg = d.lemma(p.abs_nonneg, &[negative]);
        let reflexive = d.lemma(p.equiv_refl, &[zero]);
        let absurd = d.lemma(
            p.le_congr,
            &[zero, zero, magnitude, negative, reflexive, h, nonneg],
        );
        let refuted = d.lemma(p.not_le_zero_neg_one, &[]);
        let contradiction = d.apply(refuted, &[absurd]);
        let value = d.lam_fv(h_fv, hypothesis, contradiction);
        let ty = d.not(hypothesis);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.not_equiv_abs_neg_one,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

// --- monotonicity and the spread (ADR-0519; the Fundamental Theorem, rung 3) --
//
// A **second** entry point, dispatched after
// `order_extra::declare_order_extra_abs` in `creal.rs`'s build order:
// [`CRealPrelude::max_sub_min`] needs [`CRealPrelude::neg_sub_swap`], which
// that step provides and which [`declare_lattice`] above therefore cannot use.
//
// ## Why these two facts, and why neither is an estimate
//
// `CReal.antiderivative`'s argument is the clamp `max a (min x b)`
// (`creal/integral.rs`), so the Fundamental Theorem needs exactly two things
// about the lattice that the six laws do not give:
//
// - **`clamp_mono`** — the clamp is monotone. `HasDerivativeOn`'s spec
//   quantifies over an unordered pair `x, y` and the two antiderivative values
//   are integrals up to `clamp x` and `clamp y`, so relating them at all needs
//   `x ≤ y → clamp x ≤ clamp y`. Both halves are one `le_trans` against a
//   universal property; no sample and no index appears.
// - **`max_sub_min`** — `max x y − min x y ≈ |y − x|`. This is the step that
//   turns the orientation-free estimate (both legs based at `min x y`) back
//   into the `|y − x|` the spec asks for.
//
// ## The orientation obstruction, and why it is not here
//
// `max x y − min x y = |y − x|` is proved **by cases** in every classical
// text, and `CReal.le` is undecidable, so that case split is unavailable. It
// is also unnecessary — both inequalities are one-sided consequences of the
// universal properties:
//
// - `|y − x| ≤ max − min` is [`CRealPrelude::abs_le`] against two
//   `add_le_add`s, each pairing a projection (`le_max_left`/`le_max_right`)
//   with `neg_le_neg` of a projection (`min_le_left`/`min_le_right`).
// - `max − min ≤ |y − x|` is `max_le` against `x, y ≤ min x y + |y − x|`, and
//   each of those is `le_min` against a pair whose second leg is exactly
//   `le_abs_self`/`neg_le_abs`. The **lower** bound on the meet — the
//   direction a meet does not hand you — is `le_min`, which is the only way to
//   bound a meet from below and is precisely what makes the decision
//   unnecessary.
//
// The three `le`-transposition steps are `creal/crossing.rs`'s own
// `le_sub_of_le_add` / `le_add_of_le_sub_right`, made `pub(super)` there
// rather than copied here.

/// Admit the two lattice monotonicity laws, the clamp's monotonicity, and
/// `CReal.max_sub_min`. See this section's own documentation.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_lattice_extra(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_min_mono_left(d, p)?;
    declare_max_mono_right(d, p)?;
    declare_clamp_mono(d, p)?;
    declare_clamp_id(d, p)?;
    declare_max_sub_min(d, p)
}

/// `CReal.clamp_id : ∀ a b x, le a x → le x b →
/// Equiv (max a (min x b)) x` — **the clamp is the identity on its own
/// interval**.
///
/// The Fundamental Theorem's spec quantifies over `x` with `a ≤ x ≤ b`, and
/// `CReal.antiderivative`'s value at `x` is an integral up to `max a (min x
/// b)`. Every algebraic step that has to see the raw `x` — the error term
/// `F(x)·(y − x)` and the bound `|y − x|` — needs this.
///
/// Both halves are [`CRealPrelude::equiv_of_le_le`] against the universal
/// properties: `min x b ≈ x` from `min_le_left` and `le_min` at `hxb`, and
/// `max a x ≈ x` from `max_le` at `hax` and `le_max_right`. No case split
/// and no sample.
fn declare_clamp_id(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let hax_ty = cle(d, p, a, x);
    let hax_fv = d.fresh_fvar();
    let hax = d.kernel().fvar(hax_fv);
    let hxb_ty = cle(d, p, x, b);
    let hxb_fv = d.fresh_fvar();
    let hxb = d.kernel().fvar(hxb_fv);

    let mn = d.const_app(p.min, &[x, b]);
    let clamp = d.const_app(p.max, &[a, mn]);
    let max_ax = d.const_app(p.max, &[a, x]);

    let refl_x = d.lemma(p.le_refl, &[x]);
    let mn_le_x = d.lemma(p.min_le_left, &[x, b]);
    let x_le_mn = d.lemma(p.le_min, &[x, b, x, refl_x, hxb]);
    let mn_eq = d.lemma(p.equiv_of_le_le, &[mn, x, mn_le_x, x_le_mn]);

    let refl_a = d.lemma(p.equiv_refl, &[a]);
    let outer = d.lemma(p.max_congr, &[a, a, mn, x, refl_a, mn_eq]);

    let refl_x2 = d.lemma(p.le_refl, &[x]);
    let max_le_x = d.lemma(p.max_le, &[a, x, x, hax, refl_x2]);
    let x_le_max = d.lemma(p.le_max_right, &[a, x]);
    let max_eq = d.lemma(p.equiv_of_le_le, &[max_ax, x, max_le_x, x_le_max]);

    let body = d.lemma(p.equiv_trans, &[clamp, max_ax, x, outer, max_eq]);

    let concl = equiv(d, p, clamp, x);
    let ty = {
        let t = d.arrow(hxb_ty, concl);
        let t = d.arrow(hax_ty, t);
        let t = d.pi_fv(x_fv, carrier, t);
        let t = d.pi_fv(b_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    let value = {
        let v = d.lam_fv(hxb_fv, hxb_ty, body);
        let v = d.lam_fv(hax_fv, hax_ty, v);
        let v = d.lam_fv(x_fv, carrier, v);
        let v = d.lam_fv(b_fv, carrier, v);
        d.lam_fv(a_fv, carrier, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.clamp_id,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.neg x`.
fn lneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

/// `CReal.min_mono_left : ∀ x y b, le x y → le (min x b) (min y b)`.
fn declare_min_mono_left(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let h_ty = cle(d, p, x, y);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let mxb = d.const_app(p.min, &[x, b]);
    let myb = d.const_app(p.min, &[y, b]);

    let mxb_le_x = d.lemma(p.min_le_left, &[x, b]);
    let mxb_le_y = d.lemma(p.le_trans, &[mxb, x, y, mxb_le_x, h]);
    let mxb_le_b = d.lemma(p.min_le_right, &[x, b]);
    let body = d.lemma(p.le_min, &[y, b, mxb, mxb_le_y, mxb_le_b]);

    let concl = cle(d, p, mxb, myb);
    let ty = {
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(b_fv, carrier, t);
        let t = d.pi_fv(y_fv, carrier, t);
        d.pi_fv(x_fv, carrier, t)
    };
    let value = {
        let v = d.lam_fv(h_fv, h_ty, body);
        let v = d.lam_fv(b_fv, carrier, v);
        let v = d.lam_fv(y_fv, carrier, v);
        d.lam_fv(x_fv, carrier, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.min_mono_left,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.max_mono_right : ∀ a u v, le u v → le (max a u) (max a v)`.
fn declare_max_mono_right(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let h_ty = cle(d, p, u, v);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let mau = d.const_app(p.max, &[a, u]);
    let mav = d.const_app(p.max, &[a, v]);

    let a_le = d.lemma(p.le_max_left, &[a, v]);
    let v_le = d.lemma(p.le_max_right, &[a, v]);
    let u_le = d.lemma(p.le_trans, &[u, v, mav, h, v_le]);
    let body = d.lemma(p.max_le, &[a, u, mav, a_le, u_le]);

    let concl = cle(d, p, mau, mav);
    let ty = {
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(v_fv, carrier, t);
        let t = d.pi_fv(u_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    let value = {
        let w = d.lam_fv(h_fv, h_ty, body);
        let w = d.lam_fv(v_fv, carrier, w);
        let w = d.lam_fv(u_fv, carrier, w);
        d.lam_fv(a_fv, carrier, w)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.max_mono_right,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.clamp_mono : ∀ a b x y, le x y →
/// le (max a (min x b)) (max a (min y b))` — the clamp
/// `creal/integral.rs`'s `CReal.antiderivative` is built from is monotone.
fn declare_clamp_mono(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let h_ty = cle(d, p, x, y);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let mxb = d.const_app(p.min, &[x, b]);
    let myb = d.const_app(p.min, &[y, b]);
    let inner = d.lemma(p.min_mono_left, &[x, y, b, h]);
    let body = d.lemma(p.max_mono_right, &[a, mxb, myb, inner]);

    let cx = d.const_app(p.max, &[a, mxb]);
    let cy = d.const_app(p.max, &[a, myb]);
    let concl = cle(d, p, cx, cy);
    let ty = {
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(y_fv, carrier, t);
        let t = d.pi_fv(x_fv, carrier, t);
        let t = d.pi_fv(b_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    let value = {
        let v = d.lam_fv(h_fv, h_ty, body);
        let v = d.lam_fv(y_fv, carrier, v);
        let v = d.lam_fv(x_fv, carrier, v);
        let v = d.lam_fv(b_fv, carrier, v);
        d.lam_fv(a_fv, carrier, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.clamp_mono,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.max_sub_min : ∀ x y,
/// Equiv (add (max x y) (neg (min x y))) (abs (add y (neg x)))` — the spread
/// of a pair is the magnitude of its difference, with **no case split**. See
/// this section's own documentation for why the classical proof's decision is
/// not needed.
fn declare_max_sub_min(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let mx = d.const_app(p.max, &[x, y]);
    let mn = d.const_app(p.min, &[x, y]);
    let n_mn = lneg(d, p, mn);
    let n_x = lneg(d, p, x);
    let n_y = lneg(d, p, y);
    let spread = super::cadd(d, p, mx, n_mn);
    let diff = super::cadd(d, p, y, n_x);
    let magnitude = d.const_app(p.abs, &[diff]);
    let n_mag = lneg(d, p, magnitude);
    let neg_diff = lneg(d, p, diff);
    let x_ny = super::cadd(d, p, x, n_y);

    // `Equiv (neg (y − x)) (x − y)`.
    let swap = d.lemma(p.neg_sub_swap, &[y, x]);

    // --- |y − x| ≤ max x y − min x y ---------------------------------------
    let y_le_mx = d.lemma(p.le_max_right, &[x, y]);
    let mn_le_x = d.lemma(p.min_le_left, &[x, y]);
    let nx_le_nmn = d.lemma(p.neg_le_neg, &[mn, x, mn_le_x]);
    let leg1 = d.lemma(p.add_le_add, &[y, mx, n_x, n_mn, y_le_mx, nx_le_nmn]);

    let x_le_mx = d.lemma(p.le_max_left, &[x, y]);
    let mn_le_y = d.lemma(p.min_le_right, &[x, y]);
    let ny_le_nmn = d.lemma(p.neg_le_neg, &[mn, y, mn_le_y]);
    let pre2 = d.lemma(p.add_le_add, &[x, mx, n_y, n_mn, x_le_mx, ny_le_nmn]);
    let swap_symm = d.lemma(p.equiv_symm, &[neg_diff, x_ny, swap]);
    let refl_spread = d.lemma(p.equiv_refl, &[spread]);
    let leg2 = d.lemma(
        p.le_congr,
        &[x_ny, neg_diff, spread, spread, swap_symm, refl_spread, pre2],
    );
    let upper = d.lemma(p.abs_le, &[diff, spread, leg1, leg2]);

    // --- max x y − min x y ≤ |y − x| ---------------------------------------
    //
    // `le (neg |y − x|) zero`, so subtracting the magnitude only decreases.
    let mag_nonneg = d.lemma(p.abs_nonneg, &[diff]);
    let nmag_le_nzero = d.lemma(p.neg_le_neg, &[zero_c, magnitude, mag_nonneg]);
    let neg_zero = lneg(d, p, zero_c);
    let nz = super::series::neg_zero_equiv(d, p);
    let refl_nmag = d.lemma(p.equiv_refl, &[n_mag]);
    let nmag_le_zero = d.lemma(
        p.le_congr,
        &[n_mag, n_mag, neg_zero, zero_c, refl_nmag, nz, nmag_le_nzero],
    );

    // `le (add w (neg |y − x|)) w`, at `w := x` and `w := y`.
    let sub_le_self = |d: &mut IntDev<'_>, w: ExprId| -> ExprId {
        let refl_w = d.lemma(p.le_refl, &[w]);
        let step = d.lemma(p.add_le_add, &[w, w, n_mag, zero_c, refl_w, nmag_le_zero]);
        let w_zero = super::cadd(d, p, w, zero_c);
        let trim = d.lemma(p.add_zero, &[w]);
        let shifted = super::cadd(d, p, w, n_mag);
        let refl_shifted = d.lemma(p.equiv_refl, &[shifted]);
        d.lemma(
            p.le_congr,
            &[shifted, shifted, w_zero, w, refl_shifted, trim, step],
        )
    };
    let x_nmag_le_x = sub_le_self(d, x);
    let y_nmag_le_y = sub_le_self(d, y);

    // `x − y ≤ |y − x|` and `y − x ≤ |y − x|`.
    let refl_mag = d.lemma(p.equiv_refl, &[magnitude]);
    let negdiff_le_mag = d.lemma(p.neg_le_abs, &[diff]);
    let xny_le_mag = d.lemma(
        p.le_congr,
        &[
            neg_diff,
            x_ny,
            magnitude,
            magnitude,
            swap,
            refl_mag,
            negdiff_le_mag,
        ],
    );
    let diff_le_mag = d.lemma(p.le_abs_self, &[diff]);

    // Transpose each into `w − |y − x| ≤ (the other point)`.
    let x_step = super::crossing::le_add_of_le_sub_right(d, p, x, y, magnitude, xny_le_mag);
    let x_nmag_le_y = super::crossing::le_sub_of_le_add(d, p, x, magnitude, y, x_step);
    let y_step = super::crossing::le_add_of_le_sub_right(d, p, y, x, magnitude, diff_le_mag);
    let y_nmag_le_x = super::crossing::le_sub_of_le_add(d, p, y, magnitude, x, y_step);

    // The lower bound on the meet — the only route that does not decide the
    // order — then `max_le` and one last transposition.
    let x_nmag = super::cadd(d, p, x, n_mag);
    let y_nmag = super::cadd(d, p, y, n_mag);
    let x_nmag_le_mn = d.lemma(p.le_min, &[x, y, x_nmag, x_nmag_le_x, x_nmag_le_y]);
    let y_nmag_le_mn = d.lemma(p.le_min, &[x, y, y_nmag, y_nmag_le_x, y_nmag_le_y]);
    let x_le = super::crossing::le_add_of_le_sub_right(d, p, x, magnitude, mn, x_nmag_le_mn);
    let y_le = super::crossing::le_add_of_le_sub_right(d, p, y, magnitude, mn, y_nmag_le_mn);
    let mn_mag = super::cadd(d, p, mn, magnitude);
    let mx_le = d.lemma(p.max_le, &[x, y, mn_mag, x_le, y_le]);
    let lower = super::crossing::le_sub_of_le_add(d, p, mx, mn, magnitude, mx_le);

    let body = d.lemma(p.equiv_of_le_le, &[spread, magnitude, lower, upper]);

    let concl = equiv(d, p, spread, magnitude);
    let ty = {
        let t = d.pi_fv(y_fv, carrier, concl);
        d.pi_fv(x_fv, carrier, t)
    };
    let value = {
        let v = d.lam_fv(y_fv, carrier, body);
        d.lam_fv(x_fv, carrier, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.max_sub_min,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod lattice_extra_tests {
    use super::*;
    use crate::Declaration;

    /// **Mandatory concrete instantiation, three positives and three
    /// negative controls**, at `x := 0`, `y := 1` — the one pair for which
    /// both order facts are CLOSED terms ([`CRealPrelude::zero_lt_one`]), so
    /// nothing about the instance is assumed.
    ///
    /// Each control differs in a **small** term, never by transposing two
    /// large ones, and is checked in both directions the repository's
    /// guidance demands: not *vacuous* (the two terms are asserted not
    /// `def_eq`) and not *inverted* (the variant is genuinely FALSE here).
    ///
    /// 1. `clamp_mono` at `a := 0`, `b := 1`: `clamp 0 ≤ clamp 1`, i.e.
    ///    `0 ≤ 1`. The control exchanges the two clamps, giving `1 ≤ 0`.
    /// 2. `clamp_id` at `a := 0`, `b := 1`, `x := 1`: `max 0 (min 1 1) ≈ 1`.
    ///    The control points the same proof term at `max 0 (min 0 1) ≈ 1`,
    ///    i.e. `0 ≈ 1`.
    /// 3. `max_sub_min`: the spread is the magnitude. The
    ///    control replaces `min 0 1` by `max 0 1` — ONE subterm — making the
    ///    left side `1 − 1 ≈ 0` against a right side of `1`.
    #[test]
    fn lattice_extra_concrete_and_negative_controls() {
        crate::on_a_deep_stack(lattice_extra_concrete_and_negative_controls_body);
    }

    fn lattice_extra_concrete_and_negative_controls_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let anon = d.kernel().anon();

        let zero_c = d.kernel().const_(p.zero, vec![]);
        let one_c = d.kernel().const_(p.one, vec![]);
        let lt01 = d.lemma(p.zero_lt_one, &[]);
        let le01 = d.lemma(p.le_of_lt, &[zero_c, one_c, lt01]);

        // --- 1. clamp_mono -------------------------------------------------
        let proof_clamp = d.lemma(p.clamp_mono, &[zero_c, one_c, zero_c, one_c, le01]);
        let mn_x = d.const_app(p.min, &[zero_c, one_c]);
        let mn_y = d.const_app(p.min, &[one_c, one_c]);
        let clamp_x = d.const_app(p.max, &[zero_c, mn_x]);
        let clamp_y = d.const_app(p.max, &[zero_c, mn_y]);
        assert!(
            !d.kernel().def_eq(clamp_x, clamp_y),
            "negative control must not be vacuous: `clamp 0` and `clamp 1` \
             must be different terms"
        );

        let ty_ok = cle(&mut d, p, clamp_x, clamp_y);
        let name_ok = d.kernel().name_str(anon, "__clampMonoOk");
        let res_ok = d.kernel().add_declaration(Declaration::Theorem {
            name: name_ok,
            uparams: vec![],
            ty: ty_ok,
            value: proof_clamp,
        });
        assert!(
            res_ok.is_ok(),
            "clamp_mono at a := 0, b := 1, x := 0, y := 1 must prove \
             `max 0 (min 0 1) ≤ max 0 (min 1 1)`: {:?}",
            res_ok.err()
        );

        let ty_bad = cle(&mut d, p, clamp_y, clamp_x);
        let name_bad = d.kernel().name_str(anon, "__clampMonoBad");
        let res_bad = d.kernel().add_declaration(Declaration::Theorem {
            name: name_bad,
            uparams: vec![],
            ty: ty_bad,
            value: proof_clamp,
        });
        assert!(
            res_bad.is_err(),
            "negative control must be REJECTED: the same proof term cannot \
             prove the reversed `max 0 (min 1 1) ≤ max 0 (min 0 1)`, i.e. 1 ≤ 0"
        );

        // --- 2. clamp_id ---------------------------------------------------
        //
        // At `a := 0`, `b := 1`, `x := 1`: `max 0 (min 1 1) ≈ 1`. The
        // control keeps the same proof term against `max 0 (min 0 1) ≈ 1`,
        // i.e. `0 ≈ 1` — ONE subterm changed, and the two clamp terms were
        // already asserted distinct above.
        let refl_one = d.lemma(p.le_refl, &[one_c]);
        let proof_id = d.lemma(p.clamp_id, &[zero_c, one_c, one_c, le01, refl_one]);
        let ty_id_ok = equiv(&mut d, p, clamp_y, one_c);
        let name_id_ok = d.kernel().name_str(anon, "__clampIdOk");
        let res_id_ok = d.kernel().add_declaration(Declaration::Theorem {
            name: name_id_ok,
            uparams: vec![],
            ty: ty_id_ok,
            value: proof_id,
        });
        assert!(
            res_id_ok.is_ok(),
            "clamp_id at a := 0, b := 1, x := 1 must prove \
             `max 0 (min 1 1) ≈ 1`: {:?}",
            res_id_ok.err()
        );
        let ty_id_bad = equiv(&mut d, p, clamp_x, one_c);
        let name_id_bad = d.kernel().name_str(anon, "__clampIdBad");
        let res_id_bad = d.kernel().add_declaration(Declaration::Theorem {
            name: name_id_bad,
            uparams: vec![],
            ty: ty_id_bad,
            value: proof_id,
        });
        assert!(
            res_id_bad.is_err(),
            "negative control must be REJECTED: `max 0 (min 0 1)` is 0, \
             not 1"
        );

        // --- 3. max_sub_min ------------------------------------------------
        let proof_spread = d.lemma(p.max_sub_min, &[zero_c, one_c]);
        let mx = d.const_app(p.max, &[zero_c, one_c]);
        let mn = d.const_app(p.min, &[zero_c, one_c]);
        let n_mn = lneg(&mut d, p, mn);
        let n_mx = lneg(&mut d, p, mx);
        let spread = super::super::cadd(&mut d, p, mx, n_mn);
        let spread_bad = super::super::cadd(&mut d, p, mx, n_mx);
        let n_zero = lneg(&mut d, p, zero_c);
        let diff = super::super::cadd(&mut d, p, one_c, n_zero);
        let magnitude = d.const_app(p.abs, &[diff]);
        assert!(
            !d.kernel().def_eq(spread, spread_bad),
            "negative control must not be vacuous: `max − min` and \
             `max − max` must be different terms"
        );

        let ty_spread_ok = equiv(&mut d, p, spread, magnitude);
        let name_spread_ok = d.kernel().name_str(anon, "__maxSubMinOk");
        let res_spread_ok = d.kernel().add_declaration(Declaration::Theorem {
            name: name_spread_ok,
            uparams: vec![],
            ty: ty_spread_ok,
            value: proof_spread,
        });
        assert!(
            res_spread_ok.is_ok(),
            "max_sub_min at x := 0, y := 1 must prove \
             `max 0 1 − min 0 1 ≈ |1 − 0|`: {:?}",
            res_spread_ok.err()
        );

        let ty_spread_bad = equiv(&mut d, p, spread_bad, magnitude);
        let name_spread_bad = d.kernel().name_str(anon, "__maxSubMinBad");
        let res_spread_bad = d.kernel().add_declaration(Declaration::Theorem {
            name: name_spread_bad,
            uparams: vec![],
            ty: ty_spread_bad,
            value: proof_spread,
        });
        assert!(
            res_spread_bad.is_err(),
            "negative control must be REJECTED: `max 0 1 − max 0 1 ≈ 0`, \
             not `|1 − 0| = 1`"
        );
    }
}
