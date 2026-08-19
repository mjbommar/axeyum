//! **The lattice on ℝ**: `CReal.max`, `CReal.min` and `CReal.abs`, pointwise
//! and with **no index shift** (ADR-0490, phase R5).
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
