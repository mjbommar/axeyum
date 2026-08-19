//! **Apartness**, and the theorem that says why a total inverse cannot exist
//! (ADR-0510, phase F1).
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
//! choosing which of the two reciprocals to compute means eliminating the
//! disjunction into `Type`. That is not a limitation of this kernel — it is the
//! reason CoRN carries apartness in `CProp`, a `Type`-valued logic, rather than
//! in `Prop`.
//!
//! **But the `Prop`-ness of the hypothesis is not the obstruction, and that is
//! worth being exact about.** A function may take a `Prop` argument and return
//! a `Type`; what it may not do is *branch* on it. So the one-sided
//! [`PosBound`](super::CRealPrelude::pos_bound) — `1/(k+1) ≤ x`, no
//! disjunction anywhere — supports
//!
//! ```text
//! inv : (x : CReal) → (k : Nat) → PosBound x k → CReal
//! ```
//!
//! outright, because the proof is only ever used to discharge `CReal.mk`'s
//! `Prop`-valued regularity field while the representative sequence depends on
//! `k` alone. The thing that must be data is the **modulus**, not the proof.
//! [`pos_bound_of_lt`](super::CRealPrelude::pos_bound_of_lt) is the other half
//! of that story: `0 < x` and `∃ k, PosBound x k` are the same proposition, so
//! the modulus always exists — and it exists inside an `Exists`, which is a
//! `Prop`, so no amount of proof gets it out. See
//! [`declare_no_total_inverse`] for the half of the trade that is a theorem.
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

use super::{
    CRealPrelude, DERIVED_HEIGHT, and_intro, cadd, cle, clt, creal_ty, div_succ, embed, equiv,
    gap_elim, gap_halves, gap_intro,
};
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rat_ty, rle, rneg, rzero};

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
    declare_no_total_inverse(d, p)?;
    declare_of_rat_le(d, p)?;
    declare_pos_bound(d, p)?;
    declare_pos_of_pos_bound(d, p)?;
    declare_pos_bound_of_lt(d, p)?;
    declare_of_rat_pos(d, p)?;
    declare_mul_pos(d, p)
}

/// `Equiv (add zero y) y`, as a proof term — the forward direction of
/// [`zero_add_back`].
fn zero_add_forward(d: &mut IntDev<'_>, p: CRealPrelude, y: ExprId) -> ExprId {
    let zero = czero(d, p);
    let padded = cadd(d, p, zero, y);
    let flipped = cadd(d, p, y, zero);
    let commute = d.lemma(p.add_comm, &[zero, y]);
    let collapse = d.lemma(p.add_zero, &[y]);
    d.lemma(p.equiv_trans, &[padded, flipped, y, commute, collapse])
}

/// `Equiv y (add zero y)`, as a proof term — there is no `CReal.zero_add`, the
/// 22 name `add_zero` only.
fn zero_add_back(d: &mut IntDev<'_>, p: CRealPrelude, y: ExprId) -> ExprId {
    let zero = czero(d, p);
    let padded = cadd(d, p, zero, y);
    let flipped = cadd(d, p, y, zero);
    let commute = d.lemma(p.add_comm, &[zero, y]);
    let collapse = d.lemma(p.add_zero, &[y]);
    let forward = d.lemma(p.equiv_trans, &[padded, flipped, y, commute, collapse]);
    d.lemma(p.equiv_symm, &[padded, y, forward])
}

/// `CReal.PosBound x k`.
fn pos_bound(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.pos_bound, &[x, k])
}

/// `ofRat_le : ∀ a b, Rat.le a b → CReal.le (ofRat a) (ofRat b)`.
///
/// The embedding `ℚ ↪ ℝ` is monotone, and it is not an estimate: both sides
/// sample at the *same* index, the difference is `a − b ≤ 0`, and `0` is below
/// every `2/(n+1)`.
fn declare_of_rat_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let rat_carrier = rat_ty(d);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hypothesis = rle(d, rat, a, b);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let difference = rsub(d, rat, a, b);
    let bound = div_succ(d, p, 2, n);
    let zero = rzero(d, rat);
    let opposite = rneg(d, b);
    let reflexive = d.lemma(rat.le_refl, &[opposite]);
    let shifted = d.lemma(rat.add_le_add, &[a, b, opposite, opposite, h, reflexive]);
    let cancelled = radd(d, b, opposite);
    let vanish = d.lemma(rat.add_neg, &[b]);
    let nonpositive = rat_eq_rewrite(d, cancelled, zero, vanish, shifted, &|d, t| {
        rle(d, rat, difference, t)
    });
    let two = d.num(2);
    let bound_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two, n]);
    let at_index = d.lemma(
        rat.le_trans,
        &[difference, zero, bound, nonpositive, bound_nonneg],
    );

    let value = {
        let over_n = d.lam_fv(n_fv, nat, at_index);
        let with_h = d.lam_fv(h_fv, hypothesis, over_n);
        let with_b = d.lam_fv(b_fv, rat_carrier, with_h);
        d.lam_fv(a_fv, rat_carrier, with_b)
    };
    let ty = {
        let left = embed(d, p, a);
        let right = embed(d, p, b);
        let conclusion = cle(d, p, left, right);
        let inner = d.arrow(hypothesis, conclusion);
        let with_b = d.pi_fv(b_fv, rat_carrier, inner);
        d.pi_fv(a_fv, rat_carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_rat_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.PosBound x k := CReal.le (CReal.ofRat (Rat.natDivSucc 1 k)) x`.
fn declare_pos_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let gap = div_succ(d, p, 1, k);
    let embedded = embed(d, p, gap);
    let body = cle(d, p, embedded, x);
    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        d.lam_fv(x_fv, carrier, with_k)
    };
    let ty = {
        let inner = d.arrow(nat, prop);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pos_bound,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 9),
    })
}

/// `pos_of_pos_bound : ∀ x k, PosBound x k → lt zero x` — a witnessed bound is
/// positivity.
fn declare_pos_of_pos_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hypothesis = pos_bound(d, p, x, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero = czero(d, p);
    let gap = div_succ(d, p, 1, k);
    let embedded = embed(d, p, gap);
    let unit = d.num(1);
    let unit_positive = {
        let nat_prelude = p.rat.int.nat;
        d.lemma(nat_prelude.le_refl, &[unit])
    };
    let positive = d.lemma(rat.nat_div_succ_pos, &[unit, k, unit_positive]);
    let padded = cadd(d, p, zero, embedded);
    let restore = zero_add_back(d, p, embedded);
    let reflexive = d.lemma(p.equiv_refl, &[x]);
    let bounded = d.lemma(p.le_congr, &[embedded, padded, x, x, restore, reflexive, h]);

    let rat_zero = rzero(d, rat);
    let strict = crate::rat_prelude::ops::rlt(d, rat, rat_zero, gap);
    let reached = cle(d, p, padded, x);
    let pair = and_intro(d, p, strict, reached, positive, bounded);
    let witness = gap_intro(d, p, zero, x, gap, pair);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, witness);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(x_fv, carrier, with_k)
    };
    let ty = {
        let conclusion = clt(d, p, zero, x);
        let inner = d.arrow(hypothesis, conclusion);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(x_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pos_of_pos_bound,
        uparams: vec![],
        ty,
        value,
    })
}

/// `pos_bound_of_lt : ∀ x, lt zero x → ∃ (k : Nat), PosBound x k`.
///
/// **The theorem that says exactly what the real inverse's domain is, and
/// exactly why it cannot be a `Prop`.** Together with
/// [`pos_of_pos_bound`](CRealPrelude::pos_of_pos_bound) it says `0 < x` and
/// `∃ k, 1/(k+1) ≤ x` are the same proposition — so the separating modulus
/// always exists — and the `Exists` is a `Prop`, so `Exists.rec` eliminates
/// only into `Prop` and that `k` can **never** be extracted into a `CReal`.
/// An inverse must therefore take `k` as an explicit `Nat` argument; no amount
/// of proof gets it out of the existential.
///
/// The modulus is *computed*, not searched for:
/// [`Rat.natDivSucc_lt_of_pos`](crate::RatPrelude::nat_div_succ_lt_of_pos)
/// gives `1/(1·den q + 1) < q` from the rational gap `q` the strict order
/// already carries, so `k := 1 · den q`.
fn declare_pos_bound_of_lt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let one_level = d.level_one();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let zero = czero(d, p);
    let hypothesis = clt(d, p, zero, x);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let predicate = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = pos_bound(d, p, x, k);
        d.lam_fv(k_fv, nat, body)
    };
    let target = {
        let exists_name = rat.int.logic.exists_;
        let exists = d.kernel().const_(exists_name, vec![one_level]);
        d.apply(exists, &[nat, predicate])
    };

    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let rat_carrier = rat_ty(d);
        let rat_zero = rzero(d, rat);
        let positive = crate::rat_prelude::ops::rlt(d, rat, rat_zero, q);
        let embedded_gap = embed(d, p, q);
        let padded = cadd(d, p, zero, embedded_gap);
        let reached = cle(d, p, padded, x);
        let pair_ty = d.and(positive, reached);
        let pair_fv = d.fresh_fvar();
        let pair = d.kernel().fvar(pair_fv);
        let (strict, bounded) = gap_halves(d, p, zero, x, q, pair);

        // `k := 1 · den q`, the index the Archimedean witness computes.
        let unit = d.num(1);
        let denominator = crate::rat_prelude::ops::den(d, q);
        let modulus = crate::nat_prelude::NatOps::mul(d, unit, denominator);
        let sharper = d.lemma(rat.nat_div_succ_lt_of_pos, &[unit, q, strict]);
        let gap = div_succ(d, p, 1, modulus);
        let weaker = d.lemma(rat.le_of_lt, &[gap, q, sharper]);
        let embedded = d.lemma(p.of_rat_le, &[gap, q, weaker]);
        let lifted = embed(d, p, gap);
        let restore = zero_add_back(d, p, embedded_gap);
        let shifted = d.lemma(p.le_of_equiv, &[embedded_gap, padded, restore]);
        let stepped = d.lemma(
            p.le_trans,
            &[lifted, embedded_gap, padded, embedded, shifted],
        );
        let reached_bound = d.lemma(p.le_trans, &[lifted, padded, x, stepped, bounded]);

        let intro_name = rat.int.logic.exists_intro;
        let intro = d.kernel().const_(intro_name, vec![one_level]);
        let witness = d.apply(intro, &[nat, predicate, modulus, reached_bound]);
        let with_pair = d.lam_fv(pair_fv, pair_ty, witness);
        d.lam_fv(q_fv, rat_carrier, with_pair)
    };

    let eliminated = gap_elim(d, p, zero, x, target, h, minor);
    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, eliminated);
        d.lam_fv(x_fv, carrier, with_h)
    };
    let ty = {
        let inner = d.arrow(hypothesis, target);
        d.pi_fv(x_fv, carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pos_bound_of_lt,
        uparams: vec![],
        ty,
        value,
    })
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

/// `of_rat_pos : ∀ g, Rat.lt Rat.zero g → CReal.lt CReal.zero (CReal.ofRat g)`.
///
/// The embedding takes positives to positives, and the witness is the rational
/// itself: `CReal.lt` quantifies over exactly the gap `g` already is.
fn declare_of_rat_pos(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let rat_carrier = rat_ty(d);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let rat_zero = rzero(d, rat);
    let hypothesis = crate::rat_prelude::ops::rlt(d, rat, rat_zero, g);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero = czero(d, p);
    let embedded = embed(d, p, g);
    let padded = cadd(d, p, zero, embedded);
    let collapse = zero_add_forward(d, p, embedded);
    let bounded = d.lemma(p.le_of_equiv, &[padded, embedded, collapse]);
    let reached = cle(d, p, padded, embedded);
    let pair = and_intro(d, p, hypothesis, reached, h, bounded);
    let witness = gap_intro(d, p, zero, embedded, g, pair);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, witness);
        d.lam_fv(g_fv, rat_carrier, with_h)
    };
    let ty = {
        let conclusion = clt(d, p, zero, embedded);
        let inner = d.arrow(hypothesis, conclusion);
        d.pi_fv(g_fv, rat_carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_rat_pos,
        uparams: vec![],
        ty,
        value,
    })
}

/// `mul_pos : ∀ x y, lt zero x → lt zero y → lt zero (mul x y)`.
///
/// **Positivity is closed under multiplication over the constructed reals**, and
/// it is not one of the 22 — they give `mul_nonneg`, of which the zero product
/// is a model. Strictness is what a *field* needs, and it comes from the
/// rational gaps the strict order already carries: `q₁ ≤ x` and `q₂ ≤ y` give
/// `q₁·q₂ ≤ x·y` by two applications of `mul_le_mul_of_nonneg_left`,
/// `CReal.ofRat_mul` says the embedded product is the rational product, and
/// `Rat.mul_pos` — itself a field lemma, proved through `Rat.inv_pos` — makes
/// it positive.
///
/// No modulus is extracted: both `Exists`es are eliminated into a `Prop`
/// target, which is exactly the elimination `Exists.rec` permits. The one an
/// inverse would need lands in `Type` and is not available.
fn declare_mul_pos(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let zero = czero(d, p);
    let left_hypothesis = clt(d, p, zero, x);
    let right_hypothesis = clt(d, p, zero, y);
    let product = cmul(d, p, x, y);
    let target = clt(d, p, zero, product);

    let hx_fv = d.fresh_fvar();
    let hx = d.kernel().fvar(hx_fv);
    let hy_fv = d.fresh_fvar();
    let hy = d.kernel().fvar(hy_fv);

    // `le (ofRat q) w` from a gap witness for `lt zero w`.
    let unpad = |d: &mut IntDev<'_>, w: ExprId, q: ExprId, bounded: ExprId| -> ExprId {
        let embedded = embed(d, p, q);
        let padded = cadd(d, p, zero, embedded);
        let collapse = zero_add_forward(d, p, embedded);
        let reflexive = d.lemma(p.equiv_refl, &[w]);
        d.lemma(
            p.le_congr,
            &[padded, embedded, w, w, collapse, reflexive, bounded],
        )
    };

    let outer = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let rat_zero = rzero(d, rat);
        let positive = crate::rat_prelude::ops::rlt(d, rat, rat_zero, q);
        let embedded = embed(d, p, q);
        let padded = cadd(d, p, zero, embedded);
        let reached = cle(d, p, padded, x);
        let pair_ty = d.and(positive, reached);
        let pair_fv = d.fresh_fvar();
        let pair = d.kernel().fvar(pair_fv);
        let (q_positive, q_bounded) = gap_halves(d, p, zero, x, q, pair);
        let q_le_x = unpad(d, x, q, q_bounded);

        let inner = {
            let r_fv = d.fresh_fvar();
            let r = d.kernel().fvar(r_fv);
            let r_positive_ty = crate::rat_prelude::ops::rlt(d, rat, rat_zero, r);
            let r_embedded = embed(d, p, r);
            let r_padded = cadd(d, p, zero, r_embedded);
            let r_reached = cle(d, p, r_padded, y);
            let r_pair_ty = d.and(r_positive_ty, r_reached);
            let r_pair_fv = d.fresh_fvar();
            let r_pair = d.kernel().fvar(r_pair_fv);
            let (r_positive, r_bounded) = gap_halves(d, p, zero, y, r, r_pair);
            let r_le_y = unpad(d, y, r, r_bounded);

            // `0 ≤ ofRat q`, `0 ≤ ofRat r`, hence `0 ≤ y`.
            let rat_q_nonneg = d.lemma(rat.le_of_lt, &[rat_zero, q, q_positive]);
            let rat_r_nonneg = d.lemma(rat.le_of_lt, &[rat_zero, r, r_positive]);
            let q_nonneg = d.lemma(p.of_rat_le, &[rat_zero, q, rat_q_nonneg]);
            let r_nonneg = d.lemma(p.of_rat_le, &[rat_zero, r, rat_r_nonneg]);
            let y_nonneg = d.lemma(p.le_trans, &[zero, r_embedded, y, r_nonneg, r_le_y]);

            // `q·r ≤ q·y ≤ x·y`.
            let embedded_product = cmul(d, p, embedded, r_embedded);
            let mixed = cmul(d, p, embedded, y);
            let first = d.lemma(
                p.mul_le_mul_of_nonneg_left,
                &[embedded, r_embedded, y, q_nonneg, r_le_y],
            );
            let swapped_left = cmul(d, p, y, embedded);
            let swapped_right = cmul(d, p, y, x);
            let second = d.lemma(
                p.mul_le_mul_of_nonneg_left,
                &[y, embedded, x, y_nonneg, q_le_x],
            );
            let swap_left = d.lemma(p.mul_comm, &[y, embedded]);
            let swap_right = d.lemma(p.mul_comm, &[y, x]);
            let second_oriented = d.lemma(
                p.le_congr,
                &[
                    swapped_left,
                    mixed,
                    swapped_right,
                    product,
                    swap_left,
                    swap_right,
                    second,
                ],
            );
            let chained = d.lemma(
                p.le_trans,
                &[embedded_product, mixed, product, first, second_oriented],
            );

            // The embedded product IS the rational product, and it is positive.
            let rational_product = crate::rat_prelude::ops::rmul(d, q, r);
            let lifted = embed(d, p, rational_product);
            let homomorphism = d.lemma(p.of_rat_mul, &[q, r]);
            let reflexive = d.lemma(p.equiv_refl, &[product]);
            let at_rational = d.lemma(
                p.le_congr,
                &[
                    embedded_product,
                    lifted,
                    product,
                    product,
                    homomorphism,
                    reflexive,
                    chained,
                ],
            );
            let rational_positive = d.lemma(rat.mul_pos, &[q, r, q_positive, r_positive]);
            let lifted_positive = d.lemma(p.of_rat_pos, &[rational_product, rational_positive]);
            let strict = d.lemma(
                p.lt_of_lt_of_le,
                &[zero, lifted, product, lifted_positive, at_rational],
            );
            let with_pair = d.lam_fv(r_pair_fv, r_pair_ty, strict);
            d.lam_fv(r_fv, rat_carrier, with_pair)
        };

        let eliminated = gap_elim(d, p, zero, y, target, hy, inner);
        let with_pair = d.lam_fv(pair_fv, pair_ty, eliminated);
        d.lam_fv(q_fv, rat_carrier, with_pair)
    };

    let body = gap_elim(d, p, zero, x, target, hx, outer);
    let value = {
        let with_hy = d.lam_fv(hy_fv, right_hypothesis, body);
        let with_hx = d.lam_fv(hx_fv, left_hypothesis, with_hy);
        let with_y = d.lam_fv(y_fv, carrier, with_hx);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let inner = d.arrow(right_hypothesis, target);
        let with_hx = d.arrow(left_hypothesis, inner);
        let with_y = d.pi_fv(y_fv, carrier, with_hx);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_pos,
        uparams: vec![],
        ty,
        value,
    })
}
