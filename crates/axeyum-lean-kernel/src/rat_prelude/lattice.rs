//! The **lattice** over `ℚ`: `Rat.max` and `Rat.min`, defined on the
//! representation, and the three order laws each of them satisfies
//! (ADR-0490, phase R5).
//!
//! ## The obstacle a reader expects, and why it is not there
//!
//! `max a b` looks like it needs a *decision*: pick `a` or `b` according to
//! which is larger. The order over `ℚ` is decidable —
//! [`Rat.le_or_lt`](super::RatPrelude::le_or_lt) is proved — but it is
//! `Or`-valued, hence a **`Prop`**, and eliminating a `Prop` into `Type` is
//! exactly what this kernel refuses. That is the same wall
//! [`CReal.inv`](crate::creal::CRealPrelude::inv) hit, and it is the reason
//! `crate::creal`'s module documentation says `Rat.abs` "is never needed".
//!
//! It is not a wall here, because `max` does not have to be *derived* from the
//! order — it can be **defined on the representation**, where the sign of an
//! integer is a constructor and `Int.rec` is available at every universe:
//!
//! ```text
//! gap a b   := num b · den a  −  num a · den b        (an Int)
//! max a b   := Int.rec (fun _ => Rat) (fun _ => b) (fun _ => a) (gap a b)
//! min a b   := Int.rec (fun _ => Rat) (fun _ => a) (fun _ => b) (gap a b)
//! ```
//!
//! `Rat.le a b` **is** `Int.le (num a · den b) (num b · den a)` by definition,
//! so `gap a b` is non-negative exactly when `a ≤ b`. No decision procedure is
//! invoked, nothing is eliminated out of `Prop`, and the two operations differ
//! only in which branch returns which argument — which is why one Rust builder
//! emits both, and one proof skeleton proves both.
//!
//! ## One case split, then no more
//!
//! Every lattice law below would otherwise repeat the same `Int.rec` on the
//! gap. [`Rat.max_cases`](super::RatPrelude::max_cases) does it **once**:
//!
//! ```text
//! max_cases : ∀ (a b : Rat) (P : Rat → Prop),
//!   (Rat.le a b → P b) → (Rat.le b a → P a) → P (Rat.max a b)
//! ```
//!
//! and then `le_max_left`, `le_max_right`, `max_le` are one application each
//! with `P` instantiated — `fun t => le a t`, `fun t => le b t`,
//! `fun t => le t c` — and both branches discharged by a hypothesis or by
//! `le_refl`. The higher-order `P` is unproblematic: it lands in `Prop`, so the
//! statement is `Prop` by impredicativity and no universe parameter appears.
//!
//! ## The two branch facts, and the one thing they share
//!
//! The `ofNat` branch needs `Int.le zero (gap a b) → Rat.le a b`, and the
//! `negSucc` branch needs `Int.le (gap a b) zero → Rat.le b a`. Both are the
//! *same* ordered-group shift — add `num a · den b` to both sides of the
//! hypothesis with `Int.add_le_add`, then collapse `zero + x` to `x` and
//! `(y + (−x)) + x` to `y` — used in the two possible orders. So one pair of
//! `Int` equalities serves both, and neither `Int.neg_add` nor `Int.neg_neg`
//! (which this development does not have) is needed.
//!
//! The two constructor facts are free: `Int.le zero (ofNat n)` is
//! [`int_zero_le_of_nat`](super::RatPrelude::int_zero_le_of_nat), and
//! `Int.le (negSucc m) Int.zero` **ι-reduces to `True`** — `Int.zero` is
//! `Int.ofNat 0` and `Int.le` is a four-case definition whose
//! `negSucc`/`ofNat` case is `True`. `True.intro` is the whole proof.
//!
//! ## What is deliberately not here
//!
//! - **No `Rat.abs`.** `crate::creal` writes `|r| ≤ q` as the pair
//!   `−q ≤ r ∧ r ≤ q` and has no use for an absolute value on `ℚ`;
//!   `CReal.abs` is `max x (neg x)` one level up, so the only `ℚ` fact it
//!   needs is [`zero_le_max_neg`](super::RatPrelude::zero_le_max_neg).
//! - **No `max a a = a`, no associativity, no distributivity over `add`.**
//!   Nothing consumes them yet, and each is another `max_cases` when it does.
//! - **No decidability claim.** `max_cases` is an elimination *into `Prop`*.
//!   It does not give `Or (le a b) (le b a)` as data, and `Rat.le_or_lt`
//!   (which does give it, as a `Prop`) still does not lift to `ℝ`.

use super::RatPrelude;
use super::group::rsub;
use super::ops::{den_z, num, radd, rat_theorem, rle, rneg, rzero};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.max`/`Rat.min`: above `Rat.le` (30), so a proof that
/// needs the lattice operation to reduce outranks the order it dispatches on.
const LATTICE_HEIGHT: u16 = 32;

/// `Rat.max a b`.
pub(crate) fn rmax(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.max, &[a, b])
}

/// `Rat.min a b`.
pub(crate) fn rmin(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.min, &[a, b])
}

/// `num a · den b` — the **left** side of `Rat.le a b`'s cross-multiplication.
fn cross(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let numerator = num(d, a);
    let scale = den_z(d, b);
    d.imul(numerator, scale)
}

/// `num b · den a − num a · den b`, the integer the lattice dispatches on.
///
/// `Rat.le a b` unfolds to `Int.le (cross a b) (cross b a)`, so this is
/// non-negative exactly when `a ≤ b`.
fn cross_gap(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let left = cross(d, a, b);
    let right = cross(d, b, a);
    let negated = d.ineg(left);
    d.iadd(right, negated)
}

/// `Int.rec (fun _ => Rat) (fun _ => nonneg) (fun _ => negative) z` — the body
/// both lattice operations are, as a function of the integer they dispatch on.
///
/// Factored out for the same reason
/// [`super::defs::inv_body`](super::defs) is: the case split in
/// [`declare_cases`] names *this* construction, so a change to the definition
/// fails at the kernel rather than proving something about a stale copy.
fn lattice_body(
    d: &mut IntDev<'_>,
    nonneg: ExprId,
    negative: ExprId,
    z: ExprId,
    rec_name: crate::name::NameId,
) -> ExprId {
    let carrier = super::ops::rat_ty(d);
    let nat_ty = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let int_ty = d.int_ty();
    let motive = d.kernel().lam(anon, int_ty, carrier, BinderInfo::Default);
    let minor_of_nat = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, nat_ty, nonneg)
    };
    let minor_neg_succ = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, nat_ty, negative)
    };
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[motive, minor_of_nat, minor_neg_succ, z])
}

/// `Eq Int (Int.add Int.zero x) x`.
fn int_zero_add(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    let int = p.int;
    let zero = d.izero();
    let start = d.iadd(zero, x);
    let flipped = d.iadd(x, zero);
    let commute = d.lemma(int.add_comm, &[zero, x]);
    let collapse = d.lemma(int.add_zero, &[x]);
    let (_, proof) = d.ichain(start, &[(flipped, commute), (x, collapse)]);
    proof
}

/// `Eq Int (Int.add (Int.add y (Int.neg x)) x) y` — adding `x` back to the gap.
fn int_gap_add(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, y: ExprId) -> ExprId {
    let int = p.int;
    let negated = d.ineg(x);
    let gap = d.iadd(y, negated);
    let start = d.iadd(gap, x);

    let tail = d.iadd(negated, x);
    let regrouped = d.iadd(y, tail);
    let regroup = d.lemma(int.add_assoc, &[y, negated, x]);

    let swapped = d.iadd(x, negated);
    let swap = {
        let commute = d.lemma(int.add_comm, &[negated, x]);
        d.icongr(tail, swapped, commute, &|d, t| d.iadd(y, t))
    };
    let swapped_sum = d.iadd(y, swapped);

    let zero = d.izero();
    let vanish = {
        let cancel = d.lemma(int.add_neg, &[x]);
        d.icongr(swapped, zero, cancel, &|d, t| d.iadd(y, t))
    };
    let padded = d.iadd(y, zero);
    let strip = d.lemma(int.add_zero, &[y]);

    let (_, proof) = d.ichain(
        start,
        &[
            (regrouped, regroup),
            (swapped_sum, swap),
            (padded, vanish),
            (y, strip),
        ],
    );
    proof
}

/// `h : Int.le Int.zero (gap a b)  ⊢  Rat.le a b` (definitionally
/// `Int.le (cross a b) (cross b a)`).
fn le_of_nonneg_gap(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let int = p.int;
    let x = cross(d, a, b);
    let y = cross(d, b, a);
    let gap = cross_gap(d, a, b);
    let zero = d.izero();
    let reflexive = d.lemma(int.le_refl, &[x]);
    let scaled = d.lemma(int.add_le_add, &[zero, gap, x, x, h, reflexive]);
    let left_start = d.iadd(zero, x);
    let right_start = d.iadd(gap, x);
    let left_eq = int_zero_add(d, p, x);
    let right_eq = int_gap_add(d, p, x, y);
    let at_left = d.int_eq_rewrite(left_start, x, left_eq, scaled, &|d, t| {
        d.ile(t, right_start)
    });
    d.int_eq_rewrite(right_start, y, right_eq, at_left, &|d, t| d.ile(x, t))
}

/// `h : Int.le (gap a b) Int.zero  ⊢  Rat.le b a`.
fn le_of_nonpos_gap(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let int = p.int;
    let x = cross(d, a, b);
    let y = cross(d, b, a);
    let gap = cross_gap(d, a, b);
    let zero = d.izero();
    let reflexive = d.lemma(int.le_refl, &[x]);
    let scaled = d.lemma(int.add_le_add, &[gap, zero, x, x, h, reflexive]);
    let left_start = d.iadd(gap, x);
    let right_start = d.iadd(zero, x);
    let left_eq = int_gap_add(d, p, x, y);
    let right_eq = int_zero_add(d, p, x);
    let at_left = d.int_eq_rewrite(left_start, y, left_eq, scaled, &|d, t| {
        d.ile(t, right_start)
    });
    d.int_eq_rewrite(right_start, x, right_eq, at_left, &|d, t| d.ile(y, t))
}

/// Admit the lattice: the two operations, the two case-analysis principles, the
/// six order laws, the two subtraction rearrangements, the two
/// one-Lipschitz estimates, and `0 ≤ max a (−a)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_lattice(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_operations(d, p)?;
    declare_cases(d, p, p.max_cases, false)?;
    declare_cases(d, p, p.min_cases, true)?;
    declare_lattice_laws(d, p)?;
    declare_shifts(d, p)?;
    declare_lipschitz(d, p)?;
    declare_abs_support(d, p)
}

/// `Rat.max` and `Rat.min`, which differ only in which branch returns which.
fn declare_operations(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = super::ops::rat_ty(d);
    let ty = {
        let inner = d.arrow(carrier, carrier);
        d.arrow(carrier, inner)
    };
    let rec_name = p.int.rec;

    let define = |d: &mut IntDev<'_>, name, swap: bool| -> Result<(), KernelError> {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let gap = cross_gap(d, a, b);
        let (nonneg, negative) = if swap { (a, b) } else { (b, a) };
        let body = lattice_body(d, nonneg, negative, gap, rec_name);
        let value = {
            let with_b = d.lam_fv(b_fv, carrier, body);
            d.lam_fv(a_fv, carrier, with_b)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(LATTICE_HEIGHT),
        })
    };
    define(d, p.max, false)?;
    define(d, p.min, true)
}

/// `max_cases` / `min_cases` — the **only** case split in this module.
fn declare_cases(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    name: crate::name::NameId,
    swap: bool,
) -> Result<(), KernelError> {
    let carrier = super::ops::rat_ty(d);
    let prop = d.kernel().sort_zero();
    let prop_level = d.kernel().level_zero();
    let int_ty = d.int_ty();
    let nat_ty = d.nat_ty();
    let rec_name = p.int.rec;

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let predicate_ty = d.arrow(carrier, prop);
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);

    let (nonneg, negative) = if swap { (a, b) } else { (b, a) };
    let forward = rle(d, p, a, b);
    let backward = rle(d, p, b, a);
    let on_le_ty = {
        let concl = d.apply(pred, &[nonneg]);
        d.arrow(forward, concl)
    };
    let on_ge_ty = {
        let concl = d.apply(pred, &[negative]);
        d.arrow(backward, concl)
    };
    let hl_fv = d.fresh_fvar();
    let hl = d.kernel().fvar(hl_fv);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let gap = cross_gap(d, a, b);

    // `fun z => gap = z → P (lattice_body nonneg negative z)`.
    let motive = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let equation = d.ieq(gap, z);
        let selected = lattice_body(d, nonneg, negative, z, rec_name);
        let claim = d.apply(pred, &[selected]);
        let inner = d.arrow(equation, claim);
        d.lam_fv(z_fv, int_ty, inner)
    };

    // `gap = ofNat n`: the gap is non-negative, so `a ≤ b`.
    let minor_of_nat = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let target = d.of_nat(n);
        let equation = d.ieq(gap, target);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let zero = d.izero();
        let constructor = d.lemma(p.int_zero_le_of_nat, &[n]);
        let back = d.isymm(gap, target, e);
        let at_gap = d.int_eq_rewrite(target, gap, back, constructor, &|d, t| d.ile(zero, t));
        let ordered = le_of_nonneg_gap(d, p, a, b, at_gap);
        let body = d.apply(hl, &[ordered]);
        let with_e = d.lam_fv(e_fv, equation, body);
        d.lam_fv(n_fv, nat_ty, with_e)
    };

    // `gap = negSucc m`: `Int.le (negSucc m) Int.zero` IS `True` by ι.
    let minor_neg_succ = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let target = d.neg_succ(m);
        let equation = d.ieq(gap, target);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let zero = d.izero();
        let constructor = d.true_intro();
        let back = d.isymm(gap, target, e);
        let at_gap = d.int_eq_rewrite(target, gap, back, constructor, &|d, t| d.ile(t, zero));
        let ordered = le_of_nonpos_gap(d, p, a, b, at_gap);
        let body = d.apply(hg, &[ordered]);
        let with_e = d.lam_fv(e_fv, equation, body);
        d.lam_fv(m_fv, nat_ty, with_e)
    };

    let rec = d.kernel().const_(rec_name, vec![prop_level]);
    let split = d.apply(rec, &[motive, minor_of_nat, minor_neg_succ, gap]);
    let reflexive = d.irefl(gap);
    let applied = d.apply(split, &[reflexive]);

    let value = {
        let with_hg = d.lam_fv(hg_fv, on_ge_ty, applied);
        let with_hl = d.lam_fv(hl_fv, on_le_ty, with_hg);
        let with_pred = d.lam_fv(pred_fv, predicate_ty, with_hl);
        let with_b = d.lam_fv(b_fv, carrier, with_pred);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let operation = if swap { p.min } else { p.max };
        let combined = d.const_app(operation, &[a, b]);
        let claim = d.apply(pred, &[combined]);
        let with_hg = d.arrow(on_ge_ty, claim);
        let with_hl = d.arrow(on_le_ty, with_hg);
        let with_pred = d.pi_fv(pred_fv, predicate_ty, with_hl);
        let with_b = d.pi_fv(b_fv, carrier, with_pred);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

/// The six lattice laws, one `max_cases`/`min_cases` application each.
fn declare_lattice_laws(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = super::ops::rat_ty(d);

    // le_max_left : a ≤ max a b.
    rat_theorem(d, p.le_max_left, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let combined = rmax(d, p, a, b);
        let stmt = rle(d, p, a, combined);
        let predicate = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let body = rle(d, p, a, t);
            d.lam_fv(t_fv, carrier, body)
        };
        let on_le = {
            let hypothesis = rle(d, p, a, b);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, hypothesis, h)
        };
        let on_ge = {
            let hypothesis = rle(d, p, b, a);
            let h_fv = d.fresh_fvar();
            let reflexive = d.lemma(p.le_refl, &[a]);
            d.lam_fv(h_fv, hypothesis, reflexive)
        };
        let proof = d.lemma(p.max_cases, &[a, b, predicate, on_le, on_ge]);
        (stmt, proof)
    })?;

    // le_max_right : b ≤ max a b.
    rat_theorem(d, p.le_max_right, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let combined = rmax(d, p, a, b);
        let stmt = rle(d, p, b, combined);
        let predicate = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let body = rle(d, p, b, t);
            d.lam_fv(t_fv, carrier, body)
        };
        let on_le = {
            let hypothesis = rle(d, p, a, b);
            let h_fv = d.fresh_fvar();
            let reflexive = d.lemma(p.le_refl, &[b]);
            d.lam_fv(h_fv, hypothesis, reflexive)
        };
        let on_ge = {
            let hypothesis = rle(d, p, b, a);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, hypothesis, h)
        };
        let proof = d.lemma(p.max_cases, &[a, b, predicate, on_le, on_ge]);
        (stmt, proof)
    })?;

    // max_le : a ≤ c → b ≤ c → max a b ≤ c.
    rat_theorem(d, p.max_le, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let first = rle(d, p, a, c);
        let second = rle(d, p, b, c);
        let combined = rmax(d, p, a, b);
        let conclusion = rle(d, p, combined, c);
        let stmt = {
            let inner = d.arrow(second, conclusion);
            d.arrow(first, inner)
        };
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let predicate = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let body = rle(d, p, t, c);
            d.lam_fv(t_fv, carrier, body)
        };
        let on_le = {
            let hypothesis = rle(d, p, a, b);
            let h_fv = d.fresh_fvar();
            d.lam_fv(h_fv, hypothesis, h2)
        };
        let on_ge = {
            let hypothesis = rle(d, p, b, a);
            let h_fv = d.fresh_fvar();
            d.lam_fv(h_fv, hypothesis, h1)
        };
        let applied = d.lemma(p.max_cases, &[a, b, predicate, on_le, on_ge]);
        let proof = {
            let with_h2 = d.lam_fv(h2_fv, second, applied);
            d.lam_fv(h1_fv, first, with_h2)
        };
        (stmt, proof)
    })?;

    // min_le_left : min a b ≤ a.
    rat_theorem(d, p.min_le_left, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let combined = rmin(d, p, a, b);
        let stmt = rle(d, p, combined, a);
        let predicate = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let body = rle(d, p, t, a);
            d.lam_fv(t_fv, carrier, body)
        };
        let on_le = {
            let hypothesis = rle(d, p, a, b);
            let h_fv = d.fresh_fvar();
            let reflexive = d.lemma(p.le_refl, &[a]);
            d.lam_fv(h_fv, hypothesis, reflexive)
        };
        let on_ge = {
            let hypothesis = rle(d, p, b, a);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, hypothesis, h)
        };
        let proof = d.lemma(p.min_cases, &[a, b, predicate, on_le, on_ge]);
        (stmt, proof)
    })?;

    // min_le_right : min a b ≤ b.
    rat_theorem(d, p.min_le_right, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let combined = rmin(d, p, a, b);
        let stmt = rle(d, p, combined, b);
        let predicate = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let body = rle(d, p, t, b);
            d.lam_fv(t_fv, carrier, body)
        };
        let on_le = {
            let hypothesis = rle(d, p, a, b);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, hypothesis, h)
        };
        let on_ge = {
            let hypothesis = rle(d, p, b, a);
            let h_fv = d.fresh_fvar();
            let reflexive = d.lemma(p.le_refl, &[b]);
            d.lam_fv(h_fv, hypothesis, reflexive)
        };
        let proof = d.lemma(p.min_cases, &[a, b, predicate, on_le, on_ge]);
        (stmt, proof)
    })?;

    // le_min : c ≤ a → c ≤ b → c ≤ min a b.
    rat_theorem(d, p.le_min, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let first = rle(d, p, c, a);
        let second = rle(d, p, c, b);
        let combined = rmin(d, p, a, b);
        let conclusion = rle(d, p, c, combined);
        let stmt = {
            let inner = d.arrow(second, conclusion);
            d.arrow(first, inner)
        };
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let predicate = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let body = rle(d, p, c, t);
            d.lam_fv(t_fv, carrier, body)
        };
        let on_le = {
            let hypothesis = rle(d, p, a, b);
            let h_fv = d.fresh_fvar();
            d.lam_fv(h_fv, hypothesis, h1)
        };
        let on_ge = {
            let hypothesis = rle(d, p, b, a);
            let h_fv = d.fresh_fvar();
            d.lam_fv(h_fv, hypothesis, h2)
        };
        let applied = d.lemma(p.min_cases, &[a, b, predicate, on_le, on_ge]);
        let proof = {
            let with_h2 = d.lam_fv(h2_fv, second, applied);
            d.lam_fv(h1_fv, first, with_h2)
        };
        (stmt, proof)
    })
}

/// `u − v ≤ q  ↔  u ≤ v + q`, both directions — the rearrangement every
/// Lipschitz estimate below runs on, and pure ordered-group.
fn declare_shifts(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    use super::ops::{rat_eq_rewrite, rchain, rcongr, rsymm};

    // le_of_sub_le : u − v ≤ q → u ≤ v + q.
    rat_theorem(d, p.le_of_sub_le, 3, &|d, v| {
        let (u, w, q) = (v[0], v[1], v[2]);
        let difference = rsub(d, p, u, w);
        let hypothesis = rle(d, p, difference, q);
        let shifted = radd(d, w, q);
        let conclusion = rle(d, p, u, shifted);
        let stmt = d.arrow(hypothesis, conclusion);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let reflexive = d.lemma(p.le_refl, &[w]);
        let scaled = d.lemma(p.add_le_add, &[difference, q, w, w, h, reflexive]);
        let left_start = radd(d, difference, w);
        let right_start = radd(d, q, w);

        // (u + (−w)) + w = u + ((−w) + w) = u + 0 = u.
        let negated = rneg(d, w);
        let tail = radd(d, negated, w);
        let regrouped = radd(d, u, tail);
        let regroup = d.lemma(p.add_assoc, &[u, negated, w]);
        let zero = rzero(d, p);
        let padded = radd(d, u, zero);
        let vanish = {
            let cancel = d.lemma(p.neg_add_cancel, &[w]);
            rcongr(d, tail, zero, cancel, &|d, t| radd(d, u, t))
        };
        let strip = d.lemma(p.add_zero, &[u]);
        let (_, left_eq) = rchain(
            d,
            left_start,
            &[(regrouped, regroup), (padded, vanish), (u, strip)],
        );
        let right_eq = d.lemma(p.add_comm, &[q, w]);

        let at_left = rat_eq_rewrite(d, left_start, u, left_eq, scaled, &|d, t| {
            rle(d, p, t, right_start)
        });
        let body = rat_eq_rewrite(d, right_start, shifted, right_eq, at_left, &|d, t| {
            rle(d, p, u, t)
        });
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })?;

    // sub_le_of_le : u ≤ v + q → u − v ≤ q.
    rat_theorem(d, p.sub_le_of_le, 3, &|d, v| {
        let (u, w, q) = (v[0], v[1], v[2]);
        let shifted = radd(d, w, q);
        let hypothesis = rle(d, p, u, shifted);
        let difference = rsub(d, p, u, w);
        let conclusion = rle(d, p, difference, q);
        let stmt = d.arrow(hypothesis, conclusion);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let negated = rneg(d, w);
        let reflexive = d.lemma(p.le_refl, &[negated]);
        let scaled = d.lemma(p.add_le_add, &[u, shifted, negated, negated, h, reflexive]);
        let right_start = radd(d, shifted, negated);

        // (w + q) + (−w) = w + (q + (−w)) = w + ((−w) + q)
        //               = (w + (−w)) + q = 0 + q = q.
        let tail = radd(d, q, negated);
        let regrouped = radd(d, w, tail);
        let regroup = d.lemma(p.add_assoc, &[w, q, negated]);
        let swapped = radd(d, negated, q);
        let swapped_sum = radd(d, w, swapped);
        let swap = {
            let commute = d.lemma(p.add_comm, &[q, negated]);
            rcongr(d, tail, swapped, commute, &|d, t| radd(d, w, t))
        };
        let head = radd(d, w, negated);
        let flat = radd(d, head, q);
        let flatten = {
            let forward = d.lemma(p.add_assoc, &[w, negated, q]);
            rsymm(d, flat, swapped_sum, forward)
        };
        let zero = rzero(d, p);
        let zeroed = radd(d, zero, q);
        let vanish = {
            let cancel = d.lemma(p.add_neg, &[w]);
            rcongr(d, head, zero, cancel, &|d, t| radd(d, t, q))
        };
        let strip = d.lemma(p.zero_add, &[q]);
        let (_, right_eq) = rchain(
            d,
            right_start,
            &[
                (regrouped, regroup),
                (swapped_sum, swap),
                (flat, flatten),
                (zeroed, vanish),
                (q, strip),
            ],
        );
        let body = rat_eq_rewrite(d, right_start, q, right_eq, scaled, &|d, t| {
            rle(d, p, difference, t)
        });
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })
}

/// The two **one-Lipschitz** estimates: replacing both arguments of a lattice
/// operation by ones within `q` moves the result by at most `q`.
///
/// This is exactly what makes `CReal.max` and `CReal.min` regular, and it is
/// why the real lattice needs no index shift at all.
fn declare_lipschitz(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = super::ops::rat_ty(d);

    // sub_max_le : a − c ≤ q → b − e ≤ q → max a b − max c e ≤ q.
    rat_theorem(d, p.sub_max_le, 5, &|d, v| {
        let (a, b, c, e, q) = (v[0], v[1], v[2], v[3], v[4]);
        let first = {
            let difference = rsub(d, p, a, c);
            rle(d, p, difference, q)
        };
        let second = {
            let difference = rsub(d, p, b, e);
            rle(d, p, difference, q)
        };
        let left = rmax(d, p, a, b);
        let right = rmax(d, p, c, e);
        let conclusion = {
            let difference = rsub(d, p, left, right);
            rle(d, p, difference, q)
        };
        let stmt = {
            let inner = d.arrow(second, conclusion);
            d.arrow(first, inner)
        };
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let target = radd(d, right, q);
        let reflexive = d.lemma(p.le_refl, &[q]);
        let branch = |d: &mut IntDev<'_>,
                      point: ExprId,
                      other: ExprId,
                      side: crate::name::NameId,
                      h: ExprId|
         -> ExprId {
            let opened = d.lemma(p.le_of_sub_le, &[point, other, q, h]);
            let shifted = radd(d, other, q);
            let dominated = d.lemma(side, &[c, e]);
            let widened = d.lemma(p.add_le_add, &[other, right, q, q, dominated, reflexive]);
            d.lemma(p.le_trans, &[point, shifted, target, opened, widened])
        };
        let from_a = branch(d, a, c, p.le_max_left, h1);
        let from_b = branch(d, b, e, p.le_max_right, h2);
        let combined = d.lemma(p.max_le, &[a, b, target, from_a, from_b]);
        let applied = d.lemma(p.sub_le_of_le, &[left, right, q, combined]);
        let proof = {
            let with_h2 = d.lam_fv(h2_fv, second, applied);
            d.lam_fv(h1_fv, first, with_h2)
        };
        (stmt, proof)
    })?;

    // sub_min_le : a − c ≤ q → b − e ≤ q → min a b − min c e ≤ q.
    //
    // Not the dual of the above by rearrangement: `min a b ≤ min (c+q) (e+q)`
    // still owes `min (c+q) (e+q) ≤ min c e + q`. Splitting on `min c e`
    // instead pays nothing — in each branch the bound is one of the two
    // hypotheses.
    rat_theorem(d, p.sub_min_le, 5, &|d, v| {
        let (a, b, c, e, q) = (v[0], v[1], v[2], v[3], v[4]);
        let first = {
            let difference = rsub(d, p, a, c);
            rle(d, p, difference, q)
        };
        let second = {
            let difference = rsub(d, p, b, e);
            rle(d, p, difference, q)
        };
        let left = rmin(d, p, a, b);
        let right = rmin(d, p, c, e);
        let conclusion = {
            let difference = rsub(d, p, left, right);
            rle(d, p, difference, q)
        };
        let stmt = {
            let inner = d.arrow(second, conclusion);
            d.arrow(first, inner)
        };
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let predicate = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let difference = rsub(d, p, left, t);
            let body = rle(d, p, difference, q);
            d.lam_fv(t_fv, carrier, body)
        };
        let branch = |d: &mut IntDev<'_>,
                      point: ExprId,
                      other: ExprId,
                      side: crate::name::NameId,
                      h: ExprId|
         -> ExprId {
            let opened = d.lemma(p.le_of_sub_le, &[point, other, q, h]);
            let shifted = radd(d, other, q);
            let dominated = d.lemma(side, &[a, b]);
            let chained = d.lemma(p.le_trans, &[left, point, shifted, dominated, opened]);
            d.lemma(p.sub_le_of_le, &[left, other, q, chained])
        };
        let on_le = {
            let hypothesis = rle(d, p, c, e);
            let h_fv = d.fresh_fvar();
            let body = branch(d, a, c, p.min_le_left, h1);
            d.lam_fv(h_fv, hypothesis, body)
        };
        let on_ge = {
            let hypothesis = rle(d, p, e, c);
            let h_fv = d.fresh_fvar();
            let body = branch(d, b, e, p.min_le_right, h2);
            d.lam_fv(h_fv, hypothesis, body)
        };
        let applied = d.lemma(p.min_cases, &[c, e, predicate, on_le, on_ge]);
        let proof = {
            let with_h2 = d.lam_fv(h2_fv, second, applied);
            d.lam_fv(h1_fv, first, with_h2)
        };
        (stmt, proof)
    })
}

/// `0 ≤ max a (−a)` — the **only** `ℚ` fact `CReal.abs` needs beyond the
/// lattice laws, and the one place `Rat.le_total` is used.
fn declare_abs_support(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    use super::ops::rat_eq_rewrite;

    rat_theorem(d, p.zero_le_max_neg, 1, &|d, v| {
        let a = v[0];
        let zero = rzero(d, p);
        let negated = rneg(d, a);
        let combined = rmax(d, p, a, negated);
        let stmt = rle(d, p, zero, combined);

        let left_ty = rle(d, p, zero, a);
        let right_ty = rle(d, p, a, zero);
        let total = d.lemma(p.le_total, &[zero, a]);
        let on_nonneg = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let dominated = d.lemma(p.le_max_left, &[a, negated]);
            let body = d.lemma(p.le_trans, &[zero, a, combined, h, dominated]);
            d.lam_fv(h_fv, left_ty, body)
        };
        let on_nonpos = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let flipped = d.lemma(p.neg_le_neg, &[a, zero, h]);
            let negated_zero = rneg(d, zero);
            let collapse = d.lemma(p.neg_zero, &[]);
            let lifted = rat_eq_rewrite(d, negated_zero, zero, collapse, flipped, &|d, t| {
                rle(d, p, t, negated)
            });
            let dominated = d.lemma(p.le_max_right, &[a, negated]);
            let body = d.lemma(p.le_trans, &[zero, negated, combined, lifted, dominated]);
            d.lam_fv(h_fv, right_ty, body)
        };
        let proof = d.or_elim(
            left_ty,
            right_ty,
            stmt,
            total,
            &|d, h| d.apply(on_nonneg, &[h]),
            &|d, h| d.apply(on_nonpos, &[h]),
        );
        (stmt, proof)
    })
}
