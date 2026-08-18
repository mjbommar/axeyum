//! **ℝ, constructed**: a Bishop setoid of regular sequences of rationals over
//! the proved `ℚ`, with equality carried by a *defined* relation rather than by
//! `Eq`, and costing **zero** trusted declarations.
//!
//! This is [ADR-0468](../../../docs/research/09-decisions/adr-0468-real-is-a-bishop-setoid-over-rat.md)
//! phase R1, and it is what
//! [`examples/creal_shape_probe.rs`](../../examples/creal_shape_probe.rs)
//! measured the shape of before `ℚ` had an order. The probe admitted
//! `CReal.Of (reg : (Nat → Rat) → Prop)` — the carrier *parametric* in its
//! regularity predicate, because `Rat.le` did not exist. It does now, so the
//! predicate is a definition and the carrier is concrete.
//!
//! ## Why a setoid, in one line
//!
//! ADR-0456 priced the two textbook routes and found both closed here: a Cauchy
//! **quotient** needs `Quot.sound`, which this kernel's four-declaration
//! quotient package does not contain, and **Dedekind cuts** need `funext` and
//! `propext`, neither of which exists. The missing option was that equality
//! need not be `Eq`. `CReal.Equiv` is a `Prop`-valued definition, so the whole
//! construction is ordinary definitions and theorems.
//!
//! `Eq CReal` is **not** the equality of real numbers, and nothing here pretends
//! it is. `0.999… ` and `1` are distinct `CReal`s and `CReal.Equiv`-equal, which
//! is the correct and intended state of affairs.
//!
//! ## The three shapes this module is built out of
//!
//! - **`|a| ≤ b` is a pair.** [`Within`](CRealPrelude::within) is
//!   `−b ≤ a ∧ a ≤ b`, so `Rat.abs` is never needed — no sign case split, no
//!   congruence lemma, no monotonicity theory.
//! - **Every bound is one `Rat.natDivSucc`.** `1/(m+1)`, `2/(n+1)` and `6/(j+1)`
//!   are the same construction at different numerators, which is what lets the
//!   six-term estimate in [`Equiv.trans`](CRealPrelude::equiv_trans) fuse.
//! - **Regularity is a fixed modulus, not an existential.** Bishop's
//!   `|f m − f n| ≤ 1/(m+1) + 1/(n+1)` keeps the representative a plain
//!   function: the modulus never has to be extracted, and completeness will
//!   later be provable without countable choice. That is the trap a bare-Cauchy
//!   development falls into and the reason the HoTT book reaches for a higher
//!   inductive type.
//!
//! ## What transitivity costs, and where it is paid
//!
//! Chaining two closeness hypotheses directly gives `|x_n − z_n| ≤ 4/(n+1)`,
//! which is not the `≤ 2/(n+1)` the relation asks for, and no rearrangement
//! fixes that. Bishop compares at an arbitrary third index `j`:
//!
//! ```text
//! |x_n − z_n| ≤ |x_n − x_j| + |x_j − y_j| + |y_j − z_j| + |z_j − z_n|
//!             ≤ (1/(n+1) + 1/(j+1)) + 2/(j+1) + 2/(j+1) + (1/(j+1) + 1/(n+1))
//!              = 2/(n+1) + 6/(j+1)
//! ```
//!
//! and the `6/(j+1)` is discharged by
//! [`Rat.le_of_le_add_natDivSucc`](crate::RatPrelude::le_of_le_add_natDivSucc)
//! — the **Archimedean property of ℚ**, a statement about rationals that this
//! module only consumes. That is the price of the fixed modulus, and it is paid
//! once.

// Proof scripts are long, straight-line term constructions with short
// mathematical names, exactly as in `rat_prelude`.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use crate::BinderInfo;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::{rsub, rsum, rsum_append, rsum_perm};
use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rat_ty, rchain, rcongr, rneg, rsymm, rzero};
use crate::rat_prelude::{RatPrelude, build_rat_prelude};
use crate::{Kernel, KernelError};

/// Delta heights for the real definitions: above every `Rat` definition.
const LEAF_HEIGHT: u16 = 40;
/// Height for a definition that calls a leaf one.
const DERIVED_HEIGHT: u16 = 41;

/// The interned names produced by [`build_creal_prelude`]: the carrier, its
/// constructor and recursor, the two projections, the setoid relation, and its
/// three equivalence laws — plus the embedded [`RatPrelude`] the whole thing is
/// constructed over.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CRealPrelude {
    /// The rational development `CReal` is constructed over. Its axiom
    /// footprint is empty, which is what makes every law below empty too.
    pub rat: RatPrelude,

    /// `CReal.Within : Rat → Rat → Prop` — `Within r q := −q ≤ r ∧ r ≤ q`.
    ///
    /// ADR-0468's encoding of `|r| ≤ q`, chosen so that `Rat.abs` never has to
    /// exist. Every bound in this module is stated through it.
    pub within: NameId,
    /// `CReal.Regular : (Nat → Rat) → Prop` — Bishop regularity with the
    /// **fixed** modulus `|f m − f n| ≤ 1/(m+1) + 1/(n+1)`.
    pub regular_pred: NameId,
    /// `CReal : Type` — a one-constructor inductive. **Not** a quotient: this
    /// kernel has no `Quot.sound` (ADR-0456), and does not need one.
    pub creal: NameId,
    /// `CReal.mk : (f : Nat → Rat) → CReal.Regular f → CReal`.
    pub mk: NameId,
    /// `CReal.rec` — the kernel-generated recursor.
    pub rec: NameId,
    /// `CReal.seq : CReal → Nat → Rat` — the representative, by **large
    /// elimination** out of a `Type`-valued inductive with a `Prop` field.
    pub seq: NameId,
    /// `CReal.regular : ∀ x, CReal.Regular (CReal.seq x)` — the regularity
    /// field, projected.
    pub regular: NameId,
    /// `CReal.Equiv : CReal → CReal → Prop` —
    /// `∀ n, Within (seq x n − seq y n) (2/(n+1))`.
    ///
    /// **This, and not `Eq CReal`, is the equality of real numbers.**
    pub equiv: NameId,
    /// `CReal.Equiv.refl : ∀ x, CReal.Equiv x x`.
    pub equiv_refl: NameId,
    /// `CReal.Equiv.symm : ∀ x y, CReal.Equiv x y → CReal.Equiv y x`.
    pub equiv_symm: NameId,
    /// `CReal.Equiv.trans : ∀ x y z, CReal.Equiv x y → CReal.Equiv y z → CReal.Equiv x z`.
    ///
    /// The one proof in the construction that is not routine — see the module
    /// documentation. It is the only consumer of the Archimedean property.
    pub equiv_trans: NameId,

    // --- the carrier is inhabited, and `Equiv` discriminates ------------------
    /// `CReal.ofRat : Rat → CReal` — the embedding `ℚ ↪ ℝ`, the constant
    /// sequence.
    ///
    /// It is also the **non-vacuity** witness. Everything above is a statement
    /// about the inhabitants of `CReal`, so if `CReal.Regular` had no solutions
    /// the carrier would be empty and `refl`, `symm` and `trans` would all be
    /// true and worthless — and an empty axiom footprint would not notice.
    pub of_rat: NameId,
    /// `CReal.Equiv.not_zero_one : Not (CReal.Equiv (ofRat Rat.zero) (ofRat Rat.one))`.
    ///
    /// The **discrimination** witness. `Equiv` being an equivalence relation is
    /// worth nothing if `Equiv` is the total relation; this exhibits two
    /// `CReal`s it separates, and it separates them *by computation* — the
    /// witness index is `3`, and `−1/2 ≤ −1` reduces to `Nat.le 1 0`.
    pub not_zero_one: NameId,
}

fn intern_names(kernel: &mut Kernel, rat: RatPrelude) -> CRealPrelude {
    let anon = kernel.anon();
    let creal = kernel.name_str(anon, "CReal");
    let equiv = kernel.name_str(creal, "Equiv");
    CRealPrelude {
        rat,
        within: kernel.name_str(creal, "Within"),
        regular_pred: kernel.name_str(creal, "Regular"),
        creal,
        mk: kernel.name_str(creal, "mk"),
        rec: kernel.name_str(creal, "rec"),
        seq: kernel.name_str(creal, "seq"),
        regular: kernel.name_str(creal, "regular"),
        equiv,
        equiv_refl: kernel.name_str(equiv, "refl"),
        equiv_symm: kernel.name_str(equiv, "symm"),
        equiv_trans: kernel.name_str(equiv, "trans"),
        of_rat: kernel.name_str(creal, "ofRat"),
        not_zero_one: kernel.name_str(equiv, "not_zero_one"),
    }
}

/// Build the real prelude: `ℝ` as a Bishop setoid over the constructed `ℚ`,
/// **asserting nothing**.
///
/// Idempotent on a kernel that already carries it. A failure rolls the
/// environment back to the pre-call state.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub fn build_creal_prelude(kernel: &mut Kernel) -> Result<CRealPrelude, KernelError> {
    let rat = build_rat_prelude(kernel)?;
    let prelude = intern_names(kernel, rat);
    if kernel.environment().get(prelude.creal).is_some() {
        return Ok(prelude);
    }
    let checkpoint = kernel.prelude_checkpoint();
    let built = (|| -> Result<(), KernelError> {
        let mut d = IntDev::new(kernel, rat.int);
        declare_predicates(&mut d, prelude)?;
        declare_carrier(&mut d, prelude)?;
        declare_projections(&mut d, prelude)?;
        declare_equiv(&mut d, prelude)?;
        declare_reflexivity(&mut d, prelude)?;
        declare_symmetry(&mut d, prelude)?;
        declare_transitivity(&mut d, prelude)?;
        declare_of_rat(&mut d, prelude)?;
        declare_discrimination(&mut d, prelude)
    })();
    match built {
        Ok(()) => Ok(prelude),
        Err(error) => {
            kernel.rollback_prelude(checkpoint);
            Err(error)
        }
    }
}

// --- term builders ----------------------------------------------------------

/// `Nat → Rat`, the representative type. Its own sort is `Type 0`, so a field of
/// this type does not push the carrier up a universe.
fn seq_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    d.arrow(nat, carrier)
}

/// `CReal`.
fn creal_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.creal, vec![])
}

/// `CReal.Within r q`.
fn within(d: &mut IntDev<'_>, p: CRealPrelude, r: ExprId, q: ExprId) -> ExprId {
    d.const_app(p.within, &[r, q])
}

/// `CReal.seq x n`.
fn sample(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.seq, &[x, n])
}

/// `Rat.natDivSucc k j`, with `k` a literal.
fn div_succ(d: &mut IntDev<'_>, p: CRealPrelude, k: u32, j: ExprId) -> ExprId {
    let numerator = d.num(k);
    d.const_app(p.rat.nat_div_succ, &[numerator, j])
}

/// `Rat.add (natDivSucc 1 m) (natDivSucc 1 n)` — the regularity modulus,
/// written inline rather than behind a constant so the rearrangement in
/// [`declare_transitivity`] sees the two summands.
fn modulus(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId, n: ExprId) -> ExprId {
    let left = div_succ(d, p, 1, m);
    let right = div_succ(d, p, 1, n);
    radd(d, left, right)
}

/// `CReal.Equiv x y`.
fn equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.equiv, &[x, y])
}

/// `And.intro`, at two `Prop`s.
fn and_intro(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    left: ExprId,
    right: ExprId,
    lp: ExprId,
    rp: ExprId,
) -> ExprId {
    let intro = p.rat.int.logic.and_intro;
    d.const_app(intro, &[left, right, lp, rp])
}

/// The lower and upper halves of a `Within r q` proof.
fn halves(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    r: ExprId,
    q: ExprId,
    proof: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let negated = rneg(d, q);
    let lower = crate::rat_prelude::ops::rle(d, rat, negated, r);
    let upper = crate::rat_prelude::ops::rle(d, rat, r, q);
    let left = d.and_left(lower, upper, proof);
    let right = d.and_right(lower, upper, proof);
    (left, right)
}

// --- the definitions --------------------------------------------------------

/// `CReal.Within` and `CReal.Regular`.
fn declare_predicates(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = rat_ty(d);
    let prop = d.kernel().sort_zero();

    // Within r q := And (Rat.le (Rat.neg q) r) (Rat.le r q)
    {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let negated = rneg(d, q);
        let lower = crate::rat_prelude::ops::rle(d, rat, negated, r);
        let upper = crate::rat_prelude::ops::rle(d, rat, r, q);
        let body = d.and(lower, upper);
        let value = {
            let with_q = d.lam_fv(q_fv, carrier, body);
            d.lam_fv(r_fv, carrier, with_q)
        };
        let ty = {
            let inner = d.arrow(carrier, prop);
            d.arrow(carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.within,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(LEAF_HEIGHT),
        })?;
    }

    // Regular f := ∀ (m n : Nat), Within (Rat.sub (f m) (f n)) (1/(m+1) + 1/(n+1))
    {
        let nat = d.nat_ty();
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let left = d.apply(f, &[m]);
        let right = d.apply(f, &[n]);
        let difference = rsub(d, rat, left, right);
        let bound = modulus(d, p, m, n);
        let claim = within(d, p, difference, bound);
        let body = {
            let over_n = d.pi_fv(n_fv, nat, claim);
            d.pi_fv(m_fv, nat, over_n)
        };
        let sequences = seq_ty(d);
        let value = d.lam_fv(f_fv, sequences, body);
        let ty = d.arrow(sequences, prop);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.regular_pred,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
        })?;
    }
    Ok(())
}

/// The carrier: a one-constructor inductive in `Type 0` with a function field
/// and a dependent `Prop` field over it.
fn declare_carrier(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let sequences = seq_ty(d);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    let mk_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let regular = d.const_app(p.regular_pred, &[f]);
        let result = creal_ty(d, p);
        let body = d.arrow(regular, result);
        d.pi_fv(f_fv, sequences, body)
    };
    d.kernel()
        .add_inductive(p.creal, &[], 0, type0, &[(p.mk, mk_ty)])
}

/// The two projections: the representative (large elimination, into `Type 0`)
/// and its regularity proof (into `Prop`).
fn declare_projections(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let sequences = seq_ty(d);
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();
    let anon = d.anon_name();
    let carrier = creal_ty(d, p);

    // seq x := CReal.rec (fun _ => Nat → Rat) (fun f _ => f) x
    {
        let motive = d
            .kernel()
            .lam(anon, carrier, sequences, BinderInfo::Default);
        let minor = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let regular = d.const_app(p.regular_pred, &[f]);
            let inner = d.kernel().lam(anon, regular, f, BinderInfo::Default);
            d.lam_fv(f_fv, sequences, inner)
        };
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, x]);
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = d.arrow(carrier, sequences);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.seq,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 1),
        })?;
    }

    // regular x : Regular (seq x) := CReal.rec (fun y => Regular (seq y)) (fun f h => h) x
    {
        let claim = |d: &mut IntDev<'_>, y: ExprId| {
            let representative = d.const_app(p.seq, &[y]);
            d.const_app(p.regular_pred, &[representative])
        };
        let motive = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = claim(d, y);
            d.lam_fv(y_fv, carrier, body)
        };
        let minor = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let regular = d.const_app(p.regular_pred, &[f]);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let inner = d.lam_fv(h_fv, regular, h);
            d.lam_fv(f_fv, sequences, inner)
        };
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let rec = d.kernel().const_(p.rec, vec![zero_level]);
        let body = d.apply(rec, &[motive, minor, x]);
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = {
            let inner = claim(d, x);
            d.pi_fv(x_fv, carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.regular,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `CReal.Equiv x y := ∀ n, Within (seq x n − seq y n) (2/(n+1))`.
fn declare_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let left = sample(d, p, x, n);
    let right = sample(d, p, y, n);
    let difference = rsub(d, p.rat, left, right);
    let bound = div_succ(d, p, 2, n);
    let claim = within(d, p, difference, bound);
    let body = d.pi_fv(n_fv, nat, claim);
    let value = {
        let with_y = d.lam_fv(y_fv, carrier, body);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let inner = d.arrow(carrier, prop);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.equiv,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 2),
    })
}

/// `Equiv.refl`: `seq x n − seq x n = 0`, and `0` is inside every bound.
fn declare_reflexivity(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let point = sample(d, p, x, n);
    let difference = rsub(d, rat, point, point);
    let bound = div_succ(d, p, 2, n);
    let zero = rzero(d, rat);
    let negated = rneg(d, bound);

    let collapse = d.lemma(rat.sub_self, &[point]);
    let back = rsymm(d, difference, zero, collapse);
    let two = d.num(2);
    let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two, n]);
    let nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, nonneg]);
    let lower = rat_eq_rewrite(d, zero, difference, back, nonpos, &|d, t| {
        crate::rat_prelude::ops::rle(d, rat, negated, t)
    });
    let upper = rat_eq_rewrite(d, zero, difference, back, nonneg, &|d, t| {
        crate::rat_prelude::ops::rle(d, rat, t, bound)
    });
    let lower_ty = crate::rat_prelude::ops::rle(d, rat, negated, difference);
    let upper_ty = crate::rat_prelude::ops::rle(d, rat, difference, bound);
    let pair = and_intro(d, p, lower_ty, upper_ty, lower, upper);
    let value = {
        let over_n = d.lam_fv(n_fv, nat, pair);
        d.lam_fv(x_fv, carrier, over_n)
    };
    let ty = {
        let inner = equiv(d, p, x, x);
        d.pi_fv(x_fv, carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_refl,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv.symm`: negate the two-sided bound, then `−(a − b) = b − a`.
fn declare_symmetry(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let hypothesis = equiv(d, p, x, y);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let a = sample(d, p, x, n);
    let b = sample(d, p, y, n);
    let forward = rsub(d, rat, a, b);
    let backward = rsub(d, rat, b, a);
    let bound = div_succ(d, p, 2, n);
    let instance = d.apply(h, &[n]);
    let (lower, upper) = halves(d, p, forward, bound, instance);
    let flipped = d.lemma(rat.bounds_neg, &[forward, bound, lower, upper]);
    let negated_forward = rneg(d, forward);
    let rewrite = d.lemma(rat.neg_sub, &[a, b]);
    let body = rat_eq_rewrite(d, negated_forward, backward, rewrite, flipped, &|d, t| {
        within(d, p, t, bound)
    });
    let value = {
        let over_n = d.lam_fv(n_fv, nat, body);
        let with_h = d.lam_fv(h_fv, hypothesis, over_n);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = equiv(d, p, y, x);
        let inner = d.arrow(hypothesis, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, inner);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_symm,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv.trans`: Bishop's four-term estimate at an arbitrary index `j`,
/// closed by the Archimedean property of `ℚ`.
fn declare_transitivity(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rle = crate::rat_prelude::ops::rle;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let first_ty = equiv(d, p, x, y);
    let second_ty = equiv(d, p, y, z);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);
    let hyz_fv = d.fresh_fvar();
    let hyz = d.kernel().fvar(hyz_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let head = sample(d, p, x, n);
    let tail = sample(d, p, z, n);
    let target = rsub(d, rat, head, tail);
    let goal_bound = div_succ(d, p, 2, n);

    // The estimate at an arbitrary index `j`, as a function of `j`.
    let estimate = |d: &mut IntDev<'_>, j: ExprId| -> (ExprId, ExprId) {
        let xj = sample(d, p, x, j);
        let yj = sample(d, p, y, j);
        let zj = sample(d, p, z, j);
        let u1 = rsub(d, rat, head, xj);
        let u2 = rsub(d, rat, xj, yj);
        let u3 = rsub(d, rat, yj, zj);
        let u4 = rsub(d, rat, zj, tail);
        let b1 = modulus(d, p, n, j);
        let b2 = div_succ(d, p, 2, j);
        let b3 = div_succ(d, p, 2, j);
        let b4 = modulus(d, p, j, n);

        let w1 = d.lemma(p.regular, &[x, n, j]);
        let w2 = d.apply(hxy, &[j]);
        let w3 = d.apply(hyz, &[j]);
        let w4 = d.lemma(p.regular, &[z, j, n]);

        let (l1, r1) = halves(d, p, u1, b1, w1);
        let (l2, r2) = halves(d, p, u2, b2, w2);
        let (l3, r3) = halves(d, p, u3, b3, w3);
        let (l4, r4) = halves(d, p, u4, b4, w4);

        // Combine right-nested, so the quantities telescope in the same order.
        let w34 = d.lemma(rat.bounds_add, &[u3, b3, u4, b4, l3, r3, l4, r4]);
        let q34 = radd(d, u3, u4);
        let c34 = radd(d, b3, b4);
        let (l34, r34) = halves(d, p, q34, c34, w34);
        let w234 = d.lemma(rat.bounds_add, &[u2, b2, q34, c34, l2, r2, l34, r34]);
        let q234 = radd(d, u2, q34);
        let c234 = radd(d, b2, c34);
        let (l234, r234) = halves(d, p, q234, c234, w234);
        let w1234 = d.lemma(rat.bounds_add, &[u1, b1, q234, c234, l1, r1, l234, r234]);
        let q1234 = radd(d, u1, q234);
        let c1234 = radd(d, b1, c234);

        // The quantity telescopes: (a−b) + (b−c) = a−c, three times, from the
        // inside out. Nothing here is a rearrangement — the four differences
        // were combined right-nested precisely so that they would chain.
        let mid_yn = rsub(d, rat, yj, tail);
        let mid_xn = rsub(d, rat, xj, tail);
        let step34 = d.lemma(rat.sub_add_sub, &[yj, zj, tail]);
        let step234 = d.lemma(rat.sub_add_sub, &[xj, yj, tail]);
        let step1234 = d.lemma(rat.sub_add_sub, &[head, xj, tail]);
        let q234_reduced = radd(d, u2, mid_yn);
        let staged = radd(d, u1, q234_reduced);
        let first = rcongr(d, q34, mid_yn, step34, &|d, t| {
            let inner = radd(d, u2, t);
            radd(d, u1, inner)
        });
        let second = rcongr(d, q234_reduced, mid_xn, step234, &|d, t| radd(d, u1, t));
        let q1234_reduced = radd(d, u1, mid_xn);
        let (_, quantity) = rchain(
            d,
            q1234,
            &[(staged, first), (q1234_reduced, second), (target, step1234)],
        );

        // The bound rearranges: (A+Bj) + (Cj + (Cj + (Bj+A))) = 2/(n+1) + 6/(j+1).
        let a_atom = div_succ(d, p, 1, n);
        let b_atom = div_succ(d, p, 1, j);
        let c_atom = div_succ(d, p, 2, j);
        let flat_atoms = [a_atom, b_atom, c_atom, c_atom, b_atom, a_atom];
        let sorted_atoms = [a_atom, a_atom, b_atom, c_atom, c_atom, b_atom];
        let flatten = rsum_append(d, rat, &flat_atoms[..2], &flat_atoms[2..]);
        let flat = rsum(d, rat, &flat_atoms);
        let permute = rsum_perm(d, rat, &flat_atoms, &sorted_atoms);
        let sorted = rsum(d, rat, &sorted_atoms);

        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let three = div_succ(d, p, 3, j);
        let five = div_succ(d, p, 5, j);
        let six = div_succ(d, p, 6, j);
        let fuse_inner = d.lemma(rat.nat_div_succ_add, &[two_nat, one_nat, j]);
        let cb = radd(d, c_atom, b_atom);
        let after_inner = rcongr(d, cb, three, fuse_inner, &|d, t| {
            let level1 = radd(d, c_atom, t);
            let level2 = radd(d, b_atom, level1);
            let level3 = radd(d, a_atom, level2);
            radd(d, a_atom, level3)
        });
        let sorted_1 = {
            let level1 = radd(d, c_atom, three);
            let level2 = radd(d, b_atom, level1);
            let level3 = radd(d, a_atom, level2);
            radd(d, a_atom, level3)
        };
        let three_nat = d.num(3);
        let fuse_mid = d.lemma(rat.nat_div_succ_add, &[two_nat, three_nat, j]);
        let c3 = radd(d, c_atom, three);
        let after_mid = rcongr(d, c3, five, fuse_mid, &|d, t| {
            let level2 = radd(d, b_atom, t);
            let level3 = radd(d, a_atom, level2);
            radd(d, a_atom, level3)
        });
        let sorted_2 = {
            let level2 = radd(d, b_atom, five);
            let level3 = radd(d, a_atom, level2);
            radd(d, a_atom, level3)
        };
        let five_nat = d.num(5);
        let fuse_outer = d.lemma(rat.nat_div_succ_add, &[one_nat, five_nat, j]);
        let b5 = radd(d, b_atom, five);
        let after_outer = rcongr(d, b5, six, fuse_outer, &|d, t| {
            let level3 = radd(d, a_atom, t);
            radd(d, a_atom, level3)
        });
        let sorted_3 = {
            let level3 = radd(d, a_atom, six);
            radd(d, a_atom, level3)
        };
        let regroup = {
            let forward = d.lemma(rat.add_assoc, &[a_atom, a_atom, six]);
            let flat_pair = {
                let aa = radd(d, a_atom, a_atom);
                radd(d, aa, six)
            };
            rsymm(d, flat_pair, sorted_3, forward)
        };
        let aa = radd(d, a_atom, a_atom);
        let flat_pair = radd(d, aa, six);
        let fuse_head = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
        let head_bound = div_succ(d, p, 2, n);
        let after_head = rcongr(d, aa, head_bound, fuse_head, &|d, t| radd(d, t, six));
        let final_bound = radd(d, head_bound, six);
        let (_, bound_chain) = rchain(
            d,
            c1234,
            &[
                (flat, flatten),
                (sorted, permute),
                (sorted_1, after_inner),
                (sorted_2, after_mid),
                (sorted_3, after_outer),
                (flat_pair, regroup),
                (final_bound, after_head),
            ],
        );

        let at_quantity = rat_eq_rewrite(d, q1234, target, quantity, w1234, &|d, t| {
            within(d, p, t, c1234)
        });
        let moved = rat_eq_rewrite(d, c1234, final_bound, bound_chain, at_quantity, &|d, t| {
            within(d, p, target, t)
        });
        (final_bound, moved)
    };

    // Upper half: `∀ j, target ≤ 2/(n+1) + 6/(j+1)`, then the Archimedean lemma.
    let six_nat = d.num(6);
    let upper_hypothesis = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let (bound, proof) = estimate(d, j);
        let (_, upper) = halves(d, p, target, bound, proof);
        d.lam_fv(j_fv, nat, upper)
    };
    let upper = d.lemma(
        rat.le_of_le_add_nat_div_succ,
        &[target, goal_bound, six_nat, upper_hypothesis],
    );

    // Lower half: negate the estimate, run the same lemma, and negate back.
    let negated_target = rneg(d, target);
    let lower_hypothesis = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let (bound, proof) = estimate(d, j);
        let (low, high) = halves(d, p, target, bound, proof);
        let flipped = d.lemma(rat.bounds_neg, &[target, bound, low, high]);
        let negated_bound = rneg(d, bound);
        let inner_lower = rle(d, rat, negated_bound, negated_target);
        let inner_upper = rle(d, rat, negated_target, bound);
        let body = d.and_right(inner_lower, inner_upper, flipped);
        d.lam_fv(j_fv, nat, body)
    };
    let lower_raw = d.lemma(
        rat.le_of_le_add_nat_div_succ,
        &[negated_target, goal_bound, six_nat, lower_hypothesis],
    );
    let lower_negated = d.lemma(rat.neg_le_neg, &[negated_target, goal_bound, lower_raw]);
    let twice = rneg(d, negated_target);
    let cancel = d.lemma(rat.neg_neg, &[target]);
    let negated_goal = rneg(d, goal_bound);
    let lower = rat_eq_rewrite(d, twice, target, cancel, lower_negated, &|d, t| {
        rle(d, rat, negated_goal, t)
    });

    let lower_ty = rle(d, rat, negated_goal, target);
    let upper_ty = rle(d, rat, target, goal_bound);
    let pair = and_intro(d, p, lower_ty, upper_ty, lower, upper);
    let value = {
        let over_n = d.lam_fv(n_fv, nat, pair);
        let with_second = d.lam_fv(hyz_fv, second_ty, over_n);
        let with_first = d.lam_fv(hxy_fv, first_ty, with_second);
        let with_z = d.lam_fv(z_fv, carrier, with_first);
        let with_y = d.lam_fv(y_fv, carrier, with_z);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = equiv(d, p, x, z);
        let after_second = d.arrow(second_ty, conclusion);
        let after_first = d.arrow(first_ty, after_second);
        let with_z = d.pi_fv(z_fv, carrier, after_first);
        let with_y = d.pi_fv(y_fv, carrier, with_z);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_trans,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.ofRat q` — the constant sequence, and with it the proof that the
/// carrier is **inhabited**.
///
/// The regularity obligation is `Within (q − q) (1/(m+1) + 1/(n+1))`, and
/// `q − q` is `0` by `Rat.sub_self`, so it reduces to "`0` is inside a
/// nonnegative bound".
fn declare_of_rat(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let rle = crate::rat_prelude::ops::rle;

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let sequences = seq_ty(d);
    let constant = {
        let anon = d.anon_name();
        d.kernel().lam(anon, nat, q, BinderInfo::Default)
    };
    let regularity = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let difference = rsub(d, rat, q, q);
        let bound = modulus(d, p, m, n);
        let zero = rzero(d, rat);
        let negated = rneg(d, bound);
        let one_nat = d.num(1);
        let left_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, m]);
        let right_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, n]);
        let left_atom = div_succ(d, p, 1, m);
        let right_atom = div_succ(d, p, 1, n);
        let nonneg = d.lemma(
            rat.add_nonneg,
            &[left_atom, right_atom, left_nonneg, right_nonneg],
        );
        let nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, nonneg]);
        let collapse = d.lemma(rat.sub_self, &[q]);
        let back = rsymm(d, difference, zero, collapse);
        let lower = rat_eq_rewrite(d, zero, difference, back, nonpos, &|d, t| {
            rle(d, rat, negated, t)
        });
        let upper = rat_eq_rewrite(d, zero, difference, back, nonneg, &|d, t| {
            rle(d, rat, t, bound)
        });
        let lower_ty = rle(d, rat, negated, difference);
        let upper_ty = rle(d, rat, difference, bound);
        let pair = and_intro(d, p, lower_ty, upper_ty, lower, upper);
        let over_n = d.lam_fv(n_fv, nat, pair);
        d.lam_fv(m_fv, nat, over_n)
    };
    let constructor = d.kernel().const_(p.mk, vec![]);
    let body = d.apply(constructor, &[constant, regularity]);
    let value = d.lam_fv(q_fv, carrier, body);
    let result = creal_ty(d, p);
    let ty = d.arrow(carrier, result);
    let _ = sequences;
    d.kernel().add_declaration(Declaration::Definition {
        name: p.of_rat,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 3),
    })
}

/// `Not (CReal.Equiv (ofRat 0) (ofRat 1))` — `Equiv` is not the total relation.
///
/// Read at index `3`, the hypothesis' lower half says `−1/2 ≤ 0 − 1`, i.e.
/// `−1/2 ≤ −1`. Every term in that is closed, so `Rat.le` unfolds through
/// `Int.le` to `Nat.le 1 0` by pure reduction and `Nat.not_succ_le_zero`
/// finishes it. Nothing in the proof is specific to the construction beyond
/// `CReal.seq (ofRat q) n` reducing to `q`, which is the point.
fn declare_discrimination(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = rat.int.nat;

    let zero_rat = rzero(d, rat);
    let one_rat = d.kernel().const_(rat.one, vec![]);
    let left = d.const_app(p.of_rat, &[zero_rat]);
    let right = d.const_app(p.of_rat, &[one_rat]);
    let claim = equiv(d, p, left, right);
    let stmt = d.not(claim);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let index = d.num(3);
    let instance = d.apply(h, &[index]);
    let a = sample(d, p, left, index);
    let b = sample(d, p, right, index);
    let difference = rsub(d, rat, a, b);
    let bound = div_succ(d, p, 2, index);
    let (lower, _upper) = halves(d, p, difference, bound, instance);
    // `lower : Rat.le (-1/2) (-1)`, which reduces to `Nat.le 1 0`.
    let zero_nat = d.zero();
    let absurd = d.lemma(nat.not_succ_le_zero, &[zero_nat, lower]);
    let value = d.lam_fv(h_fv, claim, absurd);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.not_zero_one,
        uparams: vec![],
        ty: stmt,
        value,
    })
}

#[cfg(test)]
mod creal_tests;
