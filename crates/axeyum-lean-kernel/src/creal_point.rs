//! `CPoint`: the Euclidean plane as a pair of constructed reals, and one
//! geometry theorem proved over it — the first step of discharging the
//! `geometry.*`/`cas.*` assumption family the ten `cas-certificate` geometry
//! facts currently record (see `artifacts/facts/F-geometry-*.json`).
//!
//! ## Why a sibling module, not a `creal::` submodule
//!
//! Everything here is built entirely from [`CRealPrelude`]'s **public**
//! surface (`NameId` fields) plus the crate-visible [`IntDev`]/[`NatOps`]
//! term-building toolkit `creal.rs` itself is built out of. Nothing here
//! needs `creal.rs`'s private helpers, so this stays a genuinely additive
//! file: it does not touch `CRealPrelude`'s struct, its `intern_names`, its
//! build pipeline, or its process-wide template cache — all of which are
//! shared, expensive (measured 44 s in a debug build) and actively edited by
//! other lanes. New names live under a fresh `CPoint` root, so there is no
//! collision with anything `creal.rs` declares now or later.
//!
//! ## What is proved, precisely
//!
//! [`CPointPrelude::varignon_diagonals_bisect`] is the **midpoint-of-diagonals**
//! form of Varignon's theorem: writing `P, Q, R, S` for the midpoints of
//! `AB, BC, CD, DA`, it proves `midpoint(P, R) ~ midpoint(Q, S)` — the
//! midpoints of the Varignon quadrilateral's two diagonals coincide. That is
//! the standard characterisation of "PQRS is a parallelogram" (a
//! quadrilateral is a parallelogram iff its diagonals bisect each other), and
//! it is what the ledger's `F:geometry-varignon-midpoint-parallelogram`
//! concludes. It is **not** textually the same statement as that fact's
//! literal phrasing (`Q − P ~ R − S`, a vector difference); the two are
//! algebraically equivalent in an abelian group (`Q + S ~ R + P` rearranges to
//! `Q − P ~ R − S`), but that rearrangement is not proved here — it needs a
//! cancellation/uniqueness-of-negation lemma this file does not build. See
//! the module-level status note in the lane's `docs/plan/status/` file for
//! the exact gap.
//!
//! No hypothesis is taken (the theorem holds for every configuration of four
//! points, degenerate or not), matching the `cas-certificate` route's own
//! certificate for this fact (the empty generator list — see that fact's
//! `notes`).
//!
//! ## How division is avoided being a blocker
//!
//! `CReal.inv` is total only on `PosBound`, and the midpoint needs `x ↦ x/2`.
//! `2` is `CReal.add CReal.one CReal.one`, a *concrete* term, so
//! `PosBound two 0` is provable directly from [`CRealPrelude::le_add_of_nonneg`]
//! at `x := one, q := Rat.one` — no existential witness has to be extracted,
//! and no non-degeneracy condition is needed anywhere in this file.
//!
//! ## The one property that carries the real content
//!
//! [`CPointPrelude::sum_perm`] is the reason the whole theorem is
//! **unconditional**: `(a+b)+(c+d) ~ (b+c)+(d+a)` is a pure permutation
//! identity of an abelian group (`add_comm`/`add_assoc`/`add_congr` alone,
//! six steps, no index arithmetic, no analysis). Doubling every midpoint
//! turns the geometric identity into exactly this sum, so the theorem never
//! touches [`CRealPrelude::le`]/`lt`/`mul_le_mul_of_nonneg_left` or any
//! non-degeneracy side condition at all — matching the `cas-certificate`
//! route's own empty generator list for this fact.

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
use crate::{CRealPrelude, Kernel, KernelError};

/// Heights well above every `creal.rs` height (which top out in the 40s-50s),
/// so nothing here contends with that module's own delta-unfolding order.
const LEAF_HEIGHT: u16 = 900;
const DERIVED_HEIGHT: u16 = 901;

/// The interned names produced by [`build_cpoint_prelude`].
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CPointPrelude {
    /// The reals this plane is built over. Its own axiom footprint is empty,
    /// which is what makes everything below empty too.
    pub creal: CRealPrelude,
    /// `CPoint : Type` — a one-constructor inductive, `mk : CReal → CReal →
    /// CPoint`. Not a quotient and needs none: two coordinates are enough
    /// data, and equality of points is [`Self::point_equiv`], not `Eq`.
    pub point: NameId,
    /// `CPoint.mk`.
    pub mk: NameId,
    /// `CPoint.rec` — the kernel-generated recursor.
    pub rec: NameId,
    /// `CPoint.x : CPoint → CReal`, by large elimination out of the
    /// `Type`-valued inductive.
    pub x: NameId,
    /// `CPoint.y : CPoint → CReal`.
    pub y: NameId,
    /// `CPoint.Equiv p q := And (Equiv (x p) (x q)) (Equiv (y p) (y q))`.
    ///
    /// **This, not `Eq CPoint`, is the equality of points** — it is only ever
    /// as good as `CReal.Equiv` itself, which relates sequences that are
    /// merely asymptotically close.
    pub point_equiv: NameId,
    /// `CPoint.Scalar.two := CReal.add CReal.one CReal.one`.
    pub two: NameId,
    /// `CPoint.Scalar.twoPosBound : CReal.PosBound two 0`.
    ///
    /// Admitted directly from [`CRealPrelude::le_add_of_nonneg`] at
    /// `x := CReal.one, q := Rat.one` — `2`'s positivity needs no existential
    /// witness because `2` is a concrete term, not an arbitrary hypothesis.
    pub two_pos_bound: NameId,
    /// `CPoint.Scalar.inv2 := CReal.inv two 0 twoPosBound` — division by two.
    pub inv2: NameId,
    /// `CPoint.Scalar.midpoint a b := CReal.mul inv2 (CReal.add a b)`.
    pub midpoint: NameId,
    /// `CPoint.Scalar.midpoint_comm : ∀ a b, Equiv (midpoint a b) (midpoint b a)`.
    ///
    /// A cheap sanity witness, not used by [`Self::varignon_diagonals_bisect`].
    pub midpoint_comm: NameId,
    /// `CPoint.Scalar.midpoint_self : ∀ a, Equiv (midpoint a a) a`.
    ///
    /// **The discrimination witness for `midpoint`.** The permutation identity
    /// [`Self::sum_perm`] would hold, footprint-free, for *any* binary scalar
    /// multiplied in via [`Self::inv2`] — it says nothing about `inv2`
    /// actually being `1/2`. This is the fact that pins it: it goes through
    /// [`CRealPrelude::mul_inv_cancel`], the one lemma in this file that
    /// actually consumes [`Self::two_pos_bound`].
    pub midpoint_self: NameId,
    /// `CPoint.Scalar.sum_perm : ∀ a b c e,
    /// Equiv (add (add a b) (add c e)) (add (add b c) (add e a))`.
    ///
    /// The whole reason the theorem needs no hypothesis: a pure abelian-group
    /// permutation of four opaque terms, six steps of
    /// `add_comm`/`add_assoc`/`add_congr` and nothing else. (The fourth
    /// variable is named `e` here, not `d` — this crate's convention makes
    /// `d` the `IntDev` builder in every function signature, and shadowing it
    /// with a scalar would make the builder inaccessible for the rest of the
    /// function body.)
    pub sum_perm: NameId,
    /// `CPoint.Scalar.midpoint_diag_core : ∀ a b c e,
    /// Equiv (midpoint (midpoint a b) (midpoint c e))
    ///       (midpoint (midpoint b c) (midpoint e a))`.
    ///
    /// [`Self::sum_perm`] lifted through [`Self::inv2`] twice via
    /// `left_distrib`/`mul_congr` — the per-coordinate content of
    /// [`Self::varignon_diagonals_bisect`].
    pub midpoint_diag_core: NameId,
    /// `CPoint.midpoint P Q := CPoint.mk (midpoint (x P) (x Q)) (midpoint (y P) (y Q))`.
    pub point_midpoint: NameId,
    /// `CPoint.varignon_diagonals_bisect : ∀ A B C D,
    /// Equiv (midpoint (midpoint A B) (midpoint C D))
    ///       (midpoint (midpoint B C) (midpoint D A))`.
    ///
    /// Writing `P,Q,R,S` for the midpoints of `AB,BC,CD,DA`, this is
    /// `midpoint(P,R) ~ midpoint(Q,S)` — the diagonals of the Varignon
    /// quadrilateral bisect each other, hence PQRS is a parallelogram. No
    /// hypothesis, and axiom-footprint free.
    pub varignon_diagonals_bisect: NameId,
}

/// Build the plane over the constructed reals, and Varignon's theorem
/// (midpoint-of-diagonals form) over it.
///
/// Builds [`CRealPrelude`] first (idempotent, cached) if the kernel does not
/// already carry it.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub fn build_cpoint_prelude(kernel: &mut Kernel) -> Result<CPointPrelude, KernelError> {
    let creal = crate::build_creal_prelude(kernel)?;
    let p = intern_names(kernel, creal);
    if kernel.environment().get(p.point).is_some() {
        return Ok(p);
    }
    let mut d = IntDev::new(kernel, creal.rat.int);
    declare_carrier(&mut d, p)?;
    declare_projections(&mut d, p)?;
    declare_point_equiv(&mut d, p)?;
    declare_two(&mut d, p)?;
    declare_inv2(&mut d, p)?;
    declare_midpoint(&mut d, p)?;
    declare_midpoint_comm(&mut d, p)?;
    declare_midpoint_self(&mut d, p)?;
    declare_sum_perm(&mut d, p)?;
    declare_midpoint_diag_core(&mut d, p)?;
    declare_point_midpoint(&mut d, p)?;
    declare_varignon(&mut d, p)?;
    Ok(p)
}

fn intern_names(kernel: &mut Kernel, creal: CRealPrelude) -> CPointPrelude {
    let anon = kernel.anon();
    let point = kernel.name_str(anon, "CPoint");
    let scalar = kernel.name_str(point, "Scalar");
    CPointPrelude {
        creal,
        point,
        mk: kernel.name_str(point, "mk"),
        rec: kernel.name_str(point, "rec"),
        x: kernel.name_str(point, "x"),
        y: kernel.name_str(point, "y"),
        point_equiv: kernel.name_str(point, "Equiv"),
        two: kernel.name_str(scalar, "two"),
        two_pos_bound: kernel.name_str(scalar, "twoPosBound"),
        inv2: kernel.name_str(scalar, "inv2"),
        midpoint: kernel.name_str(scalar, "midpoint"),
        midpoint_comm: kernel.name_str(scalar, "midpoint_comm"),
        midpoint_self: kernel.name_str(scalar, "midpoint_self"),
        sum_perm: kernel.name_str(scalar, "sum_perm"),
        midpoint_diag_core: kernel.name_str(scalar, "midpoint_diag_core"),
        point_midpoint: kernel.name_str(point, "midpoint"),
        varignon_diagonals_bisect: kernel.name_str(point, "varignon_diagonals_bisect"),
    }
}

// --- term builders -----------------------------------------------------------

fn creal_ty(d: &mut IntDev<'_>, p: CPointPrelude) -> ExprId {
    d.kernel().const_(p.creal.creal, vec![])
}

fn point_ty(d: &mut IntDev<'_>, p: CPointPrelude) -> ExprId {
    d.kernel().const_(p.point, vec![])
}

fn equiv(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.creal.equiv, &[x, y])
}

fn cadd(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.creal.add, &[x, y])
}

fn cmul(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.creal.mul, &[x, y])
}

fn midpoint(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.midpoint, &[a, b])
}

fn refl(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId) -> ExprId {
    d.lemma(p.creal.equiv_refl, &[x])
}

fn symm(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.creal.equiv_symm, &[x, y, h])
}

/// Chain `Equiv start …` through `(next, step)` pairs, the way `creal.rs`'s
/// own `equiv_chain`/`echain` do (duplicated here rather than imported: those
/// are private to `creal.rs`, and this is ten lines).
fn chain(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> ExprId {
    let mut current = start;
    let mut proof = refl(d, p, start);
    for &(next, step) in steps {
        proof = d.lemma(p.creal.equiv_trans, &[start, current, next, proof, step]);
        current = next;
    }
    proof
}

fn and_intro(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    left: ExprId,
    right: ExprId,
    lp: ExprId,
    rp: ExprId,
) -> ExprId {
    let intro = p.creal.rat.int.logic.and_intro;
    d.const_app(intro, &[left, right, lp, rp])
}

// --- the carrier ---------------------------------------------------------

/// `CPoint`: a one-constructor inductive in `Type 0`, `mk : CReal → CReal → CPoint`.
fn declare_carrier(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = creal_ty(d, p);
    let point = point_ty(d, p);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);
    let mk_ty = {
        let inner = d.arrow(creal, point);
        d.arrow(creal, inner)
    };
    d.kernel()
        .add_inductive(p.point, &[], 0, type0, &[(p.mk, mk_ty)])
}

/// The two projections, both by large elimination into `Type 0`.
fn declare_projections(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = creal_ty(d, p);
    let point = point_ty(d, p);
    let one = d.level_one();
    let anon = d.anon_name();

    // x (a b : CReal) := a
    {
        let motive = d.kernel().lam(anon, point, creal, BinderInfo::Default);
        let minor = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let inner = d.lam_fv(b_fv, creal, a);
            d.lam_fv(a_fv, creal, inner)
        };
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, t]);
        let value = d.lam_fv(t_fv, point, body);
        let ty = d.arrow(point, creal);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.x,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(LEAF_HEIGHT),
        })?;
    }
    // y (a b : CReal) := b
    {
        let motive = d.kernel().lam(anon, point, creal, BinderInfo::Default);
        let minor = {
            let a_fv = d.fresh_fvar();
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let inner = d.lam_fv(b_fv, creal, b);
            d.lam_fv(a_fv, creal, inner)
        };
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, t]);
        let value = d.lam_fv(t_fv, point, body);
        let ty = d.arrow(point, creal);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.y,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(LEAF_HEIGHT),
        })
    }
}

/// `CPoint.Equiv p q := And (Equiv (x p) (x q)) (Equiv (y p) (y q))`.
fn declare_point_equiv(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let prop = d.kernel().sort_zero();

    let p_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(p_fv);
    let q_fv = d.fresh_fvar();
    let qt = d.kernel().fvar(q_fv);
    let px = d.const_app(p.x, &[pt]);
    let py = d.const_app(p.y, &[pt]);
    let qx = d.const_app(p.x, &[qt]);
    let qy = d.const_app(p.y, &[qt]);
    let ex = equiv(d, p, px, qx);
    let ey = equiv(d, p, py, qy);
    let claim = d.and(ex, ey);
    let value = {
        let inner = d.lam_fv(q_fv, point, claim);
        d.lam_fv(p_fv, point, inner)
    };
    let ty = {
        let inner = d.arrow(point, prop);
        d.arrow(point, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.point_equiv,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
    })
}

// --- division by two, for a concrete term only ----------------------------

/// `two := CReal.add CReal.one CReal.one`, and `twoPosBound : PosBound two 0`.
fn declare_two(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = creal_ty(d, p);

    let one_a = d.kernel().const_(creal.one, vec![]);
    let one_b = d.kernel().const_(creal.one, vec![]);
    let two_value = cadd(d, p, one_a, one_b);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.two,
        uparams: vec![],
        ty: carrier,
        value: two_value,
        hint: ReducibilityHint::Regular(LEAF_HEIGHT),
    })?;

    let rat = creal.rat;
    let rat_zero = d.kernel().const_(rat.zero, vec![]);
    let rat_one = d.kernel().const_(rat.one, vec![]);
    let strict = d.lemma(rat.zero_lt_one, &[]);
    let nonneg = d.lemma(rat.le_of_lt, &[rat_zero, rat_one, strict]);
    let one_c = d.kernel().const_(creal.one, vec![]);
    let proof = d.lemma(creal.le_add_of_nonneg, &[one_c, rat_one, nonneg]);
    let two_const = d.kernel().const_(p.two, vec![]);
    let zero_nat = d.num(0);
    let ty = d.const_app(creal.pos_bound, &[two_const, zero_nat]);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.two_pos_bound,
        uparams: vec![],
        ty,
        value: proof,
    })
}

/// `inv2 := CReal.inv two 0 twoPosBound`.
fn declare_inv2(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = creal_ty(d, p);
    let two_const = d.kernel().const_(p.two, vec![]);
    let zero_nat = d.num(0);
    let h = d.kernel().const_(p.two_pos_bound, vec![]);
    let value = d.const_app(creal.inv, &[two_const, zero_nat, h]);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.inv2,
        uparams: vec![],
        ty: carrier,
        value,
        hint: ReducibilityHint::Regular(LEAF_HEIGHT + 1),
    })
}

/// `midpoint a b := CReal.mul inv2 (CReal.add a b)`.
fn declare_midpoint(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let inv2 = d.kernel().const_(p.inv2, vec![]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let sum = cadd(d, p, a, b);
    let body = cmul(d, p, inv2, sum);
    let value = {
        let inner = d.lam_fv(b_fv, carrier, body);
        d.lam_fv(a_fv, carrier, inner)
    };
    let ty = {
        let inner = d.arrow(carrier, carrier);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.midpoint,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(LEAF_HEIGHT + 2),
    })
}

/// `midpoint_comm : ∀ a b, Equiv (midpoint a b) (midpoint b a)` — a cheap
/// sanity witness, not used below.
fn declare_midpoint_comm(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = creal_ty(d, p);
    let inv2 = d.kernel().const_(p.inv2, vec![]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let sum_ab = cadd(d, p, a, b);
    let sum_ba = cadd(d, p, b, a);
    let comm_ab = d.lemma(creal.add_comm, &[a, b]);
    let refl_inv2 = refl(d, p, inv2);
    let proof = d.lemma(
        creal.mul_congr,
        &[inv2, inv2, sum_ab, sum_ba, refl_inv2, comm_ab],
    );

    let lhs = midpoint(d, p, a, b);
    let rhs = midpoint(d, p, b, a);
    let ty_body = equiv(d, p, lhs, rhs);
    let value = {
        let inner = d.lam_fv(b_fv, carrier, proof);
        d.lam_fv(a_fv, carrier, inner)
    };
    let ty = {
        let inner = d.pi_fv(b_fv, carrier, ty_body);
        d.pi_fv(a_fv, carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.midpoint_comm,
        uparams: vec![],
        ty,
        value,
    })
}

/// `midpoint_self : ∀ a, Equiv (midpoint a a) a`.
///
/// `mul two a ~ add a a` (via `mul_comm`, `left_distrib`, `mul_one` twice),
/// `mul inv2 two ~ one` (via `mul_comm`, `mul_inv_cancel`), then
/// `mul inv2 (mul two a) ~ a` (via `mul_assoc`, `mul_congr`, `one_mul` built
/// from `mul_comm`+`mul_one`), and the two chains meet at `mul inv2 (add a a)
/// = midpoint a a`.
fn declare_midpoint_self(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = creal_ty(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let one = d.kernel().const_(creal.one, vec![]);
    let two = d.kernel().const_(p.two, vec![]);
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let zero_nat = d.num(0);
    let h_two = d.kernel().const_(p.two_pos_bound, vec![]);

    // TA : Equiv (mul two a) (add a a)
    let mul_two_a = cmul(d, p, two, a);
    let mul_a_two = cmul(d, p, a, two);
    let one_one = cadd(d, p, one, one);
    let mul_a_one_one = cmul(d, p, a, one_one);
    let mul_a_one = cmul(d, p, a, one);
    let sum_mul_a_one = cadd(d, p, mul_a_one, mul_a_one);
    let sum_a_a = cadd(d, p, a, a);

    let step1 = d.lemma(creal.mul_comm, &[two, a]); // mul two a ~ mul a two
    let step2 = d.lemma(creal.left_distrib, &[a, one, one]); // mul a (one+one) ~ (mul a one)+(mul a one)
    let mul_one_a = d.lemma(creal.mul_one, &[a]); // mul a one ~ a
    let step3 = d.lemma(
        creal.add_congr,
        &[mul_a_one, a, mul_a_one, a, mul_one_a, mul_one_a],
    ); // (mul a one)+(mul a one) ~ a+a

    let refl_mul_a_one_one = refl(d, p, mul_a_one_one);
    let ta = chain(
        d,
        p,
        mul_two_a,
        &[
            (mul_a_two, step1),
            (mul_a_one_one, refl_mul_a_one_one), // mul a two =defeq= mul a (one+one)
            (sum_mul_a_one, step2),
            (sum_a_a, step3),
        ],
    );

    // INV2_TWO_ONE : Equiv (mul inv2 two) one
    let mul_two_inv2 = cmul(d, p, two, inv2);
    let mul_inv2_two = cmul(d, p, inv2, two);
    let comm_step = d.lemma(creal.mul_comm, &[inv2, two]); // mul inv2 two ~ mul two inv2
    let cancel = d.lemma(creal.mul_inv_cancel, &[two, zero_nat, h_two]); // mul two (inv two 0 h) ~ one =defeq mul two inv2 ~ one
    let inv2_two_one = chain(
        d,
        p,
        mul_inv2_two,
        &[(mul_two_inv2, comm_step), (one, cancel)],
    );

    // inv2 undoes mul by two: Equiv (mul inv2 (mul two a)) a
    let mul_inv2_two_a = cmul(d, p, mul_inv2_two, a);
    let mul_inv2_mul_two_a = cmul(d, p, inv2, mul_two_a);
    let assoc = d.lemma(creal.mul_assoc, &[inv2, two, a]); // (mul inv2 two) a ~ mul inv2 (mul two a)
    let assoc_symm = symm(d, p, mul_inv2_two_a, mul_inv2_mul_two_a, assoc);
    let refl_a2 = refl(d, p, a);
    let congr1 = d.lemma(
        creal.mul_congr,
        &[mul_inv2_two, one, a, a, inv2_two_one, refl_a2],
    ); // (mul inv2 two) a ~ mul one a
    let mul_one_a_term = cmul(d, p, one, a);
    let mc = d.lemma(creal.mul_comm, &[one, a]); // mul one a ~ mul a one
    let mo = d.lemma(creal.mul_one, &[a]); // mul a one ~ a
    let mul_a_one_repeat = cmul(d, p, a, one);
    let one_mul_a = chain(d, p, mul_one_a_term, &[(mul_a_one_repeat, mc), (a, mo)]);

    let inv2_undoes = chain(
        d,
        p,
        mul_inv2_mul_two_a,
        &[
            (mul_inv2_two_a, assoc_symm),
            (mul_one_a_term, congr1),
            (a, one_mul_a),
        ],
    );

    // Meet: midpoint a a = mul inv2 (add a a) ~ mul inv2 (mul two a) ~ a
    let midpoint_aa = cmul(d, p, inv2, sum_a_a);
    let ta_symm = symm(d, p, mul_two_a, sum_a_a, ta);
    let refl_inv2_2 = refl(d, p, inv2);
    let congr2 = d.lemma(
        creal.mul_congr,
        &[inv2, inv2, sum_a_a, mul_two_a, refl_inv2_2, ta_symm],
    ); // mul inv2 (add a a) ~ mul inv2 (mul two a)
    let final_proof = chain(
        d,
        p,
        midpoint_aa,
        &[(mul_inv2_mul_two_a, congr2), (a, inv2_undoes)],
    );

    let midpoint_a_a = midpoint(d, p, a, a);
    let ty_body = equiv(d, p, midpoint_a_a, a);
    let ty = d.pi_fv(a_fv, carrier, ty_body);
    let value = d.lam_fv(a_fv, carrier, final_proof);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.midpoint_self,
        uparams: vec![],
        ty,
        value,
    })
}

/// `sum_perm : ∀ a b c e, Equiv (add (add a b) (add c e)) (add (add b c) (add e a))`.
///
/// A pure abelian-group rearrangement of four opaque terms — see the module
/// doc for the six-step derivation this mirrors.
fn declare_sum_perm(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = creal_ty(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let ab = cadd(d, p, a, b);
    let ce = cadd(d, p, c, e);
    let s = cadd(d, p, ab, ce); // S = (a+b)+(c+e)

    let bc = cadd(d, p, b, c);
    let ea = cadd(d, p, e, a);
    let t = cadd(d, p, bc, ea); // T = (b+c)+(e+a)

    // n1 = a+(b+(c+e))
    let bce = cadd(d, p, b, ce);
    let n1 = cadd(d, p, a, bce);
    let step1 = d.lemma(creal.add_assoc, &[a, b, ce]); // s ~ n1

    // n2 = a+((b+c)+e)
    let bc_e = cadd(d, p, bc, e);
    let n2 = cadd(d, p, a, bc_e);
    let assoc_bce = d.lemma(creal.add_assoc, &[b, c, e]); // (b+c)+e ~ b+(c+e), i.e. bc_e ~ bce
    let assoc_bce_symm = symm(d, p, bc_e, bce, assoc_bce); // bce ~ bc_e
    let refl_a = refl(d, p, a);
    let step2 = d.lemma(creal.add_congr, &[a, a, bce, bc_e, refl_a, assoc_bce_symm]); // n1 ~ n2

    // n3 = a+(e+(b+c))
    let e_bc = cadd(d, p, e, bc);
    let n3 = cadd(d, p, a, e_bc);
    let comm_bce = d.lemma(creal.add_comm, &[bc, e]); // bc_e ~ e_bc
    let step3 = d.lemma(creal.add_congr, &[a, a, bc_e, e_bc, refl_a, comm_bce]); // n2 ~ n3

    // n4 = (a+e)+(b+c)
    let ae = cadd(d, p, a, e);
    let n4 = cadd(d, p, ae, bc);
    let assoc_a_e_bc = d.lemma(creal.add_assoc, &[a, e, bc]); // n4 ~ n3
    let step4 = symm(d, p, n4, n3, assoc_a_e_bc); // n3 ~ n4

    // n5 = (e+a)+(b+c)
    let n5 = cadd(d, p, ea, bc);
    let comm_ae = d.lemma(creal.add_comm, &[a, e]); // ae ~ ea
    let refl_bc = refl(d, p, bc);
    let step5 = d.lemma(creal.add_congr, &[ae, ea, bc, bc, comm_ae, refl_bc]); // n4 ~ n5

    // t = (b+c)+(e+a)
    let step6 = d.lemma(creal.add_comm, &[ea, bc]); // n5 ~ t

    let proof = chain(
        d,
        p,
        s,
        &[
            (n1, step1),
            (n2, step2),
            (n3, step3),
            (n4, step4),
            (n5, step5),
            (t, step6),
        ],
    );

    let ty_body = equiv(d, p, s, t);
    let ty = {
        let w4 = d.pi_fv(e_fv, carrier, ty_body);
        let w3 = d.pi_fv(c_fv, carrier, w4);
        let w2 = d.pi_fv(b_fv, carrier, w3);
        d.pi_fv(a_fv, carrier, w2)
    };
    let value = {
        let w4 = d.lam_fv(e_fv, carrier, proof);
        let w3 = d.lam_fv(c_fv, carrier, w4);
        let w2 = d.lam_fv(b_fv, carrier, w3);
        d.lam_fv(a_fv, carrier, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_perm,
        uparams: vec![],
        ty,
        value,
    })
}

/// `midpoint_diag_core : ∀ a b c e,
/// Equiv (midpoint (midpoint a b) (midpoint c e)) (midpoint (midpoint b c) (midpoint e a))`.
///
/// `left_distrib` folds each side's two midpoints into `mul inv2 (mul inv2 S)`
/// / `mul inv2 (mul inv2 T)`, [`declare_sum_perm`]'s `S ~ T` is lifted through
/// `mul_congr` twice, and the two sides meet.
fn declare_midpoint_diag_core(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = creal_ty(d, p);
    let inv2 = d.kernel().const_(p.inv2, vec![]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let ab = cadd(d, p, a, b);
    let ce = cadd(d, p, c, e);
    let s = cadd(d, p, ab, ce);
    let bc = cadd(d, p, b, c);
    let ea = cadd(d, p, e, a);
    let t = cadd(d, p, bc, ea);

    let m1 = midpoint(d, p, a, b);
    let m2 = midpoint(d, p, c, e);
    let lhs = midpoint(d, p, m1, m2);
    let n1 = midpoint(d, p, b, c);
    let n2 = midpoint(d, p, e, a);
    let rhs = midpoint(d, p, n1, n2);

    // lhs ~ mul inv2 (mul inv2 s)
    let mul_inv2_ab = cmul(d, p, inv2, ab);
    let mul_inv2_ce = cmul(d, p, inv2, ce);
    let ld_s = d.lemma(creal.left_distrib, &[inv2, ab, ce]); // mul inv2 s ~ (mul inv2 ab)+(mul inv2 ce)
    let mul_inv2_s = cmul(d, p, inv2, s);
    let sum_m1_m2_raw = cadd(d, p, mul_inv2_ab, mul_inv2_ce);
    let ld_s_symm = symm(d, p, mul_inv2_s, sum_m1_m2_raw, ld_s); // (mul inv2 ab)+(mul inv2 ce) ~ mul inv2 s
    let add_m1_m2 = cadd(d, p, m1, m2);
    let refl_inv2 = refl(d, p, inv2);
    let congr_s = d.lemma(
        creal.mul_congr,
        &[inv2, inv2, add_m1_m2, mul_inv2_s, refl_inv2, ld_s_symm],
    ); // lhs ~ mul inv2 (mul inv2 s)
    let quarter_s = cmul(d, p, inv2, mul_inv2_s);

    // rhs ~ mul inv2 (mul inv2 t)
    let mul_inv2_bc = cmul(d, p, inv2, bc);
    let mul_inv2_ea = cmul(d, p, inv2, ea);
    let ld_t = d.lemma(creal.left_distrib, &[inv2, bc, ea]);
    let mul_inv2_t = cmul(d, p, inv2, t);
    let sum_n1_n2_raw = cadd(d, p, mul_inv2_bc, mul_inv2_ea);
    let ld_t_symm = symm(d, p, mul_inv2_t, sum_n1_n2_raw, ld_t);
    let add_n1_n2 = cadd(d, p, n1, n2);
    let congr_t = d.lemma(
        creal.mul_congr,
        &[inv2, inv2, add_n1_n2, mul_inv2_t, refl_inv2, ld_t_symm],
    ); // rhs ~ mul inv2 (mul inv2 t)
    let quarter_t = cmul(d, p, inv2, mul_inv2_t);

    // quarter_s ~ quarter_t, from sum_perm
    let sp = d.lemma(p.sum_perm, &[a, b, c, e]); // s ~ t
    let inner_congr = d.lemma(creal.mul_congr, &[inv2, inv2, s, t, refl_inv2, sp]); // mul inv2 s ~ mul inv2 t
    let outer_congr = d.lemma(
        creal.mul_congr,
        &[inv2, inv2, mul_inv2_s, mul_inv2_t, refl_inv2, inner_congr],
    ); // quarter_s ~ quarter_t

    let congr_t_symm = symm(d, p, rhs, quarter_t, congr_t); // quarter_t ~ rhs

    let proof = chain(
        d,
        p,
        lhs,
        &[
            (quarter_s, congr_s),
            (quarter_t, outer_congr),
            (rhs, congr_t_symm),
        ],
    );

    let ty_body = equiv(d, p, lhs, rhs);
    let ty = {
        let w4 = d.pi_fv(e_fv, carrier, ty_body);
        let w3 = d.pi_fv(c_fv, carrier, w4);
        let w2 = d.pi_fv(b_fv, carrier, w3);
        d.pi_fv(a_fv, carrier, w2)
    };
    let value = {
        let w4 = d.lam_fv(e_fv, carrier, proof);
        let w3 = d.lam_fv(c_fv, carrier, w4);
        let w2 = d.lam_fv(b_fv, carrier, w3);
        d.lam_fv(a_fv, carrier, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.midpoint_diag_core,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CPoint.midpoint P Q := CPoint.mk (midpoint (x P) (x Q)) (midpoint (y P) (y Q))`.
fn declare_point_midpoint(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let mx = midpoint(d, p, ax, bx);
    let my = midpoint(d, p, ay, by);
    let value_body = d.const_app(p.mk, &[mx, my]);

    let value = {
        let inner = d.lam_fv(pb_fv, point, value_body);
        d.lam_fv(pa_fv, point, inner)
    };
    let ty = {
        let inner = d.arrow(point, point);
        d.arrow(point, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.point_midpoint,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 3),
    })
}

/// `varignon_diagonals_bisect : ∀ A B C D,
/// Equiv (midpoint (midpoint A B) (midpoint C D)) (midpoint (midpoint B C) (midpoint D A))`.
///
/// Writing `P,Q,R,S` for the midpoints of `AB,BC,CD,DA`: this is
/// `midpoint(P,R) ~ midpoint(Q,S)`, i.e. the diagonals of the Varignon
/// quadrilateral bisect each other — no hypothesis, for every configuration.
fn declare_varignon(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    // The fourth point ("D"); the fvar is named `e_fv` so the local `d`
    // (the `IntDev` builder) is never shadowed.
    let e_fv = d.fresh_fvar();
    let pd = d.kernel().fvar(e_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);
    let dx = d.const_app(p.x, &[pd]);
    let dy = d.const_app(p.y, &[pd]);

    let core_x = d.lemma(p.midpoint_diag_core, &[ax, bx, cx, dx]);
    let core_y = d.lemma(p.midpoint_diag_core, &[ay, by, cy, dy]);

    let claim_x = {
        let mab_x = midpoint(d, p, ax, bx);
        let mcd_x = midpoint(d, p, cx, dx);
        let mbc_x = midpoint(d, p, bx, cx);
        let mda_x = midpoint(d, p, dx, ax);
        let left_x = midpoint(d, p, mab_x, mcd_x);
        let right_x = midpoint(d, p, mbc_x, mda_x);
        equiv(d, p, left_x, right_x)
    };
    let claim_y = {
        let mab_y = midpoint(d, p, ay, by);
        let mcd_y = midpoint(d, p, cy, dy);
        let mbc_y = midpoint(d, p, by, cy);
        let mda_y = midpoint(d, p, dy, ay);
        let left_y = midpoint(d, p, mab_y, mcd_y);
        let right_y = midpoint(d, p, mbc_y, mda_y);
        equiv(d, p, left_y, right_y)
    };
    let proof = and_intro(d, p, claim_x, claim_y, core_x, core_y);

    let pmab = d.const_app(p.point_midpoint, &[pa, pb]);
    let pmcd = d.const_app(p.point_midpoint, &[pc, pd]);
    let left = d.const_app(p.point_midpoint, &[pmab, pmcd]);
    let pmbc = d.const_app(p.point_midpoint, &[pb, pc]);
    let pmda = d.const_app(p.point_midpoint, &[pd, pa]);
    let right = d.const_app(p.point_midpoint, &[pmbc, pmda]);
    let ty_body = d.const_app(p.point_equiv, &[left, right]);

    let ty = {
        let w4 = d.pi_fv(e_fv, point, ty_body);
        let w3 = d.pi_fv(c_fv, point, w4);
        let w2 = d.pi_fv(b_fv, point, w3);
        d.pi_fv(a_fv, point, w2)
    };
    let value = {
        let w4 = d.lam_fv(e_fv, point, proof);
        let w3 = d.lam_fv(c_fv, point, w4);
        let w2 = d.lam_fv(b_fv, point, w3);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.varignon_diagonals_bisect,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod creal_point_tests;
