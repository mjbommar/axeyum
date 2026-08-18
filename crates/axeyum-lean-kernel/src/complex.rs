//! **ℂ, constructed**: pairs of `CReal`s under a *defined* equality, costing
//! **zero** trusted declarations, and with the ordered-ring laws deliberately
//! absent — refuted, not merely omitted.
//!
//! This is ADR-0479
//! (`docs/research/09-decisions/adr-0479-complex-is-a-pair-setoid-over-creal-and-carries-no-order.md`),
//! and it continues ADR-0468 one layer up. `CReal` is a Bishop setoid of regular ℚ-sequences whose
//! equality is `CReal.Equiv`, a `Prop`-valued *definition* rather than `Eq`;
//! `Complex` inherits exactly that discipline:
//!
//! ```text
//! Complex.Equiv z w := CReal.Equiv (re z) (re w) ∧ CReal.Equiv (im z) (im w)
//! ```
//!
//! so `Eq Complex` is **not** the equality of complex numbers, every operation
//! owes a congruence lemma, and every law that mentions equality is stated over
//! `Complex.Equiv`. Nothing here needs `Quot.sound`, `funext` or `propext`, for
//! the same reason `CReal` did not: the quotient is never taken.
//!
//! # ℂ is a ring, and that is the *whole* of it
//!
//! `ArithPrelude`'s axiomatized `Real` package is an **ordered** commutative
//! ring: 22 laws, of which 13 mention `le` or `lt`. Nine do not, and those nine
//! — `add_comm`, `add_assoc`, `add_zero`, `add_neg`, `mul_comm`, `mul_assoc`,
//! `mul_one`, `mul_zero`, `left_distrib` — are exactly the ones proved here, in
//! `Complex.Equiv` form. See [`ComplexPrelude::ring_laws`].
//!
//! The other 13 are not *unavailable*; they are **jointly refutable**, and
//! [`ComplexPrelude::no_compatible_order`] says so as a theorem rather than as a
//! comment: for any two relations `le`, `lt` on `Complex` satisfying seven of
//! those 13 (reflexivity, irreflexivity of `lt`, `lt_of_le_of_lt`, `add_le_add`,
//! the setoid's `le_congr`, `sq_nonneg`, and `zero_lt_one`), `False` follows.
//! The witness is `I`: `sq_nonneg I` plus [`ComplexPrelude::i_sq`] gives
//! `0 ≤ −1`, adding `1` gives `1 ≤ 0`, and `0 < 1` closes it. **No** classical
//! reasoning is involved — the proof is a direct term, and `¬¬P → P` does not
//! exist in this logic prelude.
//!
//! That is the precise sense in which "ℂ is not ordered" is a *result* of this
//! module and not a scoping decision.
//!
//! # Why the component laws are cheap, and where the work actually went
//!
//! Every `Complex` law reduces, by `Complex.Equiv`'s definition, to two
//! `CReal.Equiv` obligations on the components — and those are *algebraic*
//! identities in a commutative ring, with no analysis left in them. The real
//! part of `(z·w)·v` and of `z·(w·v)` are the same four monomials in a different
//! order. Deriving each such rearrangement by hand from `add_comm`, `add_assoc`,
//! `mul_comm`, `mul_assoc`, `left_distrib` and the three congruences is where a
//! development of this shape goes wrong silently, so it is done once, by
//! decision procedure: [`ring`] normalizes a `CReal` expression to a sorted
//! multiset of signed monomials and emits the `Equiv` proof. It declares
//! nothing, so the `CReal` namespace is untouched and the trusted surface is
//! unchanged.
//!
//! # What is *not* claimed
//!
//! No order, by design and by [`ComplexPrelude::no_compatible_order`]. No
//! inverse, no division, no `√`, no completeness, no algebraic closure — each is
//! a separate development, and none of them is one of the nine. `Complex.normSq`
//! and [`ComplexPrelude::mul_conj`] land in `CReal`'s **existing** order
//! (`CReal.le`), which is available precisely because it is a statement about
//! the components rather than about ℂ.

// Proof scripts are long, straight-line term constructions with short
// mathematical names, exactly as in `creal` and `rat_prelude`.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines,
    // The `declare_*` helpers take one-shot builder closures whose types are
    // read once, at the call site directly below them; naming them adds
    // indirection without adding meaning, and a `type` alias also fixes the
    // closure's captured lifetime, which these do not want.
    clippy::type_complexity
)]

use crate::BinderInfo;
use crate::CRealPrelude;
use crate::creal::build_creal_prelude;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::{Kernel, KernelError};

mod ring;

#[cfg(test)]
mod complex_tests;

use ring::{RExpr, cadd, ceq, cmul, cneg, cone, crefl, czero, ring_proof};

/// Delta height for the leaf complex definitions: above every `CReal` one.
const LEAF_HEIGHT: u16 = 60;
/// Height for a definition that calls a leaf one.
const DERIVED_HEIGHT: u16 = 61;

/// The interned names produced by [`build_complex_prelude`].
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ComplexPrelude {
    /// The real development ℂ is constructed over. Its trusted surface is
    /// empty, which is what makes every law below empty too.
    pub creal: CRealPrelude,

    /// `Complex : Type` — a one-constructor inductive with two `CReal` fields.
    /// **Not** a quotient.
    pub complex: NameId,
    /// `Complex.mk : CReal → CReal → Complex`.
    pub mk: NameId,
    /// `Complex.rec` — the kernel-generated recursor.
    pub rec: NameId,
    /// `Complex.re : Complex → CReal`.
    pub re: NameId,
    /// `Complex.im : Complex → CReal`.
    pub im: NameId,

    /// `Complex.Equiv : Complex → Complex → Prop` — componentwise
    /// `CReal.Equiv`.
    ///
    /// **This, and not `Eq Complex`, is the equality of complex numbers.**
    pub equiv: NameId,
    /// `Complex.Equiv.refl`.
    pub equiv_refl: NameId,
    /// `Complex.Equiv.symm`.
    pub equiv_symm: NameId,
    /// `Complex.Equiv.trans`.
    pub equiv_trans: NameId,

    /// `Complex.ofReal : CReal → Complex` — the embedding ℝ ↪ ℂ, and the
    /// **non-vacuity** witness for the carrier.
    pub of_real: NameId,
    /// `Complex.I : Complex` — the imaginary unit, `ofReal 0 + i·1` written
    /// directly as the pair `(0, 1)`.
    pub i: NameId,
    /// `Complex.zero : Complex`.
    pub zero: NameId,
    /// `Complex.one : Complex`.
    pub one: NameId,

    /// `Complex.add : Complex → Complex → Complex`, componentwise.
    pub add: NameId,
    /// `Complex.neg : Complex → Complex`, componentwise.
    pub neg: NameId,
    /// `Complex.mul : Complex → Complex → Complex` — the **only** operation
    /// that mixes the components, and the reason ℂ is not just ℝ².
    pub mul: NameId,

    /// `Complex.add_congr` — the first setoid congruence obligation.
    pub add_congr: NameId,
    /// `Complex.neg_congr`.
    pub neg_congr: NameId,
    /// `Complex.mul_congr`.
    pub mul_congr: NameId,
    /// `Complex.conj_congr`.
    pub conj_congr: NameId,

    /// `Complex.add_comm` — one of the nine, in `Equiv` form.
    pub add_comm: NameId,
    /// `Complex.add_assoc` — one of the nine.
    pub add_assoc: NameId,
    /// `Complex.add_zero` — one of the nine.
    pub add_zero: NameId,
    /// `Complex.add_neg` — one of the nine.
    pub add_neg: NameId,
    /// `Complex.mul_comm` — one of the nine.
    pub mul_comm: NameId,
    /// `Complex.mul_assoc` — one of the nine, and the identity that pays for
    /// the ring calculus on its own: eight monomials, two orderings.
    pub mul_assoc: NameId,
    /// `Complex.mul_one` — one of the nine.
    pub mul_one: NameId,
    /// `Complex.mul_zero` — one of the nine.
    pub mul_zero: NameId,
    /// `Complex.left_distrib` — one of the nine.
    pub left_distrib: NameId,

    /// `Complex.ofReal_add : Equiv (add (ofReal a) (ofReal b)) (ofReal (a + b))`
    /// — the embedding is additive.
    pub of_real_add: NameId,
    /// `Complex.ofReal_mul : Equiv (mul (ofReal a) (ofReal b)) (ofReal (a · b))`.
    ///
    /// The **pinning** witness for the product: `mul_comm`, `mul_zero` and
    /// `left_distrib` all hold, footprint-free, of `fun _ _ => zero`. This
    /// fixes the operation on the whole embedded ℝ rather than asserting a
    /// property of it.
    pub of_real_mul: NameId,
    /// `Complex.I_sq : Equiv (mul I I) (neg one)`.
    ///
    /// The **pinning** witness for the imaginary unit — and the engine of
    /// [`Self::no_compatible_order`]. Without it `I` could be anything;
    /// `ofReal_mul` says nothing about it, because `I` is not in the image of
    /// `ofReal`.
    pub i_sq: NameId,
    /// `Complex.Equiv.not_zero_one : Not (Equiv zero one)` — the
    /// **discrimination** witness for the real component.
    pub not_zero_one: NameId,
    /// `Complex.Equiv.not_zero_I : Not (Equiv zero I)` — the discrimination
    /// witness for the *imaginary* component, and the statement that `I` is not
    /// `0`. An equivalence relation that relates everything is still an
    /// equivalence relation, and `not_zero_one` alone would not notice a
    /// `Complex.Equiv` that ignored the imaginary part entirely.
    pub not_zero_i: NameId,

    /// `Complex.conj : Complex → Complex`.
    pub conj: NameId,
    /// `Complex.normSq : Complex → CReal` — `re z ² + im z ²`, valued in ℝ
    /// because ℂ has no order to be nonneg *in*.
    pub norm_sq: NameId,
    /// `Complex.mul_conj : ∀ z, Equiv (mul z (conj z)) (ofReal (normSq z))`.
    ///
    /// The identity `z · z̄ = ‖z‖²`, and the one law whose imaginary part needs
    /// the ring calculus's **cancellation** pass: `a·(−b) + b·a` is two
    /// monomials that annihilate, not two that reorder.
    pub mul_conj: NameId,
    /// `Complex.normSq_nonneg : ∀ z, CReal.le CReal.zero (normSq z)` — the
    /// norm lands in `CReal`'s nonneg cone.
    pub norm_sq_nonneg: NameId,

    /// `Complex.no_compatible_order` — **ℂ admits no ordered-ring structure**,
    /// as a theorem. See the module documentation.
    pub no_compatible_order: NameId,
}

impl ComplexPrelude {
    /// The nine commutative-**ring** laws over `Complex`, in the declaration
    /// order of the `Real` package.
    ///
    /// These are exactly the `Real` package's 22 ordered-commutative-ring laws
    /// **minus** the 13 that mention `le` or `lt`. The omission is not a gap:
    /// [`Self::no_compatible_order`] proves that no `le`/`lt` on `Complex` can
    /// satisfy them. All nine mention equality in the axiomatized package and
    /// are therefore stated here over [`Complex.Equiv`](Self::equiv), because
    /// `Eq Complex` is not the equality of complex numbers.
    ///
    /// This list exists so that "9 of 9" is read out of the kernel by a test
    /// rather than asserted in prose.
    #[must_use]
    pub fn ring_laws(&self) -> [NameId; 9] {
        [
            self.add_comm,
            self.add_assoc,
            self.add_zero,
            self.add_neg,
            self.mul_comm,
            self.mul_assoc,
            self.mul_one,
            self.mul_zero,
            self.left_distrib,
        ]
    }
}

fn intern_names(kernel: &mut Kernel, creal: CRealPrelude) -> ComplexPrelude {
    let anon = kernel.anon();
    let complex = kernel.name_str(anon, "Complex");
    let equiv = kernel.name_str(complex, "Equiv");
    ComplexPrelude {
        creal,
        complex,
        mk: kernel.name_str(complex, "mk"),
        rec: kernel.name_str(complex, "rec"),
        re: kernel.name_str(complex, "re"),
        im: kernel.name_str(complex, "im"),
        equiv,
        equiv_refl: kernel.name_str(equiv, "refl"),
        equiv_symm: kernel.name_str(equiv, "symm"),
        equiv_trans: kernel.name_str(equiv, "trans"),
        of_real: kernel.name_str(complex, "ofReal"),
        i: kernel.name_str(complex, "I"),
        zero: kernel.name_str(complex, "zero"),
        one: kernel.name_str(complex, "one"),
        add: kernel.name_str(complex, "add"),
        neg: kernel.name_str(complex, "neg"),
        mul: kernel.name_str(complex, "mul"),
        add_congr: kernel.name_str(complex, "add_congr"),
        neg_congr: kernel.name_str(complex, "neg_congr"),
        mul_congr: kernel.name_str(complex, "mul_congr"),
        conj_congr: kernel.name_str(complex, "conj_congr"),
        add_comm: kernel.name_str(complex, "add_comm"),
        add_assoc: kernel.name_str(complex, "add_assoc"),
        add_zero: kernel.name_str(complex, "add_zero"),
        add_neg: kernel.name_str(complex, "add_neg"),
        mul_comm: kernel.name_str(complex, "mul_comm"),
        mul_assoc: kernel.name_str(complex, "mul_assoc"),
        mul_one: kernel.name_str(complex, "mul_one"),
        mul_zero: kernel.name_str(complex, "mul_zero"),
        left_distrib: kernel.name_str(complex, "left_distrib"),
        of_real_add: kernel.name_str(complex, "ofReal_add"),
        of_real_mul: kernel.name_str(complex, "ofReal_mul"),
        i_sq: kernel.name_str(complex, "I_sq"),
        not_zero_one: kernel.name_str(equiv, "not_zero_one"),
        not_zero_i: kernel.name_str(equiv, "not_zero_I"),
        conj: kernel.name_str(complex, "conj"),
        norm_sq: kernel.name_str(complex, "normSq"),
        mul_conj: kernel.name_str(complex, "mul_conj"),
        norm_sq_nonneg: kernel.name_str(complex, "normSq_nonneg"),
        no_compatible_order: kernel.name_str(complex, "no_compatible_order"),
    }
}

/// Build the complex prelude: ℂ as pairs of constructed reals, **asserting
/// nothing**.
///
/// Idempotent on a kernel that already carries it. A failure rolls the
/// environment back to the pre-call state.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub fn build_complex_prelude(kernel: &mut Kernel) -> Result<ComplexPrelude, KernelError> {
    let creal = build_creal_prelude(kernel)?;
    let prelude = intern_names(kernel, creal);
    if kernel.environment().get(prelude.complex).is_some() {
        return Ok(prelude);
    }
    let checkpoint = kernel.prelude_checkpoint();
    let built = (|| -> Result<(), KernelError> {
        let mut d = IntDev::new(kernel, creal.rat.int);
        declare_carrier(&mut d, prelude)?;
        declare_projections(&mut d, prelude)?;
        declare_equiv(&mut d, prelude)?;
        declare_setoid_laws(&mut d, prelude)?;
        declare_constants(&mut d, prelude)?;
        declare_operations(&mut d, prelude)?;
        declare_congruences(&mut d, prelude)?;
        declare_ring_laws(&mut d, prelude)?;
        declare_pinning(&mut d, prelude)?;
        declare_norm(&mut d, prelude)?;
        declare_no_order(&mut d, prelude)
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

/// `Complex`.
fn complex_ty(d: &mut IntDev<'_>, p: ComplexPrelude) -> ExprId {
    d.kernel().const_(p.complex, vec![])
}

/// `CReal`.
fn creal_ty(d: &mut IntDev<'_>, p: ComplexPrelude) -> ExprId {
    d.kernel().const_(p.creal.creal, vec![])
}

/// `Complex.re z`.
fn re_of(d: &mut IntDev<'_>, p: ComplexPrelude, z: ExprId) -> ExprId {
    d.const_app(p.re, &[z])
}

/// `Complex.im z`.
fn im_of(d: &mut IntDev<'_>, p: ComplexPrelude, z: ExprId) -> ExprId {
    d.const_app(p.im, &[z])
}

/// `Complex.Equiv z w`.
fn zeq(d: &mut IntDev<'_>, p: ComplexPrelude, z: ExprId, w: ExprId) -> ExprId {
    d.const_app(p.equiv, &[z, w])
}

/// `And.intro` at two `Prop`s.
fn and_intro(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    left: ExprId,
    right: ExprId,
    lp: ExprId,
    rp: ExprId,
) -> ExprId {
    let intro = p.creal.rat.int.logic.and_intro;
    d.const_app(intro, &[left, right, lp, rp])
}

/// A symbolic complex expression, in the language every law below is written
/// in.
///
/// The point of the type is [`parts`]: a `CExpr` knows its own real and
/// imaginary parts as [`RExpr`]s, so a `Complex` law becomes two `CReal` ring
/// identities mechanically rather than by hand.
#[derive(Clone)]
enum CExpr {
    /// A `Complex` variable, carrying its term and its two projections.
    Var(ExprId, ExprId, ExprId),
    /// `Complex.zero`.
    Zero,
    /// `Complex.one`.
    One,
    /// `Complex.I`.
    I,
    /// `Complex.ofReal`, of a real expression.
    OfReal(RExpr, ExprId),
    /// `Complex.add`.
    Add(Box<CExpr>, Box<CExpr>),
    /// `Complex.neg`.
    Neg(Box<CExpr>),
    /// `Complex.mul`.
    Mul(Box<CExpr>, Box<CExpr>),
    /// `Complex.conj`.
    Conj(Box<CExpr>),
}

impl CExpr {
    fn var(d: &mut IntDev<'_>, p: ComplexPrelude, z: ExprId) -> CExpr {
        let re = re_of(d, p, z);
        let im = im_of(d, p, z);
        CExpr::Var(z, re, im)
    }
    fn add(a: CExpr, b: CExpr) -> CExpr {
        CExpr::Add(Box::new(a), Box::new(b))
    }
    fn mul(a: CExpr, b: CExpr) -> CExpr {
        CExpr::Mul(Box::new(a), Box::new(b))
    }
    fn neg(a: CExpr) -> CExpr {
        CExpr::Neg(Box::new(a))
    }
    fn conj(a: CExpr) -> CExpr {
        CExpr::Conj(Box::new(a))
    }
}

/// The real and imaginary parts of a symbolic complex expression, as `CReal`
/// expressions the ring calculus can decide.
///
/// This *is* the definition of each operation, transcribed once. `Mul` is the
/// only clause that mixes the components.
fn parts(e: &CExpr) -> (RExpr, RExpr) {
    match e {
        CExpr::Var(_, re, im) => (RExpr::Atom(*re), RExpr::Atom(*im)),
        CExpr::Zero => (RExpr::Zero, RExpr::Zero),
        CExpr::One => (RExpr::One, RExpr::Zero),
        CExpr::I => (RExpr::Zero, RExpr::One),
        CExpr::OfReal(r, _) => (r.clone(), RExpr::Zero),
        CExpr::Add(a, b) => {
            let (ar, ai) = parts(a);
            let (br, bi) = parts(b);
            (RExpr::add(ar, br), RExpr::add(ai, bi))
        }
        CExpr::Neg(a) => {
            let (ar, ai) = parts(a);
            (RExpr::neg(ar), RExpr::neg(ai))
        }
        CExpr::Mul(a, b) => {
            let (ar, ai) = parts(a);
            let (br, bi) = parts(b);
            (
                RExpr::add(
                    RExpr::mul(ar.clone(), br.clone()),
                    RExpr::neg(RExpr::mul(ai.clone(), bi.clone())),
                ),
                RExpr::add(RExpr::mul(ar, bi), RExpr::mul(ai, br)),
            )
        }
        CExpr::Conj(a) => {
            let (ar, ai) = parts(a);
            (ar, RExpr::neg(ai))
        }
    }
}

/// The `Complex` term a symbolic expression denotes.
fn render_c(d: &mut IntDev<'_>, p: ComplexPrelude, e: &CExpr) -> ExprId {
    match e {
        CExpr::Var(z, _, _) => *z,
        CExpr::Zero => d.kernel().const_(p.zero, vec![]),
        CExpr::One => d.kernel().const_(p.one, vec![]),
        CExpr::I => d.kernel().const_(p.i, vec![]),
        CExpr::OfReal(_, term) => d.const_app(p.of_real, &[*term]),
        CExpr::Add(a, b) => {
            let left = render_c(d, p, a);
            let right = render_c(d, p, b);
            d.const_app(p.add, &[left, right])
        }
        CExpr::Neg(a) => {
            let inner = render_c(d, p, a);
            d.const_app(p.neg, &[inner])
        }
        CExpr::Mul(a, b) => {
            let left = render_c(d, p, a);
            let right = render_c(d, p, b);
            d.const_app(p.mul, &[left, right])
        }
        CExpr::Conj(a) => {
            let inner = render_c(d, p, a);
            d.const_app(p.conj, &[inner])
        }
    }
}

/// The `And.intro` proof of `Complex.Equiv lhs rhs`, both components decided by
/// the ring calculus.
///
/// The proof's *type* is the reduced, componentwise one; the kernel accepts it
/// against the `Complex.Equiv` statement by δι-reduction, which is exactly the
/// property that makes the pair carrier worth having.
fn ring_law_proof(d: &mut IntDev<'_>, p: ComplexPrelude, lhs: &CExpr, rhs: &CExpr) -> ExprId {
    let creal = p.creal;
    let (lr, li) = parts(lhs);
    let (rr, ri) = parts(rhs);
    let real_proof = ring_proof(d, creal, &lr, &rr);
    let imag_proof = ring_proof(d, creal, &li, &ri);
    let lr_term = ring::render(d, creal, &lr);
    let rr_term = ring::render(d, creal, &rr);
    let li_term = ring::render(d, creal, &li);
    let ri_term = ring::render(d, creal, &ri);
    let real_claim = ceq(d, creal, lr_term, rr_term);
    let imag_claim = ceq(d, creal, li_term, ri_term);
    and_intro(d, p, real_claim, imag_claim, real_proof, imag_proof)
}

// --- the carrier ------------------------------------------------------------

/// `Complex`, a one-constructor inductive in `Type 0` with two `CReal` fields.
fn declare_carrier(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let real = creal_ty(d, p);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);
    let result = complex_ty(d, p);
    let mk_ty = {
        let inner = d.arrow(real, result);
        d.arrow(real, inner)
    };
    d.kernel()
        .add_inductive(p.complex, &[], 0, type0, &[(p.mk, mk_ty)])
}

/// The two projections, by large elimination out of the `Type`-valued
/// inductive.
fn declare_projections(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let real = creal_ty(d, p);
    let carrier = complex_ty(d, p);
    let one = d.level_one();
    let anon = d.anon_name();

    let project = |d: &mut IntDev<'_>, name: NameId, first: bool| -> Result<(), KernelError> {
        let motive = d.kernel().lam(anon, carrier, real, BinderInfo::Default);
        let minor = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let chosen = if first { a } else { b };
            let inner = d.lam_fv(b_fv, real, chosen);
            d.lam_fv(a_fv, real, inner)
        };
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, z]);
        let value = d.lam_fv(z_fv, carrier, body);
        let ty = d.arrow(carrier, real);
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(LEAF_HEIGHT),
        })
    };
    project(d, p.re, true)?;
    project(d, p.im, false)
}

/// `Complex.Equiv z w := CReal.Equiv (re z) (re w) ∧ CReal.Equiv (im z) (im w)`.
fn declare_equiv(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let prop = d.kernel().sort_zero();
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let re_z = re_of(d, p, z);
    let re_w = re_of(d, p, w);
    let im_z = im_of(d, p, z);
    let im_w = im_of(d, p, w);
    let left = ceq(d, p.creal, re_z, re_w);
    let right = ceq(d, p.creal, im_z, im_w);
    let body = d.and(left, right);
    let value = {
        let with_w = d.lam_fv(w_fv, carrier, body);
        d.lam_fv(z_fv, carrier, with_w)
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
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
    })
}

/// The two component `CReal.Equiv` propositions of `Complex.Equiv z w`, and the
/// two halves of a proof of it.
fn equiv_halves(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    z: ExprId,
    w: ExprId,
    proof: ExprId,
) -> (ExprId, ExprId) {
    let re_z = re_of(d, p, z);
    let re_w = re_of(d, p, w);
    let im_z = im_of(d, p, z);
    let im_w = im_of(d, p, w);
    let left = ceq(d, p.creal, re_z, re_w);
    let right = ceq(d, p.creal, im_z, im_w);
    let first = d.and_left(left, right, proof);
    let second = d.and_right(left, right, proof);
    (first, second)
}

/// `Equiv.refl`, `Equiv.symm`, `Equiv.trans`: componentwise, and nothing more.
fn declare_setoid_laws(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    // refl
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let re_z = re_of(d, p, z);
        let im_z = im_of(d, p, z);
        let left = ceq(d, creal, re_z, re_z);
        let right = ceq(d, creal, im_z, im_z);
        let lp = crefl(d, creal, re_z);
        let rp = crefl(d, creal, im_z);
        let body = and_intro(d, p, left, right, lp, rp);
        let value = d.lam_fv(z_fv, carrier, body);
        let ty = {
            let claim = zeq(d, p, z, z);
            d.pi_fv(z_fv, carrier, claim)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.equiv_refl,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // symm
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let hypothesis = zeq(d, p, z, w);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let (first, second) = equiv_halves(d, p, z, w, h);
        let re_z = re_of(d, p, z);
        let re_w = re_of(d, p, w);
        let im_z = im_of(d, p, z);
        let im_w = im_of(d, p, w);
        let lp = d.lemma(creal.equiv_symm, &[re_z, re_w, first]);
        let rp = d.lemma(creal.equiv_symm, &[im_z, im_w, second]);
        let left = ceq(d, creal, re_w, re_z);
        let right = ceq(d, creal, im_w, im_z);
        let body = and_intro(d, p, left, right, lp, rp);
        let value = {
            let with_h = d.lam_fv(h_fv, hypothesis, body);
            let with_w = d.lam_fv(w_fv, carrier, with_h);
            d.lam_fv(z_fv, carrier, with_w)
        };
        let ty = {
            let conclusion = zeq(d, p, w, z);
            let inner = d.arrow(hypothesis, conclusion);
            let with_w = d.pi_fv(w_fv, carrier, inner);
            d.pi_fv(z_fv, carrier, with_w)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.equiv_symm,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // trans
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let first_ty = zeq(d, p, z, w);
        let second_ty = zeq(d, p, w, v);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let (a1, b1) = equiv_halves(d, p, z, w, h1);
        let (a2, b2) = equiv_halves(d, p, w, v, h2);
        let re_z = re_of(d, p, z);
        let re_w = re_of(d, p, w);
        let re_v = re_of(d, p, v);
        let im_z = im_of(d, p, z);
        let im_w = im_of(d, p, w);
        let im_v = im_of(d, p, v);
        let lp = d.lemma(creal.equiv_trans, &[re_z, re_w, re_v, a1, a2]);
        let rp = d.lemma(creal.equiv_trans, &[im_z, im_w, im_v, b1, b2]);
        let left = ceq(d, creal, re_z, re_v);
        let right = ceq(d, creal, im_z, im_v);
        let body = and_intro(d, p, left, right, lp, rp);
        let value = {
            let with2 = d.lam_fv(h2_fv, second_ty, body);
            let with1 = d.lam_fv(h1_fv, first_ty, with2);
            let with_v = d.lam_fv(v_fv, carrier, with1);
            let with_w = d.lam_fv(w_fv, carrier, with_v);
            d.lam_fv(z_fv, carrier, with_w)
        };
        let ty = {
            let conclusion = zeq(d, p, z, v);
            let after2 = d.arrow(second_ty, conclusion);
            let after1 = d.arrow(first_ty, after2);
            let with_v = d.pi_fv(v_fv, carrier, after1);
            let with_w = d.pi_fv(w_fv, carrier, with_v);
            d.pi_fv(z_fv, carrier, with_w)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.equiv_trans,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `ofReal`, `zero`, `one`, `I`.
fn declare_constants(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let real = creal_ty(d, p);
    let carrier = complex_ty(d, p);

    // ofReal r := mk r CReal.zero
    {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let zero = czero(d, creal);
        let constructor = d.kernel().const_(p.mk, vec![]);
        let body = d.apply(constructor, &[r, zero]);
        let value = d.lam_fv(r_fv, real, body);
        let ty = d.arrow(real, carrier);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.of_real,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 1),
        })?;
    }

    let constant = |d: &mut IntDev<'_>, name: NameId, real_part: ExprId, imag_part: ExprId| {
        let constructor = d.kernel().const_(p.mk, vec![]);
        let value = d.apply(constructor, &[real_part, imag_part]);
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty: carrier,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 2),
        })
    };
    let zero = czero(d, creal);
    let one = cone(d, creal);
    constant(d, p.zero, zero, zero)?;
    constant(d, p.one, one, zero)?;
    constant(d, p.i, zero, one)
}

/// `add`, `neg`, `mul`, `conj`, `normSq`.
fn declare_operations(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);

    let binary =
        |d: &mut IntDev<'_>,
         name: NameId,
         combine: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId, ExprId, ExprId) -> (ExprId, ExprId)|
         -> Result<(), KernelError> {
            let z_fv = d.fresh_fvar();
            let z = d.kernel().fvar(z_fv);
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let a = re_of(d, p, z);
            let b = im_of(d, p, z);
            let c = re_of(d, p, w);
            let e = im_of(d, p, w);
            let (real_part, imag_part) = combine(d, a, b, c, e);
            let constructor = d.kernel().const_(p.mk, vec![]);
            let body = d.apply(constructor, &[real_part, imag_part]);
            let value = {
                let with_w = d.lam_fv(w_fv, carrier, body);
                d.lam_fv(z_fv, carrier, with_w)
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
                hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 3),
            })
        };

    binary(d, p.add, &|d, a, b, c, e| {
        let real_part = cadd(d, creal, a, c);
        let imag_part = cadd(d, creal, b, e);
        (real_part, imag_part)
    })?;
    binary(d, p.mul, &|d, a, b, c, e| {
        let ac = cmul(d, creal, a, c);
        let be = cmul(d, creal, b, e);
        let negated = cneg(d, creal, be);
        let real_part = cadd(d, creal, ac, negated);
        let ae = cmul(d, creal, a, e);
        let bc = cmul(d, creal, b, c);
        let imag_part = cadd(d, creal, ae, bc);
        (real_part, imag_part)
    })?;

    let unary = |d: &mut IntDev<'_>,
                 name: NameId,
                 combine: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> (ExprId, ExprId)|
     -> Result<(), KernelError> {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let a = re_of(d, p, z);
        let b = im_of(d, p, z);
        let (real_part, imag_part) = combine(d, a, b);
        let constructor = d.kernel().const_(p.mk, vec![]);
        let body = d.apply(constructor, &[real_part, imag_part]);
        let value = d.lam_fv(z_fv, carrier, body);
        let ty = d.arrow(carrier, carrier);
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 3),
        })
    };
    unary(d, p.neg, &|d, a, b| {
        let real_part = cneg(d, creal, a);
        let imag_part = cneg(d, creal, b);
        (real_part, imag_part)
    })?;
    unary(d, p.conj, &|d, a, b| {
        let imag_part = cneg(d, creal, b);
        (a, imag_part)
    })?;

    // normSq z := re z * re z + im z * im z, valued in CReal.
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let a = re_of(d, p, z);
        let b = im_of(d, p, z);
        let aa = cmul(d, creal, a, a);
        let bb = cmul(d, creal, b, b);
        let body = cadd(d, creal, aa, bb);
        let value = d.lam_fv(z_fv, carrier, body);
        let ty = d.arrow(carrier, real);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.norm_sq,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 4),
        })?;
    }
    Ok(())
}

/// The four setoid congruence obligations: `add`, `neg`, `mul`, `conj`.
///
/// None of them needs the ring calculus — each component of the conclusion is
/// the corresponding `CReal` congruence applied to the hypotheses' components.
/// `mul` is the one that mixes: its real part needs `mul_congr` twice and
/// `neg_congr` once, under `add_congr`.
fn declare_congruences(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    // A binary congruence, from the four component proofs.
    let binary = |d: &mut IntDev<'_>,
                  name: NameId,
                  op: NameId,
                  components: &dyn Fn(
        &mut IntDev<'_>,
        [ExprId; 4],
        [ExprId; 4],
        [ExprId; 4],
    ) -> (ExprId, ExprId, ExprId, ExprId)|
     -> Result<(), KernelError> {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let z2_fv = d.fresh_fvar();
        let z2 = d.kernel().fvar(z2_fv);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let w2_fv = d.fresh_fvar();
        let w2 = d.kernel().fvar(w2_fv);
        let first_ty = zeq(d, p, z, z2);
        let second_ty = zeq(d, p, w, w2);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let (za, zb) = equiv_halves(d, p, z, z2, h1);
        let (wa, wb) = equiv_halves(d, p, w, w2, h2);
        let left_parts = [
            re_of(d, p, z),
            im_of(d, p, z),
            re_of(d, p, w),
            im_of(d, p, w),
        ];
        let right_parts = [
            re_of(d, p, z2),
            im_of(d, p, z2),
            re_of(d, p, w2),
            im_of(d, p, w2),
        ];
        let (real_claim, imag_claim, real_proof, imag_proof) =
            components(d, left_parts, right_parts, [za, zb, wa, wb]);
        let body = and_intro(d, p, real_claim, imag_claim, real_proof, imag_proof);
        let value = {
            let with2 = d.lam_fv(h2_fv, second_ty, body);
            let with1 = d.lam_fv(h1_fv, first_ty, with2);
            let with_w2 = d.lam_fv(w2_fv, carrier, with1);
            let with_w = d.lam_fv(w_fv, carrier, with_w2);
            let with_z2 = d.lam_fv(z2_fv, carrier, with_w);
            d.lam_fv(z_fv, carrier, with_z2)
        };
        let ty = {
            let left = d.const_app(op, &[z, w]);
            let right = d.const_app(op, &[z2, w2]);
            let conclusion = zeq(d, p, left, right);
            let after2 = d.arrow(second_ty, conclusion);
            let after1 = d.arrow(first_ty, after2);
            let with_w2 = d.pi_fv(w2_fv, carrier, after1);
            let with_w = d.pi_fv(w_fv, carrier, with_w2);
            let with_z2 = d.pi_fv(z2_fv, carrier, with_w);
            d.pi_fv(z_fv, carrier, with_z2)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
    };

    binary(d, p.add_congr, p.add, &|d, l, r, h| {
        let [a, b, c, e] = l;
        let [a2, b2, c2, e2] = r;
        let [ha, hb, hc, he] = h;
        let real_left = cadd(d, creal, a, c);
        let real_right = cadd(d, creal, a2, c2);
        let imag_left = cadd(d, creal, b, e);
        let imag_right = cadd(d, creal, b2, e2);
        let real_claim = ceq(d, creal, real_left, real_right);
        let imag_claim = ceq(d, creal, imag_left, imag_right);
        let real_proof = d.lemma(creal.add_congr, &[a, a2, c, c2, ha, hc]);
        let imag_proof = d.lemma(creal.add_congr, &[b, b2, e, e2, hb, he]);
        (real_claim, imag_claim, real_proof, imag_proof)
    })?;

    binary(d, p.mul_congr, p.mul, &|d, l, r, h| {
        let [a, b, c, e] = l;
        let [a2, b2, c2, e2] = r;
        let [ha, hb, hc, he] = h;
        // real: a·c + −(b·e)
        let ac = cmul(d, creal, a, c);
        let be = cmul(d, creal, b, e);
        let nbe = cneg(d, creal, be);
        let real_left = cadd(d, creal, ac, nbe);
        let ac2 = cmul(d, creal, a2, c2);
        let be2 = cmul(d, creal, b2, e2);
        let nbe2 = cneg(d, creal, be2);
        let real_right = cadd(d, creal, ac2, nbe2);
        let ac_proof = d.lemma(creal.mul_congr, &[a, a2, c, c2, ha, hc]);
        let be_proof = d.lemma(creal.mul_congr, &[b, b2, e, e2, hb, he]);
        let nbe_proof = d.lemma(creal.neg_congr, &[be, be2, be_proof]);
        let real_proof = d.lemma(creal.add_congr, &[ac, ac2, nbe, nbe2, ac_proof, nbe_proof]);
        // imag: a·e + b·c
        let ae = cmul(d, creal, a, e);
        let bc = cmul(d, creal, b, c);
        let imag_left = cadd(d, creal, ae, bc);
        let ae2 = cmul(d, creal, a2, e2);
        let bc2 = cmul(d, creal, b2, c2);
        let imag_right = cadd(d, creal, ae2, bc2);
        let ae_proof = d.lemma(creal.mul_congr, &[a, a2, e, e2, ha, he]);
        let bc_proof = d.lemma(creal.mul_congr, &[b, b2, c, c2, hb, hc]);
        let imag_proof = d.lemma(creal.add_congr, &[ae, ae2, bc, bc2, ae_proof, bc_proof]);
        let real_claim = ceq(d, creal, real_left, real_right);
        let imag_claim = ceq(d, creal, imag_left, imag_right);
        (real_claim, imag_claim, real_proof, imag_proof)
    })?;

    // The two unary congruences.
    let unary = |d: &mut IntDev<'_>,
                 name: NameId,
                 op: NameId,
                 negate_real: bool|
     -> Result<(), KernelError> {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let hypothesis = zeq(d, p, z, w);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let (first, second) = equiv_halves(d, p, z, w, h);
        let a = re_of(d, p, z);
        let b = im_of(d, p, z);
        let a2 = re_of(d, p, w);
        let b2 = im_of(d, p, w);
        let nb = cneg(d, creal, b);
        let nb2 = cneg(d, creal, b2);
        let imag_proof = d.lemma(creal.neg_congr, &[b, b2, second]);
        let imag_claim = ceq(d, creal, nb, nb2);
        let (real_claim, real_proof) = if negate_real {
            let na = cneg(d, creal, a);
            let na2 = cneg(d, creal, a2);
            let proof = d.lemma(creal.neg_congr, &[a, a2, first]);
            let claim = ceq(d, creal, na, na2);
            (claim, proof)
        } else {
            let claim = ceq(d, creal, a, a2);
            (claim, first)
        };
        let body = and_intro(d, p, real_claim, imag_claim, real_proof, imag_proof);
        let value = {
            let with_h = d.lam_fv(h_fv, hypothesis, body);
            let with_w = d.lam_fv(w_fv, carrier, with_h);
            d.lam_fv(z_fv, carrier, with_w)
        };
        let ty = {
            let left = d.const_app(op, &[z]);
            let right = d.const_app(op, &[w]);
            let conclusion = zeq(d, p, left, right);
            let inner = d.arrow(hypothesis, conclusion);
            let with_w = d.pi_fv(w_fv, carrier, inner);
            d.pi_fv(z_fv, carrier, with_w)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
    };
    unary(d, p.neg_congr, p.neg, true)?;
    unary(d, p.conj_congr, p.conj, false)
}

/// The nine commutative-ring laws, every one decided by the ring calculus.
fn declare_ring_laws(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);

    let law = |d: &mut IntDev<'_>,
               name: NameId,
               arity: usize,
               build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (CExpr, CExpr)|
     -> Result<(), KernelError> {
        let fvars: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvars.iter().map(|&f| d.kernel().fvar(f)).collect();
        let (lhs, rhs) = build(d, &vars);
        let body = ring_law_proof(d, p, &lhs, &rhs);
        let left = render_c(d, p, &lhs);
        let right = render_c(d, p, &rhs);
        let claim = zeq(d, p, left, right);
        let mut value = body;
        let mut ty = claim;
        for &f in fvars.iter().rev() {
            value = d.lam_fv(f, carrier, value);
            ty = d.pi_fv(f, carrier, ty);
        }
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
    };

    law(d, p.add_comm, 2, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        let w = CExpr::var(d, p, v[1]);
        (CExpr::add(z.clone(), w.clone()), CExpr::add(w, z))
    })?;
    law(d, p.add_assoc, 3, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        let w = CExpr::var(d, p, v[1]);
        let u = CExpr::var(d, p, v[2]);
        (
            CExpr::add(CExpr::add(z.clone(), w.clone()), u.clone()),
            CExpr::add(z, CExpr::add(w, u)),
        )
    })?;
    law(d, p.add_zero, 1, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        (CExpr::add(z.clone(), CExpr::Zero), z)
    })?;
    law(d, p.add_neg, 1, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        (CExpr::add(z.clone(), CExpr::neg(z)), CExpr::Zero)
    })?;
    law(d, p.mul_comm, 2, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        let w = CExpr::var(d, p, v[1]);
        (CExpr::mul(z.clone(), w.clone()), CExpr::mul(w, z))
    })?;
    law(d, p.mul_assoc, 3, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        let w = CExpr::var(d, p, v[1]);
        let u = CExpr::var(d, p, v[2]);
        (
            CExpr::mul(CExpr::mul(z.clone(), w.clone()), u.clone()),
            CExpr::mul(z, CExpr::mul(w, u)),
        )
    })?;
    law(d, p.mul_one, 1, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        (CExpr::mul(z.clone(), CExpr::One), z)
    })?;
    law(d, p.mul_zero, 1, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        (CExpr::mul(z, CExpr::Zero), CExpr::Zero)
    })?;
    law(d, p.left_distrib, 3, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        let w = CExpr::var(d, p, v[1]);
        let u = CExpr::var(d, p, v[2]);
        (
            CExpr::mul(z.clone(), CExpr::add(w.clone(), u.clone())),
            CExpr::add(CExpr::mul(z.clone(), w), CExpr::mul(z, u)),
        )
    })
}

/// The witnesses that pin the operations down, and the two that keep `Equiv`
/// from being the total relation.
fn declare_pinning(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let real = creal_ty(d, p);

    // ofReal_add and ofReal_mul: the embedding is a ring homomorphism.
    let embedding =
        |d: &mut IntDev<'_>, name: NameId, multiplicative: bool| -> Result<(), KernelError> {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let combined = if multiplicative {
                cmul(d, creal, a, b)
            } else {
                cadd(d, creal, a, b)
            };
            let left = CExpr::OfReal(RExpr::Atom(a), a);
            let right = CExpr::OfReal(RExpr::Atom(b), b);
            let lhs = if multiplicative {
                CExpr::mul(left, right)
            } else {
                CExpr::add(left, right)
            };
            let combined_expr = if multiplicative {
                RExpr::mul(RExpr::Atom(a), RExpr::Atom(b))
            } else {
                RExpr::add(RExpr::Atom(a), RExpr::Atom(b))
            };
            let rhs = CExpr::OfReal(combined_expr, combined);
            let body = ring_law_proof(d, p, &lhs, &rhs);
            let left_term = render_c(d, p, &lhs);
            let right_term = render_c(d, p, &rhs);
            let claim = zeq(d, p, left_term, right_term);
            let value = {
                let with_b = d.lam_fv(b_fv, real, body);
                d.lam_fv(a_fv, real, with_b)
            };
            let ty = {
                let with_b = d.pi_fv(b_fv, real, claim);
                d.pi_fv(a_fv, real, with_b)
            };
            d.kernel().add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty,
                value,
            })
        };
    embedding(d, p.of_real_add, false)?;
    embedding(d, p.of_real_mul, true)?;

    // I_sq : Equiv (mul I I) (neg one)
    {
        let lhs = CExpr::mul(CExpr::I, CExpr::I);
        let rhs = CExpr::neg(CExpr::One);
        let value = ring_law_proof(d, p, &lhs, &rhs);
        let left = render_c(d, p, &lhs);
        let right = render_c(d, p, &rhs);
        let ty = zeq(d, p, left, right);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.i_sq,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // The two discrimination witnesses, each a projection of CReal's.
    let discriminate = |d: &mut IntDev<'_>,
                        name: NameId,
                        other: NameId,
                        real_half: bool|
     -> Result<(), KernelError> {
        let zero = d.kernel().const_(p.zero, vec![]);
        let target = d.kernel().const_(other, vec![]);
        let hypothesis = zeq(d, p, zero, target);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let (first, second) = equiv_halves(d, p, zero, target, h);
        let chosen = if real_half { first } else { second };
        let refutation = d.kernel().const_(creal.not_zero_one, vec![]);
        let body = d.kernel().app(refutation, chosen);
        let value = d.lam_fv(h_fv, hypothesis, body);
        let ty = d.not(hypothesis);
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
    };
    discriminate(d, p.not_zero_one, p.one, true)?;
    discriminate(d, p.not_zero_i, p.i, false)
}

/// `mul_conj` and `normSq_nonneg`: the norm, and where it lands.
fn declare_norm(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    // mul_conj : Equiv (mul z (conj z)) (ofReal (normSq z))
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let var = CExpr::var(d, p, z);
        let a = re_of(d, p, z);
        let b = im_of(d, p, z);
        let norm = d.const_app(p.norm_sq, &[z]);
        let lhs = CExpr::mul(var.clone(), CExpr::conj(var));
        let unfolded = RExpr::add(
            RExpr::mul(RExpr::Atom(a), RExpr::Atom(a)),
            RExpr::mul(RExpr::Atom(b), RExpr::Atom(b)),
        );
        let rhs = CExpr::OfReal(unfolded, norm);
        let body = ring_law_proof(d, p, &lhs, &rhs);
        let left = render_c(d, p, &lhs);
        let right = render_c(d, p, &rhs);
        let claim = zeq(d, p, left, right);
        let value = d.lam_fv(z_fv, carrier, body);
        let ty = d.pi_fv(z_fv, carrier, claim);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.mul_conj,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // normSq_nonneg : CReal.le CReal.zero (normSq z)
    //
    // `sq_nonneg` twice, `add_le_add` once, and one `le_congr` to read
    // `0 + 0` as `0` -- ADR-0468's order laws, used verbatim.
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let a = re_of(d, p, z);
        let b = im_of(d, p, z);
        let zero = czero(d, creal);
        let aa = cmul(d, creal, a, a);
        let bb = cmul(d, creal, b, b);
        let sum = cadd(d, creal, aa, bb);
        let first = d.lemma(creal.sq_nonneg, &[a]);
        let second = d.lemma(creal.sq_nonneg, &[b]);
        let combined = d.lemma(creal.add_le_add, &[zero, aa, zero, bb, first, second]);
        let padded = cadd(d, creal, zero, zero);
        let collapse = d.lemma(creal.add_zero, &[zero]);
        let sum_refl = crefl(d, creal, sum);
        let body = d.lemma(
            creal.le_congr,
            &[padded, zero, sum, sum, collapse, sum_refl, combined],
        );
        let value = d.lam_fv(z_fv, carrier, body);
        let ty = {
            let norm = d.const_app(p.norm_sq, &[z]);
            let claim = d.const_app(creal.le, &[zero, norm]);
            d.pi_fv(z_fv, carrier, claim)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.norm_sq_nonneg,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// **ℂ admits no ordered-ring structure**, proved rather than asserted.
///
/// The statement quantifies over the two relations, so it refutes *every*
/// candidate order at once rather than the one this module might have picked.
/// Seven of the `Real` package's 13 order laws are enough; `I` is the witness.
fn declare_no_order(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let prop = d.kernel().sort_zero();
    let relation = {
        let inner = d.arrow(carrier, prop);
        d.arrow(carrier, inner)
    };

    let le_fv = d.fresh_fvar();
    let le = d.kernel().fvar(le_fv);
    let lt_fv = d.fresh_fvar();
    let lt = d.kernel().fvar(lt_fv);
    let rel = |d: &mut IntDev<'_>, r: ExprId, a: ExprId, b: ExprId| d.apply(r, &[a, b]);

    // The seven hypotheses, in the `Real` package's own shapes.
    let le_refl_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let claim = rel(d, le, x, x);
        d.pi_fv(x_fv, carrier, claim)
    };
    let lt_irrefl_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let claim = rel(d, lt, x, x);
        let negated = d.not(claim);
        d.pi_fv(x_fv, carrier, negated)
    };
    let lt_of_le_of_lt_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let first = rel(d, le, x, y);
        let second = rel(d, lt, y, z);
        let conclusion = rel(d, lt, x, z);
        let after2 = d.arrow(second, conclusion);
        let after1 = d.arrow(first, after2);
        let with_z = d.pi_fv(z_fv, carrier, after1);
        let with_y = d.pi_fv(y_fv, carrier, with_z);
        d.pi_fv(x_fv, carrier, with_y)
    };
    let add_le_add_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let x2_fv = d.fresh_fvar();
        let x2 = d.kernel().fvar(x2_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let y2_fv = d.fresh_fvar();
        let y2 = d.kernel().fvar(y2_fv);
        let first = rel(d, le, x, x2);
        let second = rel(d, le, y, y2);
        let left = d.const_app(p.add, &[x, y]);
        let right = d.const_app(p.add, &[x2, y2]);
        let conclusion = rel(d, le, left, right);
        let after2 = d.arrow(second, conclusion);
        let after1 = d.arrow(first, after2);
        let with_y2 = d.pi_fv(y2_fv, carrier, after1);
        let with_y = d.pi_fv(y_fv, carrier, with_y2);
        let with_x2 = d.pi_fv(x2_fv, carrier, with_y);
        d.pi_fv(x_fv, carrier, with_x2)
    };
    let le_congr_ty = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let first = zeq(d, p, a, b);
        let second = zeq(d, p, c, e);
        let third = rel(d, le, a, c);
        let conclusion = rel(d, le, b, e);
        let after3 = d.arrow(third, conclusion);
        let after2 = d.arrow(second, after3);
        let after1 = d.arrow(first, after2);
        let with_e = d.pi_fv(e_fv, carrier, after1);
        let with_c = d.pi_fv(c_fv, carrier, with_e);
        let with_b = d.pi_fv(b_fv, carrier, with_c);
        d.pi_fv(a_fv, carrier, with_b)
    };
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);
    let sq_nonneg_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let square = d.const_app(p.mul, &[x, x]);
        let claim = rel(d, le, zero, square);
        d.pi_fv(x_fv, carrier, claim)
    };
    let zero_lt_one_ty = rel(d, lt, zero, one);

    // The proof, as the seven hypotheses arrive.
    let h_refl_fv = d.fresh_fvar();
    let h_refl = d.kernel().fvar(h_refl_fv);
    let h_irrefl_fv = d.fresh_fvar();
    let h_irrefl = d.kernel().fvar(h_irrefl_fv);
    let h_mixed_fv = d.fresh_fvar();
    let h_mixed = d.kernel().fvar(h_mixed_fv);
    let h_add_fv = d.fresh_fvar();
    let h_add = d.kernel().fvar(h_add_fv);
    let h_congr_fv = d.fresh_fvar();
    let h_congr = d.kernel().fvar(h_congr_fv);
    let h_sq_fv = d.fresh_fvar();
    let h_sq = d.kernel().fvar(h_sq_fv);
    let h_one_fv = d.fresh_fvar();
    let h_one = d.kernel().fvar(h_one_fv);

    let imaginary = d.kernel().const_(p.i, vec![]);
    let square = d.const_app(p.mul, &[imaginary, imaginary]);
    let negated_one = d.const_app(p.neg, &[one]);

    // 0 ≤ I·I, and I·I ~ −1, so 0 ≤ −1.
    let square_nonneg = d.apply(h_sq, &[imaginary]);
    let zero_refl = d.lemma(p.equiv_refl, &[zero]);
    let i_sq = d.kernel().const_(p.i_sq, vec![]);
    let neg_one_nonneg = d.apply(
        h_congr,
        &[
            zero,
            zero,
            square,
            negated_one,
            zero_refl,
            i_sq,
            square_nonneg,
        ],
    );

    // 1 + 0 ≤ 1 + (−1), i.e. 1 ≤ 0.
    let one_refl = d.apply(h_refl, &[one]);
    let padded = d.apply(
        h_add,
        &[one, one, zero, negated_one, one_refl, neg_one_nonneg],
    );
    let left_sum = d.const_app(p.add, &[one, zero]);
    let right_sum = d.const_app(p.add, &[one, negated_one]);
    let trim_left = d.lemma(p.add_zero, &[one]);
    let trim_right = d.lemma(p.add_neg, &[one]);
    let one_le_zero = d.apply(
        h_congr,
        &[
            left_sum, one, right_sum, zero, trim_left, trim_right, padded,
        ],
    );

    // 1 ≤ 0 and 0 < 1 give 1 < 1, which `lt_irrefl` refuses.
    let one_lt_one = d.apply(h_mixed, &[one, zero, one, one_le_zero, h_one]);
    let body = d.apply(h_irrefl, &[one, one_lt_one]);

    let value = {
        let mut acc = body;
        acc = d.lam_fv(h_one_fv, zero_lt_one_ty, acc);
        acc = d.lam_fv(h_sq_fv, sq_nonneg_ty, acc);
        acc = d.lam_fv(h_congr_fv, le_congr_ty, acc);
        acc = d.lam_fv(h_add_fv, add_le_add_ty, acc);
        acc = d.lam_fv(h_mixed_fv, lt_of_le_of_lt_ty, acc);
        acc = d.lam_fv(h_irrefl_fv, lt_irrefl_ty, acc);
        acc = d.lam_fv(h_refl_fv, le_refl_ty, acc);
        acc = d.lam_fv(lt_fv, relation, acc);
        d.lam_fv(le_fv, relation, acc)
    };
    let ty = {
        let false_ty = d.false_ty();
        let mut acc = false_ty;
        acc = d.arrow(zero_lt_one_ty, acc);
        acc = d.arrow(sq_nonneg_ty, acc);
        acc = d.arrow(le_congr_ty, acc);
        acc = d.arrow(add_le_add_ty, acc);
        acc = d.arrow(lt_of_le_of_lt_ty, acc);
        acc = d.arrow(lt_irrefl_ty, acc);
        acc = d.arrow(le_refl_ty, acc);
        acc = d.pi_fv(lt_fv, relation, acc);
        d.pi_fv(le_fv, relation, acc)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.no_compatible_order,
        uparams: vec![],
        ty,
        value,
    })
}
