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
//! quadrilateral is a parallelogram iff its diagonals bisect each other), but
//! it is **not** textually the ledger's `F:geometry-varignon-midpoint-parallelogram`
//! statement (`Q − P ~ R − S`, a vector difference).
//!
//! [`CPointPrelude::varignon_vector_parallel`] is that literal statement, and
//! it *is* what the fact now records (`proof_route: kernel-lean`,
//! `axiom_footprint: []`). The bridge the note above used to say was missing
//! is [`CPointPrelude::add_right_cancel`] — `CReal` uniqueness of the
//! additive inverse, phrased as right-cancellation (`x+z ~ y+z → x ~ y`),
//! proved from `add_zero`/`add_neg`/`add_assoc`/`add_congr` alone (seven
//! `equiv_trans` steps, no analysis, see [`declare_add_right_cancel`]).
//! [`sum_swap_proof`] is the one place it is consumed: given
//! `a+b ~ c+e` it derives `c−a ~ b−e`, and applying that to
//! [`CPointPrelude::sum_of_midpoints_perm`]'s `P+R ~ Q+S` (the
//! single-`inv2`-level sibling of [`Self::midpoint_diag_core`]) yields
//! [`CPointPrelude::midpoint_vector_swap`]'s `Q−P ~ R−S` per coordinate,
//! which [`declare_varignon_vector`] packages at the `CPoint` level through
//! the new [`CPointPrelude::point_sub`].
//!
//! No hypothesis is taken anywhere in this file (both Varignon theorems hold
//! for every configuration of four points, degenerate or not), matching the
//! `cas-certificate` route's own certificate for this fact (the empty
//! generator list — see that fact's `notes`).
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
    /// `CReal.add_right_cancel : ∀ x y z, Equiv (add x z) (add y z) → Equiv x y`.
    ///
    /// The bridge lemma the module doc identified as missing: uniqueness of
    /// the additive inverse, phrased as right-cancellation. Declared under the
    /// `CReal` root (via [`CRealPrelude::creal`]) because it is a genuine fact
    /// about `CReal`, not about `CPoint` — but declared *here*, not in
    /// `creal.rs`, so this file stays additive (see the module doc): it does
    /// not touch `creal.rs`'s source, its struct, or its build pipeline, only
    /// interns one more child of a name that file already owns. Proved from
    /// `add_zero`/`add_neg`/`add_assoc`/`add_congr` alone — seven
    /// `equiv_trans` steps, no analysis, matching the style of
    /// [`Self::sum_perm`].
    pub add_right_cancel: NameId,
    /// `CPoint.Scalar.sum_of_midpoints_perm : ∀ a b c e,
    /// Equiv (add (midpoint a b) (midpoint c e))
    ///       (add (midpoint b c) (midpoint e a))`.
    ///
    /// The single-`inv2`-level sibling of [`Self::midpoint_diag_core`]: that
    /// theorem compares the midpoint of the two midpoint-sums (an extra
    /// `inv2` factor on each side that cancels), this one compares the sums
    /// themselves. It is what lets [`Self::midpoint_vector_swap`] avoid ever
    /// reconstructing the "multiply by two" argument
    /// [`Self::midpoint_self`] already paid for.
    pub sum_of_midpoints_perm: NameId,
    /// `CPoint.Scalar.midpoint_vector_swap : ∀ a b c e,
    /// Equiv (add (midpoint b c) (neg (midpoint a b)))
    ///       (add (midpoint c e) (neg (midpoint e a)))`.
    ///
    /// The per-coordinate content of the ledger's vector-difference Varignon
    /// (`Q − P ~ R − S`): [`Self::sum_of_midpoints_perm`] gives `P + R ~ Q + S`
    /// (writing `P,Q,R,S` for the midpoints of `ab,bc,ce,ea`), and this
    /// rearranges that sum identity into the difference identity via
    /// [`Self::add_right_cancel`] — the one place in this file the new
    /// cancellation lemma is actually used.
    pub midpoint_vector_swap: NameId,
    /// `CPoint.sub P Q := CPoint.mk (add (x P) (neg (x Q))) (add (y P) (neg (y Q)))`
    /// — vector subtraction of points, coordinatewise.
    pub point_sub: NameId,
    /// `CPoint.varignon_vector_parallel : ∀ A B C D,
    /// CPoint.Equiv (CPoint.sub (midpoint B C) (midpoint A B))
    ///              (CPoint.sub (midpoint C D) (midpoint D A))`.
    ///
    /// The **vector-difference** form of Varignon's theorem, matching
    /// `F:geometry-varignon-midpoint-parallelogram`'s literal formal statement
    /// (`Q − P ~ R − S`) rather than [`Self::varignon_diagonals_bisect`]'s
    /// midpoint-of-diagonals form. `CPoint.Equiv` unfolds to exactly the `And`
    /// of two `CReal.Equiv`s the fact's SMT-LIB `and` states, coordinate by
    /// coordinate. No hypothesis, axiom-footprint free.
    pub varignon_vector_parallel: NameId,
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
    declare_add_right_cancel(&mut d, p)?;
    declare_sum_of_midpoints_perm(&mut d, p)?;
    declare_midpoint_vector_swap(&mut d, p)?;
    declare_point_sub(&mut d, p)?;
    declare_varignon_vector(&mut d, p)?;
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
        add_right_cancel: kernel.name_str(creal.creal, "add_right_cancel"),
        sum_of_midpoints_perm: kernel.name_str(scalar, "sum_of_midpoints_perm"),
        midpoint_vector_swap: kernel.name_str(scalar, "midpoint_vector_swap"),
        point_sub: kernel.name_str(point, "sub"),
        varignon_vector_parallel: kernel.name_str(point, "varignon_vector_parallel"),
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

fn cneg(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId) -> ExprId {
    d.const_app(p.creal.neg, &[x])
}

fn czero(d: &mut IntDev<'_>, p: CPointPrelude) -> ExprId {
    d.kernel().const_(p.creal.zero, vec![])
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

/// Proof of `Equiv (add CReal.zero x) x`, from `add_comm` and `add_zero`
/// alone. Not declared as its own theorem — it is only ever used as an
/// intermediate step inside a larger proof term, the way `refl`/`symm` are.
fn zero_add_proof(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId) -> ExprId {
    let creal = p.creal;
    let zero = czero(d, p);
    let lhs = cadd(d, p, zero, x);
    let rhs = cadd(d, p, x, zero);
    let comm = d.lemma(creal.add_comm, &[zero, x]);
    let az = d.lemma(creal.add_zero, &[x]);
    chain(d, p, lhs, &[(rhs, comm), (x, az)])
}

/// Proof of `Equiv (add (neg x) x) CReal.zero`, from `add_comm` and `add_neg`.
fn neg_add_cancel_proof(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId) -> ExprId {
    let creal = p.creal;
    let nx = cneg(d, p, x);
    let lhs = cadd(d, p, nx, x);
    let rhs = cadd(d, p, x, nx);
    let zero = czero(d, p);
    let comm = d.lemma(creal.add_comm, &[nx, x]);
    let an = d.lemma(creal.add_neg, &[x]);
    chain(d, p, lhs, &[(rhs, comm), (zero, an)])
}

/// Given `h : Equiv (add a b) (add c e)`, builds a proof of
/// `Equiv (add c (neg a)) (add b (neg e))` — the abstract group rearrangement
/// `a + b ~ c + e  ⟹  c − a ~ b − e`. This is the one place
/// [`CPointPrelude::add_right_cancel`] is consumed: everything else here is
/// `add_comm`/`add_assoc`/`add_congr`, applied to cancel `a` and `e` out of
/// `(c + (-a)) + (a + e)` and `(b + (-e)) + (a + e)` down to `c + e` and
/// `a + b` respectively, then `add_right_cancel` strips the shared `a + e`.
fn sum_swap_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
    h: ExprId,
) -> ExprId {
    let creal = p.creal;
    let na = cneg(d, p, a);
    let ne = cneg(d, p, e);
    let big_x = cadd(d, p, c, na); // X = c + (-a)
    let big_y = cadd(d, p, b, ne); // Y = b + (-e)
    let big_z = cadd(d, p, a, e); // Z = a + e
    let ab = cadd(d, p, a, b);
    let ce = cadd(d, p, c, e);

    // X_reduce : Equiv (add X Z) ce
    let x_reduce = {
        let xz = cadd(d, p, big_x, big_z); // (c + -a) + (a + e)
        let inner1 = cadd(d, p, na, big_z); // -a + (a + e)
        let c_inner1 = cadd(d, p, c, inner1); // c + (-a + (a+e))
        let assoc1 = d.lemma(creal.add_assoc, &[c, na, big_z]); // Equiv(xz, c_inner1)

        let na_a = cadd(d, p, na, a); // -a + a
        let na_a_e = cadd(d, p, na_a, e); // (-a+a) + e
        let assoc2 = d.lemma(creal.add_assoc, &[na, a, e]); // Equiv(na_a_e, inner1)
        let step_inner1 = symm(d, p, na_a_e, inner1, assoc2); // Equiv(inner1, na_a_e)
        let cancel_a = neg_add_cancel_proof(d, p, a); // Equiv(na_a, zero)
        let zero = czero(d, p);
        let zero_e = cadd(d, p, zero, e);
        let refl_e = refl(d, p, e);
        let congr_a = d.lemma(creal.add_congr, &[na_a, zero, e, e, cancel_a, refl_e]); // Equiv(na_a_e, zero_e)
        let za = zero_add_proof(d, p, e); // Equiv(zero_e, e)
        let inner1_reduce = chain(
            d,
            p,
            inner1,
            &[(na_a_e, step_inner1), (zero_e, congr_a), (e, za)],
        );

        let refl_c = refl(d, p, c);
        let congr_c = d.lemma(creal.add_congr, &[c, c, inner1, e, refl_c, inner1_reduce]); // Equiv(c_inner1, ce)
        chain(d, p, xz, &[(c_inner1, assoc1), (ce, congr_c)])
    };

    // Y_reduce : Equiv (add Y Z) ab
    let y_reduce = {
        let yz = cadd(d, p, big_y, big_z); // (b + -e) + (a + e)
        let inner2 = cadd(d, p, ne, big_z); // -e + (a + e)
        let b_inner2 = cadd(d, p, b, inner2); // b + (-e + (a+e))
        let assoc3 = d.lemma(creal.add_assoc, &[b, ne, big_z]); // Equiv(yz, b_inner2)

        let ea = cadd(d, p, e, a); // e + a
        let comm_ae = d.lemma(creal.add_comm, &[a, e]); // Equiv(a+e, e+a) = Equiv(big_z, ea)
        let ne_ea = cadd(d, p, ne, ea); // -e + (e+a)
        let refl_ne = refl(d, p, ne);
        let congr_ne = d.lemma(creal.add_congr, &[ne, ne, big_z, ea, refl_ne, comm_ae]); // Equiv(inner2, ne_ea)

        let ne_e = cadd(d, p, ne, e); // -e + e
        let ne_e_a = cadd(d, p, ne_e, a); // (-e+e) + a
        let assoc4 = d.lemma(creal.add_assoc, &[ne, e, a]); // Equiv(ne_e_a, ne_ea)
        let step_ne_ea = symm(d, p, ne_e_a, ne_ea, assoc4); // Equiv(ne_ea, ne_e_a)

        let cancel_e = neg_add_cancel_proof(d, p, e); // Equiv(ne_e, zero)
        let zero = czero(d, p);
        let zero_a = cadd(d, p, zero, a);
        let refl_a = refl(d, p, a);
        let congr_ne2 = d.lemma(creal.add_congr, &[ne_e, zero, a, a, cancel_e, refl_a]); // Equiv(ne_e_a, zero_a)
        let za2 = zero_add_proof(d, p, a); // Equiv(zero_a, a)
        let inner2_reduce = chain(
            d,
            p,
            inner2,
            &[
                (ne_ea, congr_ne),
                (ne_e_a, step_ne_ea),
                (zero_a, congr_ne2),
                (a, za2),
            ],
        );

        let ba = cadd(d, p, b, a); // b + a
        let refl_b = refl(d, p, b);
        let congr_b = d.lemma(creal.add_congr, &[b, b, inner2, a, refl_b, inner2_reduce]); // Equiv(b_inner2, ba)
        let comm_ba = d.lemma(creal.add_comm, &[b, a]); // Equiv(ba, ab)
        chain(
            d,
            p,
            yz,
            &[(b_inner2, assoc3), (ba, congr_b), (ab, comm_ba)],
        )
    };

    let symm_h = symm(d, p, ab, ce, h); // Equiv(ce, ab)
    let big_xz = cadd(d, p, big_x, big_z);
    let big_yz = cadd(d, p, big_y, big_z);
    let symm_y = symm(d, p, big_yz, ab, y_reduce); // Equiv(ab, big_yz)
    let combined = chain(
        d,
        p,
        big_xz,
        &[(ce, x_reduce), (ab, symm_h), (big_yz, symm_y)],
    );
    d.lemma(p.add_right_cancel, &[big_x, big_y, big_z, combined])
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

/// `CReal.add_right_cancel : ∀ x y z, Equiv (add x z) (add y z) → Equiv x y`.
///
/// `x ~ x+0 ~ x+(z+-z) ~ (x+z)+-z ~ (y+z)+-z ~ y+(z+-z) ~ y+0 ~ y`, seven
/// `equiv_trans` steps built from `add_zero`, `add_neg`, `add_assoc` and
/// `add_congr` alone.
fn declare_add_right_cancel(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = creal_ty(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let xz = cadd(d, p, x, z);
    let yz = cadd(d, p, y, z);
    let hyp_ty = equiv(d, p, xz, yz);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let nz = cneg(d, p, z);
    let zero = czero(d, p);

    let x_zero = cadd(d, p, x, zero); // x + 0
    let az_x = d.lemma(creal.add_zero, &[x]); // Equiv(x_zero, x)
    let step_a = symm(d, p, x_zero, x, az_x); // Equiv(x, x_zero)

    let z_negz = cadd(d, p, z, nz); // z + -z
    let x_z_negz = cadd(d, p, x, z_negz); // x + (z + -z)
    let refl_x = refl(d, p, x);
    let an_z0 = d.lemma(creal.add_neg, &[z]); // Equiv(z_negz, zero)
    let symm_an_z = symm(d, p, z_negz, zero, an_z0); // Equiv(zero, z_negz)
    let step_b = d.lemma(creal.add_congr, &[x, x, zero, z_negz, refl_x, symm_an_z]); // Equiv(x_zero, x_z_negz)

    let xz_negz = cadd(d, p, xz, nz); // (x+z) + -z
    let assoc_x = d.lemma(creal.add_assoc, &[x, z, nz]); // Equiv(xz_negz, x_z_negz)
    let step_c = symm(d, p, xz_negz, x_z_negz, assoc_x); // Equiv(x_z_negz, xz_negz)

    let yz_negz = cadd(d, p, yz, nz); // (y+z) + -z
    let refl_nz = refl(d, p, nz);
    let step_d = d.lemma(creal.add_congr, &[xz, yz, nz, nz, h, refl_nz]); // Equiv(xz_negz, yz_negz)

    let y_z_negz = cadd(d, p, y, z_negz); // y + (z + -z)
    let step_e = d.lemma(creal.add_assoc, &[y, z, nz]); // Equiv(yz_negz, y_z_negz)

    let y_zero = cadd(d, p, y, zero); // y + 0
    let refl_y = refl(d, p, y);
    let an_z = d.lemma(creal.add_neg, &[z]); // Equiv(z_negz, zero)
    let step_f = d.lemma(creal.add_congr, &[y, y, z_negz, zero, refl_y, an_z]); // Equiv(y_z_negz, y_zero)

    let step_g = d.lemma(creal.add_zero, &[y]); // Equiv(y_zero, y)

    let proof = chain(
        d,
        p,
        x,
        &[
            (x_zero, step_a),
            (x_z_negz, step_b),
            (xz_negz, step_c),
            (yz_negz, step_d),
            (y_z_negz, step_e),
            (y_zero, step_f),
            (y, step_g),
        ],
    );

    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        let with_z = d.lam_fv(z_fv, carrier, with_h);
        let with_y = d.lam_fv(y_fv, carrier, with_z);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = equiv(d, p, x, y);
        let after_hyp = d.arrow(hyp_ty, conclusion);
        let with_z = d.pi_fv(z_fv, carrier, after_hyp);
        let with_y = d.pi_fv(y_fv, carrier, with_z);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.add_right_cancel,
        uparams: vec![],
        ty,
        value,
    })
}

/// `sum_of_midpoints_perm : ∀ a b c e,
/// Equiv (add (midpoint a b) (midpoint c e)) (add (midpoint b c) (midpoint e a))`.
///
/// The single-`inv2`-level analogue of [`declare_midpoint_diag_core`]: reuses
/// [`CPointPrelude::sum_perm`] directly (no need to redo the permutation
/// argument) and `left_distrib` once on each side instead of twice.
fn declare_sum_of_midpoints_perm(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
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
    let s = cadd(d, p, ab, ce); // s = (a+b)+(c+e)
    let bc = cadd(d, p, b, c);
    let ea = cadd(d, p, e, a);
    let t = cadd(d, p, bc, ea); // t = (b+c)+(e+a)

    let m1 = midpoint(d, p, a, b);
    let m2 = midpoint(d, p, c, e);
    let lhs = cadd(d, p, m1, m2);
    let n1 = midpoint(d, p, b, c);
    let n2 = midpoint(d, p, e, a);
    let rhs = cadd(d, p, n1, n2);

    let mul_inv2_s = cmul(d, p, inv2, s);
    let ld_s = d.lemma(creal.left_distrib, &[inv2, ab, ce]); // Equiv(mul_inv2_s, lhs)
    let lhs_reduce = symm(d, p, mul_inv2_s, lhs, ld_s); // Equiv(lhs, mul_inv2_s)

    let mul_inv2_t = cmul(d, p, inv2, t);
    let ld_t = d.lemma(creal.left_distrib, &[inv2, bc, ea]); // Equiv(mul_inv2_t, rhs)

    let sp = d.lemma(p.sum_perm, &[a, b, c, e]); // Equiv(s, t)
    let refl_inv2 = refl(d, p, inv2);
    let inner_congr = d.lemma(creal.mul_congr, &[inv2, inv2, s, t, refl_inv2, sp]); // Equiv(mul_inv2_s, mul_inv2_t)

    let proof = chain(
        d,
        p,
        lhs,
        &[
            (mul_inv2_s, lhs_reduce),
            (mul_inv2_t, inner_congr),
            (rhs, ld_t),
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
        name: p.sum_of_midpoints_perm,
        uparams: vec![],
        ty,
        value,
    })
}

/// `midpoint_vector_swap : ∀ a b c e,
/// Equiv (add (midpoint b c) (neg (midpoint a b)))
///       (add (midpoint c e) (neg (midpoint e a)))`.
///
/// [`declare_sum_of_midpoints_perm`] gives `P + R ~ Q + S` (writing
/// `P,Q,R,S` for the midpoints of `ab,bc,ce,ea`); [`sum_swap_proof`] turns
/// that into `Q − P ~ R − S`, consuming [`CPointPrelude::add_right_cancel`].
fn declare_midpoint_vector_swap(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let big_p = midpoint(d, p, a, b);
    let big_r = midpoint(d, p, c, e);
    let big_q = midpoint(d, p, b, c);
    let big_s = midpoint(d, p, e, a);

    let h = d.lemma(p.sum_of_midpoints_perm, &[a, b, c, e]); // Equiv(add P R, add Q S)
    let proof = sum_swap_proof(d, p, big_p, big_r, big_q, big_s, h); // Equiv(add Q (neg P), add R (neg S))

    let neg_big_p = cneg(d, p, big_p);
    let lhs = cadd(d, p, big_q, neg_big_p);
    let neg_big_s = cneg(d, p, big_s);
    let rhs = cadd(d, p, big_r, neg_big_s);
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
        name: p.midpoint_vector_swap,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CPoint.sub P Q := CPoint.mk (add (x P) (neg (x Q))) (add (y P) (neg (y Q)))`.
fn declare_point_sub(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let neg_bx = cneg(d, p, bx);
    let dx = cadd(d, p, ax, neg_bx);
    let neg_by = cneg(d, p, by);
    let dy = cadd(d, p, ay, neg_by);
    let value_body = d.const_app(p.mk, &[dx, dy]);

    let value = {
        let inner = d.lam_fv(pb_fv, point, value_body);
        d.lam_fv(pa_fv, point, inner)
    };
    let ty = {
        let inner = d.arrow(point, point);
        d.arrow(point, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.point_sub,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 4),
    })
}

/// `varignon_vector_parallel : ∀ A B C D,
/// CPoint.Equiv (CPoint.sub (midpoint B C) (midpoint A B))
///              (CPoint.sub (midpoint C D) (midpoint D A))`.
///
/// The ledger's literal `Q − P ~ R − S`. Packages
/// [`declare_midpoint_vector_swap`] at both coordinates via `And.intro`,
/// exactly the way [`declare_varignon`] packages [`declare_midpoint_diag_core`].
fn declare_varignon_vector(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
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

    let core_x = d.lemma(p.midpoint_vector_swap, &[ax, bx, cx, dx]);
    let core_y = d.lemma(p.midpoint_vector_swap, &[ay, by, cy, dy]);

    let claim_x = {
        let q_x = midpoint(d, p, bx, cx);
        let p_x = midpoint(d, p, ax, bx);
        let r_x = midpoint(d, p, cx, dx);
        let s_x = midpoint(d, p, dx, ax);
        let neg_p_x = cneg(d, p, p_x);
        let left_x = cadd(d, p, q_x, neg_p_x);
        let neg_s_x = cneg(d, p, s_x);
        let right_x = cadd(d, p, r_x, neg_s_x);
        equiv(d, p, left_x, right_x)
    };
    let claim_y = {
        let q_y = midpoint(d, p, by, cy);
        let p_y = midpoint(d, p, ay, by);
        let r_y = midpoint(d, p, cy, dy);
        let s_y = midpoint(d, p, dy, ay);
        let neg_p_y = cneg(d, p, p_y);
        let left_y = cadd(d, p, q_y, neg_p_y);
        let neg_s_y = cneg(d, p, s_y);
        let right_y = cadd(d, p, r_y, neg_s_y);
        equiv(d, p, left_y, right_y)
    };
    let proof = and_intro(d, p, claim_x, claim_y, core_x, core_y);

    let pmbc = d.const_app(p.point_midpoint, &[pb, pc]);
    let pmab = d.const_app(p.point_midpoint, &[pa, pb]);
    let left = d.const_app(p.point_sub, &[pmbc, pmab]);
    let pmcd = d.const_app(p.point_midpoint, &[pc, pd]);
    let pmda = d.const_app(p.point_midpoint, &[pd, pa]);
    let right = d.const_app(p.point_sub, &[pmcd, pmda]);
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
        name: p.varignon_vector_parallel,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod creal_point_tests;
