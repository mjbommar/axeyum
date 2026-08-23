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
    /// `CPoint.add P Q := CPoint.mk (add (x P) (x Q)) (add (y P) (y Q))` —
    /// coordinatewise point addition, the sibling [`Self::point_sub`] never
    /// needed until now: `declare_thales`'s telescoping identity
    /// `A - C ~ (A - O) + (O - C)` is stated with a genuine point-level `+`.
    pub point_add: NameId,
    /// `CPoint.neg P := CPoint.mk (neg (x P)) (neg (y P))`.
    pub point_neg: NameId,
    /// `CPoint.dot P Q := CReal.add (CReal.mul (x P) (x Q)) (CReal.mul (y P) (y Q))`
    /// — the inner product Pythagoras and Thales are both stated over.
    pub dot: NameId,
    /// `CPoint.dot_congr : ∀ P P' Q Q', CPoint.Equiv P P' → CPoint.Equiv Q Q' →
    /// Equiv (dot P Q) (dot P' Q')` — the setoid obligation `dot` needs before
    /// any point-level rewriting under it is legal (used to transport along
    /// the diff-of-diffs and telescoping identities below).
    pub dot_congr: NameId,
    /// `CPoint.dot_comm : ∀ P Q, Equiv (dot P Q) (dot Q P)`.
    pub dot_comm: NameId,
    /// `CPoint.dot_add_left : ∀ P Q R,
    /// Equiv (dot (add P Q) R) (add (dot P R) (dot Q R))`.
    pub dot_add_left: NameId,
    /// `CPoint.dot_add_right : ∀ P Q R,
    /// Equiv (dot P (add Q R)) (add (dot P Q) (dot P R))`.
    pub dot_add_right: NameId,
    /// `CPoint.dot_sub_left : ∀ P Q R,
    /// Equiv (dot (sub P Q) R) (add (dot P R) (neg (dot Q R)))`.
    ///
    /// `declare_pythagoras` is built from: with `U := sub A C`, `V := sub B C`,
    /// `W := sub U V`, this expands `dot W W` twice (once per slot) into
    /// `dot U U`/`dot V V`/`dot U V` terms, and the hypothesis `dot U V ~ 0`
    /// kills the cross terms.
    pub dot_sub_left: NameId,
    /// `CPoint.dot_sub_right : ∀ P Q R,
    /// Equiv (dot P (sub Q R)) (add (dot P Q) (neg (dot P R)))`.
    pub dot_sub_right: NameId,
    /// `CPoint.dot_neg_left : ∀ P Q, Equiv (dot (neg P) Q) (neg (dot P Q))`.
    pub dot_neg_left: NameId,
    /// **Elements I.47.** `∀ A B C, Equiv (dot (sub A C) (sub B C)) zero →
    /// Equiv (dot (sub A B) (sub A B))
    ///        (add (dot (sub A C) (sub A C)) (dot (sub B C) (sub B C)))`.
    ///
    /// The hypothesis `(A-C)·(B-C) ~ 0` *is* "the angle at `C` is right"; the
    /// conclusion *is* `|AB|² = |AC|² + |CB|²`. No square roots, no order, no
    /// non-degeneracy side condition — pure bilinearity of [`Self::dot`] plus
    /// the ring identity `A - B ~ (A - C) - (B - C)` (`diff_diff_scalar_proof`,
    /// applied per coordinate and packaged into a `CPoint.Equiv` transported
    /// through [`Self::dot_congr`]).
    pub pythagoras: NameId,
    /// **Elements III.31**, the converse direction. `∀ A B C O,
    /// CPoint.Equiv O (point_midpoint A B) →
    /// Equiv (dot (sub C O) (sub C O)) (dot (sub A O) (sub A O)) →
    /// Equiv (dot (sub A C) (sub B C)) zero`.
    ///
    /// If `C` lies on the circle with diameter `AB` (`O` its centre, so
    /// `|CO| = |AO|`, the circle's radius), the angle at `C` is right. Proved
    /// via the telescoping identities `A - C ~ (A-O) + (O-C)` and
    /// `B - C ~ neg (A-O) + (O-C)` — the second is where `O ~ midpoint A B`
    /// is actually consumed, through `2 · midpoint a b ~ a + b`
    /// (`double_midpoint_proof`) — then [`Self::dot_add_left`]/
    /// [`Self::dot_add_right`]/[`Self::dot_neg_left`] expand
    /// `dot ((A-O)+(O-C)) (neg(A-O)+(O-C))` into
    /// `dot(O-C,O-C) - dot(A-O,A-O)`, which the hypothesis makes zero.
    pub thales: NameId,
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
    declare_point_add(&mut d, p)?;
    declare_point_neg(&mut d, p)?;
    declare_dot(&mut d, p)?;
    declare_dot_congr(&mut d, p)?;
    declare_dot_comm(&mut d, p)?;
    declare_dot_add_left(&mut d, p)?;
    declare_dot_add_right(&mut d, p)?;
    declare_dot_sub_left(&mut d, p)?;
    declare_dot_sub_right(&mut d, p)?;
    declare_dot_neg_left(&mut d, p)?;
    declare_pythagoras(&mut d, p)?;
    declare_thales(&mut d, p)?;
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
        point_add: kernel.name_str(point, "add"),
        point_neg: kernel.name_str(point, "neg"),
        dot: kernel.name_str(point, "dot"),
        dot_congr: kernel.name_str(point, "dot_congr"),
        dot_comm: kernel.name_str(point, "dot_comm"),
        dot_add_left: kernel.name_str(point, "dot_add_left"),
        dot_add_right: kernel.name_str(point, "dot_add_right"),
        dot_sub_left: kernel.name_str(point, "dot_sub_left"),
        dot_sub_right: kernel.name_str(point, "dot_sub_right"),
        dot_neg_left: kernel.name_str(point, "dot_neg_left"),
        pythagoras: kernel.name_str(point, "pythagoras"),
        thales: kernel.name_str(point, "thales"),
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

/// `CPoint.sub P Q`.
fn psub(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.point_sub, &[x, y])
}

/// `CPoint.add P Q`.
fn padd(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.point_add, &[x, y])
}

/// `CPoint.neg P`.
fn pneg(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId) -> ExprId {
    d.const_app(p.point_neg, &[x])
}

/// `CPoint.dot P Q`.
fn dotp(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.dot, &[x, y])
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

// --- CReal ring toolkit ------------------------------------------------------
//
// Private proof-term builders, not separate kernel declarations: each is
// short, used only to assemble the `dot` family and the two headline
// theorems below, and gets fully re-checked by the kernel as part of
// whichever declaration consumes it — exactly like `zero_add_proof`/
// `neg_add_cancel_proof`/`sum_swap_proof` above. `add_left_cancel_proof` is
// the one new *pattern* (the mirror of `add_right_cancel`, needed because
// several identities below cancel a shared term on the left); everything
// else is an `add_comm`/`add_assoc`/`add_neg`/`left_distrib`/`mul_comm`
// chain in the same style.

/// Given `h : Equiv (add z x) (add z y)`, produce `Equiv x y` — the mirror of
/// [`CPointPrelude::add_right_cancel`] with the shared term on the left.
fn add_left_cancel_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    h: ExprId,
) -> ExprId {
    let creal = p.creal;
    let zx = cadd(d, p, z, x);
    let xz = cadd(d, p, x, z);
    let zy = cadd(d, p, z, y);
    let yz = cadd(d, p, y, z);
    let comm_zx = d.lemma(creal.add_comm, &[z, x]); // Equiv(zx, xz)
    let step1 = symm(d, p, zx, xz, comm_zx); // Equiv(xz, zx)
    let comm_zy = d.lemma(creal.add_comm, &[z, y]); // Equiv(zy, yz)
    let combined = chain(d, p, xz, &[(zx, step1), (zy, h), (yz, comm_zy)]);
    d.lemma(p.add_right_cancel, &[x, y, z, combined])
}

/// `Equiv (add (add x y) (neg y)) x` — "add `y` then subtract it cancels".
fn add_sub_cancel_right(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    let creal = p.creal;
    let ny = cneg(d, p, y);
    let xy = cadd(d, p, x, y);
    let xy_ny = cadd(d, p, xy, ny);
    let y_ny = cadd(d, p, y, ny);
    let x_y_ny = cadd(d, p, x, y_ny);
    let zero = czero(d, p);
    let x_zero = cadd(d, p, x, zero);
    let assoc = d.lemma(creal.add_assoc, &[x, y, ny]); // Equiv(xy_ny, x_y_ny)
    let an = d.lemma(creal.add_neg, &[y]); // Equiv(y_ny, zero)
    let refl_x = refl(d, p, x);
    let congr = d.lemma(creal.add_congr, &[x, x, y_ny, zero, refl_x, an]); // Equiv(x_y_ny, x_zero)
    let az = d.lemma(creal.add_zero, &[x]); // Equiv(x_zero, x)
    chain(d, p, xy_ny, &[(x_y_ny, assoc), (x_zero, congr), (x, az)])
}

/// `Equiv (add (add x y) (neg x)) y` — the mirror, cancelling the left addend.
fn add_sub_cancel_left(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    let creal = p.creal;
    let xy = cadd(d, p, x, y);
    let yx = cadd(d, p, y, x);
    let nx = cneg(d, p, x);
    let xy_nx = cadd(d, p, xy, nx);
    let yx_nx = cadd(d, p, yx, nx);
    let comm = d.lemma(creal.add_comm, &[x, y]); // Equiv(xy, yx)
    let refl_nx = refl(d, p, nx);
    let congr = d.lemma(creal.add_congr, &[xy, yx, nx, nx, comm, refl_nx]); // Equiv(xy_nx, yx_nx)
    let reduce = add_sub_cancel_right(d, p, y, x); // Equiv(yx_nx, y)
    chain(d, p, xy_nx, &[(yx_nx, congr), (y, reduce)])
}

/// `Equiv (neg zero) zero`.
fn neg_zero_proof(d: &mut IntDev<'_>, p: CPointPrelude) -> ExprId {
    let creal = p.creal;
    let zero = czero(d, p);
    let nz = cneg(d, p, zero);
    let zero_nz = cadd(d, p, zero, nz);
    let zero_zero = cadd(d, p, zero, zero);
    let an = d.lemma(creal.add_neg, &[zero]); // Equiv(zero_nz, zero)
    let az = d.lemma(creal.add_zero, &[zero]); // Equiv(zero_zero, zero)
    let az_symm = symm(d, p, zero_zero, zero, az); // Equiv(zero, zero_zero)
    let h = chain(d, p, zero_nz, &[(zero, an), (zero_zero, az_symm)]);
    add_left_cancel_proof(d, p, nz, zero, zero, h)
}

/// `Equiv (neg (neg x)) x`.
fn neg_neg_proof(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId) -> ExprId {
    let creal = p.creal;
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);
    let nnx_nx = cadd(d, p, nnx, nx);
    let x_nx = cadd(d, p, x, nx);
    let zero = czero(d, p);
    let cancel1 = neg_add_cancel_proof(d, p, nx); // Equiv(nnx_nx, zero)
    let cancel2 = d.lemma(creal.add_neg, &[x]); // Equiv(x_nx, zero)
    let cancel2_symm = symm(d, p, x_nx, zero, cancel2); // Equiv(zero, x_nx)
    let h = chain(d, p, nnx_nx, &[(zero, cancel1), (x_nx, cancel2_symm)]);
    // h : Equiv(add nnx nx, add x nx) — the shared term `nx` is on the RIGHT,
    // so this is `add_right_cancel`'s pattern, not `add_left_cancel_proof`'s.
    d.lemma(p.add_right_cancel, &[nnx, x, nx, h])
}

/// `Equiv (neg (add x y)) (add (neg x) (neg y))`.
fn neg_add_proof(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    let creal = p.creal;
    let zero = czero(d, p);
    let big_x = cadd(d, p, x, y); // X = x + y
    let nx = cneg(d, p, x);
    let ny = cneg(d, p, y);
    let big_y = cadd(d, p, nx, ny); // Y = -x + -y
    let n_big_x = cneg(d, p, big_x); // -X

    let xy_sum = cadd(d, p, big_x, big_y); // X + Y
    let x_nx = cadd(d, p, big_x, nx); // X + -x
    let lhs1 = cadd(d, p, x_nx, ny); // (X + -x) + -y
    let assoc = d.lemma(creal.add_assoc, &[big_x, nx, ny]); // Equiv(lhs1, xy_sum)
    let step_a = symm(d, p, lhs1, xy_sum, assoc); // Equiv(xy_sum, lhs1)
    let reduce1 = add_sub_cancel_left(d, p, x, y); // Equiv(X + -x, y)
    let y_ny = cadd(d, p, y, ny);
    let refl_ny = refl(d, p, ny);
    let congr_step = d.lemma(creal.add_congr, &[x_nx, y, ny, ny, reduce1, refl_ny]); // Equiv(lhs1, y_ny)
    let an_y = d.lemma(creal.add_neg, &[y]); // Equiv(y_ny, zero)
    let xy_sum_zero = chain(
        d,
        p,
        xy_sum,
        &[(lhs1, step_a), (y_ny, congr_step), (zero, an_y)],
    );

    let x_nbig_x = cadd(d, p, big_x, n_big_x); // X + -X
    let an_bigx = d.lemma(creal.add_neg, &[big_x]); // Equiv(x_nbig_x, zero)
    let xy_sum_zero_symm = symm(d, p, xy_sum, zero, xy_sum_zero); // Equiv(zero, xy_sum)
    let h = chain(
        d,
        p,
        x_nbig_x,
        &[(zero, an_bigx), (xy_sum, xy_sum_zero_symm)],
    );
    // h : Equiv(add X (-X))(add X Y)
    add_left_cancel_proof(d, p, n_big_x, big_y, big_x, h)
}

/// `Equiv (mul a (neg b)) (neg (mul a b))`.
fn mul_neg_right_proof(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    let creal = p.creal;
    let nb = cneg(d, p, b);
    let big_x = cmul(d, p, a, nb); // X = a * -b
    let m = cmul(d, p, a, b); // M = a * b
    let nb_b = cadd(d, p, nb, b); // -b + b
    let zero = czero(d, p);
    let cancel = neg_add_cancel_proof(d, p, b); // Equiv(nb_b, zero)
    let a_nbb = cmul(d, p, a, nb_b); // a * (-b + b)
    let xm_sum = cadd(d, p, big_x, m);
    let ld = d.lemma(creal.left_distrib, &[a, nb, b]); // Equiv(a_nbb, xm_sum)
    let a_zero = cmul(d, p, a, zero);
    let refl_a = refl(d, p, a);
    let congr = d.lemma(creal.mul_congr, &[a, a, nb_b, zero, refl_a, cancel]); // Equiv(a_nbb, a_zero)
    let mz = d.lemma(creal.mul_zero, &[a]); // Equiv(a_zero, zero)
    let ld_symm = symm(d, p, a_nbb, xm_sum, ld); // Equiv(xm_sum, a_nbb)
    let xm_zero = chain(
        d,
        p,
        xm_sum,
        &[(a_nbb, ld_symm), (a_zero, congr), (zero, mz)],
    );

    let nm = cneg(d, p, m);
    let nm_m = cadd(d, p, nm, m);
    let cancel_m = neg_add_cancel_proof(d, p, m); // Equiv(nm_m, zero)
    let cancel_m_symm = symm(d, p, nm_m, zero, cancel_m); // Equiv(zero, nm_m)
    let h = chain(d, p, xm_sum, &[(zero, xm_zero), (nm_m, cancel_m_symm)]);
    // h : Equiv(add X M)(add (neg M) M)
    d.lemma(p.add_right_cancel, &[big_x, nm, m, h])
}

/// `Equiv (mul (neg a) b) (neg (mul a b))`.
fn mul_neg_left_proof(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    let creal = p.creal;
    let na = cneg(d, p, a);
    let na_b = cmul(d, p, na, b);
    let b_na = cmul(d, p, b, na);
    let ba = cmul(d, p, b, a);
    let ab = cmul(d, p, a, b);
    let neg_ba = cneg(d, p, ba);
    let neg_ab = cneg(d, p, ab);
    let comm1 = d.lemma(creal.mul_comm, &[na, b]); // Equiv(na_b, b_na)
    let b_neg_a = mul_neg_right_proof(d, p, b, a); // Equiv(b_na, neg_ba)
    let comm2 = d.lemma(creal.mul_comm, &[b, a]); // Equiv(ba, ab)
    let neg_congr_ba_ab = d.lemma(creal.neg_congr, &[ba, ab, comm2]); // Equiv(neg_ba, neg_ab)
    chain(
        d,
        p,
        na_b,
        &[(b_na, comm1), (neg_ba, b_neg_a), (neg_ab, neg_congr_ba_ab)],
    )
}

/// `Equiv (mul (add a b) c) (add (mul a c) (mul b c))`.
fn right_distrib_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let creal = p.creal;
    let ab = cadd(d, p, a, b);
    let ab_c = cmul(d, p, ab, c);
    let c_ab = cmul(d, p, c, ab);
    let ca = cmul(d, p, c, a);
    let cb = cmul(d, p, c, b);
    let ca_cb = cadd(d, p, ca, cb);
    let ac = cmul(d, p, a, c);
    let bc = cmul(d, p, b, c);
    let ac_bc = cadd(d, p, ac, bc);
    let comm1 = d.lemma(creal.mul_comm, &[ab, c]); // Equiv(ab_c, c_ab)
    let ld = d.lemma(creal.left_distrib, &[c, a, b]); // Equiv(c_ab, ca_cb)
    let comm_ca = d.lemma(creal.mul_comm, &[c, a]); // Equiv(ca, ac)
    let comm_cb = d.lemma(creal.mul_comm, &[c, b]); // Equiv(cb, bc)
    let congr = d.lemma(creal.add_congr, &[ca, ac, cb, bc, comm_ca, comm_cb]); // Equiv(ca_cb, ac_bc)
    chain(d, p, ab_c, &[(c_ab, comm1), (ca_cb, ld), (ac_bc, congr)])
}

/// `Equiv (mul a (add b (neg c))) (add (mul a b) (neg (mul a c)))`.
fn mul_sub_right_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let creal = p.creal;
    let nc = cneg(d, p, c);
    let b_nc = cadd(d, p, b, nc);
    let a_b_nc = cmul(d, p, a, b_nc);
    let ab = cmul(d, p, a, b);
    let ac = cmul(d, p, a, c);
    let a_nc = cmul(d, p, a, nc);
    let ab_anc = cadd(d, p, ab, a_nc);
    let nac = cneg(d, p, ac);
    let ab_nac = cadd(d, p, ab, nac);
    let ld = d.lemma(creal.left_distrib, &[a, b, nc]); // Equiv(a_b_nc, ab_anc)
    let mnr = mul_neg_right_proof(d, p, a, c); // Equiv(a_nc, nac)
    let refl_ab = refl(d, p, ab);
    let congr = d.lemma(creal.add_congr, &[ab, ab, a_nc, nac, refl_ab, mnr]); // Equiv(ab_anc, ab_nac)
    chain(d, p, a_b_nc, &[(ab_anc, ld), (ab_nac, congr)])
}

/// `Equiv (mul (add a (neg b)) c) (add (mul a c) (neg (mul b c)))`.
fn mul_sub_left_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let creal = p.creal;
    let nb = cneg(d, p, b);
    let a_nb = cadd(d, p, a, nb);
    let a_nb_c = cmul(d, p, a_nb, c);
    let ac = cmul(d, p, a, c);
    let nb_c = cmul(d, p, nb, c);
    let ac_nbc = cadd(d, p, ac, nb_c);
    let bc = cmul(d, p, b, c);
    let nbc = cneg(d, p, bc);
    let ac_nbc2 = cadd(d, p, ac, nbc);
    let rd = right_distrib_proof(d, p, a, nb, c); // Equiv(a_nb_c, ac_nbc)
    let mnl = mul_neg_left_proof(d, p, b, c); // Equiv(nb_c, nbc)
    let refl_ac = refl(d, p, ac);
    let congr = d.lemma(creal.add_congr, &[ac, ac, nb_c, nbc, refl_ac, mnl]); // Equiv(ac_nbc, ac_nbc2)
    chain(d, p, a_nb_c, &[(ac_nbc, rd), (ac_nbc2, congr)])
}

/// `Equiv (add (add a b) (add c e)) (add (add a c) (add b e))` — the
/// "middle two swap" 4-term rearrangement.
fn add_middle_swap_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
) -> ExprId {
    let creal = p.creal;
    let ab = cadd(d, p, a, b);
    let ce = cadd(d, p, c, e);
    let s = cadd(d, p, ab, ce); // (a+b)+(c+e)
    let ac = cadd(d, p, a, c);
    let be = cadd(d, p, b, e);
    let t = cadd(d, p, ac, be); // (a+c)+(b+e)

    let bce = cadd(d, p, b, ce);
    let n1 = cadd(d, p, a, bce); // a+(b+(c+e))
    let step1 = d.lemma(creal.add_assoc, &[a, b, ce]); // Equiv(s, n1)

    let bc = cadd(d, p, b, c);
    let bc_e = cadd(d, p, bc, e);
    let n2 = cadd(d, p, a, bc_e); // a+((b+c)+e)
    let assoc_bce = d.lemma(creal.add_assoc, &[b, c, e]); // Equiv(bc_e, bce)
    let assoc_bce_symm = symm(d, p, bc_e, bce, assoc_bce); // Equiv(bce, bc_e)
    let refl_a = refl(d, p, a);
    let step2 = d.lemma(creal.add_congr, &[a, a, bce, bc_e, refl_a, assoc_bce_symm]); // Equiv(n1, n2)

    let cb = cadd(d, p, c, b);
    let cb_e = cadd(d, p, cb, e);
    let n3 = cadd(d, p, a, cb_e); // a+((c+b)+e)
    let comm_bc = d.lemma(creal.add_comm, &[b, c]); // Equiv(bc, cb)
    let refl_e = refl(d, p, e);
    let congr_cbe = d.lemma(creal.add_congr, &[bc, cb, e, e, comm_bc, refl_e]); // Equiv(bc_e, cb_e)
    let step3 = d.lemma(creal.add_congr, &[a, a, bc_e, cb_e, refl_a, congr_cbe]); // Equiv(n2, n3)

    let assoc_a_c_be = d.lemma(creal.add_assoc, &[a, c, be]); // Equiv(t, a+(c+be))
    let c_be = cadd(d, p, c, be);
    let n4 = cadd(d, p, a, c_be); // a+(c+(b+e))
    let step4 = symm(d, p, t, n4, assoc_a_c_be); // Equiv(n4, t)

    // n3 = a+((c+b)+e), n4 = a+(c+(b+e)): (c+b)+e ~ c+(b+e) by add_assoc(c,b,e).
    let assoc_c_b_e = d.lemma(creal.add_assoc, &[c, b, e]); // Equiv(cb_e, c_be)
    let step3b = d.lemma(creal.add_congr, &[a, a, cb_e, c_be, refl_a, assoc_c_b_e]); // Equiv(n3, n4)

    chain(
        d,
        p,
        s,
        &[
            (n1, step1),
            (n2, step2),
            (n3, step3),
            (n4, step3b),
            (t, step4),
        ],
    )
}

/// `Equiv (add a (neg b)) (add (add a (neg c)) (neg (add b (neg c))))` —
/// `a - b ~ (a - c) - (b - c)`, the diff-of-diffs identity behind Pythagoras.
fn diff_diff_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let creal = p.creal;
    let nb = cneg(d, p, b);
    let nc = cneg(d, p, c);
    let b_nc = cadd(d, p, b, nc); // b - c
    let n_b_nc = cneg(d, p, b_nc); // -(b-c)
    let a_nc = cadd(d, p, a, nc); // a - c
    let rhs = cadd(d, p, a_nc, n_b_nc); // (a-c) + -(b-c)

    let neg_b_nc = neg_add_proof(d, p, b, nc); // Equiv(n_b_nc, add(neg b)(neg nc))
    let nnc = neg_neg_proof(d, p, c); // Equiv(neg nc, c)
    let neg_nc = cneg(d, p, nc);
    let nb_nnc = cadd(d, p, nb, neg_nc);

    let nb_c = cadd(d, p, nb, c); // -b + c
    let step_inner = {
        let refl_nb2 = refl(d, p, nb);
        let congr = d.lemma(creal.add_congr, &[nb, nb, neg_nc, c, refl_nb2, nnc]);
        chain(d, p, n_b_nc, &[(nb_nnc, neg_b_nc), (nb_c, congr)])
    };
    // rhs ~ (a-c) + (-b+c)
    let refl_a_nc = refl(d, p, a_nc);
    let rhs_reduce1 = d.lemma(
        creal.add_congr,
        &[a_nc, a_nc, n_b_nc, nb_c, refl_a_nc, step_inner],
    );
    let target1 = cadd(d, p, a_nc, nb_c);

    // (a-c)+(-b+c) ~ (a+-b)+(-c+c) via add_middle_swap(a,-c,-b,c)
    let swap = add_middle_swap_proof(d, p, a, nc, nb, c); // Equiv((a+-c)+(-b+c), (a+-b)+(-c+c))
    let a_nb = cadd(d, p, a, nb);
    let nc_c = cadd(d, p, nc, c);
    let target2 = cadd(d, p, a_nb, nc_c);

    let cancel = neg_add_cancel_proof(d, p, c); // Equiv(nc_c, zero)
    let zero = czero(d, p);
    let refl_a_nb = refl(d, p, a_nb);
    let congr2 = d.lemma(
        creal.add_congr,
        &[a_nb, a_nb, nc_c, zero, refl_a_nb, cancel],
    );
    let a_nb_zero = cadd(d, p, a_nb, zero);
    let az = d.lemma(creal.add_zero, &[a_nb]); // Equiv(a_nb_zero, a_nb)

    let reduce_chain = chain(
        d,
        p,
        rhs,
        &[
            (target1, rhs_reduce1),
            (target2, swap),
            (a_nb_zero, congr2),
            (a_nb, az),
        ],
    );
    // reduce_chain : Equiv(rhs, a_nb) — we want Equiv(a_nb, rhs).
    symm(d, p, rhs, a_nb, reduce_chain)
}

/// `Equiv (mul two x) (add x x)`.
fn two_mul_eq_double_proof(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId) -> ExprId {
    let creal = p.creal;
    let two = d.kernel().const_(p.two, vec![]);
    let one_a = d.kernel().const_(creal.one, vec![]);
    let one_b = d.kernel().const_(creal.one, vec![]);
    let mul_two_x = cmul(d, p, two, x);
    let mul_x_two = cmul(d, p, x, two);
    let one_one = cadd(d, p, one_a, one_b);
    let mul_x_one_one = cmul(d, p, x, one_one);
    let mul_x_one = cmul(d, p, x, one_a);
    let sum_mul_x_one = cadd(d, p, mul_x_one, mul_x_one);
    let sum_x_x = cadd(d, p, x, x);

    let step1 = d.lemma(creal.mul_comm, &[two, x]); // Equiv(mul_two_x, mul_x_two)
    let refl_mxoo = refl(d, p, mul_x_one_one); // mul_x_two =defeq= mul_x_one_one
    let step2 = d.lemma(creal.left_distrib, &[x, one_a, one_b]); // Equiv(mul_x_one_one, sum_mul_x_one)
    let mul_one_x = d.lemma(creal.mul_one, &[x]); // Equiv(mul_x_one, x)
    let step3 = d.lemma(
        creal.add_congr,
        &[mul_x_one, x, mul_x_one, x, mul_one_x, mul_one_x],
    ); // Equiv(sum_mul_x_one, sum_x_x)

    chain(
        d,
        p,
        mul_two_x,
        &[
            (mul_x_two, step1),
            (mul_x_one_one, refl_mxoo),
            (sum_mul_x_one, step2),
            (sum_x_x, step3),
        ],
    )
}

/// `Equiv (mul two (midpoint a b)) (add a b)`.
fn double_midpoint_proof(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    let creal = p.creal;
    let two = d.kernel().const_(p.two, vec![]);
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let s = cadd(d, p, a, b);
    let mid = cmul(d, p, inv2, s); // =defeq= midpoint a b
    let two_mid = cmul(d, p, two, mid);
    let two_inv2 = cmul(d, p, two, inv2);
    let two_inv2_s = cmul(d, p, two_inv2, s);
    let zero_nat = d.num(0);
    let h_two = d.kernel().const_(p.two_pos_bound, vec![]);

    let assoc = d.lemma(creal.mul_assoc, &[two, inv2, s]); // Equiv(two_inv2_s, two_mid)
    let step_a = symm(d, p, two_inv2_s, two_mid, assoc); // Equiv(two_mid, two_inv2_s)
    let cancel = d.lemma(creal.mul_inv_cancel, &[two, zero_nat, h_two]); // Equiv(two_inv2, one)
    let one = d.kernel().const_(creal.one, vec![]);
    let refl_s = refl(d, p, s);
    let congr1 = d.lemma(creal.mul_congr, &[two_inv2, one, s, s, cancel, refl_s]); // Equiv(two_inv2_s, mul one s)
    let mul_one_s = cmul(d, p, one, s);
    let comm = d.lemma(creal.mul_comm, &[one, s]); // Equiv(mul_one_s, mul s one)
    let mul_s_one = cmul(d, p, s, one);
    let mo = d.lemma(creal.mul_one, &[s]); // Equiv(mul_s_one, s)
    let one_mul_s = chain(d, p, mul_one_s, &[(mul_s_one, comm), (s, mo)]); // Equiv(mul_one_s, s)

    chain(
        d,
        p,
        two_mid,
        &[(two_inv2_s, step_a), (mul_one_s, congr1), (s, one_mul_s)],
    )
}

/// `Equiv (add a (neg c)) (add (add a (neg o)) (add o (neg c)))` —
/// `a - c ~ (a - o) + (o - c)`, true for any `o`.
fn telescope_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    o: ExprId,
    c: ExprId,
) -> ExprId {
    let creal = p.creal;
    let no = cneg(d, p, o);
    let nc = cneg(d, p, c);
    let a_no = cadd(d, p, a, no); // a - o
    let o_nc = cadd(d, p, o, nc); // o - c
    let rhs = cadd(d, p, a_no, o_nc);
    let a_nc = cadd(d, p, a, nc);

    let no_o_nc = cadd(d, p, no, o_nc);
    let assoc1 = d.lemma(creal.add_assoc, &[a, no, o_nc]); // Equiv(rhs, a + (no+o_nc))
    let a_no_onc = cadd(d, p, a, no_o_nc);

    let no_o = cadd(d, p, no, o);
    let no_o_nc2 = cadd(d, p, no_o, nc);
    let assoc2 = d.lemma(creal.add_assoc, &[no, o, nc]); // Equiv(no_o_nc2, no_o_nc)
    let assoc2_symm = symm(d, p, no_o_nc2, no_o_nc, assoc2); // Equiv(no_o_nc, no_o_nc2)

    let zero = czero(d, p);
    let cancel = neg_add_cancel_proof(d, p, o); // Equiv(no_o, zero)
    let refl_nc = refl(d, p, nc);
    let congr_zero_nc = d.lemma(creal.add_congr, &[no_o, zero, nc, nc, cancel, refl_nc]); // Equiv(no_o_nc2, zero+nc)
    let zero_nc = cadd(d, p, zero, nc);
    let za = zero_add_proof(d, p, nc); // Equiv(zero_nc, nc)

    let inner_reduce = chain(
        d,
        p,
        no_o_nc,
        &[(no_o_nc2, assoc2_symm), (zero_nc, congr_zero_nc), (nc, za)],
    ); // Equiv(no_o_nc, nc)

    let refl_a = refl(d, p, a);
    let congr_outer = d.lemma(creal.add_congr, &[a, a, no_o_nc, nc, refl_a, inner_reduce]); // Equiv(a_no_onc, a_nc)

    let combined = chain(d, p, rhs, &[(a_no_onc, assoc1), (a_nc, congr_outer)]);
    // combined : Equiv(rhs, a_nc); want Equiv(a_nc, rhs).
    symm(d, p, rhs, a_nc, combined)
}

/// `Equiv (add o o) (add a b)`, given `ho : Equiv o (midpoint a b)`.
fn double_o_eq_a_plus_b_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    o: ExprId,
    ho: ExprId,
) -> ExprId {
    let mid = midpoint(d, p, a, b);
    let o_o = cadd(d, p, o, o);
    let mid_mid = cadd(d, p, mid, mid);
    let congr_oo = d.lemma(p.creal.add_congr, &[o, mid, o, mid, ho, ho]); // Equiv(o_o, mid_mid)
    let two = d.kernel().const_(p.two, vec![]);
    let two_mid = cmul(d, p, two, mid);
    let two_mul_eq_double = two_mul_eq_double_proof(d, p, mid); // Equiv(two_mid, mid_mid)
    let double_eq_two_mul = symm(d, p, two_mid, mid_mid, two_mul_eq_double); // Equiv(mid_mid, two_mid)
    let dm = double_midpoint_proof(d, p, a, b); // Equiv(two_mid, add a b)
    let ab = cadd(d, p, a, b);
    chain(
        d,
        p,
        o_o,
        &[(mid_mid, congr_oo), (two_mid, double_eq_two_mul), (ab, dm)],
    )
}

/// `Equiv (add b (neg c)) (add (neg (add a (neg o))) (add o (neg c)))` —
/// `b - c ~ neg (a - o) + (o - c)`, given `ho : Equiv o (midpoint a b)`.
/// This is where `O ~ midpoint A B` is actually consumed (via
/// [`double_o_eq_a_plus_b_proof`]).
fn telescope_neg_scalar_proof(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    a: ExprId,
    b: ExprId,
    o: ExprId,
    c: ExprId,
    ho: ExprId,
) -> ExprId {
    let creal = p.creal;
    let no = cneg(d, p, o);
    let nc = cneg(d, p, c);
    let na = cneg(d, p, a);
    let a_no = cadd(d, p, a, no); // a - o
    let n_a_no = cneg(d, p, a_no); // -(a-o)
    let o_nc = cadd(d, p, o, nc); // o - c
    let rhs = cadd(d, p, n_a_no, o_nc);
    let b_nc = cadd(d, p, b, nc);

    // -(a-o) ~ -a + o
    let neg_add = neg_add_proof(d, p, a, no); // Equiv(n_a_no, add(-a)(-(-o)))
    let nno = cneg(d, p, no);
    let na_nno = cadd(d, p, na, nno);
    let nno_eq_o = neg_neg_proof(d, p, o); // Equiv(nno, o)
    let refl_na = refl(d, p, na);
    let congr_na_o = d.lemma(creal.add_congr, &[na, na, nno, o, refl_na, nno_eq_o]); // Equiv(na_nno, na+o)
    let na_o = cadd(d, p, na, o);
    let neg_a_no_reduce = chain(d, p, n_a_no, &[(na_nno, neg_add), (na_o, congr_na_o)]); // Equiv(n_a_no, na_o)

    let refl_o_nc = refl(d, p, o_nc);
    let rhs_reduce1 = d.lemma(
        creal.add_congr,
        &[n_a_no, na_o, o_nc, o_nc, neg_a_no_reduce, refl_o_nc],
    ); // Equiv(rhs, (na+o)+(o+nc))
    let target1 = cadd(d, p, na_o, o_nc);

    // (na+o)+(o+nc) ~ na+(o+(o+nc))
    let assoc1 = d.lemma(creal.add_assoc, &[na, o, o_nc]); // Equiv(target1, na+(o+o_nc))
    let o_o_nc = cadd(d, p, o, o_nc);
    let na_o_o_nc = cadd(d, p, na, o_o_nc);

    // o+(o+nc) ~ (o+o)+nc
    let o_o = cadd(d, p, o, o);
    let o_o_nc2 = cadd(d, p, o_o, nc);
    let assoc2 = d.lemma(creal.add_assoc, &[o, o, nc]); // Equiv(o_o_nc2, o_o_nc)
    let assoc2_symm = symm(d, p, o_o_nc2, o_o_nc, assoc2); // Equiv(o_o_nc, o_o_nc2)
    let refl_na3 = refl(d, p, na);
    let step2 = d.lemma(
        creal.add_congr,
        &[na, na, o_o_nc, o_o_nc2, refl_na3, assoc2_symm],
    ); // Equiv(na_o_o_nc, na+(o_o_nc2))
    let na_oonc2 = cadd(d, p, na, o_o_nc2);

    // o+o ~ a+b
    let double_oo = double_o_eq_a_plus_b_proof(d, p, a, b, o, ho); // Equiv(o_o, a+b)
    let ab = cadd(d, p, a, b);
    let ab_nc = cadd(d, p, ab, nc);
    let refl_nc2 = refl(d, p, nc);
    let step3 = d.lemma(creal.add_congr, &[o_o, ab, nc, nc, double_oo, refl_nc2]); // Equiv(o_o_nc2, ab_nc)
    let refl_na4 = refl(d, p, na);
    let step3b = d.lemma(creal.add_congr, &[na, na, o_o_nc2, ab_nc, refl_na4, step3]); // Equiv(na_oonc2, na+ab_nc)
    let na_abnc = cadd(d, p, na, ab_nc);

    // na + (ab + nc) ~ (na + ab) + nc ~ ((na+a)+b) + nc ~ (zero+b)+nc ~ b+nc
    let assoc3 = d.lemma(creal.add_assoc, &[na, ab, nc]); // Equiv((na+ab)+nc, na+(ab+nc))
    let na_ab = cadd(d, p, na, ab);
    let na_ab_nc = cadd(d, p, na_ab, nc);
    let assoc3_symm = symm(d, p, na_ab_nc, na_abnc, assoc3); // Equiv(na_abnc, na_ab_nc)

    let assoc4 = d.lemma(creal.add_assoc, &[na, a, b]); // Equiv((na+a)+b, na+(a+b)) = Equiv(_, na+ab)
    let na_a = cadd(d, p, na, a);
    let na_a_b = cadd(d, p, na_a, b);
    let assoc4_symm = symm(d, p, na_a_b, na_ab, assoc4); // Equiv(na_ab, na_a_b)
    let refl_nc3 = refl(d, p, nc);
    let congr4 = d.lemma(
        creal.add_congr,
        &[na_ab, na_a_b, nc, nc, assoc4_symm, refl_nc3],
    ); // Equiv(na_ab_nc, na_a_b_nc)
    let na_a_b_nc = cadd(d, p, na_a_b, nc);

    let cancel_na = neg_add_cancel_proof(d, p, a); // Equiv(na_a, zero)
    let zero = czero(d, p);
    let refl_b = refl(d, p, b);
    let congr5 = d.lemma(creal.add_congr, &[na_a, zero, b, b, cancel_na, refl_b]); // Equiv(na_a_b, zero+b)
    let zero_b = cadd(d, p, zero, b);
    let za = zero_add_proof(d, p, b); // Equiv(zero_b, b)

    let na_a_b_reduce = chain(d, p, na_a_b, &[(zero_b, congr5), (b, za)]); // Equiv(na_a_b, b)
    let refl_nc5 = refl(d, p, nc);
    let congr7 = d.lemma(
        creal.add_congr,
        &[na_a_b, b, nc, nc, na_a_b_reduce, refl_nc5],
    ); // Equiv(na_a_b_nc, b_nc)

    let combined = chain(
        d,
        p,
        rhs,
        &[
            (target1, rhs_reduce1),
            (na_o_o_nc, assoc1),
            (na_oonc2, step2),
            (na_abnc, step3b),
            (na_ab_nc, assoc3_symm),
            (na_a_b_nc, congr4),
            (b_nc, congr7),
        ],
    );
    // combined : Equiv(rhs, b_nc) — the function's contract is the reverse.
    symm(d, p, rhs, b_nc, combined)
}

/// `Equiv (neg (add x (neg y))) (add y (neg x))` — `neg (x - y) ~ y - x`.
fn neg_sub_comm_scalar_proof(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    let creal = p.creal;
    let ny = cneg(d, p, y);
    let x_ny = cadd(d, p, x, ny);
    let n_x_ny = cneg(d, p, x_ny);
    let nx = cneg(d, p, x);
    let nny = cneg(d, p, ny);
    let na = neg_add_proof(d, p, x, ny); // Equiv(n_x_ny, add nx nny)
    let nx_nny = cadd(d, p, nx, nny);
    let nny_eq_y = neg_neg_proof(d, p, y); // Equiv(nny, y)
    let refl_nx = refl(d, p, nx);
    let congr = d.lemma(creal.add_congr, &[nx, nx, nny, y, refl_nx, nny_eq_y]); // Equiv(nx_nny, nx+y)
    let nx_y = cadd(d, p, nx, y);
    let comm = d.lemma(creal.add_comm, &[nx, y]); // Equiv(nx_y, y+nx)... wait add_comm(nx,y): Equiv(add nx y, add y nx)
    let y_nx = cadd(d, p, y, nx);
    chain(d, p, n_x_ny, &[(nx_nny, na), (nx_y, congr), (y_nx, comm)])
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

// --- the inner product ------------------------------------------------------

/// `CPoint.add P Q := CPoint.mk (add (x P) (x Q)) (add (y P) (y Q))`.
fn declare_point_add(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let sx = cadd(d, p, ax, bx);
    let sy = cadd(d, p, ay, by);
    let value_body = d.const_app(p.mk, &[sx, sy]);

    let value = {
        let inner = d.lam_fv(pb_fv, point, value_body);
        d.lam_fv(pa_fv, point, inner)
    };
    let ty = {
        let inner = d.arrow(point, point);
        d.arrow(point, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.point_add,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 5),
    })
}

/// `CPoint.neg P := CPoint.mk (neg (x P)) (neg (y P))`.
fn declare_point_neg(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let nx = cneg(d, p, ax);
    let ny = cneg(d, p, ay);
    let value_body = d.const_app(p.mk, &[nx, ny]);

    let value = d.lam_fv(pa_fv, point, value_body);
    let ty = d.arrow(point, point);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.point_neg,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 6),
    })
}

/// `CPoint.dot P Q := CReal.add (CReal.mul (x P) (x Q)) (CReal.mul (y P) (y Q))`.
fn declare_dot(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let mx = cmul(d, p, ax, bx);
    let my = cmul(d, p, ay, by);
    let value_body = cadd(d, p, mx, my);

    let value = {
        let inner = d.lam_fv(pb_fv, point, value_body);
        d.lam_fv(pa_fv, point, inner)
    };
    let ty = {
        let inner = d.arrow(point, carrier);
        d.arrow(point, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.dot,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 7),
    })
}

/// `dot_congr : ∀ P P' Q Q', CPoint.Equiv P P' → CPoint.Equiv Q Q' →
/// Equiv (dot P Q) (dot P' Q')`.
fn declare_dot_congr(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);
    let qa_fv = d.fresh_fvar();
    let qa = d.kernel().fvar(qa_fv);
    let qb_fv = d.fresh_fvar();
    let qb = d.kernel().fvar(qb_fv);

    let pax = d.const_app(p.x, &[pa]);
    let pay = d.const_app(p.y, &[pa]);
    let pbx = d.const_app(p.x, &[pb]);
    let pby = d.const_app(p.y, &[pb]);
    let qax = d.const_app(p.x, &[qa]);
    let qay = d.const_app(p.y, &[qa]);
    let qbx = d.const_app(p.x, &[qb]);
    let qby = d.const_app(p.y, &[qb]);

    let hp_ty = d.const_app(p.point_equiv, &[pa, pb]);
    let hq_ty = d.const_app(p.point_equiv, &[qa, qb]);
    let hp_fv = d.fresh_fvar();
    let hp = d.kernel().fvar(hp_fv);
    let hq_fv = d.fresh_fvar();
    let hq = d.kernel().fvar(hq_fv);

    let ex_ty = equiv(d, p, pax, pbx);
    let ey_ty = equiv(d, p, pay, pby);
    let hpx = d.and_left(ex_ty, ey_ty, hp);
    let hpy = d.and_right(ex_ty, ey_ty, hp);
    let fx_ty = equiv(d, p, qax, qbx);
    let fy_ty = equiv(d, p, qay, qby);
    let hqx = d.and_left(fx_ty, fy_ty, hq);
    let hqy = d.and_right(fx_ty, fy_ty, hq);

    let mx1 = cmul(d, p, pax, qax);
    let mx2 = cmul(d, p, pbx, qbx);
    let my1 = cmul(d, p, pay, qay);
    let my2 = cmul(d, p, pby, qby);
    let congr_x = d.lemma(creal.mul_congr, &[pax, pbx, qax, qbx, hpx, hqx]);
    let congr_y = d.lemma(creal.mul_congr, &[pay, pby, qay, qby, hpy, hqy]);
    let proof = d.lemma(creal.add_congr, &[mx1, mx2, my1, my2, congr_x, congr_y]);

    let dot_pq = dotp(d, p, pa, qa);
    let dot_pq2 = dotp(d, p, pb, qb);
    let ty_body = equiv(d, p, dot_pq, dot_pq2);
    let ty = {
        let inner = d.arrow(hq_ty, ty_body);
        let with_hp = d.arrow(hp_ty, inner);
        let with_qb = d.pi_fv(qb_fv, point, with_hp);
        let with_qa = d.pi_fv(qa_fv, point, with_qb);
        let with_pb = d.pi_fv(pb_fv, point, with_qa);
        d.pi_fv(pa_fv, point, with_pb)
    };
    let value = {
        let with_hq = d.lam_fv(hq_fv, hq_ty, proof);
        let with_hp = d.lam_fv(hp_fv, hp_ty, with_hq);
        let with_qb = d.lam_fv(qb_fv, point, with_hp);
        let with_qa = d.lam_fv(qa_fv, point, with_qb);
        let with_pb = d.lam_fv(pb_fv, point, with_qa);
        d.lam_fv(pa_fv, point, with_pb)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `dot_comm : ∀ P Q, Equiv (dot P Q) (dot Q P)`.
fn declare_dot_comm(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let mx1 = cmul(d, p, ax, bx);
    let mx2 = cmul(d, p, bx, ax);
    let my1 = cmul(d, p, ay, by);
    let my2 = cmul(d, p, by, ay);
    let comm_x = d.lemma(creal.mul_comm, &[ax, bx]);
    let comm_y = d.lemma(creal.mul_comm, &[ay, by]);
    let proof = d.lemma(creal.add_congr, &[mx1, mx2, my1, my2, comm_x, comm_y]);

    let dot1 = dotp(d, p, pa, pb);
    let dot2 = dotp(d, p, pb, pa);
    let ty_body = equiv(d, p, dot1, dot2);
    let ty = {
        let inner = d.pi_fv(pb_fv, point, ty_body);
        d.pi_fv(pa_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(pb_fv, point, proof);
        d.lam_fv(pa_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_comm,
        uparams: vec![],
        ty,
        value,
    })
}

/// `dot_add_left : ∀ P Q R, Equiv (dot (add P Q) R) (add (dot P R) (dot Q R))`.
fn declare_dot_add_left(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);
    let pc_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(pc_fv);

    let px = d.const_app(p.x, &[pa]);
    let py = d.const_app(p.y, &[pa]);
    let qx = d.const_app(p.x, &[pb]);
    let qy = d.const_app(p.y, &[pb]);
    let rx = d.const_app(p.x, &[pc]);
    let ry = d.const_app(p.y, &[pc]);

    let pq_x = cadd(d, p, px, qx);
    let pq_y = cadd(d, p, py, qy);
    let lhs_x = cmul(d, p, pq_x, rx);
    let lhs_y = cmul(d, p, pq_y, ry);
    let lhs_raw = cadd(d, p, lhs_x, lhs_y);

    let pxrx = cmul(d, p, px, rx);
    let qxrx = cmul(d, p, qx, rx);
    let pyry = cmul(d, p, py, ry);
    let qyry = cmul(d, p, qy, ry);
    let rd_x = right_distrib_proof(d, p, px, qx, rx); // Equiv(lhs_x, add pxrx qxrx)
    let rd_y = right_distrib_proof(d, p, py, qy, ry);
    let mid_x = cadd(d, p, pxrx, qxrx);
    let mid_y = cadd(d, p, pyry, qyry);
    let mid = cadd(d, p, mid_x, mid_y);
    let combined = d.lemma(creal.add_congr, &[lhs_x, mid_x, lhs_y, mid_y, rd_x, rd_y]);

    let swap = add_middle_swap_proof(d, p, pxrx, qxrx, pyry, qyry);
    let rhs_left = cadd(d, p, pxrx, pyry);
    let rhs_right = cadd(d, p, qxrx, qyry);
    let rhs_raw = cadd(d, p, rhs_left, rhs_right);

    let proof = chain(d, p, lhs_raw, &[(mid, combined), (rhs_raw, swap)]);

    let sum_pq = padd(d, p, pa, pb);
    let dot_sum_r = dotp(d, p, sum_pq, pc);
    let dot_p_r = dotp(d, p, pa, pc);
    let dot_q_r = dotp(d, p, pb, pc);
    let rhs_named = cadd(d, p, dot_p_r, dot_q_r);
    let ty_body = equiv(d, p, dot_sum_r, rhs_named);
    let ty = {
        let w3 = d.pi_fv(pc_fv, point, ty_body);
        let w2 = d.pi_fv(pb_fv, point, w3);
        d.pi_fv(pa_fv, point, w2)
    };
    let value = {
        let w3 = d.lam_fv(pc_fv, point, proof);
        let w2 = d.lam_fv(pb_fv, point, w3);
        d.lam_fv(pa_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_add_left,
        uparams: vec![],
        ty,
        value,
    })
}

/// `dot_add_right : ∀ P Q R, Equiv (dot P (add Q R)) (add (dot P Q) (dot P R))`.
fn declare_dot_add_right(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);
    let pc_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(pc_fv);

    let px = d.const_app(p.x, &[pa]);
    let py = d.const_app(p.y, &[pa]);
    let qx = d.const_app(p.x, &[pb]);
    let qy = d.const_app(p.y, &[pb]);
    let rx = d.const_app(p.x, &[pc]);
    let ry = d.const_app(p.y, &[pc]);

    let qr_x = cadd(d, p, qx, rx);
    let qr_y = cadd(d, p, qy, ry);
    let lhs_x = cmul(d, p, px, qr_x);
    let lhs_y = cmul(d, p, py, qr_y);
    let lhs_raw = cadd(d, p, lhs_x, lhs_y);

    let pxqx = cmul(d, p, px, qx);
    let pxrx = cmul(d, p, px, rx);
    let pyqy = cmul(d, p, py, qy);
    let pyry = cmul(d, p, py, ry);
    let ld_x = d.lemma(creal.left_distrib, &[px, qx, rx]);
    let ld_y = d.lemma(creal.left_distrib, &[py, qy, ry]);
    let mid_x = cadd(d, p, pxqx, pxrx);
    let mid_y = cadd(d, p, pyqy, pyry);
    let mid = cadd(d, p, mid_x, mid_y);
    let combined = d.lemma(creal.add_congr, &[lhs_x, mid_x, lhs_y, mid_y, ld_x, ld_y]);

    let swap = add_middle_swap_proof(d, p, pxqx, pxrx, pyqy, pyry);
    let rhs_left = cadd(d, p, pxqx, pyqy);
    let rhs_right = cadd(d, p, pxrx, pyry);
    let rhs_raw = cadd(d, p, rhs_left, rhs_right);

    let proof = chain(d, p, lhs_raw, &[(mid, combined), (rhs_raw, swap)]);

    let sum_qr = padd(d, p, pb, pc);
    let dot_p_sum = dotp(d, p, pa, sum_qr);
    let dot_p_q = dotp(d, p, pa, pb);
    let dot_p_r = dotp(d, p, pa, pc);
    let rhs_named = cadd(d, p, dot_p_q, dot_p_r);
    let ty_body = equiv(d, p, dot_p_sum, rhs_named);
    let ty = {
        let w3 = d.pi_fv(pc_fv, point, ty_body);
        let w2 = d.pi_fv(pb_fv, point, w3);
        d.pi_fv(pa_fv, point, w2)
    };
    let value = {
        let w3 = d.lam_fv(pc_fv, point, proof);
        let w2 = d.lam_fv(pb_fv, point, w3);
        d.lam_fv(pa_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_add_right,
        uparams: vec![],
        ty,
        value,
    })
}

/// `dot_sub_left : ∀ P Q R,
/// Equiv (dot (sub P Q) R) (add (dot P R) (neg (dot Q R)))`.
fn declare_dot_sub_left(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);
    let pc_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(pc_fv);

    let px = d.const_app(p.x, &[pa]);
    let py = d.const_app(p.y, &[pa]);
    let qx = d.const_app(p.x, &[pb]);
    let qy = d.const_app(p.y, &[pb]);
    let rx = d.const_app(p.x, &[pc]);
    let ry = d.const_app(p.y, &[pc]);

    let n_qx = cneg(d, p, qx);
    let n_qy = cneg(d, p, qy);
    let pq_x = cadd(d, p, px, n_qx);
    let pq_y = cadd(d, p, py, n_qy);
    let lhs_x = cmul(d, p, pq_x, rx);
    let lhs_y = cmul(d, p, pq_y, ry);
    let lhs_raw = cadd(d, p, lhs_x, lhs_y);

    let pxrx = cmul(d, p, px, rx);
    let qxrx = cmul(d, p, qx, rx);
    let pyry = cmul(d, p, py, ry);
    let qyry = cmul(d, p, qy, ry);
    let n_qxrx = cneg(d, p, qxrx);
    let n_qyry = cneg(d, p, qyry);
    let ms_x = mul_sub_left_proof(d, p, px, qx, rx); // Equiv(lhs_x, add pxrx (neg qxrx))
    let ms_y = mul_sub_left_proof(d, p, py, qy, ry);
    let mid_x = cadd(d, p, pxrx, n_qxrx);
    let mid_y = cadd(d, p, pyry, n_qyry);
    let mid = cadd(d, p, mid_x, mid_y);
    let combined = d.lemma(creal.add_congr, &[lhs_x, mid_x, lhs_y, mid_y, ms_x, ms_y]);

    let swap = add_middle_swap_proof(d, p, pxrx, n_qxrx, pyry, n_qyry);
    let swapped_left = cadd(d, p, pxrx, pyry);
    let swapped_right = cadd(d, p, n_qxrx, n_qyry);
    let swapped = cadd(d, p, swapped_left, swapped_right);

    let sum_pxrx_pyry = cadd(d, p, pxrx, pyry);
    let sum_qxrx_qyry = cadd(d, p, qxrx, qyry);
    let neg_sum_qxrx_qyry = cneg(d, p, sum_qxrx_qyry);
    let na = neg_add_proof(d, p, qxrx, qyry); // Equiv(neg_sum_qxrx_qyry, add n_qxrx n_qyry)
    let na_symm = symm(d, p, neg_sum_qxrx_qyry, swapped_right, na);
    let refl_sum = refl(d, p, sum_pxrx_pyry);
    let congr_final = d.lemma(
        creal.add_congr,
        &[
            sum_pxrx_pyry,
            sum_pxrx_pyry,
            swapped_right,
            neg_sum_qxrx_qyry,
            refl_sum,
            na_symm,
        ],
    );
    let rhs_raw = cadd(d, p, sum_pxrx_pyry, neg_sum_qxrx_qyry);

    let proof = chain(
        d,
        p,
        lhs_raw,
        &[(mid, combined), (swapped, swap), (rhs_raw, congr_final)],
    );

    let sub_pq = psub(d, p, pa, pb);
    let dot_sub_r = dotp(d, p, sub_pq, pc);
    let dot_p_r = dotp(d, p, pa, pc);
    let dot_q_r = dotp(d, p, pb, pc);
    let neg_dot_q_r = cneg(d, p, dot_q_r);
    let rhs_named = cadd(d, p, dot_p_r, neg_dot_q_r);
    let ty_body = equiv(d, p, dot_sub_r, rhs_named);
    let ty = {
        let w3 = d.pi_fv(pc_fv, point, ty_body);
        let w2 = d.pi_fv(pb_fv, point, w3);
        d.pi_fv(pa_fv, point, w2)
    };
    let value = {
        let w3 = d.lam_fv(pc_fv, point, proof);
        let w2 = d.lam_fv(pb_fv, point, w3);
        d.lam_fv(pa_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_sub_left,
        uparams: vec![],
        ty,
        value,
    })
}

/// `dot_sub_right : ∀ P Q R,
/// Equiv (dot P (sub Q R)) (add (dot P Q) (neg (dot P R)))`.
fn declare_dot_sub_right(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);
    let pc_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(pc_fv);

    let px = d.const_app(p.x, &[pa]);
    let py = d.const_app(p.y, &[pa]);
    let qx = d.const_app(p.x, &[pb]);
    let qy = d.const_app(p.y, &[pb]);
    let rx = d.const_app(p.x, &[pc]);
    let ry = d.const_app(p.y, &[pc]);

    let n_rx = cneg(d, p, rx);
    let n_ry = cneg(d, p, ry);
    let qr_x = cadd(d, p, qx, n_rx);
    let qr_y = cadd(d, p, qy, n_ry);
    let lhs_x = cmul(d, p, px, qr_x);
    let lhs_y = cmul(d, p, py, qr_y);
    let lhs_raw = cadd(d, p, lhs_x, lhs_y);

    let pxqx = cmul(d, p, px, qx);
    let pxrx = cmul(d, p, px, rx);
    let pyqy = cmul(d, p, py, qy);
    let pyry = cmul(d, p, py, ry);
    let n_pxrx = cneg(d, p, pxrx);
    let n_pyry = cneg(d, p, pyry);
    let ms_x = mul_sub_right_proof(d, p, px, qx, rx); // Equiv(lhs_x, add pxqx (neg pxrx))
    let ms_y = mul_sub_right_proof(d, p, py, qy, ry);
    let mid_x = cadd(d, p, pxqx, n_pxrx);
    let mid_y = cadd(d, p, pyqy, n_pyry);
    let mid = cadd(d, p, mid_x, mid_y);
    let combined = d.lemma(creal.add_congr, &[lhs_x, mid_x, lhs_y, mid_y, ms_x, ms_y]);

    let swap = add_middle_swap_proof(d, p, pxqx, n_pxrx, pyqy, n_pyry);
    let swapped_left = cadd(d, p, pxqx, pyqy);
    let swapped_right = cadd(d, p, n_pxrx, n_pyry);
    let swapped = cadd(d, p, swapped_left, swapped_right);

    let sum_pxqx_pyqy = cadd(d, p, pxqx, pyqy);
    let sum_pxrx_pyry = cadd(d, p, pxrx, pyry);
    let neg_sum_pxrx_pyry = cneg(d, p, sum_pxrx_pyry);
    let na = neg_add_proof(d, p, pxrx, pyry); // Equiv(neg_sum_pxrx_pyry, add n_pxrx n_pyry)
    let na_symm = symm(d, p, neg_sum_pxrx_pyry, swapped_right, na);
    let refl_sum = refl(d, p, sum_pxqx_pyqy);
    let congr_final = d.lemma(
        creal.add_congr,
        &[
            sum_pxqx_pyqy,
            sum_pxqx_pyqy,
            swapped_right,
            neg_sum_pxrx_pyry,
            refl_sum,
            na_symm,
        ],
    );
    let rhs_raw = cadd(d, p, sum_pxqx_pyqy, neg_sum_pxrx_pyry);

    let proof = chain(
        d,
        p,
        lhs_raw,
        &[(mid, combined), (swapped, swap), (rhs_raw, congr_final)],
    );

    let sub_qr = psub(d, p, pb, pc);
    let dot_p_sub = dotp(d, p, pa, sub_qr);
    let dot_p_q = dotp(d, p, pa, pb);
    let dot_p_r = dotp(d, p, pa, pc);
    let neg_dot_p_r = cneg(d, p, dot_p_r);
    let rhs_named = cadd(d, p, dot_p_q, neg_dot_p_r);
    let ty_body = equiv(d, p, dot_p_sub, rhs_named);
    let ty = {
        let w3 = d.pi_fv(pc_fv, point, ty_body);
        let w2 = d.pi_fv(pb_fv, point, w3);
        d.pi_fv(pa_fv, point, w2)
    };
    let value = {
        let w3 = d.lam_fv(pc_fv, point, proof);
        let w2 = d.lam_fv(pb_fv, point, w3);
        d.lam_fv(pa_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_sub_right,
        uparams: vec![],
        ty,
        value,
    })
}

/// `dot_neg_left : ∀ P Q, Equiv (dot (neg P) Q) (neg (dot P Q))`.
fn declare_dot_neg_left(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let pa_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(pa_fv);
    let pb_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(pb_fv);

    let px = d.const_app(p.x, &[pa]);
    let py = d.const_app(p.y, &[pa]);
    let qx = d.const_app(p.x, &[pb]);
    let qy = d.const_app(p.y, &[pb]);

    let n_px = cneg(d, p, px);
    let n_py = cneg(d, p, py);
    let lhs_x = cmul(d, p, n_px, qx);
    let lhs_y = cmul(d, p, n_py, qy);
    let lhs_raw = cadd(d, p, lhs_x, lhs_y);

    let pxqx = cmul(d, p, px, qx);
    let pyqy = cmul(d, p, py, qy);
    let n_pxqx = cneg(d, p, pxqx);
    let n_pyqy = cneg(d, p, pyqy);
    let mnl_x = mul_neg_left_proof(d, p, px, qx); // Equiv(lhs_x, n_pxqx)
    let mnl_y = mul_neg_left_proof(d, p, py, qy);
    let mid = cadd(d, p, n_pxqx, n_pyqy);
    let combined = d.lemma(
        creal.add_congr,
        &[lhs_x, n_pxqx, lhs_y, n_pyqy, mnl_x, mnl_y],
    );

    let sum_pxqx_pyqy = cadd(d, p, pxqx, pyqy);
    let neg_sum = cneg(d, p, sum_pxqx_pyqy);
    let na = neg_add_proof(d, p, pxqx, pyqy); // Equiv(neg_sum, add n_pxqx n_pyqy)
    let na_symm = symm(d, p, neg_sum, mid, na);

    let proof = chain(d, p, lhs_raw, &[(mid, combined), (neg_sum, na_symm)]);

    let neg_p = pneg(d, p, pa);
    let dot_negp_q = dotp(d, p, neg_p, pb);
    let dot_p_q = dotp(d, p, pa, pb);
    let rhs_named = cneg(d, p, dot_p_q);
    let ty_body = equiv(d, p, dot_negp_q, rhs_named);
    let ty = {
        let inner = d.pi_fv(pb_fv, point, ty_body);
        d.pi_fv(pa_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(pb_fv, point, proof);
        d.lam_fv(pa_fv, point, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.dot_neg_left,
        uparams: vec![],
        ty,
        value,
    })
}

/// **Elements I.47.** See [`CPointPrelude::pythagoras`].
fn declare_pythagoras(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);

    let sub_ab = psub(d, p, pa, pb);
    let big_u = psub(d, p, pa, pc); // A - C
    let big_v = psub(d, p, pb, pc); // B - C
    let big_w = psub(d, p, big_u, big_v); // (A-C) - (B-C)

    let dot_uv = dotp(d, p, big_u, big_v);
    let zero = czero(d, p);
    let hyp_ty = equiv(d, p, dot_uv, zero);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // point_sub_diff: CPoint.Equiv (A - B) ((A-C) - (B-C)), per coordinate.
    let n_bx = cneg(d, p, bx);
    let n_cx = cneg(d, p, cx);
    let n_by = cneg(d, p, by);
    let n_cy = cneg(d, p, cy);
    let ax_bx = cadd(d, p, ax, n_bx);
    let ax_cx = cadd(d, p, ax, n_cx);
    let bx_cx = cadd(d, p, bx, n_cx);
    let n_bx_cx = cneg(d, p, bx_cx);
    let ac_bc_x = cadd(d, p, ax_cx, n_bx_cx);
    let claim_x = equiv(d, p, ax_bx, ac_bc_x);
    let ay_by = cadd(d, p, ay, n_by);
    let ay_cy = cadd(d, p, ay, n_cy);
    let by_cy = cadd(d, p, by, n_cy);
    let n_by_cy = cneg(d, p, by_cy);
    let ac_bc_y = cadd(d, p, ay_cy, n_by_cy);
    let claim_y = equiv(d, p, ay_by, ac_bc_y);
    let diff_x = diff_diff_scalar_proof(d, p, ax, bx, cx);
    let diff_y = diff_diff_scalar_proof(d, p, ay, by, cy);
    let diff_ab_w = and_intro(d, p, claim_x, claim_y, diff_x, diff_y);

    // dot(A-B,A-B) ~ dot(W,W)
    let dot_ww = dotp(d, p, big_w, big_w);
    let step1 = d.lemma(
        p.dot_congr,
        &[sub_ab, big_w, sub_ab, big_w, diff_ab_w, diff_ab_w],
    );

    // dot(W,W) ~ add(dot U W)(neg(dot V W))
    let dot_uw = dotp(d, p, big_u, big_w);
    let dot_vw = dotp(d, p, big_v, big_w);
    let neg_dot_vw = cneg(d, p, dot_vw);
    let mid_expr = cadd(d, p, dot_uw, neg_dot_vw);
    let step2 = d.lemma(p.dot_sub_left, &[big_u, big_v, big_w]); // Equiv(dot_ww, mid_expr)

    // dot(U,W) ~ add(dot_uu)(neg dot_uv)
    let dot_uu = dotp(d, p, big_u, big_u);
    let neg_dot_uv = cneg(d, p, dot_uv);
    let rhs_step3 = cadd(d, p, dot_uu, neg_dot_uv);
    let step3 = d.lemma(p.dot_sub_right, &[big_u, big_u, big_v]); // Equiv(dot_uw, rhs_step3)

    // dot(V,W) ~ add(dot_vu)(neg dot_vv) ~ add(dot_uv)(neg dot_vv)
    let dot_vv = dotp(d, p, big_v, big_v);
    let dot_vu = dotp(d, p, big_v, big_u);
    let neg_dot_vv = cneg(d, p, dot_vv);
    let rhs_step4 = cadd(d, p, dot_vu, neg_dot_vv);
    let step4 = d.lemma(p.dot_sub_right, &[big_v, big_u, big_v]); // Equiv(dot_vw, rhs_step4)
    let cvu = d.lemma(p.dot_comm, &[big_v, big_u]); // Equiv(dot_vu, dot_uv)
    let refl_neg_dot_vv = refl(d, p, neg_dot_vv);
    let rhs_step4b = cadd(d, p, dot_uv, neg_dot_vv);
    let step4b = d.lemma(
        creal.add_congr,
        &[dot_vu, dot_uv, neg_dot_vv, neg_dot_vv, cvu, refl_neg_dot_vv],
    ); // Equiv(rhs_step4, rhs_step4b)
    let dot_vw_reduced = chain(d, p, dot_vw, &[(rhs_step4, step4), (rhs_step4b, step4b)]);

    // Combine: dot(W,W) ~ add(rhs_step3)(neg rhs_step4b)
    let neg_dot_vw_congr = d.lemma(creal.neg_congr, &[dot_vw, rhs_step4b, dot_vw_reduced]);
    let neg_rhs_step4b = cneg(d, p, rhs_step4b);
    let mid_expr2 = cadd(d, p, rhs_step3, neg_rhs_step4b);
    let combined34 = d.lemma(
        creal.add_congr,
        &[
            dot_uw,
            rhs_step3,
            neg_dot_vw,
            neg_rhs_step4b,
            step3,
            neg_dot_vw_congr,
        ],
    );

    // Simplify neg(add dot_uv (neg dot_vv)) ~ add(neg dot_uv)(dot_vv)
    let na = neg_add_proof(d, p, dot_uv, neg_dot_vv);
    let nn = neg_neg_proof(d, p, dot_vv);
    let refl_neg_uv = refl(d, p, neg_dot_uv);
    let neg_neg_dot_vv = cneg(d, p, neg_dot_vv);
    let congr_nn = d.lemma(
        creal.add_congr,
        &[
            neg_dot_uv,
            neg_dot_uv,
            neg_neg_dot_vv,
            dot_vv,
            refl_neg_uv,
            nn,
        ],
    );
    let na_target = cadd(d, p, neg_dot_uv, neg_neg_dot_vv);
    let nn_target = cadd(d, p, neg_dot_uv, dot_vv);
    let simplify_neg = chain(
        d,
        p,
        neg_rhs_step4b,
        &[(na_target, na), (nn_target, congr_nn)],
    );
    let refl_first = refl(d, p, rhs_step3);
    let mid_expr3 = cadd(d, p, rhs_step3, nn_target);
    let combined_simplify = d.lemma(
        creal.add_congr,
        &[
            rhs_step3,
            rhs_step3,
            neg_rhs_step4b,
            nn_target,
            refl_first,
            simplify_neg,
        ],
    );

    // Use the hypothesis: neg dot_uv ~ zero.
    let neg_r_eq_neg_zero = d.lemma(creal.neg_congr, &[dot_uv, zero, h]);
    let nz = neg_zero_proof(d, p);
    let neg_zero = cneg(d, p, zero);
    let neg_r_zero = chain(
        d,
        p,
        neg_dot_uv,
        &[(neg_zero, neg_r_eq_neg_zero), (zero, nz)],
    );

    let refl_dotuu = refl(d, p, dot_uu);
    let congr_p = d.lemma(
        creal.add_congr,
        &[dot_uu, dot_uu, neg_dot_uv, zero, refl_dotuu, neg_r_zero],
    );
    let dotuu_zero = cadd(d, p, dot_uu, zero);
    let az_p = d.lemma(creal.add_zero, &[dot_uu]);
    let p_reduce = chain(d, p, rhs_step3, &[(dotuu_zero, congr_p), (dot_uu, az_p)]);

    let refl_dotvv = refl(d, p, dot_vv);
    let congr_q = d.lemma(
        creal.add_congr,
        &[neg_dot_uv, zero, dot_vv, dot_vv, neg_r_zero, refl_dotvv],
    );
    let zero_dotvv = cadd(d, p, zero, dot_vv);
    let za_q = zero_add_proof(d, p, dot_vv);
    let q_expr = nn_target;
    let q_reduce = chain(d, p, q_expr, &[(zero_dotvv, congr_q), (dot_vv, za_q)]);

    let dot_uu_dot_vv = cadd(d, p, dot_uu, dot_vv);
    let final_combine = d.lemma(
        creal.add_congr,
        &[rhs_step3, dot_uu, q_expr, dot_vv, p_reduce, q_reduce],
    );

    let sub_ab_dot = dotp(d, p, sub_ab, sub_ab);
    let final_proof = chain(
        d,
        p,
        sub_ab_dot,
        &[
            (dot_ww, step1),
            (mid_expr, step2),
            (mid_expr2, combined34),
            (mid_expr3, combined_simplify),
            (dot_uu_dot_vv, final_combine),
        ],
    );

    let ty_body = {
        let concl = equiv(d, p, sub_ab_dot, dot_uu_dot_vv);
        d.arrow(hyp_ty, concl)
    };
    let ty = {
        let w3 = d.pi_fv(c_fv, point, ty_body);
        let w2 = d.pi_fv(b_fv, point, w3);
        d.pi_fv(a_fv, point, w2)
    };
    let value = {
        let inner = d.lam_fv(h_fv, hyp_ty, final_proof);
        let w3 = d.lam_fv(c_fv, point, inner);
        let w2 = d.lam_fv(b_fv, point, w3);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pythagoras,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (dot (neg P) (neg P)) (dot P P)`.
fn dot_neg_neg_proof(d: &mut IntDev<'_>, p: CPointPrelude, big_p: ExprId) -> ExprId {
    let creal = p.creal;
    let neg_p = pneg(d, p, big_p);
    let dot_pp = dotp(d, p, big_p, big_p);
    let dot_np_p = dotp(d, p, neg_p, big_p);
    let dot_p_np = dotp(d, p, big_p, neg_p);
    let dot_np_np = dotp(d, p, neg_p, neg_p);
    let neg_dot_pp = cneg(d, p, dot_pp);

    let dnl1 = d.lemma(p.dot_neg_left, &[big_p, big_p]); // Equiv(dot_np_p, neg_dot_pp)
    let comm1 = d.lemma(p.dot_comm, &[big_p, neg_p]); // Equiv(dot_p_np, dot_np_p)
    let dot_p_np_reduce = chain(d, p, dot_p_np, &[(dot_np_p, comm1), (neg_dot_pp, dnl1)]);

    let dnl2 = d.lemma(p.dot_neg_left, &[big_p, neg_p]); // Equiv(dot_np_np, neg dot_p_np)
    let neg_congr1 = d.lemma(creal.neg_congr, &[dot_p_np, neg_dot_pp, dot_p_np_reduce]);
    let nn = neg_neg_proof(d, p, dot_pp); // Equiv(neg neg_dot_pp, dot_pp)

    let neg_dot_p_np = cneg(d, p, dot_p_np);
    let neg_neg_dot_pp = cneg(d, p, neg_dot_pp);
    chain(
        d,
        p,
        dot_np_np,
        &[
            (neg_dot_p_np, dnl2),
            (neg_neg_dot_pp, neg_congr1),
            (dot_pp, nn),
        ],
    )
}

/// **Elements III.31**, the converse direction. See [`CPointPrelude::thales`].
fn declare_thales(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let creal = p.creal;

    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);
    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);

    let ax = d.const_app(p.x, &[pa]);
    let ay = d.const_app(p.y, &[pa]);
    let bx = d.const_app(p.x, &[pb]);
    let by = d.const_app(p.y, &[pb]);
    let cx = d.const_app(p.x, &[pc]);
    let cy = d.const_app(p.y, &[pc]);
    let ox = d.const_app(p.x, &[po]);
    let oy = d.const_app(p.y, &[po]);

    // Hypothesis 1: O ~ midpoint A B.
    let mid_ab = d.const_app(p.point_midpoint, &[pa, pb]);
    let ho_ty = d.const_app(p.point_equiv, &[po, mid_ab]);
    let ho_fv = d.fresh_fvar();
    let ho = d.kernel().fvar(ho_fv);

    let mx = midpoint(d, p, ax, bx);
    let my = midpoint(d, p, ay, by);
    let ho_x_ty = equiv(d, p, ox, mx);
    let ho_y_ty = equiv(d, p, oy, my);
    let ho_x = d.and_left(ho_x_ty, ho_y_ty, ho);
    let ho_y = d.and_right(ho_x_ty, ho_y_ty, ho);

    // Hypothesis 2: dot(C-O,C-O) ~ dot(A-O,A-O).
    let sub_co = psub(d, p, pc, po);
    let sub_ao = psub(d, p, pa, po);
    let dot_coco = dotp(d, p, sub_co, sub_co);
    let dot_aoao = dotp(d, p, sub_ao, sub_ao);
    let h2_ty = equiv(d, p, dot_coco, dot_aoao);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    // pt_x := A - O, pt_y := O - C, pt_z := neg(pt_x) + pt_y, pt_w := pt_x + pt_y.
    let pt_x = psub(d, p, pa, po);
    let pt_y = psub(d, p, po, pc);
    let neg_pt_x = pneg(d, p, pt_x);
    let pt_z = padd(d, p, neg_pt_x, pt_y);
    let pt_w = padd(d, p, pt_x, pt_y);

    // Shared negated/compound coordinate terms.
    let n_cx = cneg(d, p, cx);
    let n_cy = cneg(d, p, cy);
    let n_ox = cneg(d, p, ox);
    let n_oy = cneg(d, p, oy);
    let ax_ox = cadd(d, p, ax, n_ox);
    let ay_oy = cadd(d, p, ay, n_oy);
    let ox_cx = cadd(d, p, ox, n_cx);
    let oy_cy = cadd(d, p, oy, n_cy);

    // claim1: A - C ~ (A-O) + (O-C).
    let ax_cx = cadd(d, p, ax, n_cx);
    let ax_ox_ox_cx = cadd(d, p, ax_ox, ox_cx);
    let claim1_x_ty = equiv(d, p, ax_cx, ax_ox_ox_cx);
    let claim1_x = telescope_scalar_proof(d, p, ax, ox, cx);
    let ay_cy = cadd(d, p, ay, n_cy);
    let ay_oy_oy_cy = cadd(d, p, ay_oy, oy_cy);
    let claim1_y_ty = equiv(d, p, ay_cy, ay_oy_oy_cy);
    let claim1_y = telescope_scalar_proof(d, p, ay, oy, cy);
    let claim1 = and_intro(d, p, claim1_x_ty, claim1_y_ty, claim1_x, claim1_y);

    // claim2: B - C ~ neg(A-O) + (O-C).
    let bx_cx = cadd(d, p, bx, n_cx);
    let neg_ax_ox = cneg(d, p, ax_ox);
    let claim2_x_rhs = cadd(d, p, neg_ax_ox, ox_cx);
    let claim2_x_ty = equiv(d, p, bx_cx, claim2_x_rhs);
    let claim2_x = telescope_neg_scalar_proof(d, p, ax, bx, ox, cx, ho_x);
    let by_cy = cadd(d, p, by, n_cy);
    let neg_ay_oy = cneg(d, p, ay_oy);
    let claim2_y_rhs = cadd(d, p, neg_ay_oy, oy_cy);
    let claim2_y_ty = equiv(d, p, by_cy, claim2_y_rhs);
    let claim2_y = telescope_neg_scalar_proof(d, p, ay, by, oy, cy, ho_y);
    let claim2 = and_intro(d, p, claim2_x_ty, claim2_y_ty, claim2_x, claim2_y);

    // dot(A-C,B-C) ~ dot(W,Z).
    let sub_ac = psub(d, p, pa, pc);
    let sub_bc = psub(d, p, pb, pc);
    let step1 = d.lemma(p.dot_congr, &[sub_ac, pt_w, sub_bc, pt_z, claim1, claim2]);
    let dot_wz = dotp(d, p, pt_w, pt_z);

    // dot(W,Z) ~ add(dot(X,Z))(dot(Y,Z))  [dot_add_left]
    let dot_xz = dotp(d, p, pt_x, pt_z);
    let dot_yz = dotp(d, p, pt_y, pt_z);
    let dal = d.lemma(p.dot_add_left, &[pt_x, pt_y, pt_z]); // Equiv(dot_wz, add dot_xz dot_yz)

    // dot(X,Z) ~ T1 + T2, T1 := neg(dot X X), T2 := dot(X,Y)
    let dot_xx = dotp(d, p, pt_x, pt_x);
    let dot_xy = dotp(d, p, pt_x, pt_y);
    let dot_yy = dotp(d, p, pt_y, pt_y);
    let t1 = cneg(d, p, dot_xx);
    let t2 = dot_xy;
    let t3 = cneg(d, p, dot_xy);
    let t4 = dot_yy;

    let dar_x = d.lemma(p.dot_add_right, &[pt_x, neg_pt_x, pt_y]); // Equiv(dot_xz, add(dot(X,-X))(dot(X,Y)))
    let dot_x_negx = dotp(d, p, pt_x, neg_pt_x);
    let comm_a = d.lemma(p.dot_comm, &[pt_x, neg_pt_x]); // Equiv(dot_x_negx, dot(-X,X))
    let dot_negx_x = dotp(d, p, neg_pt_x, pt_x);
    let dnl_a = d.lemma(p.dot_neg_left, &[pt_x, pt_x]); // Equiv(dot_negx_x, t1)
    let dot_x_negx_reduce = chain(d, p, dot_x_negx, &[(dot_negx_x, comm_a), (t1, dnl_a)]);
    let refl_t2 = refl(d, p, t2);
    let congr_a = d.lemma(
        creal.add_congr,
        &[dot_x_negx, t1, dot_xy, t2, dot_x_negx_reduce, refl_t2],
    );
    let mid_a = cadd(d, p, dot_x_negx, dot_xy);
    let t1_t2 = cadd(d, p, t1, t2);
    let dot_xz_reduce = chain(d, p, dot_xz, &[(mid_a, dar_x), (t1_t2, congr_a)]);

    // dot(Y,Z) ~ T3 + T4
    let dar_y = d.lemma(p.dot_add_right, &[pt_y, neg_pt_x, pt_y]); // Equiv(dot_yz, add(dot(Y,-X))(dot(Y,Y)))
    let dot_y_negx = dotp(d, p, pt_y, neg_pt_x);
    let comm_b = d.lemma(p.dot_comm, &[pt_y, neg_pt_x]); // Equiv(dot_y_negx, dot(-X,Y))
    let dot_negx_y = dotp(d, p, neg_pt_x, pt_y);
    let dnl_b = d.lemma(p.dot_neg_left, &[pt_x, pt_y]); // Equiv(dot_negx_y, t3)
    let dot_y_negx_reduce = chain(d, p, dot_y_negx, &[(dot_negx_y, comm_b), (t3, dnl_b)]);
    let refl_t4 = refl(d, p, t4);
    let congr_b = d.lemma(
        creal.add_congr,
        &[dot_y_negx, t3, dot_yy, t4, dot_y_negx_reduce, refl_t4],
    );
    let mid_b = cadd(d, p, dot_y_negx, dot_yy);
    let t3_t4 = cadd(d, p, t3, t4);
    let dot_yz_reduce = chain(d, p, dot_yz, &[(mid_b, dar_y), (t3_t4, congr_b)]);

    // dot(W,Z) ~ add(t1_t2)(t3_t4)
    let congr_combine = d.lemma(
        creal.add_congr,
        &[dot_xz, t1_t2, dot_yz, t3_t4, dot_xz_reduce, dot_yz_reduce],
    );
    let mid_ab_sum = cadd(d, p, dot_xz, dot_yz);
    let t1t2_t3t4 = cadd(d, p, t1_t2, t3_t4);
    let dot_wz_expand = chain(
        d,
        p,
        dot_wz,
        &[(mid_ab_sum, dal), (t1t2_t3t4, congr_combine)],
    );

    // (T1+T2)+(T3+T4) ~ T1+T4  [T3 = neg T2]
    let zero = czero(d, p);
    let t2_t3 = cadd(d, p, t2, t3);
    let an_t2 = d.lemma(creal.add_neg, &[t2]); // Equiv(t2_t3, zero)
    let refl_t4b = refl(d, p, t4);
    let congr_zero_t4 = d.lemma(creal.add_congr, &[t2_t3, zero, t4, t4, an_t2, refl_t4b]);
    let zero_t4 = cadd(d, p, zero, t4);
    let za_t4 = zero_add_proof(d, p, t4); // Equiv(zero_t4, t4)
    let t2_t3_t4 = cadd(d, p, t2_t3, t4);
    let t3_t4_full = cadd(d, p, t3, t4);
    let assoc_inner = d.lemma(creal.add_assoc, &[t2, t3, t4]); // Equiv(t2_t3_t4, add t2 t3_t4_full)
    let t2_t3t4 = cadd(d, p, t2, t3_t4_full);
    let assoc_inner_symm = symm(d, p, t2_t3_t4, t2_t3t4, assoc_inner); // Equiv(t2_t3t4, t2_t3_t4)
    let inner_reduce = chain(
        d,
        p,
        t2_t3t4,
        &[
            (t2_t3_t4, assoc_inner_symm),
            (zero_t4, congr_zero_t4),
            (t4, za_t4),
        ],
    );
    let refl_t1 = refl(d, p, t1);
    let congr_outer = d.lemma(
        creal.add_congr,
        &[t1, t1, t2_t3t4, t4, refl_t1, inner_reduce],
    );
    let t1_t2t3t4 = cadd(d, p, t1, t2_t3t4);
    let assoc_outer = d.lemma(creal.add_assoc, &[t1, t2, t3_t4]); // Equiv(t1t2_t3t4, t1_t2t3t4)
    let t1_t4 = cadd(d, p, t1, t4);
    let cancel_middle = chain(
        d,
        p,
        t1t2_t3t4,
        &[(t1_t2t3t4, assoc_outer), (t1_t4, congr_outer)],
    );

    // dot(Y,Y) ~ dot(X,X), via hypothesis 2 and O-C ~ neg(C-O).
    let cx_ox = cadd(d, p, cx, n_ox);
    let cy_oy = cadd(d, p, cy, n_oy);
    let neg_cx_ox = cneg(d, p, cx_ox);
    let neg_cy_oy = cneg(d, p, cy_oy);
    let nsc_x = {
        let inner = neg_sub_comm_scalar_proof(d, p, cx, ox); // Equiv(neg_cx_ox, ox_cx)
        symm(d, p, neg_cx_ox, ox_cx, inner)
    }; // Equiv(ox_cx, neg_cx_ox)
    let nsc_y = {
        let inner = neg_sub_comm_scalar_proof(d, p, cy, oy); // Equiv(neg_cy_oy, oy_cy)
        symm(d, p, neg_cy_oy, oy_cy, inner)
    };
    let neg_sub_co = pneg(d, p, sub_co);
    let nsc_x_ty = equiv(d, p, ox_cx, neg_cx_ox);
    let nsc_y_ty = equiv(d, p, oy_cy, neg_cy_oy);
    let neg_sub_comm_point = and_intro(d, p, nsc_x_ty, nsc_y_ty, nsc_x, nsc_y);
    // neg_sub_comm_point : CPoint.Equiv pt_y neg_sub_co

    let dyy_congr = d.lemma(
        p.dot_congr,
        &[
            pt_y,
            neg_sub_co,
            pt_y,
            neg_sub_co,
            neg_sub_comm_point,
            neg_sub_comm_point,
        ],
    ); // Equiv(dot_yy, dot(neg_sub_co, neg_sub_co))
    let dot_negsubco_negsubco = dotp(d, p, neg_sub_co, neg_sub_co);
    let dnn = dot_neg_neg_proof(d, p, sub_co); // Equiv(dot(neg sub_co, neg sub_co), dot_coco)
    let dot_yy_reduce = chain(
        d,
        p,
        dot_yy,
        &[
            (dot_negsubco_negsubco, dyy_congr),
            (dot_coco, dnn),
            (dot_aoao, h2),
        ],
    );
    // dot_yy_reduce : Equiv(dot_yy, dot_aoao) = Equiv(dot_yy, dot_xx) since sub_ao == pt_x

    // T1 + T4 ~ T1 + dot_xx ~ zero
    let refl_t1b = refl(d, p, t1);
    let congr_final = d.lemma(
        creal.add_congr,
        &[t1, t1, t4, dot_xx, refl_t1b, dot_yy_reduce],
    );
    let t1_dotxx = cadd(d, p, t1, dot_xx);
    let cancel_final = neg_add_cancel_proof(d, p, dot_xx); // Equiv(add(neg dot_xx) dot_xx, zero) = Equiv(t1_dotxx, zero)

    let sub_ac_bc_dot = dotp(d, p, sub_ac, sub_bc);
    let final_proof = chain(
        d,
        p,
        sub_ac_bc_dot,
        &[
            (dot_wz, step1),
            (t1t2_t3t4, dot_wz_expand),
            (t1_t4, cancel_middle),
            (t1_dotxx, congr_final),
            (zero, cancel_final),
        ],
    );

    let concl = equiv(d, p, sub_ac_bc_dot, zero);
    let ty_body = {
        let inner = d.arrow(h2_ty, concl);
        d.arrow(ho_ty, inner)
    };
    let ty = {
        let w4 = d.pi_fv(o_fv, point, ty_body);
        let w3 = d.pi_fv(c_fv, point, w4);
        let w2 = d.pi_fv(b_fv, point, w3);
        d.pi_fv(a_fv, point, w2)
    };
    let value = {
        let inner = d.lam_fv(h2_fv, h2_ty, final_proof);
        let with_ho = d.lam_fv(ho_fv, ho_ty, inner);
        let w4 = d.lam_fv(o_fv, point, with_ho);
        let w3 = d.lam_fv(c_fv, point, w4);
        let w2 = d.lam_fv(b_fv, point, w3);
        d.lam_fv(a_fv, point, w2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.thales,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod creal_point_tests;
